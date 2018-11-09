#include "config.h"
#include "crypto/bn.h"
#include "tl-parser/portable_endian.h"
#include "tgl.h"
#include "tools.h"
#include "mtproto-utils.h"

static unsigned long long gcd (unsigned long long a, unsigned long long b) {
  return b ? gcd (b, a % b) : a;
}

static int check_prime (struct tgl_state *TLS, TGLC_bn *p) {
  int r = TGLC_bn_is_prime (p, /* "use default" */ 0, 0, TLS->TGLC_bn_ctx, 0);
  ensure (r >= 0);
  return r;
}


// Complete set of checks see at https://core.telegram.org/mtproto/security_guidelines


// Checks that (p,g) is acceptable pair for DH
int tglmp_check_DH_params (struct tgl_state *TLS, TGLC_bn *p, int g) {
  if (g < 2 || g > 7) { return -1; }
  if (TGLC_bn_num_bits (p) != 2048) { return -1; }

  TGLC_bn *t = TGLC_bn_new ();

  TGLC_bn *dh_g = TGLC_bn_new ();

  ensure (TGLC_bn_set_word (dh_g, 4 * g));
  ensure (TGLC_bn_mod (t, p, dh_g, TLS->TGLC_bn_ctx));
  int x = TGLC_bn_get_word (t);
  assert (x >= 0 && x < 4 * g);

  TGLC_bn_free (dh_g);

  int res = 0;
  switch (g) {
  case 2:
    if (x != 7) { res = -1; }
    break;
  case 3:
    if (x % 3 != 2) { res = -1; }
    break;
  case 4:
    break;
  case 5:
    if (x % 5 != 1 && x % 5 != 4) { res = -1; }
    break;
  case 6:
    if (x != 19 && x != 23) { res = -1; }
    break;
  case 7:
    if (x % 7 != 3 && x % 7 != 5 && x % 7 != 6) { res = -1; }
    break;
  }

  if (res < 0 || !check_prime (TLS, p)) {
    TGLC_bn_free (t);
    return -1;
  }

  TGLC_bn *b = TGLC_bn_new ();
  ensure (TGLC_bn_set_word (b, 2));
  ensure (TGLC_bn_div (t, 0, p, b, TLS->TGLC_bn_ctx));
  if (!check_prime (TLS, t)) {
    res = -1;
  }
  TGLC_bn_free (b);
  TGLC_bn_free (t);
  return res;
}

// checks that g_a is acceptable for DH
int tglmp_check_g_a (struct tgl_state *TLS, TGLC_bn *p, TGLC_bn *g_a) {
  if (TGLC_bn_num_bytes (g_a) > 256) {
    return -1;
  }
  if (TGLC_bn_num_bits (g_a) < 2048 - 64) {
    return -1;
  }
  if (TGLC_bn_cmp (p, g_a) <= 0) {
    return -1;
  }

  TGLC_bn *dif = TGLC_bn_new ();
  TGLC_bn_sub (dif, p, g_a);
  if (TGLC_bn_num_bits (dif) < 2048 - 64) {
    TGLC_bn_free (dif);
    return -1;
  }
  TGLC_bn_free (dif);
  return 0;
}

static unsigned long long BN2ull (TGLC_bn *b) {
  if (sizeof (unsigned long) == 8) {
    return TGLC_bn_get_word (b);
  } else if (sizeof (unsigned long long) == 8) {
    assert (0); // As long as nobody ever uses this code, assume it is broken.
    unsigned long long tmp;
    /* Here be dragons, but it should be okay due to be64toh */
    TGLC_bn_bn2bin (b, (unsigned char *) &tmp);
    return be64toh (tmp);
  } else {
    assert (0);
  }
}

static void ull2BN (TGLC_bn *b, unsigned long long val) {
  if (sizeof (unsigned long) == 8 || val < (1ll << 32)) {
    TGLC_bn_set_word (b, val);
  } else if (sizeof (unsigned long long) == 8) {
    assert (0); // As long as nobody ever uses this code, assume it is broken.
    htobe64(val);
    /* Here be dragons, but it should be okay due to htobe64 */
    TGLC_bn_bin2bn ((unsigned char *) &val, 8, b);
  } else {
    assert (0);
  }
}

int bn_factorize (TGLC_bn *pq, TGLC_bn *p, TGLC_bn *q) {
  // Should work in any case
  // Rewrite this code
  unsigned long long what = BN2ull (pq);

  int it = 0;

  unsigned long long g = 0;
  int i;
  for (i = 0; i < 3 || it < 1000; i++) {
    int q = ((rand() & 15) + 17) % what;
    unsigned long long x = (long long)rand () % (what - 1) + 1, y = x;
    int lim = 1 << (i + 18);
    int j;
    for (j = 1; j < lim; j++) {
      ++it;
      unsigned long long a = x, b = x, c = q;
      while (b) {
        if (b & 1) {
          c += a;
          if (c >= what) {
            c -= what;
          }
        }
        a += a;
        if (a >= what) {
          a -= what;
        }
        b >>= 1;
      }
      x = c;
      unsigned long long z = x < y ? what + x - y : x - y;
      g = gcd (z, what);
      if (g != 1) {
        break;
      }
      if (!(j & (j - 1))) {
        y = x;
      }
    }
    if (g > 1 && g < what) break;
  }

  assert (g > 1 && g < what);
  unsigned long long p1 = g;
  unsigned long long p2 = what / g;
  if (p1 > p2) {
    unsigned long long t = p1; p1 = p2; p2 = t;
  }
  ull2BN (p, p1);
  ull2BN (q, p2);
  return 0;
}

void tgl_code_to_str(const char *str, size_t maxlen, int code) {
  switch (code) {
    /* DH key exchange protocol data structures */
    case 0x60469778: snprintf((char *)str, maxlen, "req_pq"); break;
    case 0x05162463: snprintf((char *)str, maxlen, "resPQ"); break;
    case 0xd712e4be: snprintf((char *)str, maxlen, "req_DH_params"); break;
    case 0x83c95aec: snprintf((char *)str, maxlen, "p_q_inner_data"); break;
    case 0x3c6a84d4: snprintf((char *)str, maxlen, "p_q_inner_data_temp"); break;
    case 0xb5890dba: snprintf((char *)str, maxlen, "server_DH_inner_data"); break;
    case 0x79cb045d: snprintf((char *)str, maxlen, "server_DH_params_fail"); break;
    case 0xd0e8075c: snprintf((char *)str, maxlen, "server_DH_params_ok"); break;
    case 0xf5045f1f: snprintf((char *)str, maxlen, "set_client_DH_params"); break;
    case 0x6643b654: snprintf((char *)str, maxlen, "client_DH_inner_data"); break;
    case 0x3bcbf734: snprintf((char *)str, maxlen, "dh_gen_ok"); break;
    case 0x46dc1fb9: snprintf((char *)str, maxlen, "dh_gen_retry"); break;
    case 0xa69dae02: snprintf((char *)str, maxlen, "dh_gen_fail"); break;
    case 0x75a3f765: snprintf((char *)str, maxlen, "bind_auth_key_inner"); break;
    /* service messages */
    case 0xf35c6d01: snprintf((char *)str, maxlen, "rpc_result"); break;
    case 0x2144ca19: snprintf((char *)str, maxlen, "rpc_error"); break;
    case 0x73f1f8dc: snprintf((char *)str, maxlen, "msg_container"); break;
    case 0xe06046b2: snprintf((char *)str, maxlen, "msg_copy"); break;
    case 0x62d6b459: snprintf((char *)str, maxlen, "msgs_ack"); break;
    case 0xa7eff811: snprintf((char *)str, maxlen, "bad_msg_notification"); break;
    case 0xedab447b: snprintf((char *)str, maxlen, "bad_server_salt"); break;
    case 0xda69fb52: snprintf((char *)str, maxlen, "msgs_state_req"); break;
    case 0x04deb57d: snprintf((char *)str, maxlen, "msgs_state_info"); break;
    case 0x8cc0d131: snprintf((char *)str, maxlen, "msgs_all_info"); break;
    case 0x9ec20908: snprintf((char *)str, maxlen, "new_session_created"); break;
    case 0x7d861a08: snprintf((char *)str, maxlen, "msg_resend_req"); break;
    case 0x7abe77ec: snprintf((char *)str, maxlen, "ping"); break;
    case 0x347773c5: snprintf((char *)str, maxlen, "pong"); break;
    case 0xe7512126: snprintf((char *)str, maxlen, "destroy_session"); break;
    case 0xe22045fc: snprintf((char *)str, maxlen, "destroy_session_ok"); break;
    case 0x62d350c9: snprintf((char *)str, maxlen, "destroy_session_none"); break;
    case 0x9a6face8: snprintf((char *)str, maxlen, "destroy_sessions"); break;
    case 0xa8164668: snprintf((char *)str, maxlen, "destroy_sessions_res"); break;
    case 0xb921bd04: snprintf((char *)str, maxlen, "get_future_salts"); break;
    case 0x0949d9dc: snprintf((char *)str, maxlen, "future_salt"); break;
    case 0xae500895: snprintf((char *)str, maxlen, "future_salts"); break;
    case 0x58e4a740: snprintf((char *)str, maxlen, "rpc_drop_answer"); break;
    case 0x5e2ad36e: snprintf((char *)str, maxlen, "rpc_answer_unknown"); break;
    case 0xcd78e586: snprintf((char *)str, maxlen, "rpc_answer_dropped_running"); break;
    case 0xa43ad8b7: snprintf((char *)str, maxlen, "rpc_answer_dropped"); break;
    case 0x276d3ec6: snprintf((char *)str, maxlen, "msg_detailed_info"); break;
    case 0x809db6df: snprintf((char *)str, maxlen, "msg_new_detailed_info"); break;
    case 0xf3427b8c: snprintf((char *)str, maxlen, "ping_delay_disconnect"); break;
    case 0x3072cfa1: snprintf((char *)str, maxlen, "gzip_packed"); break;

    case 0x3cf4b1be: snprintf((char *)str, maxlen, "input_peer_notify_settings_old"); break;
    case 0xddbcd4a5: snprintf((char *)str, maxlen, "peer_notify_settings_old"); break;
    case 0x990d1493: snprintf((char *)str, maxlen, "user_profile_photo_old"); break;
    case 0x232d5905: snprintf((char *)str, maxlen, "config_old"); break;

    case 0xa8509bda: snprintf((char *)str, maxlen, "int"); break;
    case 0x22076cba: snprintf((char *)str, maxlen, "long"); break;
    case 0x2210c154: snprintf((char *)str, maxlen, "double"); break;
    case 0xb5286e24: snprintf((char *)str, maxlen, "string"); break;
    case 0x0ee1379f: snprintf((char *)str, maxlen, "bytes"); break;
    case 0x7d36c439: snprintf((char *)str, maxlen, "int128"); break;
    case 0xf2c798b3: snprintf((char *)str, maxlen, "int256"); break;
    case 0xbc799737: snprintf((char *)str, maxlen, "bool_false"); break;
    case 0x997275b5: snprintf((char *)str, maxlen, "bool_true"); break;
    case 0x3fedd339: snprintf((char *)str, maxlen, "true"); break;
    case 0x1cb5c415: snprintf((char *)str, maxlen, "vector"); break;
    case 0xc4b9f9bb: snprintf((char *)str, maxlen, "error"); break;
    case 0x56730bcc: snprintf((char *)str, maxlen, "null"); break;
    case 0x7f3b18ea: snprintf((char *)str, maxlen, "input_peer_empty"); break;
    case 0x7da07ec9: snprintf((char *)str, maxlen, "input_peer_self"); break;
    case 0x179be863: snprintf((char *)str, maxlen, "input_peer_chat"); break;
    case 0x7b8e7de6: snprintf((char *)str, maxlen, "input_peer_user"); break;
    case 0x20adaef8: snprintf((char *)str, maxlen, "input_peer_channel"); break;
    case 0xb98886cf: snprintf((char *)str, maxlen, "input_user_empty"); break;
    case 0xf7c1b13f: snprintf((char *)str, maxlen, "input_user_self"); break;
    case 0xd8292816: snprintf((char *)str, maxlen, "input_user"); break;
    case 0xf392b7f4: snprintf((char *)str, maxlen, "input_phone_contact"); break;
    case 0xf52ff27f: snprintf((char *)str, maxlen, "input_file"); break;
    case 0xfa4f0bb5: snprintf((char *)str, maxlen, "input_file_big"); break;
    case 0x9664f57f: snprintf((char *)str, maxlen, "input_media_empty"); break;
    case 0xf7aff1c0: snprintf((char *)str, maxlen, "input_media_uploaded_photo"); break;
    case 0xe9bfb4f3: snprintf((char *)str, maxlen, "input_media_photo"); break;
    case 0xf9c44144: snprintf((char *)str, maxlen, "input_media_geo_point"); break;
    case 0xa6e45987: snprintf((char *)str, maxlen, "input_media_contact"); break;
    case 0x82713fdf: snprintf((char *)str, maxlen, "input_media_uploaded_video"); break;
    case 0x7780ddf9: snprintf((char *)str, maxlen, "input_media_uploaded_thumb_video"); break;
    case 0x936a4ebd: snprintf((char *)str, maxlen, "input_media_video"); break;
    case 0x4e498cab: snprintf((char *)str, maxlen, "input_media_uploaded_audio"); break;
    case 0x89938781: snprintf((char *)str, maxlen, "input_media_audio"); break;
    case 0x1d89306d: snprintf((char *)str, maxlen, "input_media_uploaded_document"); break;
    case 0xad613491: snprintf((char *)str, maxlen, "input_media_uploaded_thumb_document"); break;
    case 0x1a77f29c: snprintf((char *)str, maxlen, "input_media_document"); break;
    case 0x2827a81a: snprintf((char *)str, maxlen, "input_media_venue"); break;
    case 0x4843b0fd: snprintf((char *)str, maxlen, "input_media_gif_external"); break;
    case 0x1ca48f57: snprintf((char *)str, maxlen, "input_chat_photo_empty"); break;
    case 0x94254732: snprintf((char *)str, maxlen, "input_chat_uploaded_photo"); break;
    case 0xb2e1bf08: snprintf((char *)str, maxlen, "input_chat_photo"); break;
    case 0xe4c123d6: snprintf((char *)str, maxlen, "input_geo_point_empty"); break;
    case 0xf3b7acc9: snprintf((char *)str, maxlen, "input_geo_point"); break;
    case 0x1cd7bf0d: snprintf((char *)str, maxlen, "input_photo_empty"); break;
    case 0xfb95c6c4: snprintf((char *)str, maxlen, "input_photo"); break;
    case 0x5508ec75: snprintf((char *)str, maxlen, "input_video_empty"); break;
    case 0xee579652: snprintf((char *)str, maxlen, "input_video"); break;
    case 0x14637196: snprintf((char *)str, maxlen, "input_file_location"); break;
    case 0x3d0364ec: snprintf((char *)str, maxlen, "input_video_file_location"); break;
    case 0xf5235d55: snprintf((char *)str, maxlen, "input_encrypted_file_location"); break;
    case 0x74dc404d: snprintf((char *)str, maxlen, "input_audio_file_location"); break;
    case 0x4e45abe9: snprintf((char *)str, maxlen, "input_document_file_location"); break;
    case 0xade6b004: snprintf((char *)str, maxlen, "input_photo_crop_auto"); break;
    case 0xd9915325: snprintf((char *)str, maxlen, "input_photo_crop"); break;
    case 0x770656a8: snprintf((char *)str, maxlen, "input_app_event"); break;
    case 0x9db1bc6d: snprintf((char *)str, maxlen, "peer_user"); break;
    case 0xbad0e5bb: snprintf((char *)str, maxlen, "peer_chat"); break;
    case 0xbddde532: snprintf((char *)str, maxlen, "peer_channel"); break;
    case 0xaa963b05: snprintf((char *)str, maxlen, "storage_file_unknown"); break;
    case 0x007efe0e: snprintf((char *)str, maxlen, "storage_file_jpeg"); break;
    case 0xcae1aadf: snprintf((char *)str, maxlen, "storage_file_gif"); break;
    case 0x0a4f63c0: snprintf((char *)str, maxlen, "storage_file_png"); break;
    case 0xae1e508d: snprintf((char *)str, maxlen, "storage_file_pdf"); break;
    case 0x528a0677: snprintf((char *)str, maxlen, "storage_file_mp3"); break;
    case 0x4b09ebbc: snprintf((char *)str, maxlen, "storage_file_mov"); break;
    case 0x40bc6f52: snprintf((char *)str, maxlen, "storage_file_partial"); break;
    case 0xb3cea0e4: snprintf((char *)str, maxlen, "storage_file_mp4"); break;
    case 0x1081464c: snprintf((char *)str, maxlen, "storage_file_webp"); break;
    case 0x7c596b46: snprintf((char *)str, maxlen, "file_location_unavailable"); break;
    case 0x53d69076: snprintf((char *)str, maxlen, "file_location"); break;
    case 0x200250ba: snprintf((char *)str, maxlen, "user_empty"); break;
    case 0xd10d979a: snprintf((char *)str, maxlen, "user"); break;
    case 0x4f11bae1: snprintf((char *)str, maxlen, "user_profile_photo_empty"); break;
    case 0xd559d8c8: snprintf((char *)str, maxlen, "user_profile_photo"); break;
    case 0x09d05049: snprintf((char *)str, maxlen, "user_status_empty"); break;
    case 0xedb93949: snprintf((char *)str, maxlen, "user_status_online"); break;
    case 0x008c703f: snprintf((char *)str, maxlen, "user_status_offline"); break;
    case 0xe26f42f1: snprintf((char *)str, maxlen, "user_status_recently"); break;
    case 0x07bf09fc: snprintf((char *)str, maxlen, "user_status_last_week"); break;
    case 0x77ebc742: snprintf((char *)str, maxlen, "user_status_last_month"); break;
    case 0x9ba2d800: snprintf((char *)str, maxlen, "chat_empty"); break;
    case 0xd91cdd54: snprintf((char *)str, maxlen, "chat"); break;
    case 0x07328bdb: snprintf((char *)str, maxlen, "chat_forbidden"); break;
    case 0x4b1b7506: snprintf((char *)str, maxlen, "channel"); break;
    case 0x2d85832c: snprintf((char *)str, maxlen, "channel_forbidden"); break;
    case 0x2e02a614: snprintf((char *)str, maxlen, "chat_full"); break;
    case 0x9e341ddf: snprintf((char *)str, maxlen, "channel_full"); break;
    case 0xc8d7493e: snprintf((char *)str, maxlen, "chat_participant"); break;
    case 0xda13538a: snprintf((char *)str, maxlen, "chat_participant_creator"); break;
    case 0xe2d6e436: snprintf((char *)str, maxlen, "chat_participant_admin"); break;
    case 0xfc900c2b: snprintf((char *)str, maxlen, "chat_participants_forbidden"); break;
    case 0x3f460fed: snprintf((char *)str, maxlen, "chat_participants"); break;
    case 0x37c1011c: snprintf((char *)str, maxlen, "chat_photo_empty"); break;
    case 0x6153276a: snprintf((char *)str, maxlen, "chat_photo"); break;
    case 0x83e5de54: snprintf((char *)str, maxlen, "message_empty"); break;
    case 0xc992e15c: snprintf((char *)str, maxlen, "message"); break;
    case 0xc06b9607: snprintf((char *)str, maxlen, "message_service"); break;
    case 0x3ded6320: snprintf((char *)str, maxlen, "message_media_empty"); break;
    case 0x3d8ce53d: snprintf((char *)str, maxlen, "message_media_photo"); break;
    case 0x5bcf1675: snprintf((char *)str, maxlen, "message_media_video"); break;
    case 0x56e0d474: snprintf((char *)str, maxlen, "message_media_geo"); break;
    case 0x5e7d2f39: snprintf((char *)str, maxlen, "message_media_contact"); break;
    case 0x9f84f49e: snprintf((char *)str, maxlen, "message_media_unsupported"); break;
    case 0xf3e02ea8: snprintf((char *)str, maxlen, "message_media_document"); break;
    case 0xc6b68300: snprintf((char *)str, maxlen, "message_media_audio"); break;
    case 0xa32dd600: snprintf((char *)str, maxlen, "message_media_web_page"); break;
    case 0x7912b71f: snprintf((char *)str, maxlen, "message_media_venue"); break;
    case 0xb6aef7b0: snprintf((char *)str, maxlen, "message_action_empty"); break;
    case 0xa6638b9a: snprintf((char *)str, maxlen, "message_action_chat_create"); break;
    case 0xb5a1ce5a: snprintf((char *)str, maxlen, "message_action_chat_edit_title"); break;
    case 0x7fcb13a8: snprintf((char *)str, maxlen, "message_action_chat_edit_photo"); break;
    case 0x95e3fbef: snprintf((char *)str, maxlen, "message_action_chat_delete_photo"); break;
    case 0x488a7337: snprintf((char *)str, maxlen, "message_action_chat_add_user"); break;
    case 0xb2ae9b0c: snprintf((char *)str, maxlen, "message_action_chat_delete_user"); break;
    case 0xf89cf5e8: snprintf((char *)str, maxlen, "message_action_chat_joined_by_link"); break;
    case 0x95d2ac92: snprintf((char *)str, maxlen, "message_action_channel_create"); break;
    case 0x51bdb021: snprintf((char *)str, maxlen, "message_action_chat_migrate_to"); break;
    case 0xb055eaee: snprintf((char *)str, maxlen, "message_action_channel_migrate_from"); break;
    case 0xc1dd804a: snprintf((char *)str, maxlen, "dialog"); break;
    case 0x5b8496b2: snprintf((char *)str, maxlen, "dialog_channel"); break;
    case 0x2331b22d: snprintf((char *)str, maxlen, "photo_empty"); break;
    case 0xcded42fe: snprintf((char *)str, maxlen, "photo"); break;
    case 0x0e17e23c: snprintf((char *)str, maxlen, "photo_size_empty"); break;
    case 0x77bfb61b: snprintf((char *)str, maxlen, "photo_size"); break;
    case 0xe9a734fa: snprintf((char *)str, maxlen, "photo_cached_size"); break;
    case 0xc10658a8: snprintf((char *)str, maxlen, "video_empty"); break;
    case 0xf72887d3: snprintf((char *)str, maxlen, "video"); break;
    case 0x1117dd5f: snprintf((char *)str, maxlen, "geo_point_empty"); break;
    case 0x2049d70c: snprintf((char *)str, maxlen, "geo_point"); break;
    case 0x811ea28e: snprintf((char *)str, maxlen, "auth_checked_phone"); break;
    case 0xefed51d9: snprintf((char *)str, maxlen, "auth_sent_code"); break;
    case 0xe325edcf: snprintf((char *)str, maxlen, "auth_sent_app_code"); break;
    case 0xff036af1: snprintf((char *)str, maxlen, "auth_authorization"); break;
    case 0xdf969c2d: snprintf((char *)str, maxlen, "auth_exported_authorization"); break;
    case 0xb8bc5b0c: snprintf((char *)str, maxlen, "input_notify_peer"); break;
    case 0x193b4417: snprintf((char *)str, maxlen, "input_notify_users"); break;
    case 0x4a95e84e: snprintf((char *)str, maxlen, "input_notify_chats"); break;
    case 0xa429b886: snprintf((char *)str, maxlen, "input_notify_all"); break;
    case 0xf03064d8: snprintf((char *)str, maxlen, "input_peer_notify_events_empty"); break;
    case 0xe86a2c74: snprintf((char *)str, maxlen, "input_peer_notify_events_all"); break;
    case 0x46a2ce98: snprintf((char *)str, maxlen, "input_peer_notify_settings"); break;
    case 0xadd53cb3: snprintf((char *)str, maxlen, "peer_notify_events_empty"); break;
    case 0x6d1ded88: snprintf((char *)str, maxlen, "peer_notify_events_all"); break;
    case 0x70a68512: snprintf((char *)str, maxlen, "peer_notify_settings_empty"); break;
    case 0x8d5e11ee: snprintf((char *)str, maxlen, "peer_notify_settings"); break;
    case 0xccb03657: snprintf((char *)str, maxlen, "wall_paper"); break;
    case 0x63117f24: snprintf((char *)str, maxlen, "wall_paper_solid"); break;
    case 0x58dbcab8: snprintf((char *)str, maxlen, "input_report_reason_spam"); break;
    case 0x1e22c78d: snprintf((char *)str, maxlen, "input_report_reason_violence"); break;
    case 0x2e59d922: snprintf((char *)str, maxlen, "input_report_reason_pornography"); break;
    case 0xe1746d0a: snprintf((char *)str, maxlen, "input_report_reason_other"); break;
    case 0x5a89ac5b: snprintf((char *)str, maxlen, "user_full"); break;
    case 0xf911c994: snprintf((char *)str, maxlen, "contact"); break;
    case 0xd0028438: snprintf((char *)str, maxlen, "imported_contact"); break;
    case 0x561bc879: snprintf((char *)str, maxlen, "contact_blocked"); break;
    case 0x3de191a1: snprintf((char *)str, maxlen, "contact_suggested"); break;
    case 0xd3680c61: snprintf((char *)str, maxlen, "contact_status"); break;
    case 0x3ace484c: snprintf((char *)str, maxlen, "contacts_link"); break;
    case 0xb74ba9d2: snprintf((char *)str, maxlen, "contacts_contacts_not_modified"); break;
    case 0x6f8b8cb2: snprintf((char *)str, maxlen, "contacts_contacts"); break;
    case 0xad524315: snprintf((char *)str, maxlen, "contacts_imported_contacts"); break;
    case 0x1c138d15: snprintf((char *)str, maxlen, "contacts_blocked"); break;
    case 0x900802a1: snprintf((char *)str, maxlen, "contacts_blocked_slice"); break;
    case 0x5649dcc5: snprintf((char *)str, maxlen, "contacts_suggested"); break;
    case 0x15ba6c40: snprintf((char *)str, maxlen, "messages_dialogs"); break;
    case 0x71e094f3: snprintf((char *)str, maxlen, "messages_dialogs_slice"); break;
    case 0x8c718e87: snprintf((char *)str, maxlen, "messages_messages"); break;
    case 0x0b446ae3: snprintf((char *)str, maxlen, "messages_messages_slice"); break;
    case 0xbc0f17bc: snprintf((char *)str, maxlen, "messages_channel_messages"); break;
    case 0x64ff9fd5: snprintf((char *)str, maxlen, "messages_chats"); break;
    case 0xe5d7d19c: snprintf((char *)str, maxlen, "messages_chat_full"); break;
    case 0xb45c69d1: snprintf((char *)str, maxlen, "messages_affected_history"); break;
    case 0x57e2f66c: snprintf((char *)str, maxlen, "input_messages_filter_empty"); break;
    case 0x9609a51c: snprintf((char *)str, maxlen, "input_messages_filter_photos"); break;
    case 0x9fc00e65: snprintf((char *)str, maxlen, "input_messages_filter_video"); break;
    case 0x56e9f0e4: snprintf((char *)str, maxlen, "input_messages_filter_photo_video"); break;
    case 0xd95e73bb: snprintf((char *)str, maxlen, "input_messages_filter_photo_video_documents"); break;
    case 0x9eddf188: snprintf((char *)str, maxlen, "input_messages_filter_document"); break;
    case 0xcfc87522: snprintf((char *)str, maxlen, "input_messages_filter_audio"); break;
    case 0x5afbf764: snprintf((char *)str, maxlen, "input_messages_filter_audio_documents"); break;
    case 0x7ef0dd87: snprintf((char *)str, maxlen, "input_messages_filter_url"); break;
    case 0xffc86587: snprintf((char *)str, maxlen, "input_messages_filter_gif"); break;
    case 0x1f2b0afd: snprintf((char *)str, maxlen, "update_new_message"); break;
    case 0x4e90bfd6: snprintf((char *)str, maxlen, "update_message_i_d"); break;
    case 0xa20db0e5: snprintf((char *)str, maxlen, "update_delete_messages"); break;
    case 0x5c486927: snprintf((char *)str, maxlen, "update_user_typing"); break;
    case 0x9a65ea1f: snprintf((char *)str, maxlen, "update_chat_user_typing"); break;
    case 0x07761198: snprintf((char *)str, maxlen, "update_chat_participants"); break;
    case 0x1bfbd823: snprintf((char *)str, maxlen, "update_user_status"); break;
    case 0xa7332b73: snprintf((char *)str, maxlen, "update_user_name"); break;
    case 0x95313b0c: snprintf((char *)str, maxlen, "update_user_photo"); break;
    case 0x2575bbb9: snprintf((char *)str, maxlen, "update_contact_registered"); break;
    case 0x9d2e67c5: snprintf((char *)str, maxlen, "update_contact_link"); break;
    case 0x8f06529a: snprintf((char *)str, maxlen, "update_new_authorization"); break;
    case 0x12bcbd9a: snprintf((char *)str, maxlen, "update_new_encrypted_message"); break;
    case 0x1710f156: snprintf((char *)str, maxlen, "update_encrypted_chat_typing"); break;
    case 0xb4a2e88d: snprintf((char *)str, maxlen, "update_encryption"); break;
    case 0x38fe25b7: snprintf((char *)str, maxlen, "update_encrypted_messages_read"); break;
    case 0xea4b0e5c: snprintf((char *)str, maxlen, "update_chat_participant_add"); break;
    case 0x6e5f8c22: snprintf((char *)str, maxlen, "update_chat_participant_delete"); break;
    case 0x8e5e9873: snprintf((char *)str, maxlen, "update_dc_options"); break;
    case 0x80ece81a: snprintf((char *)str, maxlen, "update_user_blocked"); break;
    case 0xbec268ef: snprintf((char *)str, maxlen, "update_notify_settings"); break;
    case 0x382dd3e4: snprintf((char *)str, maxlen, "update_service_notification"); break;
    case 0xee3b272a: snprintf((char *)str, maxlen, "update_privacy"); break;
    case 0x12b9417b: snprintf((char *)str, maxlen, "update_user_phone"); break;
    case 0x9961fd5c: snprintf((char *)str, maxlen, "update_read_history_inbox"); break;
    case 0x2f2f21bf: snprintf((char *)str, maxlen, "update_read_history_outbox"); break;
    case 0x7f891213: snprintf((char *)str, maxlen, "update_web_page"); break;
    case 0x68c13933: snprintf((char *)str, maxlen, "update_read_messages_contents"); break;
    case 0x60946422: snprintf((char *)str, maxlen, "update_channel_too_long"); break;
    case 0xb6d45656: snprintf((char *)str, maxlen, "update_channel"); break;
    case 0xc36c1e3c: snprintf((char *)str, maxlen, "update_channel_group"); break;
    case 0x62ba04d9: snprintf((char *)str, maxlen, "update_new_channel_message"); break;
    case 0x4214f37f: snprintf((char *)str, maxlen, "update_read_channel_inbox"); break;
    case 0xc37521c9: snprintf((char *)str, maxlen, "update_delete_channel_messages"); break;
    case 0x98a12b4b: snprintf((char *)str, maxlen, "update_channel_message_views"); break;
    case 0x6e947941: snprintf((char *)str, maxlen, "update_chat_admins"); break;
    case 0xb6901959: snprintf((char *)str, maxlen, "update_chat_participant_admin"); break;
    case 0x688a30aa: snprintf((char *)str, maxlen, "update_new_sticker_set"); break;
    case 0xf0dfb451: snprintf((char *)str, maxlen, "update_sticker_sets_order"); break;
    case 0x43ae3dec: snprintf((char *)str, maxlen, "update_sticker_sets"); break;
    case 0x9375341e: snprintf((char *)str, maxlen, "update_saved_gifs"); break;
    case 0xc01eea08: snprintf((char *)str, maxlen, "update_bot_inline_query"); break;
    case 0xa56c2a3e: snprintf((char *)str, maxlen, "updates_state"); break;
    case 0x5d75a138: snprintf((char *)str, maxlen, "updates_difference_empty"); break;
    case 0x00f49ca0: snprintf((char *)str, maxlen, "updates_difference"); break;
    case 0xa8fb1981: snprintf((char *)str, maxlen, "updates_difference_slice"); break;
    case 0xe317af7e: snprintf((char *)str, maxlen, "updates_too_long"); break;
    case 0x13e4deaa: snprintf((char *)str, maxlen, "update_short_message"); break;
    case 0x248afa62: snprintf((char *)str, maxlen, "update_short_chat_message"); break;
    case 0x78d4dec1: snprintf((char *)str, maxlen, "update_short"); break;
    case 0x725b04c3: snprintf((char *)str, maxlen, "updates_combined"); break;
    case 0x74ae4240: snprintf((char *)str, maxlen, "updates"); break;
    case 0x11f1331c: snprintf((char *)str, maxlen, "update_short_sent_message"); break;
    case 0x8dca6aa5: snprintf((char *)str, maxlen, "photos_photos"); break;
    case 0x15051f54: snprintf((char *)str, maxlen, "photos_photos_slice"); break;
    case 0x20212ca8: snprintf((char *)str, maxlen, "photos_photo"); break;
    case 0x096a18d5: snprintf((char *)str, maxlen, "upload_file"); break;
    case 0x05d8c6cc: snprintf((char *)str, maxlen, "dc_option"); break;
    case 0x06bbc5f8: snprintf((char *)str, maxlen, "config"); break;
    case 0x8e1a1775: snprintf((char *)str, maxlen, "nearest_dc"); break;
    case 0x8987f311: snprintf((char *)str, maxlen, "help_app_update"); break;
    case 0xc45a6536: snprintf((char *)str, maxlen, "help_no_app_update"); break;
    case 0x18cb9f78: snprintf((char *)str, maxlen, "help_invite_text"); break;
    case 0xab7ec0a0: snprintf((char *)str, maxlen, "encrypted_chat_empty"); break;
    case 0x3bf703dc: snprintf((char *)str, maxlen, "encrypted_chat_waiting"); break;
    case 0xc878527e: snprintf((char *)str, maxlen, "encrypted_chat_requested"); break;
    case 0xfa56ce36: snprintf((char *)str, maxlen, "encrypted_chat"); break;
    case 0x13d6dd27: snprintf((char *)str, maxlen, "encrypted_chat_discarded"); break;
    case 0xf141b5e1: snprintf((char *)str, maxlen, "input_encrypted_chat"); break;
    case 0xc21f497e: snprintf((char *)str, maxlen, "encrypted_file_empty"); break;
    case 0x4a70994c: snprintf((char *)str, maxlen, "encrypted_file"); break;
    case 0x1837c364: snprintf((char *)str, maxlen, "input_encrypted_file_empty"); break;
    case 0x64bd0306: snprintf((char *)str, maxlen, "input_encrypted_file_uploaded"); break;
    case 0x5a17b5e5: snprintf((char *)str, maxlen, "input_encrypted_file"); break;
    case 0x2dc173c8: snprintf((char *)str, maxlen, "input_encrypted_file_big_uploaded"); break;
    case 0xed18c118: snprintf((char *)str, maxlen, "encrypted_message"); break;
    case 0x23734b06: snprintf((char *)str, maxlen, "encrypted_message_service"); break;
    case 0xc0e24635: snprintf((char *)str, maxlen, "messages_dh_config_not_modified"); break;
    case 0x2c221edd: snprintf((char *)str, maxlen, "messages_dh_config"); break;
    case 0x560f8935: snprintf((char *)str, maxlen, "messages_sent_encrypted_message"); break;
    case 0x9493ff32: snprintf((char *)str, maxlen, "messages_sent_encrypted_file"); break;
    case 0xd95adc84: snprintf((char *)str, maxlen, "input_audio_empty"); break;
    case 0x77d440ff: snprintf((char *)str, maxlen, "input_audio"); break;
    case 0x72f0eaae: snprintf((char *)str, maxlen, "input_document_empty"); break;
    case 0x18798952: snprintf((char *)str, maxlen, "input_document"); break;
    case 0x586988d8: snprintf((char *)str, maxlen, "audio_empty"); break;
    case 0xf9e35055: snprintf((char *)str, maxlen, "audio"); break;
    case 0x36f8c871: snprintf((char *)str, maxlen, "document_empty"); break;
    case 0xf9a39f4f: snprintf((char *)str, maxlen, "document"); break;
    case 0x17c6b5f6: snprintf((char *)str, maxlen, "help_support"); break;
    case 0x9fd40bd8: snprintf((char *)str, maxlen, "notify_peer"); break;
    case 0xb4c83b4c: snprintf((char *)str, maxlen, "notify_users"); break;
    case 0xc007cec3: snprintf((char *)str, maxlen, "notify_chats"); break;
    case 0x74d07c60: snprintf((char *)str, maxlen, "notify_all"); break;
    case 0x16bf744e: snprintf((char *)str, maxlen, "send_message_typing_action"); break;
    case 0xfd5ec8f5: snprintf((char *)str, maxlen, "send_message_cancel_action"); break;
    case 0xa187d66f: snprintf((char *)str, maxlen, "send_message_record_video_action"); break;
    case 0xe9763aec: snprintf((char *)str, maxlen, "send_message_upload_video_action"); break;
    case 0xd52f73f7: snprintf((char *)str, maxlen, "send_message_record_audio_action"); break;
    case 0xf351d7ab: snprintf((char *)str, maxlen, "send_message_upload_audio_action"); break;
    case 0xd1d34a26: snprintf((char *)str, maxlen, "send_message_upload_photo_action"); break;
    case 0xaa0cd9e4: snprintf((char *)str, maxlen, "send_message_upload_document_action"); break;
    case 0x176f8ba1: snprintf((char *)str, maxlen, "send_message_geo_location_action"); break;
    case 0x628cbc6f: snprintf((char *)str, maxlen, "send_message_choose_contact_action"); break;
    case 0x1aa1f784: snprintf((char *)str, maxlen, "contacts_found"); break;
    case 0x4f96cb18: snprintf((char *)str, maxlen, "input_privacy_key_status_timestamp"); break;
    case 0xbc2eab30: snprintf((char *)str, maxlen, "privacy_key_status_timestamp"); break;
    case 0x0d09e07b: snprintf((char *)str, maxlen, "input_privacy_value_allow_contacts"); break;
    case 0x184b35ce: snprintf((char *)str, maxlen, "input_privacy_value_allow_all"); break;
    case 0x131cc67f: snprintf((char *)str, maxlen, "input_privacy_value_allow_users"); break;
    case 0x0ba52007: snprintf((char *)str, maxlen, "input_privacy_value_disallow_contacts"); break;
    case 0xd66b66c9: snprintf((char *)str, maxlen, "input_privacy_value_disallow_all"); break;
    case 0x90110467: snprintf((char *)str, maxlen, "input_privacy_value_disallow_users"); break;
    case 0xfffe1bac: snprintf((char *)str, maxlen, "privacy_value_allow_contacts"); break;
    case 0x65427b82: snprintf((char *)str, maxlen, "privacy_value_allow_all"); break;
    case 0x4d5bbe0c: snprintf((char *)str, maxlen, "privacy_value_allow_users"); break;
    case 0xf888fa1a: snprintf((char *)str, maxlen, "privacy_value_disallow_contacts"); break;
    case 0x8b73e763: snprintf((char *)str, maxlen, "privacy_value_disallow_all"); break;
    case 0x0c7f49b7: snprintf((char *)str, maxlen, "privacy_value_disallow_users"); break;
    case 0x554abb6f: snprintf((char *)str, maxlen, "account_privacy_rules"); break;
    case 0xb8d0afdf: snprintf((char *)str, maxlen, "account_days_t_t_l"); break;
    case 0xa4f58c4c: snprintf((char *)str, maxlen, "account_sent_change_phone_code"); break;
    case 0x6c37c15c: snprintf((char *)str, maxlen, "document_attribute_image_size"); break;
    case 0x11b58939: snprintf((char *)str, maxlen, "document_attribute_animated"); break;
    case 0x3a556302: snprintf((char *)str, maxlen, "document_attribute_sticker"); break;
    case 0x5910cccb: snprintf((char *)str, maxlen, "document_attribute_video"); break;
    case 0xded218e0: snprintf((char *)str, maxlen, "document_attribute_audio"); break;
    case 0x15590068: snprintf((char *)str, maxlen, "document_attribute_filename"); break;
    case 0xf1749a22: snprintf((char *)str, maxlen, "messages_stickers_not_modified"); break;
    case 0x8a8ecd32: snprintf((char *)str, maxlen, "messages_stickers"); break;
    case 0x12b299d4: snprintf((char *)str, maxlen, "sticker_pack"); break;
    case 0xe86602c3: snprintf((char *)str, maxlen, "messages_all_stickers_not_modified"); break;
    case 0xedfd405f: snprintf((char *)str, maxlen, "messages_all_stickers"); break;
    case 0xae636f24: snprintf((char *)str, maxlen, "disabled_feature"); break;
    case 0x84d19185: snprintf((char *)str, maxlen, "messages_affected_messages"); break;
    case 0x5f4f9247: snprintf((char *)str, maxlen, "contact_link_unknown"); break;
    case 0xfeedd3ad: snprintf((char *)str, maxlen, "contact_link_none"); break;
    case 0x268f3f59: snprintf((char *)str, maxlen, "contact_link_has_phone"); break;
    case 0xd502c2d0: snprintf((char *)str, maxlen, "contact_link_contact"); break;
    case 0xeb1477e8: snprintf((char *)str, maxlen, "web_page_empty"); break;
    case 0xc586da1c: snprintf((char *)str, maxlen, "web_page_pending"); break;
    case 0xca820ed7: snprintf((char *)str, maxlen, "web_page"); break;
    case 0x7bf2e6f6: snprintf((char *)str, maxlen, "authorization"); break;
    case 0x1250abde: snprintf((char *)str, maxlen, "account_authorizations"); break;
    case 0x96dabc18: snprintf((char *)str, maxlen, "account_no_password"); break;
    case 0x7c18141c: snprintf((char *)str, maxlen, "account_password"); break;
    case 0xb7b72ab3: snprintf((char *)str, maxlen, "account_password_settings"); break;
    case 0xbcfc532c: snprintf((char *)str, maxlen, "account_password_input_settings"); break;
    case 0x137948a5: snprintf((char *)str, maxlen, "auth_password_recovery"); break;
    case 0xa384b779: snprintf((char *)str, maxlen, "received_notify_message"); break;
    case 0x69df3769: snprintf((char *)str, maxlen, "chat_invite_empty"); break;
    case 0xfc2e05bc: snprintf((char *)str, maxlen, "chat_invite_exported"); break;
    case 0x5a686d7c: snprintf((char *)str, maxlen, "chat_invite_already"); break;
    case 0x93e99b60: snprintf((char *)str, maxlen, "chat_invite"); break;
    case 0xffb62b95: snprintf((char *)str, maxlen, "input_sticker_set_empty"); break;
    case 0x9de7a269: snprintf((char *)str, maxlen, "input_sticker_set_i_d"); break;
    case 0x861cc8a0: snprintf((char *)str, maxlen, "input_sticker_set_short_name"); break;
    case 0xcd303b41: snprintf((char *)str, maxlen, "sticker_set"); break;
    case 0xb60a24a6: snprintf((char *)str, maxlen, "messages_sticker_set"); break;
    case 0xc27ac8c7: snprintf((char *)str, maxlen, "bot_command"); break;
    case 0xbb2e37ce: snprintf((char *)str, maxlen, "bot_info_empty"); break;
    case 0x09cf585d: snprintf((char *)str, maxlen, "bot_info"); break;
    case 0xa2fa4880: snprintf((char *)str, maxlen, "keyboard_button"); break;
    case 0x77608b83: snprintf((char *)str, maxlen, "keyboard_button_row"); break;
    case 0xa03e5b85: snprintf((char *)str, maxlen, "reply_keyboard_hide"); break;
    case 0xf4108aa0: snprintf((char *)str, maxlen, "reply_keyboard_force_reply"); break;
    case 0x3502758c: snprintf((char *)str, maxlen, "reply_keyboard_markup"); break;
    case 0xaf7e0394: snprintf((char *)str, maxlen, "help_app_changelog_empty"); break;
    case 0x4668e6bd: snprintf((char *)str, maxlen, "help_app_changelog"); break;
    case 0xbb92ba95: snprintf((char *)str, maxlen, "message_entity_unknown"); break;
    case 0xfa04579d: snprintf((char *)str, maxlen, "message_entity_mention"); break;
    case 0x6f635b0d: snprintf((char *)str, maxlen, "message_entity_hashtag"); break;
    case 0x6cef8ac7: snprintf((char *)str, maxlen, "message_entity_bot_command"); break;
    case 0x6ed02538: snprintf((char *)str, maxlen, "message_entity_url"); break;
    case 0x64e475c2: snprintf((char *)str, maxlen, "message_entity_email"); break;
    case 0xbd610bc9: snprintf((char *)str, maxlen, "message_entity_bold"); break;
    case 0x826f8b60: snprintf((char *)str, maxlen, "message_entity_italic"); break;
    case 0x28a20571: snprintf((char *)str, maxlen, "message_entity_code"); break;
    case 0x73924be0: snprintf((char *)str, maxlen, "message_entity_pre"); break;
    case 0x76a6d327: snprintf((char *)str, maxlen, "message_entity_text_url"); break;
    case 0xee8c1e86: snprintf((char *)str, maxlen, "input_channel_empty"); break;
    case 0xafeb712e: snprintf((char *)str, maxlen, "input_channel"); break;
    case 0x7f077ad9: snprintf((char *)str, maxlen, "contacts_resolved_peer"); break;
    case 0x0ae30253: snprintf((char *)str, maxlen, "message_range"); break;
    case 0xe8346f53: snprintf((char *)str, maxlen, "message_group"); break;
    case 0x3e11affb: snprintf((char *)str, maxlen, "updates_channel_difference_empty"); break;
    case 0x5e167646: snprintf((char *)str, maxlen, "updates_channel_difference_too_long"); break;
    case 0x2064674e: snprintf((char *)str, maxlen, "updates_channel_difference"); break;
    case 0x94d42ee7: snprintf((char *)str, maxlen, "channel_messages_filter_empty"); break;
    case 0xcd77d957: snprintf((char *)str, maxlen, "channel_messages_filter"); break;
    case 0xfa01232e: snprintf((char *)str, maxlen, "channel_messages_filter_collapsed"); break;
    case 0x15ebac1d: snprintf((char *)str, maxlen, "channel_participant"); break;
    case 0xa3289a6d: snprintf((char *)str, maxlen, "channel_participant_self"); break;
    case 0x91057fef: snprintf((char *)str, maxlen, "channel_participant_moderator"); break;
    case 0x98192d61: snprintf((char *)str, maxlen, "channel_participant_editor"); break;
    case 0x8cc5e69a: snprintf((char *)str, maxlen, "channel_participant_kicked"); break;
    case 0xe3e2e1f9: snprintf((char *)str, maxlen, "channel_participant_creator"); break;
    case 0xde3f3c79: snprintf((char *)str, maxlen, "channel_participants_recent"); break;
    case 0xb4608969: snprintf((char *)str, maxlen, "channel_participants_admins"); break;
    case 0x3c37bb7a: snprintf((char *)str, maxlen, "channel_participants_kicked"); break;
    case 0xb0d1865b: snprintf((char *)str, maxlen, "channel_participants_bots"); break;
    case 0xb285a0c6: snprintf((char *)str, maxlen, "channel_role_empty"); break;
    case 0x9618d975: snprintf((char *)str, maxlen, "channel_role_moderator"); break;
    case 0x820bfe8c: snprintf((char *)str, maxlen, "channel_role_editor"); break;
    case 0xf56ee2a8: snprintf((char *)str, maxlen, "channels_channel_participants"); break;
    case 0xd0d9b163: snprintf((char *)str, maxlen, "channels_channel_participant"); break;
    case 0xf1ee3e90: snprintf((char *)str, maxlen, "help_terms_of_service"); break;
    case 0x162ecc1f: snprintf((char *)str, maxlen, "found_gif"); break;
    case 0x9c750409: snprintf((char *)str, maxlen, "found_gif_cached"); break;
    case 0x450a1c0a: snprintf((char *)str, maxlen, "messages_found_gifs"); break;
    case 0xe8025ca2: snprintf((char *)str, maxlen, "messages_saved_gifs_not_modified"); break;
    case 0x2e0709a5: snprintf((char *)str, maxlen, "messages_saved_gifs"); break;
    case 0x2e43e587: snprintf((char *)str, maxlen, "input_bot_inline_message_media_auto"); break;
    case 0xadf0df71: snprintf((char *)str, maxlen, "input_bot_inline_message_text"); break;
    case 0x2cbbe15a: snprintf((char *)str, maxlen, "input_bot_inline_result"); break;
    case 0xfc56e87d: snprintf((char *)str, maxlen, "bot_inline_message_media_auto"); break;
    case 0xa56197a9: snprintf((char *)str, maxlen, "bot_inline_message_text"); break;
    case 0xf897d33e: snprintf((char *)str, maxlen, "bot_inline_media_result_document"); break;
    case 0xc5528587: snprintf((char *)str, maxlen, "bot_inline_media_result_photo"); break;
    case 0x9bebaeb9: snprintf((char *)str, maxlen, "bot_inline_result"); break;
    case 0x1170b0a3: snprintf((char *)str, maxlen, "messages_bot_results"); break;
    case 0xcb9f372d: snprintf((char *)str, maxlen, "invoke_after_msg"); break;
    case 0x3dc4b4f0: snprintf((char *)str, maxlen, "invoke_after_msgs"); break;
    case 0x69796de9: snprintf((char *)str, maxlen, "init_connection"); break;
    case 0xda9b0d0d: snprintf((char *)str, maxlen, "invoke_with_layer"); break;
    case 0xbf9459b7: snprintf((char *)str, maxlen, "invoke_without_updates"); break;
    case 0x6fe51dfb: snprintf((char *)str, maxlen, "auth_check_phone"); break;
    case 0x768d5f4d: snprintf((char *)str, maxlen, "auth_send_code"); break;
    case 0x03c51564: snprintf((char *)str, maxlen, "auth_send_call"); break;
    case 0x1b067634: snprintf((char *)str, maxlen, "auth_sign_up"); break;
    case 0xbcd51581: snprintf((char *)str, maxlen, "auth_sign_in"); break;
    case 0x5717da40: snprintf((char *)str, maxlen, "auth_log_out"); break;
    case 0x9fab0d1a: snprintf((char *)str, maxlen, "auth_reset_authorizations"); break;
    case 0x771c1d97: snprintf((char *)str, maxlen, "auth_send_invites"); break;
    case 0xe5bfffcd: snprintf((char *)str, maxlen, "auth_export_authorization"); break;
    case 0xe3ef9613: snprintf((char *)str, maxlen, "auth_import_authorization"); break;
    case 0xcdd42a05: snprintf((char *)str, maxlen, "auth_bind_temp_auth_key"); break;
    case 0x0da9f3e8: snprintf((char *)str, maxlen, "auth_send_sms"); break;
    case 0x67a3ff2c: snprintf((char *)str, maxlen, "auth_import_bot_authorization"); break;
    case 0x0a63011e: snprintf((char *)str, maxlen, "auth_check_password"); break;
    case 0xd897bc66: snprintf((char *)str, maxlen, "auth_request_password_recovery"); break;
    case 0x4ea56e92: snprintf((char *)str, maxlen, "auth_recover_password"); break;
    case 0x446c712c: snprintf((char *)str, maxlen, "account_register_device"); break;
    case 0x65c55b40: snprintf((char *)str, maxlen, "account_unregister_device"); break;
    case 0x84be5b93: snprintf((char *)str, maxlen, "account_update_notify_settings"); break;
    case 0x12b3ad31: snprintf((char *)str, maxlen, "account_get_notify_settings"); break;
    case 0xdb7e1747: snprintf((char *)str, maxlen, "account_reset_notify_settings"); break;
    case 0xf0888d68: snprintf((char *)str, maxlen, "account_update_profile"); break;
    case 0x6628562c: snprintf((char *)str, maxlen, "account_update_status"); break;
    case 0xc04cfac2: snprintf((char *)str, maxlen, "account_get_wall_papers"); break;
    case 0xae189d5f: snprintf((char *)str, maxlen, "account_report_peer"); break;
    case 0x2714d86c: snprintf((char *)str, maxlen, "account_check_username"); break;
    case 0x3e0bdd7c: snprintf((char *)str, maxlen, "account_update_username"); break;
    case 0xdadbc950: snprintf((char *)str, maxlen, "account_get_privacy"); break;
    case 0xc9f81ce8: snprintf((char *)str, maxlen, "account_set_privacy"); break;
    case 0x418d4e0b: snprintf((char *)str, maxlen, "account_delete_account"); break;
    case 0x08fc711d: snprintf((char *)str, maxlen, "account_get_account_t_t_l"); break;
    case 0x2442485e: snprintf((char *)str, maxlen, "account_set_account_t_t_l"); break;
    case 0xa407a8f4: snprintf((char *)str, maxlen, "account_send_change_phone_code"); break;
    case 0x70c32edb: snprintf((char *)str, maxlen, "account_change_phone"); break;
    case 0x38df3532: snprintf((char *)str, maxlen, "account_update_device_locked"); break;
    case 0xe320c158: snprintf((char *)str, maxlen, "account_get_authorizations"); break;
    case 0xdf77f3bc: snprintf((char *)str, maxlen, "account_reset_authorization"); break;
    case 0x548a30f5: snprintf((char *)str, maxlen, "account_get_password"); break;
    case 0xbc8d11bb: snprintf((char *)str, maxlen, "account_get_password_settings"); break;
    case 0xfa7c4b86: snprintf((char *)str, maxlen, "account_update_password_settings"); break;
    case 0x0d91a548: snprintf((char *)str, maxlen, "users_get_users"); break;
    case 0xca30a5b1: snprintf((char *)str, maxlen, "users_get_full_user"); break;
    case 0xc4a353ee: snprintf((char *)str, maxlen, "contacts_get_statuses"); break;
    case 0x22c6aa08: snprintf((char *)str, maxlen, "contacts_get_contacts"); break;
    case 0xda30b32d: snprintf((char *)str, maxlen, "contacts_import_contacts"); break;
    case 0xcd773428: snprintf((char *)str, maxlen, "contacts_get_suggested"); break;
    case 0x8e953744: snprintf((char *)str, maxlen, "contacts_delete_contact"); break;
    case 0x59ab389e: snprintf((char *)str, maxlen, "contacts_delete_contacts"); break;
    case 0x332b49fc: snprintf((char *)str, maxlen, "contacts_block"); break;
    case 0xe54100bd: snprintf((char *)str, maxlen, "contacts_unblock"); break;
    case 0xf57c350f: snprintf((char *)str, maxlen, "contacts_get_blocked"); break;
    case 0x84e53737: snprintf((char *)str, maxlen, "contacts_export_card"); break;
    case 0x4fe196fe: snprintf((char *)str, maxlen, "contacts_import_card"); break;
    case 0x11f812d8: snprintf((char *)str, maxlen, "contacts_search"); break;
    case 0xf93ccba3: snprintf((char *)str, maxlen, "contacts_resolve_username"); break;
    case 0x4222fa74: snprintf((char *)str, maxlen, "messages_get_messages"); break;
    case 0x6b47f94d: snprintf((char *)str, maxlen, "messages_get_dialogs"); break;
    case 0x8a8ec2da: snprintf((char *)str, maxlen, "messages_get_history"); break;
    case 0xd4569248: snprintf((char *)str, maxlen, "messages_search"); break;
    case 0x0e306d3a: snprintf((char *)str, maxlen, "messages_read_history"); break;
    case 0xb7c13bd9: snprintf((char *)str, maxlen, "messages_delete_history"); break;
    case 0xa5f18925: snprintf((char *)str, maxlen, "messages_delete_messages"); break;
    case 0x05a954c0: snprintf((char *)str, maxlen, "messages_received_messages"); break;
    case 0xa3825e50: snprintf((char *)str, maxlen, "messages_set_typing"); break;
    case 0xfa88427a: snprintf((char *)str, maxlen, "messages_send_message"); break;
    case 0xc8f16791: snprintf((char *)str, maxlen, "messages_send_media"); break;
    case 0x708e0195: snprintf((char *)str, maxlen, "messages_forward_messages"); break;
    case 0xcf1592db: snprintf((char *)str, maxlen, "messages_report_spam"); break;
    case 0x3c6aa187: snprintf((char *)str, maxlen, "messages_get_chats"); break;
    case 0x3b831c66: snprintf((char *)str, maxlen, "messages_get_full_chat"); break;
    case 0xdc452855: snprintf((char *)str, maxlen, "messages_edit_chat_title"); break;
    case 0xca4c79d8: snprintf((char *)str, maxlen, "messages_edit_chat_photo"); break;
    case 0xf9a0aa09: snprintf((char *)str, maxlen, "messages_add_chat_user"); break;
    case 0xe0611f16: snprintf((char *)str, maxlen, "messages_delete_chat_user"); break;
    case 0x09cb126e: snprintf((char *)str, maxlen, "messages_create_chat"); break;
    case 0x33963bf9: snprintf((char *)str, maxlen, "messages_forward_message"); break;
    case 0xbf73f4da: snprintf((char *)str, maxlen, "messages_send_broadcast"); break;
    case 0x26cf8950: snprintf((char *)str, maxlen, "messages_get_dh_config"); break;
    case 0xf64daf43: snprintf((char *)str, maxlen, "messages_request_encryption"); break;
    case 0x3dbc0415: snprintf((char *)str, maxlen, "messages_accept_encryption"); break;
    case 0xedd923c5: snprintf((char *)str, maxlen, "messages_discard_encryption"); break;
    case 0x791451ed: snprintf((char *)str, maxlen, "messages_set_encrypted_typing"); break;
    case 0x7f4b690a: snprintf((char *)str, maxlen, "messages_read_encrypted_history"); break;
    case 0xa9776773: snprintf((char *)str, maxlen, "messages_send_encrypted"); break;
    case 0x9a901b66: snprintf((char *)str, maxlen, "messages_send_encrypted_file"); break;
    case 0x32d439a4: snprintf((char *)str, maxlen, "messages_send_encrypted_service"); break;
    case 0x55a5bb66: snprintf((char *)str, maxlen, "messages_received_queue"); break;
    case 0x36a73f77: snprintf((char *)str, maxlen, "messages_read_message_contents"); break;
    case 0xae22e045: snprintf((char *)str, maxlen, "messages_get_stickers"); break;
    case 0x1c9618b1: snprintf((char *)str, maxlen, "messages_get_all_stickers"); break;
    case 0x25223e24: snprintf((char *)str, maxlen, "messages_get_web_page_preview"); break;
    case 0x7d885289: snprintf((char *)str, maxlen, "messages_export_chat_invite"); break;
    case 0x3eadb1bb: snprintf((char *)str, maxlen, "messages_check_chat_invite"); break;
    case 0x6c50051c: snprintf((char *)str, maxlen, "messages_import_chat_invite"); break;
    case 0x2619a90e: snprintf((char *)str, maxlen, "messages_get_sticker_set"); break;
    case 0x7b30c3a6: snprintf((char *)str, maxlen, "messages_install_sticker_set"); break;
    case 0xf96e55de: snprintf((char *)str, maxlen, "messages_uninstall_sticker_set"); break;
    case 0xe6df7378: snprintf((char *)str, maxlen, "messages_start_bot"); break;
    case 0xc4c8a55d: snprintf((char *)str, maxlen, "messages_get_messages_views"); break;
    case 0xec8bd9e1: snprintf((char *)str, maxlen, "messages_toggle_chat_admins"); break;
    case 0xa9e69f2e: snprintf((char *)str, maxlen, "messages_edit_chat_admin"); break;
    case 0x15a3b8e3: snprintf((char *)str, maxlen, "messages_migrate_chat"); break;
    case 0x9e3cacb0: snprintf((char *)str, maxlen, "messages_search_global"); break;
    case 0x9fcfbc30: snprintf((char *)str, maxlen, "messages_reorder_sticker_sets"); break;
    case 0x338e2464: snprintf((char *)str, maxlen, "messages_get_document_by_hash"); break;
    case 0xbf9a776b: snprintf((char *)str, maxlen, "messages_search_gifs"); break;
    case 0x83bf3d52: snprintf((char *)str, maxlen, "messages_get_saved_gifs"); break;
    case 0x327a30cb: snprintf((char *)str, maxlen, "messages_save_gif"); break;
    case 0x9324600d: snprintf((char *)str, maxlen, "messages_get_inline_bot_results"); break;
    case 0x3f23ec12: snprintf((char *)str, maxlen, "messages_set_inline_bot_results"); break;
    case 0xb16e06fe: snprintf((char *)str, maxlen, "messages_send_inline_bot_result"); break;
    case 0xedd4882a: snprintf((char *)str, maxlen, "updates_get_state"); break;
    case 0x0a041495: snprintf((char *)str, maxlen, "updates_get_difference"); break;
    case 0xbb32d7c0: snprintf((char *)str, maxlen, "updates_get_channel_difference"); break;
    case 0xeef579a0: snprintf((char *)str, maxlen, "photos_update_profile_photo"); break;
    case 0xd50f9c88: snprintf((char *)str, maxlen, "photos_upload_profile_photo"); break;
    case 0x87cf7f2f: snprintf((char *)str, maxlen, "photos_delete_photos"); break;
    case 0x91cd32a8: snprintf((char *)str, maxlen, "photos_get_user_photos"); break;
    case 0xb304a621: snprintf((char *)str, maxlen, "upload_save_file_part"); break;
    case 0xe3a6cfb5: snprintf((char *)str, maxlen, "upload_get_file"); break;
    case 0xde7b673d: snprintf((char *)str, maxlen, "upload_save_big_file_part"); break;
    case 0xc4f9186b: snprintf((char *)str, maxlen, "help_get_config"); break;
    case 0x1fb33026: snprintf((char *)str, maxlen, "help_get_nearest_dc"); break;
    case 0xc812ac7e: snprintf((char *)str, maxlen, "help_get_app_update"); break;
    case 0x6f02f748: snprintf((char *)str, maxlen, "help_save_app_log"); break;
    case 0xa4a95186: snprintf((char *)str, maxlen, "help_get_invite_text"); break;
    case 0x9cdf08cd: snprintf((char *)str, maxlen, "help_get_support"); break;
    case 0x5bab7fb2: snprintf((char *)str, maxlen, "help_get_app_changelog"); break;
    case 0x37d78f83: snprintf((char *)str, maxlen, "help_get_terms_of_service"); break;
    case 0xa9d3d249: snprintf((char *)str, maxlen, "channels_get_dialogs"); break;
    case 0xddb929cb: snprintf((char *)str, maxlen, "channels_get_important_history"); break;
    case 0xcc104937: snprintf((char *)str, maxlen, "channels_read_history"); break;
    case 0x84c1fd4e: snprintf((char *)str, maxlen, "channels_delete_messages"); break;
    case 0xd10dd71b: snprintf((char *)str, maxlen, "channels_delete_user_history"); break;
    case 0xfe087810: snprintf((char *)str, maxlen, "channels_report_spam"); break;
    case 0x93d7b347: snprintf((char *)str, maxlen, "channels_get_messages"); break;
    case 0x24d98f92: snprintf((char *)str, maxlen, "channels_get_participants"); break;
    case 0x546dd7a6: snprintf((char *)str, maxlen, "channels_get_participant"); break;
    case 0x0a7f6bbb: snprintf((char *)str, maxlen, "channels_get_channels"); break;
    case 0x08736a09: snprintf((char *)str, maxlen, "channels_get_full_channel"); break;
    case 0xf4893d7f: snprintf((char *)str, maxlen, "channels_create_channel"); break;
    case 0x13e27f1e: snprintf((char *)str, maxlen, "channels_edit_about"); break;
    case 0xeb7611d0: snprintf((char *)str, maxlen, "channels_edit_admin"); break;
    case 0x566decd0: snprintf((char *)str, maxlen, "channels_edit_title"); break;
    case 0xf12e57c9: snprintf((char *)str, maxlen, "channels_edit_photo"); break;
    case 0xaaa29e88: snprintf((char *)str, maxlen, "channels_toggle_comments"); break;
    case 0x10e6bd2c: snprintf((char *)str, maxlen, "channels_check_username"); break;
    case 0x3514b3de: snprintf((char *)str, maxlen, "channels_update_username"); break;
    case 0x24b524c5: snprintf((char *)str, maxlen, "channels_join_channel"); break;
    case 0xf836aa95: snprintf((char *)str, maxlen, "channels_leave_channel"); break;
    case 0x199f3a6c: snprintf((char *)str, maxlen, "channels_invite_to_channel"); break;
    case 0xa672de14: snprintf((char *)str, maxlen, "channels_kick_from_channel"); break;
    case 0xc7560885: snprintf((char *)str, maxlen, "channels_export_invite"); break;
    case 0xc0111fe3: snprintf((char *)str, maxlen, "channels_delete_channel"); break;
    case 0x089f5c4a: snprintf((char *)str, maxlen, "decrypted_message_media_empty"); break;
    case 0x32798a8c: snprintf((char *)str, maxlen, "decrypted_message_media_photo"); break;
    case 0x35480a59: snprintf((char *)str, maxlen, "decrypted_message_media_geo_point"); break;
    case 0x588a0a97: snprintf((char *)str, maxlen, "decrypted_message_media_contact"); break;
    case 0xa1733aec: snprintf((char *)str, maxlen, "decrypted_message_action_set_message_t_t_l"); break;
    case 0xb095434b: snprintf((char *)str, maxlen, "decrypted_message_media_document"); break;
    case 0x0c4f40be: snprintf((char *)str, maxlen, "decrypted_message_action_read_messages"); break;
    case 0x65614304: snprintf((char *)str, maxlen, "decrypted_message_action_delete_messages"); break;
    case 0x8ac1f475: snprintf((char *)str, maxlen, "decrypted_message_action_screenshot_messages"); break;
    case 0x6719e45c: snprintf((char *)str, maxlen, "decrypted_message_action_flush_history"); break;
    case 0x204d3878: snprintf((char *)str, maxlen, "decrypted_message"); break;
    case 0x73164160: snprintf((char *)str, maxlen, "decrypted_message_service"); break;
    case 0x524a415d: snprintf((char *)str, maxlen, "decrypted_message_media_video"); break;
    case 0x57e0a9cb: snprintf((char *)str, maxlen, "decrypted_message_media_audio"); break;
    case 0x1be31789: snprintf((char *)str, maxlen, "decrypted_message_layer"); break;
    case 0x511110b0: snprintf((char *)str, maxlen, "decrypted_message_action_resend"); break;
    case 0xf3048883: snprintf((char *)str, maxlen, "decrypted_message_action_notify_layer"); break;
    case 0xccb27641: snprintf((char *)str, maxlen, "decrypted_message_action_typing"); break;
    case 0xf3c9611b: snprintf((char *)str, maxlen, "decrypted_message_action_request_key"); break;
    case 0x6fe1735b: snprintf((char *)str, maxlen, "decrypted_message_action_accept_key"); break;
    case 0xdd05ec6b: snprintf((char *)str, maxlen, "decrypted_message_action_abort_key"); break;
    case 0xec2e0b9b: snprintf((char *)str, maxlen, "decrypted_message_action_commit_key"); break;
    case 0xa82fdd63: snprintf((char *)str, maxlen, "decrypted_message_action_noop"); break;
    case 0xfa95b0dd: snprintf((char *)str, maxlen, "decrypted_message_media_external_document"); break;
    case 0x0377168f: snprintf((char *)str, maxlen, "binlog_encr_key"); break;
    case 0x7777bc74: snprintf((char *)str, maxlen, "binlog_peer_user"); break;
    case 0x6a48d586: snprintf((char *)str, maxlen, "binlog_peer_chat"); break;
    case 0xfdfabb06: snprintf((char *)str, maxlen, "binlog_peer_channel"); break;
    case 0x381af606: snprintf((char *)str, maxlen, "binlog_peer"); break;
    case 0x3b06de69: snprintf((char *)str, maxlen, "binlog_start"); break;
    case 0x71e8c156: snprintf((char *)str, maxlen, "binlog_auth_key"); break;
    case 0x9e83dbdc: snprintf((char *)str, maxlen, "binlog_default_dc"); break;
    case 0x26451bb5: snprintf((char *)str, maxlen, "binlog_dc_signed"); break;
    case 0xc6927307: snprintf((char *)str, maxlen, "binlog_dc_option"); break;
    case 0x68a870e8: snprintf((char *)str, maxlen, "binlog_our_id"); break;
    case 0xeaeb7826: snprintf((char *)str, maxlen, "binlog_set_dh_params"); break;
    case 0x2ca8c939: snprintf((char *)str, maxlen, "binlog_set_pts"); break;
    case 0xd95738ac: snprintf((char *)str, maxlen, "binlog_set_qts"); break;
    case 0x1d0f4b52: snprintf((char *)str, maxlen, "binlog_set_date"); break;
    case 0x6eeb2989: snprintf((char *)str, maxlen, "binlog_set_seq"); break;
    case 0xe7ccc164: snprintf((char *)str, maxlen, "binlog_peer_delete"); break;
    case 0x84977251: snprintf((char *)str, maxlen, "binlog_encr_chat"); break;
    case 0x9d49488d: snprintf((char *)str, maxlen, "binlog_encr_chat_exchange"); break;
    case 0x127cf2f9: snprintf((char *)str, maxlen, "binlog_user"); break;
    case 0x0a10aa92: snprintf((char *)str, maxlen, "binlog_chat"); break;
    case 0xa98a3d98: snprintf((char *)str, maxlen, "binlog_channel"); break;
    case 0x535475ea: snprintf((char *)str, maxlen, "binlog_chat_add_participant"); break;
    case 0x7dd1a1a2: snprintf((char *)str, maxlen, "binlog_chat_del_participant"); break;
    case 0x3c873416: snprintf((char *)str, maxlen, "binlog_set_msg_id"); break;
    case 0x847e77b1: snprintf((char *)str, maxlen, "binlog_message_delete"); break;
    case 0x427cfcdb: snprintf((char *)str, maxlen, "binlog_message_new"); break;
    case 0x6cf7cabc: snprintf((char *)str, maxlen, "binlog_message_encr_new"); break;
    case 0x6dd4d85f: snprintf((char *)str, maxlen, "binlog_msg_update"); break;
    case 0x83327955: snprintf((char *)str, maxlen, "binlog_reset_authorization"); break;
    case 0x4cee6ef3: snprintf((char *)str, maxlen, "decrypted_message_media_video_l12"); break;
    case 0x6080758f: snprintf((char *)str, maxlen, "decrypted_message_media_audio_l12"); break;
    case 0x03114739: snprintf((char *)str, maxlen, "update_msg_update"); break;
    case 0xc8c45a2a: snprintf((char *)str, maxlen, "message_media_photo_l27"); break;
    case 0xa2d24290: snprintf((char *)str, maxlen, "message_media_video_l27"); break;

    default:
      snprintf((char *)str, maxlen, "%x (unknown)", code);
      break;
  }
}
