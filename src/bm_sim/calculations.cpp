/* Copyright 2013-present Barefoot Networks, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*
 * Antonin Bas (antonin@barefootnetworks.com)
 *
 */

#include <bm/bm_sim/_assert.h>
#include <bm/bm_sim/calculations.h>
#include <bm/bm_sim/logger.h>
#include <bm/bm_sim/packet.h>
#include <bm/bm_sim/phv.h>

#include <netinet/in.h>

#include <algorithm>
#include <mutex>
#include <ostream>
#include <string>
#include <unordered_map>

#include "xxhash.h"
#include "crc_tables.h"
#include "extract.h"

namespace bm {

void
BufBuilder::push_back_field(header_id_t header, int field_offset) {
  field_t f = {header, field_offset};
  entries.emplace_back(f);
}

void
BufBuilder::push_back_constant(const ByteContainer &v, size_t nbits) {
  constant_t c = {v, nbits};
  entries.emplace_back(c);
}

void
BufBuilder::push_back_header(header_id_t header) {
  header_t h = {header};
  entries.emplace_back(h);
}

void
BufBuilder::append_payload() {
  with_payload = true;
}

struct BufBuilder::Deparse : public boost::static_visitor<> {
  Deparse(const PHV &phv, ByteContainer *buf, int init_offset = 0)
      : phv(phv), buf(buf), nbits(init_offset) { }

  char *extend(int more_bits) {
    int nbits_ = nbits + more_bits;
    buf->resize((nbits_ + 7) / 8, '\x00');
    char *ptr = buf->data() + (nbits / 8);
    nbits = nbits_;
    return ptr;
  }

  int get_offset() const {
    return nbits % 8;
  }

  void operator()(const field_t &f) {
    const Header &header = phv.get_header(f.header);
    if (!header.is_valid()) return;
    const Field &field = header.get_field(f.field_offset);
    // get_offset needs to be called before extend!
    const auto offset = get_offset();
    field.deparse(extend(field.get_nbits()), offset);
  }

  void operator()(const constant_t &c) {
    // get_offset needs to be called before extend!
    const auto offset = get_offset();
    extract::generic_deparse(&c.v[0], c.nbits, extend(c.nbits), offset);
  }

  void operator()(const header_t &h) {
    assert(get_offset() == 0);
    const Header &header = phv.get_header(h.header);
    if (header.is_valid()) {
      header.deparse(extend(header.get_nbytes_packet() * 8));
    }
  }

  Deparse(const Deparse &other) = delete;
  Deparse &operator=(const Deparse &other) = delete;

  Deparse(Deparse &&other) = delete;
  Deparse &operator=(Deparse &&other) = delete;

  const PHV &phv;
  ByteContainer *buf;
  int nbits{0};
};

void
BufBuilder::operator()(const Packet &pkt, ByteContainer *buf) const {
  buf->clear();
  const PHV *phv = pkt.get_phv();
  Deparse visitor(*phv, buf);
  std::for_each(entries.begin(), entries.end(),
                boost::apply_visitor(visitor));
  if (with_payload) {
    size_t curr = buf->size();
    size_t psize = pkt.get_data_size();
    buf->resize(curr + psize);
    std::copy(pkt.data(), pkt.data() + psize, buf->begin() + curr);
  }
}

namespace hash {

uint64_t xxh64(const char *buffer, size_t s) {
  return XXH64(buffer, s, 0);
}

}  // namespace hash

namespace {

/* This code was adapted from:
   http://www.barrgroup.com/Embedded-Systems/How-To/CRC-Calculation-C-Code */

template <typename T>
T reflect(T data, int nBits) {
  T reflection = static_cast<T>(0x00);
  int bit;

  // Reflect the data about the center bit.
  for (bit = 0; bit < nBits; ++bit) {
    // If the LSB bit is set, set the reflection of it.
    if (data & 0x01) {
      reflection |= (static_cast<T>(1) << ((nBits - 1) - bit));
    }
    data = (data >> 1);
  }

  return reflection;
}

struct xxh64 {
  uint64_t operator()(const char *buf, size_t len) const {
    return XXH64(buf, len, 0);
  }
};

struct crc16 {
  uint16_t operator()(const char *buf, size_t len) const {
    uint16_t remainder = 0x0000;
    uint16_t final_xor_value = 0x0000;
    for (unsigned int byte = 0; byte < len; byte++) {
      int data = reflect<uint16_t>(buf[byte], 8) ^ (remainder >> 8);
      remainder = table_crc16[data] ^ (remainder << 8);
    }
    return reflect<uint16_t>(remainder, 16) ^ final_xor_value;
  }
};

template <typename T>
struct crc_custom_init { };

// explicit template instantiation

// crc8

template <>
struct crc_custom_init<uint8_t> {
  static CustomCrcMgr<uint8_t>::crc_config_t config;
};

CustomCrcMgr<uint8_t>::crc_config_t crc_custom_init<uint8_t>::config =
{0x07, 0x00, 0x00, false, false};

// crc16

template <>
struct crc_custom_init<uint16_t> {
  static CustomCrcMgr<uint16_t>::crc_config_t config;
};

CustomCrcMgr<uint16_t>::crc_config_t crc_custom_init<uint16_t>::config =
{0x8005, 0x0000, 0x0000, true, true};

// crc32

template <>
struct crc_custom_init<uint32_t> {
  static CustomCrcMgr<uint32_t>::crc_config_t config;
};

CustomCrcMgr<uint32_t>::crc_config_t crc_custom_init<uint32_t>::config =
{0x04c11db7, 0xffffffff, 0xffffffff, true, true};

// crc64

template <>
struct crc_custom_init<uint64_t> {
  static CustomCrcMgr<uint64_t>::crc_config_t config;
};

CustomCrcMgr<uint64_t>::crc_config_t crc_custom_init<uint64_t>::config =
{0x000000000000001bULL, 0x0000000000000000ULL, 0x0000000000000000ULL,
true, true};

template <typename T>
struct crc_custom {
  static constexpr size_t width = sizeof(T) * 8;
  static constexpr size_t kTEntries = 256u;
  using crc_config_t = typename CustomCrcMgr<T>::crc_config_t;

  crc_custom() {
    config = crc_custom_init<T>::config;
    recompute_crc_table(config, crc_table);
  }

  T operator()(const char *buf, size_t len) const {
    // clearly not optimized (critical section may be made smaller), but we will
    // try to do better if needed
    std::unique_lock<std::mutex> lock(m);

    T remainder = config.initial_remainder;
    for (unsigned int byte = 0; byte < len; byte++) {
      unsigned char uchar = static_cast<unsigned char>(buf[byte]);
      int data = (config.data_reflected) ?
          reflect<T>(uchar, 8) ^ (remainder >> (width - 8)) :
          uchar ^ (remainder >> (width - 8));
      remainder = crc_table[data] ^ (remainder << 8);
    }
    return (config.remainder_reflected) ?
        reflect<T>(remainder, width) ^ config.final_xor_value :
        remainder ^ config.final_xor_value;
  }

  void update_config(const crc_config_t &new_config) {
    T crc_table_new[kTEntries];
    recompute_crc_table(new_config, crc_table_new);

    std::unique_lock<std::mutex> lock(m);
    config = new_config;
    std::memcpy(crc_table, crc_table_new, sizeof(crc_table));
  }

 private:
  void recompute_crc_table(const crc_config_t &new_config, T *new_table) {
    // Compute the remainder of each possible dividend
    for (size_t dividend = 0; dividend < kTEntries; dividend++) {
      // Start with the dividend followed by zeros
      T remainder = static_cast<T>(dividend) << (width - 8);
      // Perform modulo-2 division, a bit at a time
      for (unsigned char bit = 8; bit > 0; bit--) {
        // Try to divide the current data bit
        if (remainder & (static_cast<T>(1) << (width - 1))) {
          remainder = (remainder << 1) ^ new_config.polynomial;
        } else {
          remainder = (remainder << 1);
        }
      }

      // Compute the remainder of each possible dividend
      new_table[dividend] = remainder;
    }
  }

  T crc_table[kTEntries];
  crc_config_t config;
  mutable std::mutex m{};
};

struct crc32 {
  uint32_t operator()(const char *buf, size_t len) const {
    uint32_t remainder = 0xFFFFFFFF;
    uint32_t final_xor_value = 0xFFFFFFFF;
    for (unsigned int byte = 0; byte < len; byte++) {
      int data = reflect<uint32_t>(buf[byte], 8) ^ (remainder >> 24);
      remainder = table_crc32[data] ^ (remainder << 8);
    }
    return reflect<uint32_t>(remainder, 32) ^ final_xor_value;
  }
};

struct crcCCITT {
  uint16_t operator()(const char *buf, size_t len) const {
    uint16_t remainder = 0xFFFF;
    uint16_t final_xor_value = 0x0000;
    for (unsigned int byte = 0; byte < len; byte++) {
      int data = static_cast<unsigned char>(buf[byte]) ^ (remainder >> 8);
      remainder = table_crcCCITT[data] ^ (remainder << 8);
    }
    return remainder ^ final_xor_value;
  }
};

struct cksum16 {
  uint16_t operator()(const char *buf, size_t len) const {
    uint64_t sum = 0;
    const uint64_t *b = reinterpret_cast<const uint64_t *>(buf);
    uint32_t t1, t2;
    uint16_t t3, t4;
    const uint8_t *tail;
    /* Main loop - 8 bytes at a time */
    while (len >= sizeof(uint64_t)) {
      uint64_t s = *b++;
      sum += s;
      if (sum < s) sum++;
      len -= 8;
    }
    /* Handle tail less than 8-bytes long */
    tail = reinterpret_cast<const uint8_t *>(b);
    if (len & 4) {
      uint32_t s = *reinterpret_cast<const uint32_t *>(tail);
      sum += s;
      if (sum < s) sum++;
      tail += 4;
    }
    if (len & 2) {
      uint16_t s = *reinterpret_cast<const uint16_t *>(tail);
      sum += s;
      if (sum < s) sum++;
      tail += 2;
    }
    if (len & 1) {
      uint8_t s = *reinterpret_cast<const uint8_t *>(tail);
      sum += s;
      if (sum < s) sum++;
    }
    /* Fold down to 16 bits */
    t1 = sum;
    t2 = sum >> 32;
    t1 += t2;
    if (t1 < t2) t1++;
    t3 = t1;
    t4 = t1 >> 16;
    t3 += t4;
    if (t3 < t4) t3++;
    return ntohs(~t3);
  }
};

struct csum16 {
  uint16_t operator()(const char *buf, size_t len) const {
    return cksum16()(buf, len);
  }
};

struct identity {
  uint64_t operator()(const char *buf, size_t len) const {
    uint64_t res = 0ULL;
    for (size_t i = 0; i < std::min(sizeof(res), len); i++) {
      if (i > 0) res <<= 8;
      res += static_cast<uint8_t>(buf[i]);
    }
    return res;
  }
};

// This "hash" functor keeps an internal counter which is incremented by 1 every
// time it is called. It does not do any hashing but can be convenient to
// iterate through all possible scenari when a modulo is applied to the result
// of the hash (e.g. for action profile member selection).
// Different instances of the hash use different counters. As a remainder each
// instance can be executed from multiple threads (e.g. for traffic on different
// ports), thus the mutex. All the state is declared as "mutable" since we
// require that the functor be "const".
struct round_robin {
  uint64_t operator()(const char *buf, size_t len) const {
    _BM_UNUSED(buf);
    _BM_UNUSED(len);
    std::unique_lock<std::mutex> lock(m);
    return idx++;
  }

  mutable uint64_t idx{0};
  mutable std::mutex m{};
};

// Same as "round_robin" above but keeps an internal map to ensure that multiple
// calls to the functor with the same input yield the same result.
struct round_robin_consistent {
  uint64_t operator()(const char *buf, size_t len) const {
    std::unique_lock<std::mutex> lock(m);
    std::string hash(buf, len);
    auto p = hashes.emplace(hash, idx);
    // p.second == true <=> insertion took place
    return (p.second) ? (idx++) : p.first->second;
  }

  mutable uint64_t idx{0};
  mutable std::unordered_map<std::string, uint64_t> hashes;
  mutable std::mutex m{};
};

// EXTERN
#include <cstdint>
#include <cstring>

#define Nb 4
#define Nk 4        // The number of 32 bit words in a key.
#define Nr 10       // The number of rounds in AES Cipher.
#define AES_BLOCKLEN 16 //Block length in bytes AES is 128b block only
#define AES_KEYLEN 16   // Key length in bytes
#define AES_keyExpSize 176

#define Multiply(x, y)                                \
    (  ((y & 1) * x) ^                              \
       ((y>>1 & 1) * xtime(x)) ^                       \
       ((y>>2 & 1) * xtime(xtime(x))) ^                \
       ((y>>3 & 1) * xtime(xtime(xtime(x)))) ^         \
       ((y>>4 & 1) * xtime(xtime(xtime(xtime(x))))))   \

typedef uint8_t state_t[4][4];

class hmac {
private:
    struct AES_ctx
    {
        uint8_t RoundKey[AES_keyExpSize];
        uint8_t Iv[AES_BLOCKLEN];
    };

    uint8_t sbox[256] = {
        //0     1    2      3     4    5     6     7      8    9     A      B    C     D     E     F
        0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
        0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
        0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
        0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
        0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
        0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
        0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
        0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
        0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
        0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
        0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
        0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
        0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
        0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
        0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
        0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16 };

    uint8_t rsbox[256] = {
        0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
        0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
        0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
        0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
        0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
        0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
        0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
        0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
        0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
        0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
        0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
        0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
        0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
        0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
        0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
        0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d };

    // The round constant word array, Rcon[i], contains the values given by
    // x to the power (i-1) being powers of x (x is denoted as {02}) in the field GF(2^8)
    uint8_t Rcon[11] = {
        0x8d, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36 };

    // This function produces Nb(Nr+1) round keys. The round keys are used in each round to decrypt the states.
    void KeyExpansion(uint8_t* RoundKey, const uint8_t* Key)
    {
        unsigned i, j, k;
        uint8_t tempa[4]; // Used for the column/row operations

        // The first round key is the key itself.
        for (i = 0; i < Nk; ++i)
        {
            RoundKey[(i * 4) + 0] = Key[(i * 4) + 0];
            RoundKey[(i * 4) + 1] = Key[(i * 4) + 1];
            RoundKey[(i * 4) + 2] = Key[(i * 4) + 2];
            RoundKey[(i * 4) + 3] = Key[(i * 4) + 3];
        }

        // All other round keys are found from the previous round keys.
        for (i = Nk; i < Nb * (Nr + 1); ++i)
        {
            {
                k = (i - 1) * 4;
                tempa[0]=RoundKey[k + 0];
                tempa[1]=RoundKey[k + 1];
                tempa[2]=RoundKey[k + 2];
                tempa[3]=RoundKey[k + 3];

            }

            if (i % Nk == 0)
            {
                // This function shifts the 4 bytes in a word to the left once.
                // [a0,a1,a2,a3] becomes [a1,a2,a3,a0]

                // Function RotWord()
                {
                    k = tempa[0];
                    tempa[0] = tempa[1];
                    tempa[1] = tempa[2];
                    tempa[2] = tempa[3];
                    tempa[3] = k;
                }

                // SubWord() is a function that takes a four-byte input word and
                // applies the S-box to each of the four bytes to produce an output word.

                // Function Subword()
                {
                    tempa[0] = sbox[(tempa[0])];
                    tempa[1] = sbox[(tempa[1])];
                    tempa[2] = sbox[(tempa[2])];
                    tempa[3] = sbox[(tempa[3])];
                }

                tempa[0] = tempa[0] ^ Rcon[i/Nk];
            }

            j = i * 4; k=(i - Nk) * 4;
            RoundKey[j + 0] = RoundKey[k + 0] ^ tempa[0];
            RoundKey[j + 1] = RoundKey[k + 1] ^ tempa[1];
            RoundKey[j + 2] = RoundKey[k + 2] ^ tempa[2];
            RoundKey[j + 3] = RoundKey[k + 3] ^ tempa[3];
        }
    }

    void AES_init_ctx(struct AES_ctx* ctx, const uint8_t* key)
    {
        KeyExpansion(ctx->RoundKey, key);
    }
    void AES_init_ctx_iv(struct AES_ctx* ctx, const uint8_t* key, const uint8_t* iv)
    {
        KeyExpansion(ctx->RoundKey, key);
        std::memcpy (ctx->Iv, iv, AES_BLOCKLEN);
    }
    void AES_ctx_set_iv(struct AES_ctx* ctx, const uint8_t* iv)
    {
        std::memcpy (ctx->Iv, iv, AES_BLOCKLEN);
    }

    // This function adds the round key to state.
    // The round key is added to the state by an XOR function.
    void AddRoundKey(uint8_t round,state_t* state,uint8_t* RoundKey)
    {
        uint8_t i,j;
        for (i = 0; i < 4; ++i)
        {
            for (j = 0; j < 4; ++j)
            {
                (*state)[i][j] ^= RoundKey[(round * Nb * 4) + (i * Nb) + j];
            }
        }
    }

    // The SubBytes Function Substitutes the values in the
    // state matrix with values in an S-box.
    void SubBytes(state_t* state)
    {
        uint8_t i, j;
        for (i = 0; i < 4; ++i)
        {
            for (j = 0; j < 4; ++j)
            {
                (*state)[j][i] = sbox[((*state)[j][i])];
            }
        }
    }

    // The ShiftRows() function shifts the rows in the state to the left.
    // Each row is shifted with different offset.
    // Offset = Row number. So the first row is not shifted.
    void ShiftRows(state_t* state)
    {
        uint8_t temp;

        // Rotate first row 1 columns to left
        temp           = (*state)[0][1];
        (*state)[0][1] = (*state)[1][1];
        (*state)[1][1] = (*state)[2][1];
        (*state)[2][1] = (*state)[3][1];
        (*state)[3][1] = temp;

        // Rotate second row 2 columns to left
        temp           = (*state)[0][2];
        (*state)[0][2] = (*state)[2][2];
        (*state)[2][2] = temp;

        temp           = (*state)[1][2];
        (*state)[1][2] = (*state)[3][2];
        (*state)[3][2] = temp;

        // Rotate third row 3 columns to left
        temp           = (*state)[0][3];
        (*state)[0][3] = (*state)[3][3];
        (*state)[3][3] = (*state)[2][3];
        (*state)[2][3] = (*state)[1][3];
        (*state)[1][3] = temp;
    }

    uint8_t xtime(uint8_t x)
    {
        return ((x<<1) ^ (((x>>7) & 1) * 0x1b));
    }

    // MixColumns function mixes the columns of the state matrix
    void MixColumns(state_t* state)
    {
        uint8_t i;
        uint8_t Tmp, Tm, t;
        for (i = 0; i < 4; ++i)
        {
            t   = (*state)[i][0];
            Tmp = (*state)[i][0] ^ (*state)[i][1] ^ (*state)[i][2] ^ (*state)[i][3] ;
            Tm  = (*state)[i][0] ^ (*state)[i][1] ; Tm = xtime(Tm);  (*state)[i][0] ^= Tm ^ Tmp ;
            Tm  = (*state)[i][1] ^ (*state)[i][2] ; Tm = xtime(Tm);  (*state)[i][1] ^= Tm ^ Tmp ;
            Tm  = (*state)[i][2] ^ (*state)[i][3] ; Tm = xtime(Tm);  (*state)[i][2] ^= Tm ^ Tmp ;
            Tm  = (*state)[i][3] ^ t ;              Tm = xtime(Tm);  (*state)[i][3] ^= Tm ^ Tmp ;
        }
    }

    // MixColumns function mixes the columns of the state matrix.
    // The method used to multiply may be difficult to understand for the inexperienced.
    // Please use the references to gain more information.
    void InvMixColumns(state_t* state)
    {
        int i;
        uint8_t a, b, c, d;
        for (i = 0; i < 4; ++i)
        {
            a = (*state)[i][0];
            b = (*state)[i][1];
            c = (*state)[i][2];
            d = (*state)[i][3];

            (*state)[i][0] = Multiply(a, 0x0e) ^ Multiply(b, 0x0b) ^ Multiply(c, 0x0d) ^ Multiply(d, 0x09);
            (*state)[i][1] = Multiply(a, 0x09) ^ Multiply(b, 0x0e) ^ Multiply(c, 0x0b) ^ Multiply(d, 0x0d);
            (*state)[i][2] = Multiply(a, 0x0d) ^ Multiply(b, 0x09) ^ Multiply(c, 0x0e) ^ Multiply(d, 0x0b);
            (*state)[i][3] = Multiply(a, 0x0b) ^ Multiply(b, 0x0d) ^ Multiply(c, 0x09) ^ Multiply(d, 0x0e);
        }
    }

    // The SubBytes Function Substitutes the values in the
    // state matrix with values in an S-box.
    void InvSubBytes(state_t* state)
    {
        uint8_t i, j;
        for (i = 0; i < 4; ++i)
        {
            for (j = 0; j < 4; ++j)
            {
                (*state)[j][i] = rsbox[((*state)[j][i])];
            }
        }
    }

    void InvShiftRows(state_t* state)
    {
        uint8_t temp;

        // Rotate first row 1 columns to right
        temp = (*state)[3][1];
        (*state)[3][1] = (*state)[2][1];
        (*state)[2][1] = (*state)[1][1];
        (*state)[1][1] = (*state)[0][1];
        (*state)[0][1] = temp;

        // Rotate second row 2 columns to right
        temp = (*state)[0][2];
        (*state)[0][2] = (*state)[2][2];
        (*state)[2][2] = temp;

        temp = (*state)[1][2];
        (*state)[1][2] = (*state)[3][2];
        (*state)[3][2] = temp;

        // Rotate third row 3 columns to right
        temp = (*state)[0][3];
        (*state)[0][3] = (*state)[1][3];
        (*state)[1][3] = (*state)[2][3];
        (*state)[2][3] = (*state)[3][3];
        (*state)[3][3] = temp;
    }

    // Cipher is the main function that encrypts the PlainText.
    void Cipher(state_t* state, uint8_t* RoundKey)
    {
        uint8_t round = 0;

        // Add the First round key to the state before starting the rounds.
        AddRoundKey(0, state, RoundKey);

        // There will be Nr rounds.
        // The first Nr-1 rounds are identical.
        // These Nr-1 rounds are executed in the loop below.
        for (round = 1; round < Nr; ++round)
        {
            SubBytes(state);
            ShiftRows(state);
            MixColumns(state);
            AddRoundKey(round, state, RoundKey);
        }

        // The last round is given below.
        // The MixColumns function is not here in the last round.
        SubBytes(state);
        ShiftRows(state);
        AddRoundKey(Nr, state, RoundKey);
    }

    void InvCipher(state_t* state,uint8_t* RoundKey)
    {
        uint8_t round = 0;

        // Add the First round key to the state before starting the rounds.
        AddRoundKey(Nr, state, RoundKey);

        // There will be Nr rounds.
        // The first Nr-1 rounds are identical.
        // These Nr-1 rounds are executed in the loop below.
        for (round = (Nr - 1); round > 0; --round)
        {
            InvShiftRows(state);
            InvSubBytes(state);
            AddRoundKey(round, state, RoundKey);
            InvMixColumns(state);
        }

        // The last round is given below.
        // The MixColumns function is not here in the last round.
        InvShiftRows(state);
        InvSubBytes(state);
        AddRoundKey(0, state, RoundKey);
    }

    void XorWithIv(uint8_t* buf, uint8_t* Iv)
    {
        uint8_t i;
        for (i = 0; i < AES_BLOCKLEN; ++i) // The block in AES is always 128bit no matter the key size
        {
            buf[i] ^= Iv[i];
        }
    }

    void AES_CBC_encrypt_buffer(struct AES_ctx *ctx,uint8_t* buf, uint32_t length)
    {
        uintptr_t i;
        uint8_t *Iv = ctx->Iv;
        for (i = 0; i < length; i += AES_BLOCKLEN)
        {
            XorWithIv(buf, Iv);
            Cipher((state_t*)buf, ctx->RoundKey);
            Iv = buf;
            buf += AES_BLOCKLEN;
            //printf("Step %d - %d", i/16, i);
        }
        /* store Iv in ctx for next call */
        std::memcpy(ctx->Iv, Iv, AES_BLOCKLEN);
    }

    void AES_CBC_decrypt_buffer(struct AES_ctx* ctx, uint8_t* buf,  uint32_t length)
    {
        uintptr_t i;
        uint8_t storeNextIv[AES_BLOCKLEN];
        for (i = 0; i < length; i += AES_BLOCKLEN)
        {
            std::memcpy(storeNextIv, buf, AES_BLOCKLEN);
            InvCipher((state_t*)buf, ctx->RoundKey);
            XorWithIv(buf, ctx->Iv);
            std::memcpy(ctx->Iv, storeNextIv, AES_BLOCKLEN);
            buf += AES_BLOCKLEN;
        }

    }
public:
    void main(uint8_t *in, int n, uint8_t *out, uint8_t *key)
    {
        uint8_t iv[16];
        for (int i = 0; i < 16; ++i)
            iv[i] = 0x00;

        struct AES_ctx ctx;
        AES_init_ctx_iv(&ctx, key, iv);

        AES_CBC_encrypt_buffer(&ctx, in, 64);

        int offset = (n-1)*16;
        std::memcpy(out, in+offset, 16);
    }
};

struct hmac_hash {
    uint64_t operator()(const char *buf, size_t len) const {
        uint8_t key[] = { 0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6, 0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c };
        uint8_t out[16];

        hmac h;
        h.main((uint8_t *) buf, len, out, key);
        return 42;
    }
};
// -- EXTERN

}  // namespace

// if REGISTER_HASH calls placed in the anonymous namespace, some compiler can
// give an unused variable warning
REGISTER_HASH(xxh64);
REGISTER_HASH(crc16);
REGISTER_HASH(crc32);
REGISTER_HASH(crcCCITT);
REGISTER_HASH(cksum16);
REGISTER_HASH(csum16);
REGISTER_HASH(identity);
REGISTER_HASH(round_robin);
REGISTER_HASH(round_robin_consistent);
// EXTERN
REGISTER_HASH(hmac_hash);
// -- EXTERN

using crc8_custom = crc_custom<uint8_t>;
REGISTER_HASH(crc8_custom);
using crc16_custom = crc_custom<uint16_t>;
REGISTER_HASH(crc16_custom);
using crc32_custom = crc_custom<uint32_t>;
REGISTER_HASH(crc32_custom);
using crc64_custom = crc_custom<uint64_t>;
REGISTER_HASH(crc64_custom);

namespace detail {

template <typename T>
std::ostream &operator<<(std::ostream &out, const crc_config_t<T> &c) {
  out << "polynomial: " << c.polynomial << ", initial_remainder: "
      << c.initial_remainder << ", final_xor_value: " << c.final_xor_value
      << ", data_reflected: " << c.data_reflected
      << ", remainder_reflected: " << c.remainder_reflected;
  return out;
}

}  // namespace detail

template <typename T>
CustomCrcErrorCode
CustomCrcMgr<T>::update_config(NamedCalculation *calculation,
                               const crc_config_t &config) {
  Logger::get()->info("Updating config of custom crc {}: {}",
                      calculation->get_name(), config);
  auto raw_c_iface = calculation->get_raw_calculation();
  return update_config(raw_c_iface, config);
}

template <typename T>
CustomCrcErrorCode
CustomCrcMgr<T>::update_config(RawCalculationIface<uint64_t> *c,
                               const crc_config_t &config) {
  using ExpectedCType = RawCalculation<uint64_t, crc_custom<T> >;
  auto raw_c = dynamic_cast<ExpectedCType *>(c);
  if (!raw_c) return CustomCrcErrorCode::WRONG_TYPE_CALCULATION;
  raw_c->get_hash_fn().update_config(config);
  return CustomCrcErrorCode::SUCCESS;
}

// explicit instantiation, should prevent implicit instantiation
template class CustomCrcMgr<uint8_t>;
template class CustomCrcMgr<uint16_t>;
template class CustomCrcMgr<uint32_t>;
template class CustomCrcMgr<uint64_t>;

CalculationsMap * CalculationsMap::get_instance() {
  static CalculationsMap map;
  return &map;
}

bool CalculationsMap::register_one(const char *name, std::unique_ptr<MyC> c) {
  const std::string str_name = std::string(name);
  auto it = map_.find(str_name);
  if (it != map_.end()) return false;
  map_[str_name] = std::move(c);
  return true;
}

std::unique_ptr<CalculationsMap::MyC>
CalculationsMap::get_copy(const std::string &name) {
  auto it = map_.find(name);
  if (it == map_.end()) return nullptr;
  return it->second->clone();
}

}  // namespace bm
