#ifndef BLOCK_HEADER_H
#define BLOCK_HEADER_H

// Header management

#define HEADER_SIZE 1

inline static value_t header_pack(tag_t tag, value_t size) {
  return ((value_t)tag << 24) | size;
}

inline static tag_t header_unpack_tag(value_t header) {
  return (tag_t)((header >> 24) & 0xFF);
}

inline static value_t header_unpack_size(value_t header) {
  return header & 0xFFFFFF;
}

inline static value_t block_header(const value_t* block) {
  return block[-HEADER_SIZE];
}

inline static void block_set_header(value_t* block, value_t header) {
  block[-HEADER_SIZE] = header;
}

inline static tag_t block_tag(const value_t* block) {
  return header_unpack_tag(block_header(block));
}

inline static tag_t block_size(const value_t* block) {
  return header_unpack_size(block_header(block));
}

#endif
