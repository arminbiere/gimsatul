#ifndef _json_h_INCLUDED
#define _json_h_INCLUDED

#include <stdio.h>

struct json;

struct json_array {
  size_t size;
  struct json **values;
};

struct json_member {
  char *string;
  struct json *value;
};

struct json_object {
  size_t size;
  struct json_member *members;
};

enum json_tag {
  JSON_NUMBER,
  JSON_STRING,
  JSON_BOOLEAN,
  JSON_ARRAY,
  JSON_OBJECT,
};

struct json {
  enum json_tag tag;
  union {
    int boolean;     // -1=false, 0=null, 1= true
    unsigned number; // Only support 'unsigned' integers.
    char *string;
    struct json_array array;
    struct json_object object;
  };
};

const char *parse_json_file (struct json **, FILE *, size_t *linenoptr);
void print_json (struct json *, int flat, FILE *);
void delete_json (struct json *);

#endif
