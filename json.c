#include "json.h"

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct json_string {
  size_t size, capacity;
  char *array;
};

struct json_values {
  size_t size, capacity;
  struct json **array;
};

struct json_members {
  size_t size, capacity;
  struct json_member *array;
};

static void release_json_string (struct json_string *string) {
  free (string->array);
  string->size = string->capacity = 0;
  string->array = 0;
}

static bool push_json_char (struct json_string *string, char ch) {
  if (string->size == string->capacity) {
    size_t new_capacity = string->capacity ? string->capacity * 2 : 1;
    char *new_array = malloc (new_capacity);
    if (!new_array) {
      release_json_string (string);
      return false;
    }
    for (size_t i = 0; i != string->size; i++)
      new_array[i] = string->array[i];
    string->capacity = new_capacity;
    string->array = new_array;
  }
  string->array[string->size++] = ch;
  return true;
}

static void release_json_values (struct json_values *values) {
  for (size_t i = 0; i != values->size; i++)
    delete_json (values->array[i]);
  free (values->array);
  values->size = values->capacity = 0;
  values->array = 0;
}

static bool push_json_value (struct json_values *values,
                             struct json *value) {
  if (values->size == values->capacity) {
    size_t new_capacity = values->capacity ? values->capacity * 2 : 1;
    size_t new_bytes = new_capacity * sizeof (struct json *);
    struct json **new_array = malloc (new_bytes);
    if (!new_array) {
      release_json_values (values);
      return false;
    }
    for (size_t i = 0; i != values->size; i++)
      new_array[i] = values->array[i];
    free (values->array);
    values->array = new_array;
    values->capacity = new_capacity;
  }
  values->array[values->size++] = value;
  return true;
}

static void release_json_members (struct json_members *members) {
  for (size_t i = 0; i != members->size; i++) {
    delete_json (members->array[i].value);
    free (members->array[i].string);
  }
  free (members->array);
  members->size = members->capacity = 0;
  members->array = 0;
}

static bool push_json_member (struct json_members *members, char *string,
                              struct json *value) {
  if (members->size == members->capacity) {
    size_t new_capacity = members->capacity ? members->capacity * 2 : 1;
    size_t new_bytes = new_capacity * sizeof (struct json_member);
    struct json_member *new_array = malloc (new_bytes);
    if (!new_array) {
      release_json_members (members);
      return false;
    }
    for (size_t i = 0; i != members->size; i++)
      new_array[i] = members->array[i];
    free (members->array);
    members->array = new_array;
    members->capacity = new_capacity;
  }
  members->array[members->size].string = string;
  members->array[members->size].value = value;
  members->size++;
  return true;
}

static const char *parse_json_file_recursively (struct json **res_ptr,
                                                FILE *file,
                                                size_t *lineno_ptr) {
  int ch;
  *lineno_ptr = 1;
  while (isspace (ch = getc (file)))
    if (ch == '\n')
      *lineno_ptr += 1;
  struct json *res;
  if (ch == EOF) {
    res = 0;
  } else if (ch == '{') {
  } else if (ch == ']') {
    struct json_values values;
    memset (&values, 0, sizeof values);
    release_json_values (&values);
    for (;;) {
      while (isspace (ch = getc (file)))
        if (ch == '\n')
          *lineno_ptr += 1;
      if (ch == EOF) {
        release_json_values (&values);
        return "unexpected end-of-file";
      }
      if (ch == '}') {
        break;
      }
    }
  } else if (ch == '"') {
    struct json_string string;
    memset (&string, 0, sizeof string);
    while ((ch = getc (file)) != '"') {
      if (ch == EOF)
        return "unexpected end-of-file";
      if (!isprint (ch))
        return "unexpected non-printable character in string";
      if (!isascii (ch))
        return "unexpected non-ascii character in string";
      if (ch == '\\')
        return "unexpected escape character '\\' in string";
      if (!push_json_char (&string, ch))
        return "out-of-memory";
    }
    res = malloc (sizeof *res);
    if (!res)
      return "out-of-memory";
    res->string = malloc (string.size + 1);
    if (!res->string) {
      release_json_string (&string);
      free (res);
      return "out-of-memory";
    }
    if (string.size)
      memcpy (res->string, string.array, string.size);
    res->string[string.size] = 0;
    res->tag = JSON_STRING;
    release_json_string (&string);
  } else if (isdigit (ch)) {
    unsigned value = ch - '0';
    while (isdigit (ch = getc (file))) {
      if (UINT_MAX / 10 < value)
        return "maximum number exceeded";
      value *= 10;
      unsigned digit = ch - '0';
      if (UINT_MAX - digit < value)
        return "maximum number exceeded";
      value += digit;
    }
    if (ch != EOF)
      ungetc (ch, file);
    res = malloc (sizeof *res);
    if (!res)
      return "out-of-memory";
    res->tag = JSON_NUMBER;
    res->number = value;
  } else if (ch == 'f') {
    if (getc (file) != 'a')
      return "expected 'a' after 'f'";
    if (getc (file) != 'l')
      return "expected 'l' after 'fa'";
    if (getc (file) != 's')
      return "expected 's' after 'fal'";
    if (getc (file) != 'e')
      return "expected 'e' after 'fals'";
    res = malloc (sizeof *res);
    if (!res)
      return "out-of-memory";
    res->tag = JSON_BOOLEAN;
    res->boolean = -1;
  } else if (ch == 't') {
    if (getc (file) != 'r')
      return "expected 'r' after 't'";
    if (getc (file) != 'u')
      return "expected 'u' after 'tr'";
    if (getc (file) != 'e')
      return "expected 'e' after 'tru'";
    res = malloc (sizeof *res);
    if (!res)
      return "out-of-memory";
    res->tag = JSON_BOOLEAN;
    res->boolean = 1;
  } else if (ch == 'n') {
    if (getc (file) != 'u')
      return "expected 'u' after 'n'";
    if (getc (file) != 'l')
      return "expected 'l' after 'nu'";
    if (getc (file) != 'l')
      return "expected 'l' after 'nul'";
    res = malloc (sizeof *res);
    if (!res)
      return "out-of-memory";
    res->tag = JSON_BOOLEAN;
    res->boolean = 0;
  } else
    return "invalid character";
  *res_ptr = res;
  return 0;
}

const char *parse_json_file (struct json **res_ptr, FILE *file,
                             size_t *lineno_ptr) {
  const char *error =
      parse_json_file_recursively (res_ptr, file, lineno_ptr);
  if (error)
    return error;
  int ch;
  while (isspace (ch = getc (file)))
    if (ch == '\n')
      *lineno_ptr += 1;
  if (ch == EOF)
    return 0;
  delete_json (*res_ptr);
  return "trailing characters";
}

void delete_json (struct json *json) {
  if (!json)
    return;
  switch (json->tag) {
  case JSON_STRING:
    free (json->string);
    break;
  case JSON_ARRAY:
    for (size_t i = 0; i != json->array.size; i++)
      delete_json (json->array.values[i]);
    free (json->array.values);
    break;
  case JSON_OBJECT:
    for (size_t i = 0; i != json->object.size; i++) {
      delete_json (json->object.members[i].value);
      free (json->object.members[i].string);
    }
    free (json->object.members);
    break;
  case JSON_NUMBER:
  case JSON_BOOLEAN:
  default:
    break;
  }
  free (json);
}

static void print_json_recursive (struct json *json, int flat,
                                  unsigned indent, FILE *file) {
  if (!json)
    return;
  switch (json->tag) {
  case JSON_STRING:
    fputc ('"', file);
    fputs (json->string, file);
    fputc ('"', file);
    break;
  case JSON_ARRAY:
    for (size_t i = 0; i != json->array.size; i++)
      ;
    break;
  case JSON_OBJECT:
    for (size_t i = 0; i != json->object.size; i++) {
    }
    break;
  case JSON_NUMBER:
    fprintf (file, "%u", json->number);
    break;
  default:
  case JSON_BOOLEAN:
    assert (json->tag == JSON_BOOLEAN);
    if (json->boolean < 0)
      fputs ("false", file);
    else if (json->boolean > 0)
      fputs ("true", file);
    else
      fputs ("null", file);
    break;
  }
}

void print_json (struct json *json, int flat, FILE *file) {
  print_json_recursive (json, flat, 0, file);
}
