//===-- gen-bout.cpp --------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

#include "klee/Internal/ADT/KTest.h"

#if defined(__FreeBSD__) || defined(__minix)
#define stat64 stat
#endif

#define MAX 64
static void push_obj(KTest *b, const char *name, unsigned total_bytes,
                     unsigned char *bytes) {
  KTestObject *o = &b->objects[b->numObjects++];
  assert(b->numObjects < MAX);

  o->name = strdup(name);
  o->numBytes = total_bytes;
  o->bytes = (unsigned char *)malloc(o->numBytes);

  memcpy(o->bytes, bytes, total_bytes);
}

static void push_range(KTest *b, const char *name, unsigned value) {
  KTestObject *o = &b->objects[b->numObjects++];
  assert(b->numObjects < MAX);

  o->name = strdup(name);
  o->numBytes = 4;
  o->bytes = (unsigned char *)malloc(o->numBytes);

  *(unsigned *)o->bytes = value;
}

void print_usage_and_exit(char *program_name) {
  fprintf(stderr,
          "%s: Tool for generating ktest file with concrete input, "
          "e.g., for using a concrete crashing input as a ktest seed.\n",
          program_name);
  fprintf(stderr, "Usage: %s <arguments>\n", program_name);
  fprintf(stderr, "       --out-file <filename> specify the name of the output file\n");
  fprintf(stderr, "       --sym-arg <argument> are the command-line "
                  "argument of the programs\n");
  fprintf(stderr, "       --sym-args <N args> <arguments> are the command-line "
                  "arguments of the "
                  "programs, where N is the number of arguments followed by the argument list\n");

  fprintf(stderr, "       --sym-stdin <filename>      - Specifying a file that "
                  "is the content of the stdin (only once).\n");

  fprintf(stderr, "       --sym-stdout <filename>     - Specifying a file that "
                  "is the content of the stdout (only once).\n");

  fprintf(stderr, "       --sym-file <filename>       - Specifying a file that "
                  "is the content of a file named A provided for the program "
                  "(only once).\n");

  fprintf(stderr, "       --second-var <N vars> <identifier> <value>       - "
                  "Specifying a list of second order variables where N is the number of "
                  "variables followed by each variable's identifier and value pair.\n");

  fprintf(stderr,
          "   Ex: %s --sym-stdin file2 --sym-file file3 "
          "--sym-stdout file4\n",
          program_name);
  exit(1);
}

int main(int argc, char *argv[]) {
  unsigned i, argv_copy_idx;
  unsigned file_counter = 0;
  char *stdout_content_filename = NULL;
  char *stdin_content_filename = NULL;
  char *output_filename = NULL;
  char *content_filenames_list[1024];
  char **argv_copy;

  if (argc < 2)
    print_usage_and_exit(argv[0]);

  KTest b;
  b.symArgvs = 0;
  b.symArgvLen = 0;

  b.numObjects = 0;
  b.objects = (KTestObject *)malloc(MAX * sizeof *b.objects);

  if ((argv_copy = (char **)malloc(sizeof(char *) * argc * 2)) == NULL) {
    fprintf(stderr, "Could not allocate more memory\n");
    return 1;
  }

  argv_copy[0] = (char *)malloc(strlen(argv[0]) + 1);
  strcpy(argv_copy[0], argv[0]);
  argv_copy_idx = 1;

  for (i = 1; i < (unsigned)argc; i++) {

    if (strcmp(argv[i], "--sym-stdout") == 0 ||
        strcmp(argv[i], "-sym-stdout") == 0) {
      if (++i == (unsigned)argc || argv[i][0] == '-')
        print_usage_and_exit(argv[0]);

      if (stdout_content_filename)
        print_usage_and_exit(argv[0]);

      stdout_content_filename = argv[i];

    } else if (strcmp(argv[i], "--sym-stdin") == 0 ||
               strcmp(argv[i], "-sym-stdin") == 0) {
      if (++i == (unsigned)argc || argv[i][0] == '-')
        print_usage_and_exit(argv[0]);

      if (stdin_content_filename)
        print_usage_and_exit(argv[0]);

      stdin_content_filename = argv[i];
    } else if (strcmp(argv[i], "--sym-file") == 0 ||
               strcmp(argv[i], "-sym-file") == 0) {
      if (++i == (unsigned)argc || argv[i][0] == '-')
        print_usage_and_exit(argv[0]);

      content_filenames_list[file_counter++] = argv[i];

    } else if (strcmp(argv[i], "--sym-args") == 0 ||
               strcmp(argv[i], "-sym-args") == 0) {


      static int total_args = 0;
      int num_args = atoi(argv[++i]);
      printf("\tIdentified %d arguments\n", num_args);

      for (int k=0; k < num_args; k++){
        long nbytes = strlen(argv[++i]) + 1;
        static int total_args = 0;
        char arg[1024];
        sprintf(arg, "arg0%d", total_args++);
        push_obj(&b, (const char *)arg, nbytes, (unsigned char *)argv[i]);
        printf("\t\tName=%s, Size=%ld, Value=%s\n",arg, nbytes, argv[i]);
        char *buf1 = (char *)malloc(1024);
        char *buf2 = (char *)malloc(1024);
        strcpy(buf1, "-sym-arg");
        sprintf(buf2, "%ld", nbytes - 1);
        argv_copy[argv_copy_idx++] = buf1;
        argv_copy[argv_copy_idx++] = buf2;
      }

    } else if (strcmp(argv[i], "--sym-arg") == 0 ||
             strcmp(argv[i], "-sym-arg") == 0) {

      printf("\tIdentified a argument\n");
      long nbytes = strlen(argv[++i]) + 1;
      static int total_args = 0;

      char arg[1024];
      sprintf(arg, "arg0%d", total_args++);
      push_obj(&b, (const char *)arg, nbytes, (unsigned char *)argv[i]);
      printf("\t\tName=%s, Size=%ld, Value=%s\n",arg, nbytes, argv[i]);
      char *buf1 = (char *)malloc(1024);
      char *buf2 = (char *)malloc(1024);
      strcpy(buf1, "-sym-arg");
      sprintf(buf2, "%ld", nbytes - 1);
      argv_copy[argv_copy_idx++] = buf1;
      argv_copy[argv_copy_idx++] = buf2;

    } else if (strcmp(argv[i], "--second-var") == 0 ||
               strcmp(argv[i], "-second-var") == 0) {

      printf("\tIdentified a second order variable\n");
      char name[1024];
      char value[1024];
      long nbytes = 0;
      unsigned long read_value = 0;
      sprintf(name, "%s", argv[++i]);
      nbytes = atoi(argv[++i]);
      read_value = atoi(argv[++i]);
      printf("\t\tName=%s, Size=%ld, Value=%ld\n",name, nbytes, read_value);
      for (int k = nbytes - 1; k >= 0; k--) {
        value[k] = (read_value >> (8 * (k)) )& 0xFF;
      }
      push_obj(&b, (const char *)name, nbytes, (unsigned char *)value);
//      printf("\t\tName=%s, Size=%ld, Value=%ld, Value in Hex=%s\n",name, nbytes, read_value, *value);

    } else if (strcmp(argv[i], "--out-file") == 0 ||
               strcmp(argv[i], "-out-file") == 0) {
      printf("\tIdentified output file name\n");
      if (++i == (unsigned)argc || argv[i][0] == '-')
        print_usage_and_exit(argv[0]);
      if (output_filename)
        print_usage_and_exit(argv[0]);
      output_filename = argv[i];
    }
  }

  if (file_counter > 0) {
    char *prefix_list[5] = ["A", "B", "C", "D", "E"];
    for (int k=0; k<file_counter; k++) {
      FILE *fp;
      struct stat64 file_stat;
      char *content_filename = content_filenames_list[k];

      if ((fp = fopen(content_filename, "r")) == NULL ||
          stat64(content_filename, &file_stat) < 0) {
        fprintf(stderr, "Failure opening %s\n", content_filename);
        print_usage_and_exit(argv[0]);
      }

      long nbytes = file_stat.st_size;

      char filename[7];
      char statname[12];
      strcpy(filename, prefix_list[k]);
      strcat(filename, "-data");
      strcpy(statname, prefix_list[k]);
      strcat(statname, "-data-stat");


      unsigned char *file_content, *fptr;
      if ((file_content = (unsigned char *)malloc(nbytes)) == NULL) {
        fprintf(stderr, "Memory allocation failure\n");
        exit(1);
      }

      int read_char;
      fptr = file_content;
      while ((read_char = fgetc(fp)) != EOF) {
        *fptr = (unsigned char)read_char;
        fptr++;
      }

      push_obj(&b, filename, nbytes, file_content);
      push_obj(&b, statname, sizeof(struct stat64),
               (unsigned char *)&file_stat);

      free(file_content);

      char *buf1 = (char *)malloc(1024);
      char *buf2 = (char *)malloc(1024);
      char *buf3 = (char *)malloc(1024);
      sprintf(buf1, "-sym-files");
      sprintf(buf2, "1");
      sprintf(buf3, "%ld", nbytes);
      argv_copy[argv_copy_idx++] = buf1;
      argv_copy[argv_copy_idx++] = buf2;
      argv_copy[argv_copy_idx++] = buf3;
    }
  }

  if (stdin_content_filename) {
    FILE *fp;
    struct stat64 file_stat;
    char filename[6] = "stdin";
    char statname[11] = "stdin-stat";

    if ((fp = fopen(stdin_content_filename, "r")) == NULL ||
        stat64(stdin_content_filename, &file_stat) < 0) {
      fprintf(stderr, "Failure opening %s\n", stdin_content_filename);
      print_usage_and_exit(argv[0]);
    }

    unsigned char *file_content, *fptr;
    if ((file_content = (unsigned char *)malloc(file_stat.st_size)) == NULL) {
      fprintf(stderr, "Memory allocation failure\n");
      exit(1);
    }

    int read_char;
    fptr = file_content;
    while ((read_char = fgetc(fp)) != EOF) {
      *fptr = (unsigned char)read_char;
      fptr++;
    }

    push_obj(&b, filename, file_stat.st_size, file_content);
    push_obj(&b, statname, sizeof(struct stat64), (unsigned char *)&file_stat);

    free(file_content);

    char *buf1 = (char *)malloc(1024);
    char *buf2 = (char *)malloc(1024);
    sprintf(buf1, "-sym-stdin");
    sprintf(buf2, "%ld", file_stat.st_size);
    argv_copy[argv_copy_idx++] = buf1;
    argv_copy[argv_copy_idx++] = buf2;
  }

  if (stdout_content_filename) {
    FILE *fp;
    struct stat64 file_stat;
    unsigned char file_content[1024];
    char filename[7] = "stdout";
    char statname[12] = "stdout-stat";

    if ((fp = fopen(stdout_content_filename, "r")) == NULL ||
        stat64(stdout_content_filename, &file_stat) < 0) {
      fprintf(stderr, "Failure opening %s\n", stdout_content_filename);
      print_usage_and_exit(argv[0]);
    }

    int read_char;
    for (int i = 0; i < file_stat.st_size && i < 1024; ++i) {
      read_char = fgetc(fp);
      file_content[i] = (unsigned char)read_char;
    }

    for (int i = file_stat.st_size; i < 1024; ++i) {
      file_content[i] = 0;
    }

    file_stat.st_size = 1024;

    push_obj(&b, filename, 1024, file_content);
    push_obj(&b, statname, sizeof(struct stat64), (unsigned char *)&file_stat);

    char *buf = (char *)malloc(1024);
    sprintf(buf, "-sym-stdout");
    argv_copy[argv_copy_idx++] = buf;
  }

  argv_copy[argv_copy_idx] = 0;
  b.numArgs = argv_copy_idx;
  b.args = argv_copy;
  push_range(&b, "model_version", 1);
  const char* output_name = output_filename? output_filename: "file.bout";
  if (!kTest_toFile(&b, output_name))
    assert(0);
  printf("\tktest file created: %s\n", output_name);
  for (int i = 0; i < (int)b.numObjects; ++i) {
    free(b.objects[i].name);
    free(b.objects[i].bytes);
  }

  free(b.objects);

  for (int i = 0; i < (int)argv_copy_idx; ++i) {
    free(argv_copy[i]);
  }
  free(argv_copy);

  return 0;
}
