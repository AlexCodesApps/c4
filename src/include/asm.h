#pragma once
#include <stdio.h>
#include "sema.h"

void lower_to_asm(FILE * file, SemaDeclList list);
