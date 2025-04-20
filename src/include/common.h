#pragma once

#include "ints.h"

struct SrcPos {
    usize index;
    usize row;
    usize col;
} typedef SrcPos;

struct SrcSpan {
    SrcPos pos;
    usize len;
} typedef SrcSpan;
