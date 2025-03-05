// #define NDEBUG
#include <assert.h>
#include <ctype.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "tree_sitter/parser.h"

typedef enum TokenType
{
    BEGIN,
    SEPARATOR,
    END
} TokenType;

#define TOP_MAX (TREE_SITTER_SERIALIZATION_BUFFER_SIZE / sizeof(int32_t) - 1)

typedef struct ScannerState
{
    // `rulers[0]` is always zero.
    // `rulers[1]`, ..., `rulers[top]` store the rulers.
    // Negative values indicate tentative rulers.
    int32_t rulers[TOP_MAX + 1];

    // The index of the last ruler, less than or equal to `TOP_MAX`.
    int32_t top;
} ScannerState;

static inline bool valid_state(const ScannerState *const scanner_state, FILE *const file)
{
    bool valid = scanner_state->top <= TOP_MAX;
    fprintf(file, "{top: %i, rulers: [", scanner_state->top);
    int32_t prev = 0;
    for (int32_t i = 0; i <= TOP_MAX && i <= scanner_state->top; i++)
    {
        const char *sep = i < TOP_MAX ? i == scanner_state->top ? "|" : "," : "";
        fprintf(file, "%i%s", scanner_state->rulers[i], sep);
        valid &= prev <= labs(scanner_state->rulers[i]);
        if (scanner_state->rulers[i] >= 0)
            prev = scanner_state->rulers[i];
    }
    fprintf(file, "]}\n");
    return valid;
}

ScannerState *tree_sitter_axi_external_scanner_create()
{
    static ScannerState scanner_state;
    static_assert(sizeof(scanner_state.rulers) <= TREE_SITTER_SERIALIZATION_BUFFER_SIZE);
    return &scanner_state;
}

void tree_sitter_axi_external_scanner_destroy(ScannerState *scanner_state)
{
}

unsigned tree_sitter_axi_external_scanner_serialize(const ScannerState *scanner_state, char *buffer)
{
    const unsigned length = sizeof(int32_t[scanner_state->top + 1]);
    memcpy(buffer, scanner_state->rulers, length);
    return length;
}

void tree_sitter_axi_external_scanner_deserialize(ScannerState *scanner_state, const char *buffer, unsigned length)
{
    memcpy(scanner_state->rulers, buffer, length);
    scanner_state->top = length / sizeof(int32_t) - 1;
    if (scanner_state->top > TOP_MAX)
        scanner_state->top = scanner_state->rulers[0] = 0;
}

static inline bool try_emit_end(ScannerState *scanner_state, TSLexer *lexer)
{
    if (scanner_state->top > 0)
    {
        fprintf(stderr, "end: %i\n", scanner_state->rulers[scanner_state->top]);
        scanner_state->top--;
        lexer->result_symbol = END;
        return true;
    }
    return false;
}

static inline bool try_emit_begin(ScannerState *scanner_state, const int32_t column, TSLexer *lexer)
{
    if (column >= 0 && scanner_state->top < TOP_MAX)
    {
        scanner_state->top++;
        scanner_state->rulers[scanner_state->top] = ~column;
        fprintf(stderr, "begin: %i\n", scanner_state->rulers[scanner_state->top]);
        lexer->result_symbol = BEGIN;
        return true;
    }
    return false;
}

static inline bool emit_separator(TSLexer *lexer)
{
    lexer->result_symbol = SEPARATOR;
    return true;
}

bool tree_sitter_axi_external_scanner_scan(ScannerState *scanner_state, TSLexer *lexer, const bool *valid_symbols)
{
    assert(valid_state(scanner_state, stderr));
    const bool error_recovery = valid_symbols[BEGIN] && valid_symbols[SEPARATOR] && valid_symbols[END];
    if (error_recovery)
        return fprintf(stderr, "error recovery\n"), try_emit_end(scanner_state, lexer);
    if (valid_symbols[BEGIN])
        return try_emit_begin(scanner_state, lexer->get_column(lexer), lexer);
    bool line_break = false;
    for (; !lexer->eof(lexer) && isspace(lexer->lookahead); lexer->advance(lexer, false))
        if (lexer->lookahead == '\n')
            line_break = true;
    const int32_t column = (int32_t)lexer->get_column(lexer);
    if (column < 0)
        return false;
    if (line_break && scanner_state->rulers[scanner_state->top] < 0)
    {
        scanner_state->rulers[scanner_state->top] = column;
        for (int32_t i = scanner_state->top; i >= 0; i--)
        {
            if (scanner_state->rulers[i] > column)
                return false;
            if (scanner_state->rulers[i] >= 0)
                break;
        }
    }
    const int32_t ruler = scanner_state->rulers[scanner_state->top];
    if (valid_symbols[END] && column < labs(ruler))
        return try_emit_end(scanner_state, lexer);
    return valid_symbols[SEPARATOR] && column == ruler && emit_separator(lexer);
}
