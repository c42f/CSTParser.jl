function _precompile_()
    ccall(:jl_generating_output, Cint, ()) == 1 || return nothing

    precompile(Parser.INSTANCE, (ParseState,))
    precompile(Parser.IDENTIFIER, (Int, Int, Symbol))
    precompile(Parser.LITERAL, (Int, Int, Symbol))
    precompile(Parser.KEYWORD, (Int, Int))
    precompile(Parser.OPERATOR, (Int, Int))
    precompile(Parser.PUNCTUATION, (Int, Int))
    precompile(Parser.HEAD, (Int, Int))
    precompile(Parser.EXPR, (SyntaxNode, Vector{SyntaxNode}, Int, Vector{INSTANCE}, Scope))

    precompile(Parser.next, (ParseState,))
    precompile(Parser.lex_ws_comment, (Tokenize.Lexers.Lexer, Char))
    precompile(Parser.read_ws, (Tokenize.Lexers.Lexer, Bool))
    precompile(Parser.read_comment, (Tokenize.Lexers.Lexer, ))

    precompile(Parser.parse_expression, (ParseState,))
    precompile(Parser.parse_juxtaposition, (ParseState, EXPR))
    precompile(Parser.parse_juxtaposition, (ParseState, SyntaxNode))
    precompile(Parser.parse_juxtaposition, (ParseState, INSTANCE))
    precompile(Parser.parse_juxtaposition, (ParseState, LITERAL))
    precompile(Parser.parse_juxtaposition, (ParseState, Vector{SyntaxNode}))
    precompile(Parser.parse_juxtaposition, (ParseState, OPERATOR{20,Tokens.NOT}))
    precompile(Parser.parse_juxtaposition, (ParseState, OPERATOR{20,Tokens.PRIME}))
    precompile(Parser.parse_juxtaposition, (ParseState, OPERATOR{20,Tokens.ANON_FUNC}))
    precompile(Parser.parse_juxtaposition, (ParseState, OPERATOR{9,Tokens.PLUS}))
    precompile(Parser.parse_juxtaposition, (ParseState, OPERATOR{9,Tokens.MINUS}))
    precompile(Parser.parse_list, (ParseState, Vector{SyntaxNode}))
    precompile(Parser.parse_tuple, (ParseState, EXPR))
    precompile(Parser.parse_tuple, (ParseState, SyntaxNode))
    # precompile(Parser.parse_semicolon, (ParseState, EXPR))
    # precompile(Parser.parse_semicolon, (ParseState, SyntaxNode))
    precompile(Parser.parse_paren, (ParseState,))
    precompile(Parser.parse_array, (ParseState,))
    precompile(Parser.parse_quote, (ParseState,))
    precompile(Parser.parse, (String,))
    precompile(Parser.parse, (String, Bool))
    precompile(Parser.parse_unary, (ParseState, OPERATOR))
    precompile(Parser.parse_unary, (ParseState, OPERATOR{8, Tokens.COLON}))
    precompile(Parser.parse_unary, (ParseState, OPERATOR{9, Tokens.EX_OR, false}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR{1}))
    precompile(Parser.parse_operator, (ParseState, SyntaxNode, OPERATOR{1}))
    precompile(Parser.parse_operator, (ParseState, INSTANCE, OPERATOR{1, Tokens.EQ, false}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR{1, Tokens.EQ, false}))
    precompile(Parser.parse_operator, (ParseState, INSTANCE, OPERATOR{1, Tokens.PLUS_EQ, false}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR{1, Tokens.PLUS_EQ, false}))
    precompile(Parser.parse_operator, (ParseState, INSTANCE, OPERATOR{1, Tokens.STAR_EQ, false}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR{1, Tokens.STAR_EQ, false}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR{2}))
    precompile(Parser.parse_operator, (ParseState, SyntaxNode, OPERATOR{2}))
    precompile(Parser.parse_operator, (ParseState, INSTANCE, OPERATOR{2, Tokens.CONDITIONAL, false}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR{2, Tokens.CONDITIONAL, false}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR{3, Tokens.RIGHT_ARROW}))
    precompile(Parser.parse_operator, (ParseState, SyntaxNode, OPERATOR{3, Tokens.RIGHT_ARROW}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR{4}))
    precompile(Parser.parse_operator, (ParseState, SyntaxNode, OPERATOR{4}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR{5}))
    precompile(Parser.parse_operator, (ParseState, SyntaxNode, OPERATOR{5}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR{6}))
    precompile(Parser.parse_operator, (ParseState, SyntaxNode, OPERATOR{6}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR{8, Tokens.COLON}))
    precompile(Parser.parse_operator, (ParseState, SyntaxNode, OPERATOR{8, Tokens.COLON}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR{9, Tokens.PLUS}))
    precompile(Parser.parse_operator, (ParseState, SyntaxNode, OPERATOR{9, Tokens.PLUS}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR{9, Tokens.PLUS, false}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR{11, Tokens.STAR}))
    precompile(Parser.parse_operator, (ParseState, SyntaxNode, OPERATOR{11, Tokens.STAR}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR{14}))
    precompile(Parser.parse_operator, (ParseState, SyntaxNode, OPERATOR{14}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR{15}))
    precompile(Parser.parse_operator, (ParseState, SyntaxNode, OPERATOR{15}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR{0, Tokens.DDDOT}))
    precompile(Parser.parse_operator, (ParseState, SyntaxNode, OPERATOR{0, Tokens.DDDOT}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR{20, Tokens.PRIME}))
    precompile(Parser.parse_operator, (ParseState, SyntaxNode, OPERATOR{20, Tokens.PRIME}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR{20, Tokens.ANON_FUNC}))
    precompile(Parser.parse_operator, (ParseState, SyntaxNode, OPERATOR{20, Tokens.ANON_FUNC}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR{1}))
    precompile(Parser.parse_operator, (ParseState, SyntaxNode, OPERATOR{1}))
    precompile(Parser.parse_operator, (ParseState, EXPR, OPERATOR))
    precompile(Parser.parse_operator, (ParseState, SyntaxNode, OPERATOR))
    precompile(Parser.parse_curly, (ParseState, EXPR, OPERATOR))
    precompile(Parser.parse_curly, (ParseState, SyntaxNode, OPERATOR)) 
    precompile(Parser.parse_do, (ParseState, EXPR, OPERATOR))
    precompile(Parser.parse_do, (ParseState, SyntaxNode, OPERATOR)) 
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.FUNCTION}}))
    precompile(Parser.parse_call, (ParseState, EXPR, OPERATOR))
    precompile(Parser.parse_call, (ParseState, SyntaxNode, OPERATOR))
    precompile(Parser.parse_generator, (ParseState, EXPR, OPERATOR))
    precompile(Parser.parse_generator, (ParseState, SyntaxNode, OPERATOR))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.BEGIN}}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.QUOTE}}))
    precompile(Parser.parse_block, (ParseState,))
    precompile(Parser.parse_block, (ParseState, Int))
    precompile(Parser.parse_block, (ParseState, Int, EXPR))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.IF}}))
    precompile(Parser.parse_if, (ParseState,))
    precompile(Parser.parse_if, (ParseState, Bool))
    precompile(Parser.parse_if, (ParseState, Bool, Vector{SyntaxNode}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.LET}}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.FOR}}))
    precompile(Parser.parse_ranges, (ParseState,))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.WHILE}}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.BREAK}}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.CONTINUE}}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.MACRO}}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.IMPORT}}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.IMPORTALL}}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.USING}}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.EXPORT}}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.MODULE}}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.BAREMODULE}}))
    precompile(Parser.parse_dot_mod, (ParseState,))
    precompile(Parser.parse_imports, (ParseState,))
    precompile(Parser.parse_export, (ParseState,))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.CONST}}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.GLOBAL}}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.LOCAL}}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.RETURN}}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.END}}))
    precompile(Parser.parse_ref, (ParseState, EXPR))
    precompile(Parser.parse_ref, (ParseState, SyntaxNode))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.TRY}}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.ABSTRACT}}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.BITSTYPE}}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.TYPEALIAS}}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.TYPE}}))
    precompile(Parser.parse_kw, (ParseState, Type{Val{Tokens.IMMUTABLE}}))
    precompile(Parser.parse_struct, (ParseState, LITERAL))
end
