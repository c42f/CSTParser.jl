type Iterator{T}
    i::Int
    n::Int
end
+{T}(s::Iterator{T}) = (s.i+=1;s)

start(x::INSTANCE) = 1
next(x::INSTANCE, i) = x, i+1
length(x::INSTANCE) = 1
done(x::INSTANCE, i) = i>1


"""
    start(x::EXPR)

Creates an interator state for `EXPR`s. One can then iterator through all
 elements of an expression as they are ordered in the original code including 
punctuation.
"""
function start(x::EXPR)
    if x.head == CALL
        if x.args[1] isa OPERATOR{9,Tokens.PLUS} || x.args[1] isa OPERATOR{11,Tokens.STAR}
            return Iterator{:opchain}(1, max(2, length(x.args)*2-3))
        elseif x.args[1] isa OPERATOR
            return Iterator{:op}(1, length(x.args) + length(x.punctuation))
        else
            return Iterator{:call}(1, length(x.args) + length(x.punctuation))
        end
    elseif issyntaxcall(x.head) || x.head isa OPERATOR{20, Tokens.ANON_FUNC}
        if x.head isa OPERATOR{8,Tokens.COLON}
            return Iterator{:(:)}(1, length(x.args) == 2 ? 3 : 5)
        end
        return Iterator{:syntaxcall}(1, length(x.args) + 1)
    elseif x.head == COMPARISON
        return Iterator{:comparison}(1, length(x.args))
    elseif x.head isa HEAD{Tokens.KW}
        return Iterator{:syntaxcall}(1, 1 + length(x.args))
    elseif x.head == MACROCALL
        return _start_macrocall(x)
    elseif x.head isa HEAD{Tokens.IF}
        return Iterator{:?}(1, 5)
    elseif x.head == BLOCK
        return Iterator{:block}(1, length(x.args) + length(x.punctuation))
    elseif x.head isa HEAD{InvisibleBrackets}
        return Iterator{:invisiblebrackets}(1, 3)
    elseif x.head == GENERATOR
        return _start_generator(x)
    elseif x.head == COMPREHENSION
        return _start_comprehension(x)
    elseif x.head == PARAMETERS
        return _start_parameters(x)
    elseif x.head == TYPED_COMPREHENSION
        return _start_typed_comprehension(x)
    # elseif x.head == TOPLEVEL
    elseif x.head isa HEAD{Tokens.TOPLEVEL}
        return _start_toplevel(x)
    elseif x.head == CURLY
        return _start_curly(x)
    elseif x.head == QUOTE
        return Iterator{:quote}(1, length(x.args) + length(x.punctuation))
    elseif x.head == REF
        return _start_ref(x)
    elseif x.head == VECT
        return _start_vect(x)
    elseif x.head == TUPLE
        if isempty(x.punctuation) || first(x.punctuation) isa PUNCTUATION{Tokens.COMMA}
            return Iterator{:tuplenoparen}(1, length(x.args) + length(x.punctuation))
        else
            return Iterator{:tuple}(1, length(x.args) + length(x.punctuation))
        end
    elseif x.head isa KEYWORD
        if x.head isa KEYWORD{Tokens.ABSTRACT} 
            return Iterator{:abstract}(1, 2)
        elseif x.head isa KEYWORD{Tokens.BAREMODULE}
            return Iterator{:module}(1, 4)
        elseif x.head isa KEYWORD{Tokens.BEGIN}
            return Iterator{:begin}(1, 3)
        elseif x.head isa KEYWORD{Tokens.BITSTYPE}
            return Iterator{:bitstype}(1, 3)
        elseif x.head isa KEYWORD{Tokens.BREAK}
            return Iterator{:break}(1, 1)
        elseif x.head isa KEYWORD{Tokens.CONST}
            return Iterator{:const}(1, 2)
        elseif x.head isa KEYWORD{Tokens.CONTINUE}
            return Iterator{:continue}(1, 1)
        elseif x.head isa KEYWORD{Tokens.DO}
            return _start_do(x)
        elseif x.head isa KEYWORD{Tokens.EXPORT}
            return Iterator{:export}(1, length(x.args)*2)
        elseif x.head isa KEYWORD{Tokens.FOR}
            return _start_for(x)
        elseif x.head isa KEYWORD{Tokens.FUNCTION}
            return _start_function(x)
        elseif x.head isa KEYWORD{Tokens.GLOBAL}
            return Iterator{:global}(1, 2)
        elseif x.head isa KEYWORD{Tokens.IF}
            return _start_if(x)
        elseif x.head isa KEYWORD{Tokens.IMMUTABLE}
            return Iterator{:type}(1, 4)
        elseif x.head isa KEYWORD{Tokens.LET}
            return _start_let(x)
        elseif x.head isa KEYWORD{Tokens.LOCAL}
            return Iterator{:local}(1, 2)
        elseif x.head isa KEYWORD{Tokens.IMPORT} || 
               x.head isa KEYWORD{Tokens.IMPORTALL} || 
               x.head isa KEYWORD{Tokens.USING}
            return _start_imports(x)
        elseif x.head isa KEYWORD{Tokens.MACRO}
            return Iterator{:module}(1, 4)
        elseif x.head isa KEYWORD{Tokens.MODULE}
            return Iterator{:module}(1, 4)
        elseif x.head isa KEYWORD{Tokens.RETURN}
            return Iterator{:return}(1, 2)
        elseif x.head isa KEYWORD{Tokens.TRY}
            return _start_try(x)
        elseif x.head isa KEYWORD{Tokens.TYPE}
            return Iterator{:type}(1, 4)
        elseif x.head isa KEYWORD{Tokens.TYPEALIAS}
            return Iterator{:typealias}(1, 3)
        elseif x.head isa KEYWORD{Tokens.WHILE}
            return _start_while(x)
        end
    end
end

done(x::EXPR, s::Iterator) = s.i > s.n
length(x::EXPR) = start(x).n
last(x::EXPR) = x[length(x)]

function Base.getindex(x::EXPR, i::Int)
    s = start(x)
    @assert i<=s.n
    s.i = i
    next(x, s)[1]
end

function Base.setindex!(x::EXPR, y, i::Int)
    x_old = x[i]
    if x.head == x_old
        x.head = y
        return
    else
        for (j,a) in enumerate(x.args)
            if a == x_old
                x.args[j] = y
                return
            end
        end
        for (j,a) in enumerate(x.punctuation)
            if a == x_old
                x.punctuation[j] = y
                return
            end
        end
    end
    error(BoundsError(x, i))
end

function _find(x::EXPR, n, path, ind)
    offset = 0
    @assert n <= x.span
    push!(path, x)
    for (i, a) in enumerate(x)
        if n > offset + a.span
            offset += a.span
        else
            push!(ind, i)
            return _find(a, n-offset, path, ind)
        end
    end
end

_find(x::Union{QUOTENODE,INSTANCE}, n, path, ind) = x

function Base.find(x::EXPR, n::Int)
    path = []
    ind = Int[]
    y = _find(x, n ,path, ind)
    return y, path, ind
end


Base.find(x, n::Symbol, list) = nothing
function Base.find(x::IDENTIFIER, n::Symbol, list)
    if x.val == n
        push!(list, x)
    end
end

function Base.find(x::EXPR, n::Symbol, list = [])
    for a in x
        find(a, n, list)
    end
    list
end