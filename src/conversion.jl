import Base.Expr

Expr(x::INSTANCE{IDENTIFIER}) = Symbol(x.val)
Expr(x::INSTANCE{LITERAL}) = Base.parse(x.val)
Expr(x::INSTANCE{OPERATOR}) = Symbol(x.val)
Expr{T<:Expression}(x::Vector{T}) = Expr(:block, Expr.(x)...)
Expr(x::BLOCK) = Expr(:block, Expr.(x.args)...)

function Expr{T}(x::CHAIN{T})
    Expr(:call, Symbol(x.args[2].val), [Expr(x.args[i]) for i = 1:2:length(x.args)]...)
end

Expr(x::CHAIN{1}) = Expr(Symbol(x.args[2].val), Expr(x.args[1]), Expr(x.args[3]))
Expr(x::CHAIN{2}) = Expr(:if, Expr(x.args[1]), Expr(x.args[3]), Expr(x.args[5]))
Expr(x::CHAIN{3}) =  Expr(:(||), Expr(x.args[1]), Expr(x.args[3]))
Expr(x::CHAIN{4}) =  Expr(:(&&), Expr(x.args[1]), Expr(x.args[3]))

function Expr(x::CHAIN{6})
    if length(x.args)==3
        if x.args[2].val in ["<:", ">:"]
            return Expr(Expr(x.args[2]), Expr(x.args[1]), Expr(x.args[3]))
        else
            return Expr(:call, Expr(x.args[2]), Expr(x.args[1]), Expr(x.args[3]))
        end
    else
        return Expr(:comparison, Expr.(x.args)...)
    end
end

function Expr(x::CHAIN{8})
    if x.args[2].val == ":"
        if length(x.args) == 3
            Expr(:(:), Expr(x.args[1]), Expr(x.args[3]))
        else
            Expr(:(:), Expr(x.args[1]), Expr(x.args[3]), Expr(x.args[5]))
        end
    else
        Expr(Symbol(x.args[2].val), Expr(x.args[1]), Expr(x.args[3]))
    end
end

Expr(x::CHAIN{14}) =  Expr(:(::), Expr(x.args[1]), Expr(x.args[3]))

function Expr(x::CHAIN{15}) 
    if x.args[3] isa INSTANCE{IDENTIFIER}
        return Expr(:(.), Expr(x.args[1]), QuoteNode(Expr(x.args[3])))
    else
        return Expr(:(.), Expr(x.args[3]), Expr(x.args[3]))
    end
end

Expr(x::CHAIN{20}) =  Expr(:call, Symbol(x.args[1].val), Expr(x.args[2]))

Expr(x::CALL) = Expr(:call, Expr(x.name), Expr.(x.args)...)


Expr(x::CURLY) = Expr(:curly, Expr(x.name), Expr.(x.args)...)

Expr(x::KEYWORD_BLOCK{0}) = Symbol(x.opener.val)

Expr(x::KEYWORD_BLOCK{1}) = Expr(Symbol(x.opener.val), Expr(x.args[1]))    

Expr(x::KEYWORD_BLOCK{2}) = Expr(Symbol(x.opener.val), Expr.(x.args)...)

function Expr(x::KEYWORD_BLOCK{3})
    if x.opener.val in ["type", "module"]
        return Expr(Symbol(x.opener.val), true, Expr(x.args[1]), Expr(x.args[2]))
    elseif x.opener.val == "immutable"
        return Expr(:immutable, false, Expr(x.args[1]), Expr(x.args[2]))
    elseif x.opener.val == "baremodule"
        return Expr(:module, false, Expr(x.args[1]), Expr(x.args[2]))
    elseif x.opener.val=="function"
        if x.opener.start==x.opener.stop==0
            return Expr(:(=), Expr(x.args[1]), Expr(x.args[2]))
        else
            return Expr(Symbol(x.opener.val), Expr(x.args[1]), Expr(x.args[2]))
        end
    elseif x.opener.val == "begin"
        return Expr(x.args[1])
    else
        return Expr(Symbol(x.opener.val), Expr(x.args[1]), Expr(x.args[2]))
    end
end