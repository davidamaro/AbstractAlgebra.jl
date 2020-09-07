export Partition, AllParts, YoungTableau, SkewDiagram
export rowlength, collength, hooklength, dim, isrimhook, leglength, axialdistance
export encontrar_posicion, determinar_coeficiente_irrep_yamanouchi
export generar_matriz, primero_lexi, encontrar_esquina, encontrar_malo_imp!
export indice_tablon_semistandard, content, Θ, tablon_standar_asociado_a_semiestandar
export calcula_proto_permutacion, calcular_sα, genera_funcion

using SparseArrays
using Primes

import LinearAlgebra:  dot, I
import Combinatorics:  permutations

const Content = Vector{T} where T <: Integer
const Irrep = Vector{T} where T <: Integer
#using LinearAlgebra

##############################################################################
#
#   Partition type, AbstractVector interface
#
##############################################################################

@doc Markdown.doc"""
    size(p::Partition)
> Return the size of the vector which represents the partition.

# Examples:
```jldoctest; setup = :(using AbstractAlgebra)
julia> p = Partition([4,3,1]); size(p)
(3,)
```
"""
size(p::Partition) = size(p.part)

Base.IndexStyle(::Type{Partition}) = Base.IndexLinear()

@doc Markdown.doc"""
    getindex(p::Partition, i::Integer)
> Return the `i`-th part (in decreasing order) of the partition.
"""
getindex(p::Partition, i::Integer) = p.part[i]

Base.sum(p::Partition) = p.n

@doc Markdown.doc"""
    setindex!(p::Partition, v::Integer, i::Integer)
> Set the `i`-th part of partition `p` to `v`.
> `setindex!` will throw an error if the operation violates the non-increasing assumption.
"""
function setindex!(p::Partition, v::Integer, i::Integer)
   prev = sum(p)
   nex = 1
   if i != 1
      prev = p[i-1]
   end
   if i != length(p)
      nex = p[i+1]
   end
   nex <= v <= prev || throw(ArgumentError("Partition must be positive and non-increasing"))
   p.n += v - p.part[i]
   p.part[i] = v
   return p
end

==(p::Partition, m::Partition) = sum(p) == sum(m) && p.part == m.part
hash(p::Partition, h::UInt) = hash(p.part, hash(Partition, h))

##############################################################################
#
#   IO for Partition
#
##############################################################################

function subscriptify(n::Int)
   subscript_0 = Int(0x2080) # Char(0x2080) -> subscript 0
   return join([Char(subscript_0 + i) for i in reverse(digits(n))])
end

function show(io::IO, p::Partition)
   uniq = unique(p.part)
   mults = [count(i -> i == u, p.part) for u in uniq]
   str = join((string(u)*subscriptify(m) for (u,m) in zip(uniq, mults)))
   print(io, str)
end

show(io::IO, ::MIME"text/plain", p::Partition) = show(io, p)

##############################################################################
#
#   Iterator interface for Integer AllParts
#
##############################################################################

const _numPartsTable = Dict{Int, Int}(0 => 1, 1 => 1, 2 => 2)
const _numPartsTableBig = Dict{Int, BigInt}()

@doc Markdown.doc"""
    _numpart(n::Integer)
> Return the number of all distinct integer partitions of `n`. The function
> uses Euler pentagonal number theorem for recursive formula. For more details
> see OEIS sequence [A000041](http://oeis.org/A000041). Note that
> `_numpart(0) = 1` by convention.
"""
function _numpart(n::Integer)
   if n < 0
      return 0
   elseif n < 395
      n = Int(n)
      lookuptable = _numPartsTable
   else
      n = BigInt(n)
      lookuptable = _numPartsTableBig
   end
   return _numpart(n, lookuptable)
end

function _numpart(n::T, lookuptable::Dict{Int, T}) where T<:Integer
   s = zero(T)
   if !haskey(lookuptable, n)
      for j in 1:floor(T, (1 + Base.sqrt(1 + 24n))/6)
         p1 = _numpart(n - div(j*(3j - 1), 2))
         p2 = _numpart(n - div(j*(3j + 1), 2))
         s += (-1)^(j - 1)*(p1 + p2)
      end
      lookuptable[n] = s
   end
   return lookuptable[n]
end

# Implemented following RuleAsc (Algorithm 3.1) from
#    "Generating All Partitions: A Comparison Of Two Encodings"
# by Jerome Kelleher and Barry O’Sullivan, ArXiv:0909.2331

function Base.iterate(A::AllParts)
   if A.n < 1
      return Partition(A.part, false), 1
   elseif A.n == 1
      A.part[1] = 1
      return Partition(A.part, false), 1
   else
      A.part .= 0
      A.part[2] = A.n
      k = 2
      y = A.part[k] - 1
      k -= 1
      x = A.part[k] + 1
      while x <= y
         A.part[k] = x
         y -= x
         k += 1
      end
      A.part[k] = x + y
      return Partition(reverse!(A.part[1:k]), false), k
   end
end

function Base.iterate(A::AllParts, k)
   if k == 1
      return nothing
   end
   return nextpart_asc(A.part, k)
end

Base.length(A::AllParts) = _numpart(A.n)
Base.eltype(::Type{AllParts{T}}) where T = Partition{T}
Base.size(A::AllParts) = (length(A),)

@inbounds function nextpart_asc(part, k)
   if k == 0
      return Partition(part, false), 1
   end
   y = part[k] - 1
   k -= 1
   x = part[k] + 1
   while x <= y
      part[k] = x
      y -= x
      k += 1
   end
   part[k] = x + y
   return Partition(reverse!(part[1:k]), false), k
end

@doc Markdown.doc"""
    conj(part::Partition)
> Return the conjugated partition of `part`, i.e. the partition corresponding
> to the Young diagram of `part` reflected through the main diagonal.

# Examples:
```jldoctest; setup = :(using AbstractAlgebra)
julia> p = Partition([4,2,1,1,1])
4₁2₁1₃

julia> conj(p)
5₁2₁1₂
```
"""
function Base.conj(part::Partition)
   p = Vector{Int}(undef, maximum(part))
   for i in 1:sum(part)
      for j in length(part):-1:1
         if part[j] >= i
            p[i] = j
            break
         end
      end
   end
   return Partition(p, false)
end

@doc Markdown.doc"""
    conj(part::Partition, v::Vector)
> Return the conjugated partition of `part` together with permuted vector `v`.
"""
function Base.conj(part::Partition, v::Vector)
   w = zeros(eltype(part), size(v))

   acc = Vector{Int}(undef, length(part)+1)
   acc[1] = 0
   for i in 1:length(part)
      acc[i+1] = acc[i] + part[i]
   end

   new_idx = 1
   cpart = conj(part)

   for (i, p) in enumerate(cpart)
      for j in 1:p
         w[new_idx] = (v[acc[j]+i])
         new_idx += 1
      end
   end

   return cpart, w
end

##############################################################################
#
#   Partition sequences and Murnaghan-Nakayama formula
#
##############################################################################

@doc Markdown.doc"""
    partitionseq(lambda::Partition)
> Return a sequence (as `BitVector`) of `false`s and `true`s constructed from
> `lambda`: tracing the lower contour of the Young Diagram associated to
> `lambda` from left to right a `true` is inserted for every horizontal and
> `false` for every vertical step. The sequence always starts with `true` and
> ends with `false`.
"""
function partitionseq(lambda::Partition)
   seq = trues(maximum(lambda) + length(lambda))
   j = lambda[end]
   for i in (length(lambda)-1):-1:1
      seq[j+1] = false
      j += lambda[i] - lambda[i+1] + 1
   end
   seq[j+1] = false
   return seq
end

partitionseq(v::Vector{T}) where T<:Integer = partitionseq(Partition(v))

@doc Markdown.doc"""
    partitionseq(seq::BitVector)
> Return the essential part of the sequence `seq`, i.e. a subsequence starting
> at first `true` and ending at last `false`.
"""
partitionseq(seq::BitVector) = seq[something(findfirst(isequal(true), seq), 0):something(findlast(isequal(false), seq), 0)]

@doc Markdown.doc"""
    isrimhook(R::BitVector, idx::Integer, len::Integer)
> `R[idx:idx+len]` forms a rim hook in the Young Diagram of partition
> corresponding to `R` iff `R[idx] == true` and `R[idx+len] == false`.
"""
function isrimhook(R::BitVector, idx::Integer, len::Integer)
   return (R[idx+len] == false) && (R[idx] == true)
end

@doc Markdown.doc"""
    MN1inner(R::BitVector, mu::Partition, t::Integer, charvals)
> Return the value of $\lambda$-th irreducible character on conjugacy class of
> permutations represented by partition `mu`, where `R` is the (binary)
> partition sequence representing $\lambda$. Values already computed are stored
> in `charvals::Dict{Tuple{BitVector,Vector{Int}}, Int}`.
> This is an implementation (with slight modifications) of the
> Murnaghan-Nakayama formula as described in
>
>     Dan Bernstein,
>     "The computational complexity of rules for the character table of Sn"
>     _Journal of Symbolic Computation_, 37(6), 2004, p. 727-748.
"""
function MN1inner(R::BitVector, mu::Partition, t::Integer, charvals)
   if t > length(mu)
      chi = 1
   elseif mu[t] > length(R)
      chi = 0
   else
      chi = 0
      sgn = false

      for j in 1:mu[t]-1
         if R[j] == false
            sgn = !sgn
         end
      end
      for i in 1:length(R)-mu[t]
         if R[i] != R[i+mu[t]-1]
            sgn = !sgn
         end
         if isrimhook(R, i, mu[t])
            R[i], R[i+mu[t]] = R[i+mu[t]], R[i]
            essR = (partitionseq(R), mu[t+1:end])
            if !haskey(charvals, essR)
               charvals[essR] = MN1inner(R, mu, t+1, charvals)
            end
            chi += (-1)^Int(sgn)*charvals[essR]
            R[i], R[i+mu[t]] = R[i+mu[t]], R[i]
         end
      end
   end
   return chi
end

##############################################################################
#
#   YoungTableau type, AbstractArray interface
#
##############################################################################

YoungTableau(p::Vector{T}, fill=collect(1:sum(p))) where T<:Integer = YoungTableau(Partition(p), fill)

@doc Markdown.doc"""
    size(Y::YoungTableau)
> Return `size` of the smallest array containing `Y`, i.e. the tuple of the
> number of rows and the number of columns of `Y`.

# Examples:
```jldoctest; setup = :(using AbstractAlgebra)
julia> y = YoungTableau([4,3,1]); size(y)
(3, 4)
```
"""
size(Y::YoungTableau) = (length(Y.part), Y.part[1])

Base.IndexStyle(::Type{<:YoungTableau}) = Base.IndexLinear()

function inyoungtab(t::Tuple{Integer,Integer}, Y::YoungTableau)
   i,j = t
   i > length(Y.part) && return false
   Y.part[i] < j && return false
   return true
end

@doc Markdown.doc"""
    getindex(Y::YoungTableau, n::Integer)
> Return the column-major linear index into the `size(Y)`-array. If a box is
> outside of the array return `0`.

# Examples:
```jldoctest; setup = :(using AbstractAlgebra)
julia> y = YoungTableau([4,3,1])
┌───┬───┬───┬───┐
│ 1 │ 2 │ 3 │ 4 │
├───┼───┼───┼───┘
│ 5 │ 6 │ 7 │
├───┼───┴───┘
│ 8 │
└───┘

julia> y[1]
1

julia> y[2]
5

julia> y[4]
2

julia> y[6]
0
```
"""
function getindex(Y::YoungTableau, n::Integer)
   if n < 1 #|| n > length(Y)
      throw(BoundsError(Y.fill, n))
   else
     i, j = Tuple(CartesianIndices(Y)[n])
      if inyoungtab((i,j), Y)
         k = sum(Y.part[1:i-1]) + j
         return Y.fill[k]
      else
         return 0
      end
   end
end

function ==(Y1::YoungTableau,Y2::YoungTableau)
   Y1.part == Y2.part || return false
   Y1.fill == Y2.fill || return false
   return true
end

hash(Y::YoungTableau, h::UInt) = hash(Y.part, hash(Y.fill, hash(typeof(Y), h)))

##############################################################################
#
#   String I/O for YoungTableaux
#
##############################################################################

function Base.replace_in_print_matrix(Y::YoungTableau, i::Integer, j::Integer, s::AbstractString)
   inyoungtab((i,j), Y) ? s : Base.replace_with_centered_mark(s, c=' ')
end

const _border = Dict{Symbol,String}(
:vertical => "│",
:horizontal => "─",

:topleft => "┌", # corners
:topright => "┐",
:bottomleft => "└",
:bottomright => "┘",

:downstem => "┬", #top edge
:upstem => "┴", #bottom edge

:rightstem => "├", # left edge
:leftstem => "┤", # right edge

:cross => "┼")

function boxed_str(Y::YoungTableau, fill=Y.fill)
   r,c = size(Y)
   w = max(length(string(maximum(fill))), 3)
   horizontal = repeat(_border[:horizontal], w)

   diagram = String[]
   s = String("")

   counter = 1

   for i in 1:r
      if i == 1 # top rule:
         s =_border[:topleft]*
            join(Iterators.repeated(horizontal, c), _border[:downstem])*
            _border[:topright]

      else # upper rule:
         s = _border[:rightstem]

         if Y.part[i-1] - Y.part[i] > 0
            s *= join(Iterators.repeated(horizontal, Y.part[i]),
               _border[:cross])
            s *=_border[:cross]

            s *= join(Iterators.repeated(horizontal,
                  Y.part[i-1] - Y.part[i]),
               _border[:upstem])
            s *= _border[:bottomright]
         else
            s *= join(Iterators.repeated(horizontal, Y.part[i]),
               _border[:cross])
            s *= _border[:leftstem]
         end
      end
      push!(diagram, s)

      # contents of each row:
      s = _border[:vertical]
      for j in 1:Y.part[i]
         s *= rpad(lpad(fill[counter], div(w, 2) + 1), w) *_border[:vertical]
         counter += 1
      end
      push!(diagram, s)
   end

   # bottom rule
   s = _border[:bottomleft]
   s *= join(Iterators.repeated(horizontal, Y.part[r]), _border[:upstem])
   s *= _border[:bottomright]
   push!(diagram, s)

   return join(diagram, "\n")
end

mutable struct YoungTabDisplayStyle
   format::Symbol
end

const _youngtabstyle = YoungTabDisplayStyle(:diagram)

@doc Markdown.doc"""
    setyoungtabstyle(format::Symbol)
> Select the style in which Young tableaux are displayed (in REPL or in general
> as string). This can be either
> * `:array` - as matrices of integers, or
> * `:diagram` - as filled Young diagrams (the default).
>
> The difference is purely esthetical.

# Examples:
```jldoctest; setup = :(using AbstractAlgebra)
julia> Generic.setyoungtabstyle(:array)
:array

julia> p = Partition([4,3,1]); YoungTableau(p)
 1  2  3  4
 5  6  7
 8

julia> Generic.setyoungtabstyle(:diagram)
:diagram

julia> YoungTableau(p)
┌───┬───┬───┬───┐
│ 1 │ 2 │ 3 │ 4 │
├───┼───┼───┼───┘
│ 5 │ 6 │ 7 │
├───┼───┴───┘
│ 8 │
└───┘
```
"""
function setyoungtabstyle(s::Symbol)
   @assert s in (:diagram, :array)
   _youngtabstyle.format = s
   _youngtabstyle.format
end

function Base.show(io::IO, ::MIME"text/plain", Y::YoungTableau)
   if _youngtabstyle.format == :array
      Base.print_matrix(io, Y)
   elseif _youngtabstyle.format == :diagram
      print(io, boxed_str(Y))
   end
end

##############################################################################
#
#   Misc functions for YoungTableaux
#
##############################################################################
@doc Markdown.doc"""
    primero_lexi(YoungTableau) -> YoungTableau
    Computes the first ---in lexicographic order---
    Standard Tableaux.
# Examples:
```jldoctest; setup = :(using AbstractAlgebra)
julia> pat = YoungTableau([2,1])
julia> primero_lexi(pat)
┌───┬───┬
│ 1 │ 3 │
├───┼───┼
│ 2 │
├───┼
```
"""
function primero_lexi(pat)
    mat = Matrix(matrix_repr(pat))

    orco = zeros(Int, size(mat))
    inx = 1
    for (ind,val) in enumerate(mat)
        if val != 0
            orco[ind] = inx
            inx += 1
        end
    end
    #@show orco, reshape(orco', *(size(orco)...))
    fill!(pat, filter(x -> x > 0,reshape(orco', *(size(orco)...)) ) )
    pat
end
@doc Markdown.doc"""
    encontrar_malo_imp!(tablon de Young)
"""
function encontrar_malo_imp!(tab)
    i_max = 0
    jm = 0
    malo = 0

    lista_recorridos = typeof((1,2))[]

    for l in 1:sum(tab.part)
        i,j = encontrar_posicion(tab, l)
        push!(lista_recorridos,(i,j))
        if i >= i_max
            i_max = i
            jm = l
            #println("el maximo hasta el momento: $l")
        else
            malo = l
            break
        end

    end

    mat = matrix_repr(tab)
    pos_maximo = encontrar_posicion(tab, jm)
    pos_malo = encontrar_posicion(tab, malo)

    pos_maximo = encontrar_esquina(lista_recorridos)

    mat[pos_maximo...] = malo

    filtrado = filter(x -> x != pos_maximo, sort(lista_recorridos,by = x->(x[2], x[1])) )
    for (ind, val) in enumerate(filtrado)
        if val == pos_maximo
            continue
        else
            mat[val...] = ind
        end
    end

    yup = *(size(mat|>Matrix)...)
    #@show mat
    fill!(tab, filter(x -> x > 0, reshape(mat', yup)))

    tab
end
@doc Markdown.doc"""
    encontrar_esquina(lista tuplas)
"""
function encontrar_esquina(lista)
    (fila_malo, col_malo) = lista[end]#pop!(lista)
    i_max, jm = (1,1)
    if col_malo == 1
        return lista[end-1]
    else
       pre_col = col_malo - 1
        while (i_max <= fila_malo && pre_col > 0)
            (i_max, jm) = filter(x -> x[2] == pre_col, lista[1:end-1])[end]
            pre_col -= 1
        end
    end
    (i_max, jm)
end

@doc Markdown.doc"""
    matrix_repr(Y::YoungTableau)
> Construct sparse integer matrix representing the tableau.

# Examples:
```jldoctest; setup = :(using AbstractAlgebra)
julia> y = YoungTableau([4,3,1]);


julia> matrix_repr(y)
3×4 SparseArrays.SparseMatrixCSC{Int64,Int64} with 8 stored entries:
  [1, 1]  =  1
  [2, 1]  =  5
  [3, 1]  =  8
  [1, 2]  =  2
  [2, 2]  =  6
  [1, 3]  =  3
  [2, 3]  =  7
  [1, 4]  =  4
```
"""
function encontrar_posicion(Y::YoungTableau{T}, entrada::Int64) where T
   k=1
   for (idx, p) in enumerate(Y.part)
      for (idy, q) in enumerate(Y.fill[k:k+p-1])
        if q == entrada
          return idx, idy
        end
      end
      k += p
   end
   0,0
end

function matrix_repr(Y::YoungTableau{T}) where T
   tab = spzeros(T, length(Y.part), Y.part[1])
   k=1
   for (idx, p) in enumerate(Y.part)
      tab[idx, 1:p] = Y.fill[k:k+p-1]
      k += p
   end
   return tab
end

@doc Markdown.doc"""
    fill!(Y::YoungTableaux, V::Vector{<:Integer})
> Replace the fill vector `Y.fill` by `V`. No check if the resulting tableau is
> standard (i.e. increasing along rows and columns) is performed.

# Examples:
```jldoctest; setup = :(using AbstractAlgebra)
julia> y = YoungTableau([4,3,1])
┌───┬───┬───┬───┐
│ 1 │ 2 │ 3 │ 4 │
├───┼───┼───┼───┘
│ 5 │ 6 │ 7 │
├───┼───┴───┘
│ 8 │
└───┘

julia> fill!(y, [2:9...])
┌───┬───┬───┬───┐
│ 2 │ 3 │ 4 │ 5 │
├───┼───┼───┼───┘
│ 6 │ 7 │ 8 │
├───┼───┴───┘
│ 9 │
└───┘
```
"""
function Base.fill!(Y::YoungTableau, V::AbstractVector{<:Integer})
   length(V) == sum(Y.part) || throw(ArgumentError("Length of fill vector must match the size of partition"))
   Y.fill .= V
   return Y
end

@doc Markdown.doc"""
    conj(Y::YoungTableau)
> Return the conjugated tableau, i.e. the tableau reflected through the main
> diagonal.

# Examples
```jldoctest; setup = :(using AbstractAlgebra)
julia> y = YoungTableau([4,3,1])
┌───┬───┬───┬───┐
│ 1 │ 2 │ 3 │ 4 │
├───┼───┼───┼───┘
│ 5 │ 6 │ 7 │
├───┼───┴───┘
│ 8 │
└───┘

julia> conj(y)
┌───┬───┬───┐
│ 1 │ 5 │ 8 │
├───┼───┼───┘
│ 2 │ 6 │
├───┼───┤
│ 3 │ 7 │
├───┼───┘
│ 4 │
└───┘
```
"""
Base.conj(Y::YoungTableau) = YoungTableau(conj(Y.part, Y.fill)...)

@doc Markdown.doc"""
    rowlength(Y::YoungTableau, i, j)
> Return the row length of `Y` at box `(i,j)`, i.e. the number of boxes in the
> `i`-th row of the diagram of `Y` located to the right of the `(i,j)`-th box.

# Examples
```jldoctest; setup = :(using AbstractAlgebra)
julia> y = YoungTableau([4,3,1])
┌───┬───┬───┬───┐
│ 1 │ 2 │ 3 │ 4 │
├───┼───┼───┼───┘
│ 5 │ 6 │ 7 │
├───┼───┴───┘
│ 8 │
└───┘

julia> Generic.rowlength(y, 1,2)
2

julia> Generic.rowlength(y, 2,3)
0

julia> Generic.rowlength(y, 3,3)
0
```
"""
rowlength(Y::YoungTableau, i::Integer, j::Integer) = Y.part[i] < j ? 0 : Y.part[i]-j

function rowlength(Y::YoungTableau, u::Integer) 
  i,j = encontrar_posicion(Y, u)
  Y.part[i] < j ? 0 : Y.part[i]-j
end

@doc Markdown.doc"""
    collength(Y::YoungTableau, i, j)
> Return the column length of `Y` at box `(i,j)`, i.e. the number of boxes in
> the `j`-th column of the diagram of `Y` located below of the `(i,j)`-th box.

# Examples
```jldoctest; setup = :(using AbstractAlgebra)
julia> y = YoungTableau([4,3,1])
┌───┬───┬───┬───┐
│ 1 │ 2 │ 3 │ 4 │
├───┼───┼───┼───┘
│ 5 │ 6 │ 7 │
├───┼───┴───┘
│ 8 │
└───┘

julia> Generic.collength(y, 1,1)
2

julia> Generic.collength(y, 1,3)
1

julia> Generic.collength(y, 2,4)
0
```
"""
collength(Y::YoungTableau, i::Integer, j::Integer) = count(x -> x>=j, view(Y.part, i+1:lastindex(Y.part)))

function collength(Y::YoungTableau, u::Integer) 
  i,j = encontrar_posicion(Y, u)
  count(x -> x>=j, view(Y.part, i+1:lastindex(Y.part)))
end

@doc Markdown.doc"""
    hooklength(Y::YoungTableau, i, j)
> Return the hook-length of an element in `Y` at position `(i,j)`, i.e the
> number of cells in the `i`-th row to the right of `(i,j)`-th box, plus the
> number of cells in the `j`-th column below the `(i,j)`-th box, plus `1`.
>
> Return `0` for `(i,j)` not in the tableau `Y`.

# Examples
```jldoctest; setup = :(using AbstractAlgebra)
julia> y = YoungTableau([4,3,1])
┌───┬───┬───┬───┐
│ 1 │ 2 │ 3 │ 4 │
├───┼───┼───┼───┘
│ 5 │ 6 │ 7 │
├───┼───┴───┘
│ 8 │
└───┘

julia> hooklength(y, 1,1)
6

julia> hooklength(y, 1,3)
3

julia> hooklength(y, 2,4)
0
```
"""
function hooklength(Y::YoungTableau, i::Integer, j::Integer)
   if inyoungtab((i,j), Y)
      return rowlength(Y, i, j) + collength(Y, i, j) + 1
   else
      return 0
   end
end
# david en joda
@doc Markdown.doc"""
    axialdistance(Y::YoungTableau, i, j)
> Return the hook-length of an element in `Y` at position `(i,j)`, i.e the
> number of cells in the `i`-th row to the right of `(i,j)`-th box, plus the
> number of cells in the `j`-th column below the `(i,j)`-th box, plus `1`.
>
> Return `0` for `(i,j)` not in the tableau `Y`.

# Examples
```jldoctest; setup = :(using AbstractAlgebra)
julia> y = YoungTableau([4,3,1])
┌───┬───┬───┬───┐
│ 1 │ 2 │ 3 │ 4 │
├───┼───┼───┼───┘
│ 5 │ 6 │ 7 │
├───┼───┴───┘
│ 8 │
└───┘

julia> axialdistance(y, 1,1)
6

julia> axialdistance(y, 1,3)
3

julia> axialdistance(y, 2,4)
0
```
"""
function axialdistance(Y::YoungTableau, u::Integer, v::Integer)
  #fila, columna
  i,j = encontrar_posicion(Y, u)
  k,l = encontrar_posicion(Y, v)

  #k - l - (i - j)
  l - k - (j - i)
end

function determinar_coeficiente_irrep_yamanouchi(Y::YoungTableau, u::Integer)
  #fila, columna
  v = u - 1
  i,j = encontrar_posicion(Y, u)
  k,l = encontrar_posicion(Y, v)
  
  if i == k
    return 1
  elseif j == l
    return -1 
  else
    return 0
  end
end

function intercambio(Y, m, irrep::Array{Int64,1})
    V = deepcopy(Y)
    relleno = V.fill
    @assert m > 1 && m <= maximum([length(irrep), length(relleno)])
    posiciones = Int[]
    for (indx, elem) in enumerate(relleno)
        if elem == m || elem == m - 1
            push!(posiciones, indx)
        end
        if length(posiciones) == 2
            break
        end
    end

    if length(posiciones) > 1
      tmp = relleno[posiciones[1]]
      relleno[posiciones[1]] = relleno[posiciones[2]]
      relleno[posiciones[2]] = tmp
      fill!(V, relleno)
    else
      #tmp = relleno[posiciones[1]]
      relleno[posiciones[1]] = m
      #relleno[posiciones[2]] = tmp
      fill!(V, relleno)
    end

    V
end

function bloque_yamanouchi(mat, lista_tablones, i, k, m, irrep::Array{Int64,1})
    #spzeros(Int, 3,2)
    tab_1 = lista_tablones[i]
    tab_2 = lista_tablones[k]
    if i < k && lista_tablones[i] == intercambio(lista_tablones[k], m,irrep)
        mat[i,i] = -((axialdistance(tab_1,m, m-1))^(-1))
        mat[i,k] = sqrt(1-((axialdistance(tab_1,m, m-1))^(-2)))
        mat[k,i] = sqrt(1-((axialdistance(tab_1,m, m-1))^(-2)))
        mat[k,k] = ((axialdistance(tab_1,m, m-1))^(-1))
    end
    mat
end

function generar_matriz(lista_tablones::Array{AbstractAlgebra.Generic.YoungTableau{Int64},1}, m::Int, irrep::Array{Int64,1})
    mat = spzeros(length(lista_tablones), length(lista_tablones))

    for i in 1:length(lista_tablones), k in 1:length(lista_tablones)
        if i == k && mat[i,i] == 0
            mat[i,i] = determinar_coeficiente_irrep_yamanouchi(lista_tablones[i], m)
        elseif i < k
            bloque_yamanouchi(mat, lista_tablones, i, k, m, irrep)
        end
    end


    mat
end

@doc Markdown.doc"""
  generar_matriz(Y::Array{YoungTableau}, p::Perm) -> SparseMatrixCSC
> Return non-zero entries of the orthogonal irrep given by the permutation 'p'
> The information of the irrep is introduced via 'Y' which is a list of
> Standard Young tableaux

# Examples
```jldoctest; setup = :(using AbstractAlgebra)
julia> guilty = StandardYoungTableaux([3,2])
julia> generar_matriz(guilty, Perm([2,1,3,4,5]))
[1, 1]  =  -1.0
[2, 2]  =  1.0
[3, 3]  =  -1.0
[4, 4]  =  1.0
[5, 5]  =  1.0

julia> generar_matriz(guilty, Perm([1,3,2,4,5]))
[1, 1]  =  0.5
[2, 1]  =  0.866025
[1, 2]  =  0.866025
[2, 2]  =  -0.5
[3, 3]  =  0.5
[4, 3]  =  0.866025
[3, 4]  =  0.866025
[4, 4]  =  -0.5
[5, 5]  =  1.0
```
"""
function generar_matriz(patrones::Array{AbstractAlgebra.Generic.YoungTableau{Int64},1}, p::Perm, irrep::Array{Int64,1})
    descom_en_trans = descomp_total(p)
    len = length(patrones)
    mat = I#spzeros(len,len)
    for (a,b) in descom_en_trans # a + 1 = b
        mat = generar_matriz(patrones, b, irrep)*mat
    end
    mat
end

@doc Markdown.doc"""
    dim(Y::YoungTableau) -> BigInt
> Return the dimension (using hook-length formula) of the irreducible
> representation of permutation group $S_n$ associated the partition `Y.part`.
>
> Since the computation overflows easily `BigInt` is returned. You may perform
> the computation of the dimension in different type by calling `dim(Int, Y)`.

# Examples
```jldoctest; setup = :(using AbstractAlgebra)
julia> dim(YoungTableau([4,3,1]))
70

julia> dim(YoungTableau([3,1])) # the regular representation of S_4
3
```
"""
dim(Y::YoungTableau) = dim(BigInt, Y)

function dim(::Type{T}, Y::YoungTableau) where T<:Integer
   n, m = size(Y)
   num = factorial(T(sum(Y.part)))
   den = reduce(*, (hooklength(Y,i,j) for i in 1:n, j in 1:m if j <= Y.part[i]), init=one(T))
   return divexact(num, den)::T
end

##############################################################################
#
#   SkewDiagrams
#
##############################################################################

SkewDiagram(lambda::AbstractVector{<:Integer}, mu::AbstractVector{<:Integer}) = SkewDiagram(Partition(lambda), Partition(mu))
/(lambda::Partition, mu::Partition) = SkewDiagram(lambda, mu)

@doc Markdown.doc"""
    size(xi::SkewDiagram)
> Return the size of array where `xi` is minimally contained.
> See `size(Y::YoungTableau)` for more details.
"""
Base.size(xi::SkewDiagram) = (length(xi.lam), xi.lam[1])

Base.IndexStyle(::Type{<:SkewDiagram}) = Base.IndexLinear()

@doc Markdown.doc"""
    in(t::Tuple{Integer,Integer}, xi::SkewDiagram)
> Check if box at position `(i,j)` belongs to the skew diagram `xi`.
"""
function Base.in(t::Tuple{Integer, Integer}, xi::SkewDiagram)
   i,j = t
   if i <= 0 || j <= 0
      return false
   elseif i > length(xi.lam) || j > xi.lam[1]
      return false
   elseif length(xi.mu) >= i
      return xi.mu[i] < j <= xi.lam[i]
   else
      return j <= xi.lam[i]
   end
end

@doc Markdown.doc"""
    getindex(xi::SkewDiagram, n::Integer)
> Return `1` if linear index `n` corresponds to (column-major) entry in
> `xi.lam` which is not contained in `xi.mu`. Otherwise return `0`.
"""
function getindex(xi::SkewDiagram, n::Integer)
   i, j = Tuple(CartesianIndices(xi)[n])
   (i,j) in xi && return 1
   return 0
end

==(xi::SkewDiagram, psi::SkewDiagram) = xi.lam == psi.lam && xi.mu == psi.mu
hash(xi::SkewDiagram, h::UInt) = hash(xi.lam, hash(xi.mu, hash(typeof(xi), h)))

###############################################################################
#
#   String I/O
#
###############################################################################

function Base.replace_in_print_matrix(xi::SkewDiagram, i::Integer, j::Integer, s::AbstractString)
   if j > xi.lam[i]
      Base.replace_with_centered_mark(s, c=' ')
   elseif i <= length(xi.mu)
      j > xi.mu[i] ? s : Base.replace_with_centered_mark(s)
   else
      s
   end
end

##############################################################################
#
#   Misc functions for SkewDiagrams
#
##############################################################################

@doc Markdown.doc"""
    matrix_repr(xi::SkewDiagram)
> Return a sparse representation of the diagram `xi`, i.e. a sparse array `A`
> where `A[i,j] == 1` if and only if `(i,j)` is in `xi.lam` but not in `xi.mu`.
"""
function matrix_repr(xi::SkewDiagram)
   skdiag = spzeros(eltype(xi), size(xi)...)
   for i in 1:length(xi.mu)
      skdiag[i, xi.mu[i]+1:xi.lam[i]] .= 1
   end
   for i in length(xi.mu)+1:length(xi.lam)
      skdiag[i,1:xi.lam[i]] .= 1
   end
   return skdiag
end

@doc Markdown.doc"""
    has_left_neighbor(xi::SkewDiagram, i::Integer, j::Integer)
> Check if box at position `(i,j)` has neighbour in `xi` to the left.
"""
function has_left_neighbor(xi::SkewDiagram, i::Integer, j::Integer)
   if j == 1
      return false
   else
      return (i,j) in xi && (i,j-1) in xi
   end
end

@doc Markdown.doc"""
    has_bottom_neighbor(xi::SkewDiagram, i::Integer, j::Integer)
> Check if box at position `(i,j)` has neighbour in `xi` below.
"""
function has_bottom_neighbor(xi::SkewDiagram, i::Integer, j::Integer)
   if i == length(xi.lam)
      return false
   else
      return (i,j) in xi && (i+1,j) in xi
   end
end

@doc Markdown.doc"""
    isrimhook(xi::SkewDiagram)
> Check if `xi` represents a rim-hook diagram, i.e. its diagram is
> edge-connected and contains no $2\times 2$ squares.
"""
function isrimhook(xi::SkewDiagram{T}) where T
   i = 1
   j = xi.lam[1]
   while i != length(xi.lam) && j != 1
      left = has_left_neighbor(xi, i,j)
      bottom = has_bottom_neighbor(xi, i,j)
      if left && bottom # there is 2×2 square in xi
         return false
      elseif left
         j -= 1
      elseif bottom
         i += 1
      else
         lam_tail = xi.lam[i+1:end]
         mu_tail = zeros(T, length(lam_tail))
         mu_tail[1:length(xi.mu)-i] = xi.mu[i+1:end]

         if any(lam_tail .- mu_tail .> 0)
            return false # xi is disconnected
         else
            return true # we arrived at the end of xi
         end
      end
   end
   return true
end

@doc Markdown.doc"""
    leglength(xi::SkewDiagram[, check::Bool=true])
> Compute the leglength of a rim-hook `xi`, i.e. the number of rows with
> non-zero entries minus one. If `check` is `false` function will not check
> whether `xi` is actually a rim-hook.
"""
function leglength(xi::SkewDiagram, check::Bool=true)
   if check
      isrimhook(xi) || throw(ArgumentError("$xi is not a rimhook. leglength is defined only for rim hooks"))
   end
   m = zeros(length(xi.lam))
   m[1:length(xi.mu)] = xi.mu
   return sum((xi.lam .- m) .> 0) - 1
end
####
function gen_etiqueta(lista)
    len = length(lista)
    #@show  prime(3), Base.sqrt(prime(3))
    #@show  prime(3), sqrt(prime(3))
    dot([Base.sqrt(prime(i)) for i in 1:len], lista)
end

@doc Markdown.doc"""
    indice_tablon_semistandard(p::YoungTableau)
> Returns the index of the standard YoungTableau such that the function mapping
> the filling of the semistandard to the standard Tableau is non decreasing

# Examples:
```jldoctest; setup = :(using AbstractAlgebra)
julia> patrones_gt_prueba = genera_patrones([2,1,0]);
julia> young_prueba = map(YoungTableau, patrones_gt_prueba);
julia> for elemento in young_prueba
           icons_abstract_thee(elemento)
       end
```
"""
function indice_tablon_semistandard(tablon_semistandard)
    particion = (tablon_semistandard.part) |> collect
    tablon_semistandard_v = YoungTableau(particion)# |> primero_lexi
    orden = sortperm(tablon_semistandard.fill)
    diccionario = generate_dictionary(orden)#Dict()
    nuevo_fill = [diccionario[x] for x in tablon_semistandard_v.fill]
    tablon_resultado_permutacion = AbstractAlgebra.fill!(tablon_semistandard_v, nuevo_fill)
    tablones_standard = StandardYoungTableaux(particion)
    etiquetas_semi = map(gen_etiqueta, map(x->x.fill, tablones_standard))
    
    return findfirst(x -> x ≈ gen_etiqueta(tablon_resultado_permutacion.fill), etiquetas_semi)
end

@doc Markdown.doc"""
    tablon_standar_asociado_a_semiestandar(tablon_semistandard::YoungTableau)
> Returns a YoungTableau corresponding to the standard YoungTableau such that
> f is non decreasing.
"""
function tablon_standar_asociado_a_semiestandar(tablon_semistandard)
    particion = (tablon_semistandard.part) |> collect
    tablon_standard = YoungTableau(particion)# |> primero_lexi

    orden = sortperm(tablon_semistandard.fill)
    diccionario = generate_dictionary(orden)#Dict()
    nuevo_fill = [diccionario[x] for x in tablon_standard.fill]

    tablon_resultado_permutacion = AbstractAlgebra.fill!(tablon_standard, nuevo_fill)
    tablones_standard = StandardYoungTableaux(particion)
    etiquetas_semi = map(gen_etiqueta, map(x->x.fill, tablones_standard))
    
    pos = findfirst(x -> x ≈ gen_etiqueta(tablon_resultado_permutacion.fill), etiquetas_semi)
    tablones_standard[pos]
end
@doc Markdown.doc"""
calcula_proto_permutacion(proto::Array{Int64,1})
Notese que el orden en que se ingresa la matriz es igual a la traspuesta.
Esto es debido a la forman en la que Julia recorre matrices.
> calcula_proto_permutacion([2 0 1 1])
1
1
2
2
"""
function calcula_proto_permutacion(proto::Array{Int64,1})
    len = length(proto) |> sqrt |> Int
    new_proto = reshape(proto, len, len)'

    mult = 0
    yard = Array{Int64,1}[]
    for i in 1:len
        densidad = vcat(fill.(1:len, new_proto[mult*len + 1:len*(mult + 1)])...)
        push!(yard, densidad)
        mult += 1
    end
    vcat(yard...)
end

@doc Markdown.doc"""
    genera_funcion(patron_semi::YoungTableau, irrep::Vector{T})
    genera_funcion(patron_semi::YoungTableau)
> Genera un diccionario con la función entre un tablón standar
> y uno semistandar.
# Examples:
```
julia> t_u = YoungTableau([2,2, 1]);
julia> fill!(t_u, [1,2,3,3,4]);
julia> genera_funcion(t_u)
Dict(4=>4, 2=>2, 3=>3, 5=>5, 1=>1)
```
"""
function genera_funcion(patron_semi::YoungTableau, irrep::Vector{T}) where T <: Integer
    len = length(irrep)
    relleno_semi = patron_semi.fill

    if length(relleno_semi) >= len
      return genera_funcion(patron_semi)
    end

    tablones_standard = StandardYoungTableaux((patron_semi.part) |> collect)
    tablon_standard = tablon_standar_asociado_a_semiestandar(patron_semi)
    relleno_standard = tablon_standard.fill
    
    parejas = zip(relleno_standard, relleno_semi) |> collect
    dd = Dict{Int64, Int64}()

    for (va, viene) in parejas
      dd[va] = viene
    end
    nuevos = setdiff!(collect(1:len), relleno_standard)
    for i in nuevos
      cercano = sort(relleno_standard, by=(x -> abs(x-i))) |> first
      dd[i] = dd[cercano]
    end

    dd
end

function genera_funcion(patron_semi::YoungTableau)
    relleno_semi = patron_semi.fill
    tablones_standard = StandardYoungTableaux((patron_semi.part) |> collect)
    tablon_standard = tablon_standar_asociado_a_semiestandar(patron_semi)
    relleno_standard = tablon_standard.fill
    
    parejas = zip(relleno_standard, relleno_semi) |> collect
    dd = Dict{Int64, Int64}()

    for (va, viene) in parejas
      #dd[viene] = va
      dd[va] = viene
    end
    dd
end

@doc Markdown.doc"""
    Θ(patron_semi::YoungTableau)
> Computes coefficient Θ. Returns a Float64
"""
function Θ(patron_semi::YoungTableau, irrep::Array{Int64,1})
    relleno_semi = patron_semi.fill
    tablones_standard = StandardYoungTableaux((patron_semi.part) |> collect)
    tablon_standard = tablon_standar_asociado_a_semiestandar(patron_semi)
    relleno_standard = tablon_standard.fill
    n = ((patron_semi.fill) |> collect |> length)
    n = irrep |> length
    
    parejas = zip(relleno_standard, relleno_semi) |> collect
    prod = 1.0
    for k in 1:n
        α = map(first,filter((xx -> (last(xx) == k)), parejas))
        if length(α) > 1
            for indx in 1:length(α), indy in indx+1:length(α)
                x,y = α[indx], α[indy]
                if x > y
                  prod *= (1 + (1/axialdistance(tablon_standard, y, x)))
                else
                  prod *= (1 + (1/axialdistance(tablon_standard, x, y)))
                end
            end
        end
    end
    prod
end


function generate_dictionary(lista)
    fvars = Dict()
    for (n, f) in enumerate(lista)
        fvars[f] = n
    end
    fvars
end

@doc Markdown.doc"""
    content(p::Partition, λ::Irrep)
> Return the size of the vector which represents the partition.
> ADVERTENCIA content sin λ ignora los 0s de la irrep.

# Examples:
```jldoctest; setup = :(using AbstractAlgebra)
julia> ss = YoungTableau(GTPattern([[2,1,0,0],[2,1,0],[2,1],[2]]));
julia> content(ss, [2,1,0,0])
[2,2,0,0]

julia> ss = YoungTableau(GTPattern([[2,1,0,0],[2,1,0],[2,1],[2]]));
julia> content(ss, [2,1,0,0])
[2,2,0]
```
"""
function content(y::YoungTableau, λ::Irrep)
    relleno = y.fill
    if length(relleno) <= length(λ)
      len = length(λ)
    else
      len = length(relleno)
    end
    tablon_nuevo = tablon_standar_asociado_a_semiestandar(y).fill
    nuevo_relleno = deepcopy(relleno)
    anterior = relleno[1]
    for i in 1:len
      if i ∉ tablon_nuevo
        push!(nuevo_relleno, anterior)
      end
      if i > length(relleno)
        break
      end
      relleno[i] > anterior ? anterior = relleno[i] : continue
    end

    [count(y -> x == y,nuevo_relleno) for x in 1:len]
end

function content(p::YoungTableau)
    relleno = p.fill
    len = length(relleno)
    [count(y -> x == y,relleno) for x in 1:len]
end

@doc Markdown.doc"""
    calcular_sα(c::Content)
> Return the size of the vector which represents the partition.

# Examples:
```
julia> c = [0,1,2]; calcular_sα(c)
```
"""
function calcular_sα(c::Content)
    inferior = 1
    superior = length(c) 
    list_perm_output = Perm{Int64}[]
    for sub_cjto in c
        if sub_cjto == 0
            continue
        elseif sub_cjto == 1
            inferior += 1
        elseif sub_cjto > 1 && length(list_perm_output) == 0
            conjunto = collect(inferior:(inferior + sub_cjto - 1))
            permutaciones = permutations(conjunto) |> collect

            for p in permutaciones
                lista = sortperm(vcat(collect(1:inferior - 1), p, collect((inferior + sub_cjto):superior)))
                push!(list_perm_output, Perm(lista))
            end
            inferior += sub_cjto
        else
            conjunto = collect(inferior:(inferior + sub_cjto - 1))
            permutaciones = permutations(conjunto)

            tmp = Perm{Int64}[]
            for p in permutaciones
                lista = sortperm(vcat(collect(1:inferior - 1), p , collect((inferior + sub_cjto):superior)))
                for elem in list_perm_output
                  push!(tmp, elem*Perm(lista))
                end
            end
            list_perm_output = tmp
            inferior += sub_cjto
        end
        push!(list_perm_output, Perm(1:superior |> collect))
        unique!(list_perm_output)
    end
    if length(list_perm_output) == 0
      return [Perm(1:superior |> collect)]
    end
    list_perm_output
end

function calcular_sα(tablon::YoungTableau)
  contenido = content(tablon)
  inferior = 1
  superior = length(contenido)
  list_perm_output = Perm[]
  for sub_cjto in contenido
      if sub_cjto == 0
          continue
      elseif sub_cjto == 1
          inferior += 1
      elseif sub_cjto > 1
          conjunto = collect(inferior:(inferior + sub_cjto - 1))
          permutaciones = permutations(conjunto)

          for p in permutaciones
              lista = vcat(collect(1:inferior - 1), p, collect((inferior + sub_cjto):superior))
              push!(list_perm_output, Perm(lista))
          end
          inferior += 1
      end
      unique!(list_perm_output)
  end
  if length(list_perm_output) == 0
    return [Perm(1:superior |> collect)]
  end
  list_perm_output
end
