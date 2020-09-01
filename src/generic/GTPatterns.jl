#export Partition, AllParts, YoungTableau, SkewDiagram
#export rowlength, collength, hooklength, dim, isrimhook, leglength, axialdistance
export GTPattern
export basis_states, obtener_diferencias_patron#, prematuro_pesos#, YoungTableau


using Base.Iterators

##############################################################################
#
#   Partition type, AbstractVector interface
#
##############################################################################

#@doc Markdown.doc"""
#    size(p::Partition)
#> Return the size of the vector which represents the partition.
#
## Examples:
#```jldoctest; setup = :(using AbstractAlgebra)
#julia> p = Partition([4,3,1]); size(p)
#(3,)
#```
#"""
#size(p::Partition) = size(p.part)

mutable struct GTPattern
    filas::Array{Array{Int64,1},1}
    ultima_fila::Array{Int64,1}
    function GTPattern(filas::Array{Array{Int64,1},1})
      final = filas[end]
      new(filas, final)
    end
end

function Base.show(io::IO, ::MIME"text/plain", G::GTPattern)
    list_of_rows = G.filas
    pattern = ""
    n = length(list_of_rows)
    mitad = n ÷ 2
    between = isodd(n)
    cont = 1
    i = 1
    length_first_row = length(list_of_rows[1])*2
    for row in list_of_rows
        pattern *= "│ "
        for number in row
            pattern *= string(number)
            pattern *= " "
        end
        pattern *= repeat(" ", length_first_row - 2*length(row))
        if i <= mitad
            pattern *= repeat(" ", cont - 1)
            pattern *= "╲\n"
            cont += 1
        elseif between
            pattern *= repeat(" ", cont - 1)
            pattern *= "╳\n"
            between = false
        else
            if !between && cont > mitad
                cont -= 1
            end
            pattern *= repeat(" ", cont - 1)
            pattern *= "╱\n"
            cont -= 1
        end
        i += 1
    end

    print(io, pattern)
end

function primera!(fila, a::GTPattern)
    if length(a.ultima_fila) == 0
        a.ultima_fila = fila
    end
    push!(a.filas, fila)
    a
end

function determinar_siguientes(fila)
    siguientes = UnitRange{Int64}[]
    for i in 1:length(fila)-1
        push!(siguientes, fila[i+1]:fila[i] )
    end
    product(siguientes...)
end

function generar_siguiente_fila(tab::GTPattern)
    siguientes = determinar_siguientes(tab.ultima_fila)

    lista_patrones = GTPattern[]
    for sig in siguientes
        tmp = deepcopy(tab)
        tmp.ultima_fila = collect(sig)
        push!(tmp.filas, collect(sig))

        push!(lista_patrones, tmp)
    end
    lista_patrones
end

function generar_siguiente_fila(tabs::Array{GTPattern,1})
    lista_patrones = GTPattern[]
    for tab in tabs
        siguientes = determinar_siguientes(tab.ultima_fila)


        for sig in siguientes
            tmp = deepcopy(tab)
            tmp.ultima_fila = collect(sig)
            push!(tmp.filas, collect(sig))

            push!(lista_patrones, tmp)
        end
    end
    lista_patrones
end

function basis_states(irrep::Array{Int64,1})
    ejemplo = GTPattern([], [])
    primera!(irrep, ejemplo)
    multitud_prueba = generar_siguiente_fila(ejemplo);
    for i in 3:length(irrep)
        multitud_prueba = generar_siguiente_fila(multitud_prueba)
    end
    multitud_prueba
end

##############################################################################
#
#   Codigo para la traduccion
#
##############################################################################

function obtener_diferencias_patron(tab::GTPattern,fila::Int64)
    filas = tab.filas
    if fila > length(filas)
        throw(BoundsError("te pasas"))
    end
    longitud = length(filas) + 1

    diferencias = Int64[0]
    max = 0
    for fil in reverse(filas[1:longitud - fila])
        diferencia = fil[fila] - max
        if diferencia > 0
            push!(diferencias, diferencia)
            max = fil[fila]
        else
            push!(diferencias, 0)
        end
    end
    contenido = Int64[]
    i = fila
    for punto in diferencias[2:end]
        for j in 1:punto
            push!(contenido, i)
        end
        i += 1
    end
    contenido
end

function prematuro_pesos(tab::GTPattern)
    totales = [sum(x) for x in tab.filas]
    append!(totales,0)
    final = Int[]
    for i in (1:length(tab.filas)-1)
        push!(final, totales[i]-totales[i+1])
    end
    all(x -> x == 1, final)
end

#function YoungTableau(tab::GTPattern)
#    filas = tab.filas
#    len = filas[1] |> length
#    conjunto_contenido = [obtener_diferencias_patron(tab, x) for x in 1:len]
#    p = Partition(filter(x -> x>0, filas[1]))
#    YoungTableau(p, vcat(conjunto_contenido...))
#end
