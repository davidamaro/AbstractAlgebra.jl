using AbstractAlgebra, Test

#using SparseArrays, LinearAlgebra
#using AbstractAlgebra: mul! # disambiguate from LinearAlgebra.mul!
#
#if VERSION < v"0.7.0-DEV.2004"
#   using Base.Test
#else
#   using Test
#end
#
#include("AbstractAlgebra-test.jl")
@testset "Probando calcular_sα" begin
   c = [0,1,2]
   @test calcular_sα(c) == Perm.([[1,2,3], [1,3,2]])
   c = [0,2,1]
   @test calcular_sα(c) == Perm.([[1,2,3], [2,1,3]])
end

@testset "contenido: content" begin
   ss = GTPattern([[2,1,0,0],[2,1,0],[2,1],[2]]) |> YoungTableau
   @test content(ss, [2,1,0,0]) == [2,2,0,0]
end
