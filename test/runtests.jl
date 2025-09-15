using Test
using ModelingToolkit, SIAN, HomotopyContinuation
using Nemo
using ParameterEstimation

@info "Testing started"

@testset "All the tests" begin
	@testset "Homotopy Estimation" begin
		include("homotopy_estimation_tests.jl")
	end
	@testset "Identifiability" begin
		include("identifiability_tests.jl")
	end
	@testset "MSolve Estimation" begin
		include("msolve_estimation_tests.jl")
	end
	@testset "Nemo HC Conversion" begin
		include("nemo_hc_conversion.jl")
	end
	@testset "Alg Indep" begin
		include("test_alg_indep.jl")
	end
	@testset "Varied Estimation" begin
		include("varied_estimation.jl")
	end
end
