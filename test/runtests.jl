using Test, TestSetExtensions
using ModelingToolkit, HomotopyContinuation
using ParameterEstimation

@info "Testing started"

@testset "All the tests" begin
	@includetests ARGS
end
