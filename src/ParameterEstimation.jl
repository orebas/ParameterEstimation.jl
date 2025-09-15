module ParameterEstimation

using PrecompileTools
#@recompile_invalidations begin

import DifferentialEquations: Tsit5
import DifferentialEquations: Vern9
import TaylorSeries: Taylor1
import OrderedCollections: OrderedDict
using BaryRational: BaryRational
using ForwardDiff: ForwardDiff
using LinearAlgebra: LinearAlgebra
using TaylorDiff: TaylorDiff
#using Suppressor

using ProgressMeter, Logging, Printf
using ModelingToolkit, LinearSolve, LinearAlgebra
using SIAN, HomotopyContinuation, Groebner, Nemo
using .ReturnCode
using StructuralIdentifiability: StructuralIdentifiability
import StructuralIdentifiability: ODE
using BaryRational
using ForwardDiff

#end
Float = Union{Float64, Float32, Float16, BigFloat}
include("includes.jl")

export check_identifiability, estimate, filter_solutions

@recompile_invalidations begin
	@compile_workload begin

		@parameters a
		@variables t x1(t) y1(t)
		D = Differential(t)
		states = [x1]
		parameters = [a]

		@named model = ODESystem([
				D(x1) ~ a * x1,
			], t, states, parameters)
		measured_quantities = [
			y1 ~ x1,
		]

		ic = [1.0]
		p_true = [2.0]
		time_interval = [-4.0, 4.0]
		datasize = 41
		model = complete(model)
		data_sample = ParameterEstimation.sample_data(model, measured_quantities, time_interval,
			p_true, ic, datasize;)
		res = ParameterEstimation.estimate(model, measured_quantities, data_sample)
	end
end

end
