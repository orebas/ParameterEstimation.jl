"""
	estimate(model::ModelingToolkit.ODESystem,
			measured_quantities::Vector{ModelingToolkit.Equation},
			data_sample::Dict{Any, Vector{T}} = Dict{Any, Vector{T}}();
			at_time::T = 0.0, method = :homotopy, solver = Tsit5(),
			degree_range = nothing, real_tol = 1e-12,
			threaded = Threads.nthreads() > 1) where {T <: Float}

Run estimation over a range of interpolation degrees. Return the best estimate according to a heuristic:
	- the best estimate is the one with the smallest error between sample data and ODE solution with current parameters (estimates);

# Arguments
- `model::ModelingToolkit.ODESystem`: the ODE model;
- `measured_quantities::Vector{ModelingToolkit.Equation}`: the measured quantities (output functions that were sampled experimentally);
- `data_sample::Dict{Any, Vector{T}} = Dict{Any, Vector{T}}()`: the data sample, a dictionary with keys being the measured quantities and
																values being the corresponding data. Must include the time vector;
- `at_time::T = 0.0`: the time used for derivative computation;
- `report_time = nothing`: specify a time T, at which the initial conditions (state variables) will be estimated.  If "nothing", use the leftmost time.
- `method = :homotopy`: the method used for polynomial system solving. Can be one of :homotopy (recommended) or :msolve;
- `solver`: the ODE solver used for ODE solution computation (default: Vern9());
- `interpolators = nothing`: the set of interpolators to be used.  See examples. If `nothing`, a default is used which includes AAA, FLoater-Hormann, and Fourier interpolations;
- `real_tol` = 1e-14: the tolerance used for real root finding;
- `threaded = Threads.nthreads() > 1`: whether to use multiple threads for computation (determined automatically).

# Returns
- `result::Vector{EstimationResult}`: the result of the estimation, a vector of `EstimationResult` objects.
"""
function estimate(model::ModelingToolkit.ODESystem,
	measured_quantities::Vector{ModelingToolkit.Equation},
	data_sample::AbstractDict{Any, Vector{T}} = Dict{Any, Vector{T}}();
	inputs::Vector{ModelingToolkit.Equation} = Vector{ModelingToolkit.Equation}(),
	at_time::T = data_sample["t"][fld(length((data_sample["t"])), 2)],  #uses something akin to a midpoint by default
	method = :homotopy, solver = Vern9(),
	report_time = minimum(data_sample["t"]),
	interpolators = nothing, real_tol = 1e-14,
	threaded = Threads.nthreads() > 1, filtermode = :new, parameter_constraints = nothing, ic_constraints = nothing, disable_output = false) where {T <: Float}
	if (disable_output)
		logger = NullLogger()
		old_logger = global_logger(logger)
	end
	#println("DEBUG")
	if !(method in [:homotopy, :msolve])
		throw(ArgumentError("Method $method is not supported, must be one of :homotopy or :msolve."))
	end
	if threaded
		result = estimate_threaded(model, measured_quantities, inputs, data_sample;
			at_time = at_time, solver = solver,
			interpolators = interpolators,
			method = method,
			real_tol = real_tol)
	else
		result = estimate_serial(model, measured_quantities,
			inputs,
			data_sample;
			solver = solver, at_time = at_time, report_time,
			interpolators = interpolators, method = method,
			real_tol = real_tol, filtermode, parameter_constraints = parameter_constraints, ic_constraints = ic_constraints)
	end
	if (!disable_output)
		println("Final Results:")
		for each in result
			display(each)
		end
	end
	if (disable_output)
		global_logger(old_logger)
	end
	return result
end
