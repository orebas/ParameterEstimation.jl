






################# FUNCTIONS COPED FROM StructuralIdentifiability######################

"""
	make_substitution(f, var_sub, val_numer, val_denom)

Substitute a variable in a polynomial with an expression

Input:
- `f` - the polynomial
- `var_sub` - the variable to be substituted
- `var_numer` - numerator of the substitution expression
- `var_denom` - denominator of the substitution expression

Output:
- `polynomial` - result of substitution
"""
function make_substitution(
	f::P,
	var_sub::P,
	val_numer::P,
	val_denom::P,
) where {P <: MPolyRingElem}
	d = Nemo.degree(f, var_sub)

	result = 0
	@debug "Substitution in a polynomial of degree $d"
	for i in 0:d
		@debug "\t Degree $i"
		result += coeff(f, [var_sub], [i]) * (val_numer^i) * (val_denom^(d - i))
		@debug "\t Intermediate result of size $(length(result))"
	end
	return result
end

function eval_at_nemo(e::Num, vals::Dict)
	e = Symbolics.value(e)
	return eval_at_nemo(e, vals)
end

function eval_at_nemo(e::SymbolicUtils.BasicSymbolic, vals::Dict)
	if Symbolics.istree(e)
		# checking if it is a function of the form x(t), a bit dirty
		if length(Symbolics.arguments(e)) == 1 && "$(first(Symbolics.arguments(e)))" == "t"
			return vals[e]
		end
		# checking if this is a vector entry like x(t)[1]
		if Symbolics.operation(e) == getindex
			return vals[e]
		end
		# otherwise, this is a term
		args = map(a -> eval_at_nemo(a, vals), Symbolics.arguments(e))
		if Symbolics.operation(e) in (+, -, *)
			return Symbolics.operation(e)(args...)
		elseif isequal(Symbolics.operation(e), /)
			return //(args...)
		elseif isequal(Symbolics.operation(e), ^)
			if args[2] >= 0
				return args[1]^args[2]
			end
			return 1 // args[1]^(-args[2])
		end
		throw(Base.ArgumentError("Function $(Symbolics.operation(e)) is not supported"))
	elseif e isa Symbolics.Symbolic
		return get(vals, e, e)
	end
end

function eval_at_nemo(e::Union{Integer, Rational}, vals::Dict)
	return e
end







function eval_at_nemo(e::Union{Float16, Float32, Float64}, vals::Dict)
	if isequal(e % 1, 0)
		out = Int(e)
	else
		out = rationalize(e)
	end
	@warn "Floating point value $e will be converted to $(out)."
	return out
end











"""
	func str_to_var(s, ring::MPolyRing)

Convert a `string`-typed variable to a symbol.
"""
function str_to_var(s, ring::MPolyRing)
	ind = findfirst(v -> (string(v) == s), symbols(ring))
	if ind == nothing
		throw(Base.KeyError("Variable $s is not found in ring $ring"))
	end
	return gens(ring)[ind]
end


"""
	func make_derivative(var_name, der_order)

Given a variable name `var_name` add a derivative order `der_order`.
"""
function make_derivative(var_name, der_order)
	return (string(var_name, "_", der_order))
end


"""
	func differentiate_all(diff_poly, var_list, shft, max_ord)

Differentiate a polynomial `diff_poly` with respect to `var_list` up to `max_ord` order.
"""
function differentiate_all(diff_poly, var_list, shft, max_ord)
	result = 0
	for i in 1:(shft*(max_ord+1))
		result = result + derivative(diff_poly, var_list[i]) * var_list[i+shft]
	end
	return (result)
end


"""
	func add_zero_to_vars(poly::MPolyElem, new_ring::MPolyRing)
Converts a polynomial to a different polynomial ring.

## Input

- `poly::MPolyElem` - a polynomial to be converted
- `new_ring::MPolyRing` - a polynomial ring such that every variable name
appearing in poly appears among the generators

## Output
-  a polynomial in new_ring "equal" to `poly`
"""

function add_zero_to_vars(poly::MPolyRingElem, new_ring::MPolyRing)
	old_ring = parent(poly)
	# construct a mapping for the variable indices
	var_mapping = Array{Any, 1}()
	for u in symbols(old_ring)
		push!(
			var_mapping,
			findfirst(v -> (string(u, "_0") == string(v)), symbols(new_ring)),
		)
	end
	builder = MPolyBuildCtx(new_ring)
	for term in zip(exponent_vectors(poly), Nemo.coefficients(poly))
		exp, coef = term
		new_exp = [0 for _ in gens(new_ring)]
		for i in 1:length(exp)
			if exp[i] != 0
				if var_mapping[i] == nothing
					throw(Base.ArgumentError("The polynomial contains a variable not present in the new ring $poly"))
				else
					new_exp[var_mapping[i]] = exp[i]
				end
			end
		end
		push_term!(builder, base_ring(new_ring)(coef), new_exp)
	end
	return finish(builder)
end



function get_parameters(ode; initial_conditions = true)
	if initial_conditions
		return vcat(ode.parameters, ode.x_vars)
	else
		return ode.parameters
	end
end

function get_order_var(diff_var, non_jet_ring)
	rex = match(r"^(.*_)([0-9]+)$", string(diff_var))
	if rex === nothing
		return (["", ""])
	else
		return ([str_to_var(first(rex[1], length(rex[1]) - 1), non_jet_ring), parse(Int, rex[2])])
	end
end

function get_order_var2(diff_var, non_jet_vars, shft, s)
	idx = var_index(diff_var)
	if idx <= shft * (s + 3)
		return ([non_jet_vars[rem(idx - 1, shft)+1], div(idx - 1, shft)])
	else
		return ([non_jet_vars[idx-shft*(s+2)-1], 0])
	end
end



"""
	func _reduce_poly_mod_p(poly::MPolyElem{Nemo.fmpq}, p::Int)

Reduces a polynomial modulo p.
"""
function _reduce_poly_mod_p(poly::MPolyRingElem{fmpq}, p::Int)
	"""
	Reduces a polynomial over Q modulo p
	"""
	den = denominator(poly)
	num = change_base_ring(Nemo.ZZ, den * poly)
	if Nemo.GF(p)(den) == 0
		throw(Base.ArgumentError("Prime $p divides the denominator of $poly"))
	end
	return change_base_ring(Nemo.GF(p), num) * (1 // Nemo.GF(p)(den))
end


"""
	func create_jet_ring(var_list, param_list, max_ord)

Given a list of variables `var_list` and a list of parameters `param_list`, create a jet ring of derivatives up to order `max_ord`.
"""
function create_jet_ring(var_list, param_list, max_ord)
	varnames = vcat(vec(["$(s)_$i" for s in var_list, i in 0:max_ord]), "z_aux", ["$(s)_0" for s in param_list])
	return Nemo.PolynomialRing(Nemo.QQ, varnames)[1]
end

function get_equations(ode)
	non_jet_ring = ode.poly_ring
	all_indets = Nemo.gens(non_jet_ring)
	x_vars = ode.x_vars
	y_vars = ode.y_vars
	u_vars = ode.u_vars
	mu = ode.parameters

	n = length(x_vars)
	m = length(y_vars)
	u = length(u_vars)
	s = length(mu) + n

	Rjet = create_jet_ring(vcat(x_vars, y_vars, u_vars), mu, s + 2)
	gens_Rjet = Nemo.gens(Rjet)

	x_eqs = Array{Array{Nemo.AbstractAlgebra.RingElem, 1}, 1}(undef, n)
	y_eqs = Array{Array{Nemo.AbstractAlgebra.RingElem, 1}, 1}(undef, m)
	for i in 1:n
		numer, denom = ParameterEstimation.unpack_fraction(ode.x_equations[x_vars[i]])
		x_eqs[i] = [add_to_var(x_vars[i], Rjet, 1), add_zero_to_vars(numer, Rjet) // add_zero_to_vars(denom, Rjet)]
	end
	for i in 1:m
		numer, denom = ParameterEstimation.unpack_fraction(ode.y_equations[y_vars[i]])
		y_eqs[i] = [add_to_var(y_vars[i], Rjet, 0), add_zero_to_vars(numer, Rjet) // add_zero_to_vars(denom, Rjet)]
	end

	eqs = vcat(x_eqs, y_eqs)
	Q = foldl(lcm, [ParameterEstimation.unpack_fraction(ex[2])[2] for ex in eqs])

	return eqs, Q, x_eqs, y_eqs, x_vars, y_vars, u_vars, mu, all_indets, gens_Rjet
end

function get_x_eq(x_eqs::Vector{Vector{Nemo.AbstractAlgebra.RingElem}}, y_eqs::Vector{Vector{Nemo.AbstractAlgebra.RingElem}}, n::Int, m::Int, s::Int, u::Int, gens_Rjet)
	X = Array{Nemo.fmpq_poly}(undef, 0)
	X_eq = Array{Nemo.fmpq_poly}(undef, 0)
	for i in 1:n
		X = vcat(X, [Array{Nemo.fmpq_poly}(undef, 0)])
		poly_d = ParameterEstimation.unpack_fraction(x_eqs[i][1] - x_eqs[i][2])[1]
		for j in 0:s+1
			if j > 0
				poly_d = differentiate_all(poly_d, gens_Rjet, n + m + u, j)
			end
			leader = gens_Rjet[i+(n+m+u)*(j+1)]
			separant = derivative(poly_d, leader)
			X[i] = vcat(X[i], poly_d)
			X_eq = vcat(X_eq, [[leader, -(poly_d - separant * leader) // separant]])
		end
	end
	return X, X_eq
end

function get_y_eq(x_eqs::Vector{Vector{Nemo.AbstractAlgebra.RingElem}}, y_eqs::Vector{Vector{Nemo.AbstractAlgebra.RingElem}}, n::Int, m::Int, s::Int, u::Int, gens_Rjet)
	Y = Array{Nemo.fmpq_poly}(undef, 0)
	Y_eq = Array{Nemo.fmpq_poly}(undef, 0)
	for i in 1:m
		Y = vcat(Y, [Array{Nemo.fmpq_poly}(undef, 0)])
		poly_d = unpack_fraction(y_eqs[i][1] - y_eqs[i][2])[1]
		for j in 0:s+1
			if j > 0
				poly_d = differentiate_all(poly_d, gens_Rjet, n + m + u, j - 1)
			end
			leader = gens_Rjet[i+n+(n+m+u)*j]
			separant = derivative(poly_d, leader)
			Y[i] = vcat(Y[i], poly_d)
			Y_eq = vcat(Y_eq, [[leader, -(poly_d - separant * leader) // separant]])
		end
	end
	return Y, Y_eq
end


function parent_ring_change(poly::MPolyElem, new_ring::MPolyRing)
	old_ring = parent(poly)
	# construct a mapping for the variable indices
	var_mapping = Array{Any, 1}()

	for u in symbols(old_ring)
		push!(
			var_mapping,
			findfirst(v -> (string(u) == string(v)), symbols(new_ring)),
		)
	end
	builder = MPolyBuildCtx(new_ring)
	for term in zip(exponent_vectors(poly), Nemo.coefficients(poly))
		exp, coef = term
		new_exp = [0 for _ in gens(new_ring)]
		for i in 1:length(exp)
			if exp[i] != 0
				if var_mapping[i] == nothing
					throw(Base.ArgumentError("The polynomial contains a variable not present in the new ring $poly"))
				else
					new_exp[var_mapping[i]] = exp[i]
				end
			end
		end
		if typeof(coef) <: Nemo.fmpq
			push_term!(builder, base_ring(new_ring)(coef), new_exp)
		else
			push_term!(builder, base_ring(new_ring)(Nemo.data(coef)), new_exp)
		end
	end
	return finish(builder)
end

"""
	func compare_diff_var(dvl, dvr, non_jet_vars, shft, s)
	
Comparison method of variables based on order.
"""
function compare_diff_var(dvl, dvr, non_jet_vars, shft, s)
	vl, hl = get_order_var2(dvl, non_jet_vars, shft, s)
	vr, hr = get_order_var2(dvr, non_jet_vars, shft, s)
	if hl != hr
		return (hl > hr)
	end
	if length(string(vl)) != length(string(vr))
		return (length(string(vl)) > length(string(vr)))
	end
	return (vr >= vl)
end


function replace_random_with_known(params, vals, known_states_jet_form, known_values)
	for idx in 1:length(params)
		if params[idx] in known_states_jet_form
			found_index = 1
			for i in 1:length(known_states_jet_form)
				if known_states_jet_form[i] == params[idx]
					found_index = i
					break
				end
			end
			vals[idx] = fmpq(known_values[found_index])
		end
	end
	return vals
end

"""
	func sample_point(bound, x_vars, y_vars, u_variables, all_params, X_eq, Y_eq, Q)

Sample random values for parameters of the polynomial system.
"""
function sample_point(bound, x_vars, y_vars, u_variables, all_params, X_eq, Y_eq, Q; known_values = [], known_states_jet_form = [])
	local u_hat, theta_hat, all_subs

	s = length(all_params)
	y_hat_vars = Array{fmpq_mpoly}(undef, 0)
	y_hat_vals = Array{fmpq}(undef, 0)

	while true
		theta_hat = replace_random_with_known(all_params, [fmpq(rnd) for rnd in rand(0:bound, s)], known_states_jet_form, known_values)
		u_hat = replace_random_with_known(u_variables, [fmpq(rnd) for rnd in rand(0:bound, length(u_variables))], known_states_jet_form, known_values)
		all_subs = [vcat(all_params, u_variables), vcat(theta_hat, u_hat)]
		if Nemo.evaluate(Q, all_subs[1], all_subs[2]) == 0
			continue
		end
		vls = insert_zeros_to_vals(all_subs[1], all_subs[2])
		for i in 0:(s+1)
			for j in 1:length(y_vars)
				eq = Y_eq[(j-1)*(s+2)+i+1][2]
				vl = Oscar.evaluate(unpack_fraction(eq)[1], vls) // Oscar.evaluate(unpack_fraction(eq)[2], vls)
				y_hat_vars = vcat(y_hat_vars, Y_eq[(j-1)*(s+2)+i+1][1])
				y_hat_vals = vcat(y_hat_vals, vl)
				vls[var_index(Y_eq[(j-1)*(s+2)+i+1][1])] = vl
				all_subs = [vcat(all_subs[1], Y_eq[(j-1)*(s+2)+i+1][1]), vcat(all_subs[2], vl)]
			end
			for j in 1:length(x_vars)
				eq = X_eq[(j-1)*(s+2)+i+1][2]
				vl = Oscar.evaluate(unpack_fraction(eq)[1], vls) // Oscar.evaluate(unpack_fraction(eq)[2], vls)
				all_subs = [vcat(all_subs[1], X_eq[(j-1)*(s+2)+i+1][1]), vcat(all_subs[2], vl)]
				vls[var_index(X_eq[(j-1)*(s+2)+i+1][1])] = vl
			end
		end
		break
	end
	return ([[y_hat_vars, y_hat_vals], [u_variables, u_hat], [all_params, theta_hat], all_subs])
end


"""
	func insert_zeros_to_vals(var_arr, val_arr)

Insert zeros at positions based on the variables' index.
"""
function insert_zeros_to_vals(var_arr, val_arr)
	all_val_arr = zeros(fmpq, length(gens(parent(var_arr[1]))))
	for i in 1:length(var_arr)
		all_val_arr[var_index(var_arr[i])] = val_arr[i]
	end
	return all_val_arr
end


"""
	func jacobi_matrix(pol_arr, vrs, vals)

Generate a Jacobi matrix from a given array of polynomial `pol_arr`,
with respect to variables `vars`.
The matrix is evaluated at `vals` from a symbolic to numeric representation.
"""
function jacobi_matrix(pol_arr, vrs, vals)
	m = Nemo.MatrixSpace(Nemo.QQ, length(pol_arr), length(vrs))()
	for i in 1:length(pol_arr)
		for j in 1:length(vrs)
			m[i, j] = Oscar.evaluate(derivative(pol_arr[i], vrs[j]), vals)
		end
	end
	return (m)
end


"""
	func get_vars(diff_poly, var_list, non_jet_vars, shft, s)

Get variables from `diff_poly` based on the intersection with `var_list`.
"""
function get_vars(diff_poly, var_list, non_jet_vars, shft, s)
	return [v for v in vars(diff_poly) if get_order_var2(v, non_jet_vars, shft, s)[1] in var_list]
end

"""
	func add_to_var(vr, ring, r)

Convert a variable `vr` to a derivative of order `r` and convert the result to symbol.
"""
function add_to_var(vr, ring, r)
	return str_to_var(make_derivative(vr, r), ring)
end


function get_weights(ode, non_identifiable_parameters)
	eqs, Q, x_eqs, y_eqs, x_vars, y_vars, u_vars, mu, all_indets, gens_Rjet = get_equations(ode)

	non_jet_ring = ode.poly_ring
	all_indets = gens(non_jet_ring)
	z_aux = gens_Rjet[end-length(mu)]
	Rjet = gens_Rjet[1].parent

	n = length(x_vars)
	m = length(y_vars)
	u = length(u_vars)
	s = length(mu) + n

	current_level = 0
	visible_states = Dict{Int, Set{fmpq_mpoly}}(current_level => Set{fmpq_mpoly}())
	for eq in y_eqs
		numer, denom = unpack_fraction(eq[2])
		# visible states must be in non-jet representation!
		visible_states[current_level] = union(visible_states[current_level], Set(get_order_var(vn, non_jet_ring)[1] for vn in vars(numer)))
		visible_states[current_level] = union(visible_states[current_level], Set(get_order_var(vd, non_jet_ring)[1] for vd in vars(denom)))
	end

	differentiate_ = [true for each in ode.y_equations]
	Y_eqs = Dict()
	X_eqs = Dict(a[1] => a[2] for a in x_eqs)
	seen_so_far = Set()
	for j in 1:s+1
		current_level += 1
		for i in 1:m
			if differentiate_[i] # if we need to differentiate current output
				# get the polynomial, Nemo takes care of common denominator
				poly_d = unpack_fraction(y_eqs[i][1] - y_eqs[i][2])[1]

				# differentiate
				poly_d = differentiate_all(poly_d, gens_Rjet, n + m + u, j)

				# get the leader (y[i]_k, the symbol for derivative of y)
				leader = gens_Rjet[i+n+(n+m+u)*j]

				# differentiate the polynomial w.r.t. to leader to get the "coefficient" of leader
				separant = derivative(poly_d, leader)

				# write the equation
				Y_eqs[leader] = -(poly_d - separant * leader) // separant

				# split the numerator, the denominator
				numer, denom = unpack_fraction(Y_eqs[leader])

				# substitute any derivatives of states with the original odes
				for v in vars(numer)
					v_non_jet, v_order = get_order_var(v, non_jet_ring)
					if v_non_jet in x_vars && v_order > 0
						numer = make_substitution(numer, v, unpack_fraction(X_eqs[v])[1], unpack_fraction(X_eqs[v])[2])
						denom = make_substitution(denom, v, unpack_fraction(X_eqs[v])[1], unpack_fraction(X_eqs[v])[2])
					end
				end

				# find states that newly appeared
				visible_states[current_level] = union(get(visible_states, current_level, Set{fmpq_mpoly}()), Set(get_order_var(vn, non_jet_ring)[1] for vn in vars(numer)))
				visible_states[current_level] = union(get(visible_states, current_level, Set{fmpq_mpoly}()), Set(get_order_var(vd, non_jet_ring)[1] for vd in vars(denom)))

				# add previous level to "what we have seen so far"-set
				union!(seen_so_far, visible_states[current_level-1])
				# remove states that were seen on prevous level
				visible_states[current_level] = setdiff(visible_states[current_level], seen_so_far)
				Y_eqs[leader] = numer // denom

				if length(visible_states[current_level]) == 0
					differentiate_[i] = false
				end
				y_eqs[i] = [leader, Y_eqs[leader]]
			end
		end
		if sum(differentiate_) == 0
			break
		end
	end
	weights = Dict{fmpq_mpoly, Int64}()
	max_level = current_level - 1
	for (level, states) in visible_states
		for st in states
			if st in x_vars
				weights[st] = level + 1
			end
			if st in mu && level == max_level && !(st in non_identifiable_parameters)
				weights[st] = level + 1
			end
		end
	end
	weights[z_aux] = min(3, max_level)
	return weights
end




"""
The main structure that represents input ODE system.

Stores information about states (`x_vars`), outputs (`y_vars`), inputs (`u_vars`), parameters (`parameters`) and the equations.

This structure is constructed via `@ODEmodel` macro.
"""
struct ODE{P} # P is the type of polynomials in the rhs of the ODE system
	poly_ring::MPolyRing
	x_vars::Array{P, 1}
	y_vars::Array{P, 1}
	u_vars::Array{P, 1}
	parameters::Array{P, 1}
	x_equations::Dict{P, <:Union{P, Nemo.AbstractAlgebra.Generic.Frac{P}}}
	y_equations::Dict{P, <:Union{P, Nemo.AbstractAlgebra.Generic.Frac{P}}}

	function ODE{P}(
		x_vars::Array{P, 1},
		y_vars::Array{P, 1},
		x_eqs::Dict{P, <:Union{P, Nemo.AbstractAlgebra.Generic.Frac{P}}},
		y_eqs::Dict{P, <:Union{P, Nemo.AbstractAlgebra.Generic.Frac{P}}},
		inputs::Array{P, 1},
	) where {P <: MPolyRingElem{<:FieldElem}}
		# Initialize ODE
		# x_eqs is a dictionary x_i => f_i(x, u, params)
		# y_eqs is a dictionary y_i => g_i(x, u, params)
		if isempty(y_eqs)
			@info "Could not find output variables in the model."
		end
		poly_ring = parent(first(vcat(y_vars, x_vars)))
		u_vars = inputs
		parameters = filter(
			v -> (!(v in x_vars) && !(v in u_vars) && !(v in y_vars)),
			gens(poly_ring),
		)
		new{P}(poly_ring, x_vars, y_vars, u_vars, parameters, x_eqs, y_eqs)
	end

	function ODE{P}(
		x_eqs::Dict{P, <:Union{P, Nemo.AbstractAlgebra.Generic.Frac{P}}},
		y_eqs::Dict{P, <:Union{P, Nemo.AbstractAlgebra.Generic.Frac{P}}},
		inputs::Array{P, 1},
	) where {P <: MPolyRingElem{<:FieldElem}}
		x_vars = collect(keys(x_eqs))
		y_vars = collect(keys(y_eqs))
		return ODE{P}(x_vars, y_vars, x_eqs, y_eqs, inputs)
	end
end


########################################################################################







function unpack_fraction(f::AbstractAlgebra.Generic.Frac{<:AbstractAlgebra.MPolyElem})
	return (numerator(f), denominator(f))
end

# ----------
function unpack_fraction(f::AbstractAlgebra.MPolyElem)
	return (f, one(parent(f)))
end
