using ParameterEstimation
using ModelingToolkit, DifferentialEquations
solver = Vern9()




@parameters p1 p3 p4 p6 p7
@variables t x1(t) x2(t) x3(t) u0(t) y1(t) y2(t)
D = Differential(t)
states = [x1, x2, x3, u0]
parameters = [p1, p3, p4, p6, p7]
@named model = ODESystem([
		D(x1) ~ -1.0 * p1 * x1 + x2 + u0,
		D(x2) ~ p3 * x1 - p4 * x2 + x3,
		D(x3) ~ p6 * x1 - p7 * x3,
		D(u0) ~ 1.0,
	], t, states, parameters)
measured_quantities = [
	y1 ~ x1,
	y2 ~ u0,
]

ic = [0.2, 0.4, 0.6, 0.8]
p_true = [0.167, 0.333, 0.5, 0.667, 0.833] # True Parameters
time_interval = [-0.5, 0.5]
datasize = 21
#=
@parameters p1 p2 p3 p4 p6 p7
@variables t x1(t) x2(t) x3(t) u0(t) y1(t) y2(t)
D = Differential(t)
states = [x1, x2, x3, u0]
parameters = [p1, p3, p4, p6, p7]
@named model = ODESystem([
		D(x1) ~ -1 * p1 * x1 + x2 + u0,
		D(x2) ~ p3 * x1 - p4 * x2 + x3,
		D(x3) ~ p6 * x1 - p7 * x3,
		D(u0) ~ 1,
	], t, states, parameters)
measured_quantities = [
	y1 ~ x1,
	y2 ~ u0,
]

ic = [1.0, -1.0, 1.0, -1.0]
time_interval = [0.0, 6.0]
p_true = [1, 1.3, 1.1, 1.2, 1] # True Parameters
datasize = 20
=#

data_sample = ParameterEstimation.sample_data(model, measured_quantities, time_interval,
	p_true, ic, datasize; solver = solver)

#plot(data_sample[x1])
#plot!(data_sample[u0])

res = ParameterEstimation.estimate(model, measured_quantities, data_sample)
