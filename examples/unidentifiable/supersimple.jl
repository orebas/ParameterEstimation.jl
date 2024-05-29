using ParameterEstimation
using ModelingToolkit, DifferentialEquations
solver = Vern9()

@parameters a b c d
@variables t x1(t) x2(t) x3(t)  y1(t) y2(t)
D = Differential(t)
states = [x1, x2, x3]
parameters = [a, b]

@named model = ODESystem([
		D(x1) ~ a ,
		D(x2) ~ b * x1,
		D(x3) ~ b * x1
	], t, states, parameters)
measured_quantities = [
	y1 ~ x1,
	y2 ~ x2,
]

ic = [1.0, 2.0, 3.0]
p_true = [3.0, 0.5]
time_interval = [-1.0, 1.0]
datasize = 21
data_sample = ParameterEstimation.sample_data(model, measured_quantities, time_interval,
	p_true, ic, datasize; solver = solver)
res = ParameterEstimation.estimate(model, measured_quantities, data_sample, at_time=-1.0)
