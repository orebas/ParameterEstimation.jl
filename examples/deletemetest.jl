using ModelingToolkit, ParameterEstimation
using ModelingToolkit: t_nounits as t, D_nounits as D
@parameters a
@variables x1(t) y1(t)
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
time_interval = [-1.0, 1.0]
datasize = 41
model = complete(model)
data_sample = ParameterEstimation.sample_data(model, measured_quantities, time_interval,
	p_true, ic, datasize;)
res = ParameterEstimation.estimate(model, measured_quantities, data_sample)
