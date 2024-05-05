using Test, TestSetExtensions, Nemo
using ModelingToolkit, HomotopyContinuation
using ParameterEstimation


macro includetests(testarg...)
	if length(testarg) == 0
		tests = []
	elseif length(testarg) == 1
		tests = testarg[1]
	else
		error("@includetests takes zero or one argument")
	end

	rootfile = "$(__source__.file)"
	mod = __module__

	quote
		tests = $tests
		rootfile = $rootfile

		if length(tests) == 0
			tests = readdir(dirname(rootfile))
			tests = filter(f -> endswith(f, ".jl") && f != basename(rootfile), tests)
		else
			tests = map(f -> string(f, ".jl"), tests)
		end

		println()

		for test in tests
			print(splitext(test)[1], ": ")
			Base.include($mod, test)
			println()
		end
	end
end

@info "Testing started"

@testset "All the tests" begin
	@includetests ARGS
end
