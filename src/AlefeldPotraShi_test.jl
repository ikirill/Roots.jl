include("AlefeldPotraShi.jl")

include("../test/RootTesting.jl")

@printf "%s\n" run_tests((f,b) -> Roots.a42(f, b...), name="a42"; abandon=true)
@printf "%s\n" run_tests((f,b) -> AlefeldPotraShi.a42(f, b...), name="a42"; verbose=true, abandon=true)
