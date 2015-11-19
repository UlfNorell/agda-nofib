
ghc_opts=NBodyPrim.hs -O2 -funbox-strict-fields -optc-O -optc-mfpmath=sse -optc-msse2
agda_ghc_opts=$(patsubst %,--ghc-flag=%,$(ghc_opts))

default :
	agda -c N-Body.agda $(agda_ghc_opts)

pure :
	agda -c N-BodyPure.agda $(agda_ghc_opts)

prof : default
	ghc --make MAlonzo/Code/NZ45ZBody.hs $(ghc_opts) -prof -auto-all -main-is MAlonzo.Code.NZ45ZBody -hisuf p_hi -osuf p_o -o N-Body_p -fno-warn-overlapping-patterns

