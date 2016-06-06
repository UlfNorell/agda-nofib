
hs_files=

ghc_opts=$(hs_files) -O2 -funbox-strict-fields -optc-O -optc-mfpmath=sse -optc-msse2
agda_ghc_opts=$(patsubst %,--ghc-flag=%,$(ghc_opts))

agda_module=ReverseComplement
hs_module=ReverseComplement

default :
	agda -c $(agda_module).agda $(agda_ghc_opts)

prof : default
	ghc --make MAlonzo/Code/$(hs_module).hs $(ghc_opts) -prof -auto-all -main-is MAlonzo.Code.$(hs_module) -hisuf p_hi -osuf p_o -o $(agda_module)_p -fno-warn-overlapping-patterns

