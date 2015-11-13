
default :
	agda -c N-Body.agda --ghc-flag=NBodyPrim.hs

prof : default
	ghc --make MAlonzo/Code/NZ45ZBody.hs NBodyPrim.hs -O2 -prof -auto-all -main-is MAlonzo.Code.NZ45ZBody -hisuf p_hi -osuf p_o -o N-Body_p -fno-warn-overlapping-patterns

