
default :
	agda -c --ghc-flag=-O2 PiDigits.agda

prof : default
	ghc --make MAlonzo/Code/PiDigits.hs -O2 -prof -auto-all -main-is MAlonzo.Code.PiDigits -hisuf p_hi -osuf p_o -o PiDigits_p -fno-warn-overlapping-patterns

