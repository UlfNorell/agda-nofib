
module NBodyPrim where

data GenTriple a b c = Triple !a !b !c

type Triple a = GenTriple a a a
type Body = GenTriple (Triple Double) (Triple Double) Double

