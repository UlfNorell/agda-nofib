
module NBodyPrim where

data Triple a b c = Triple !a !b !c

type Pos  = Triple Double Double Double
type Body = Triple Pos Pos Double

