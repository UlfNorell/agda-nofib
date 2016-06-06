
module RevComplFFI where

data Colist' a = Nil | Cons a (Colist a)
newtype Colist a = Colist (Colist' a)

fromList :: [a] -> Colist a
fromList = foldr (\ x xs -> Colist (Cons x xs)) (Colist Nil)

getInputLines :: IO (Colist String)
getInputLines = fromList . lines <$> getContents
