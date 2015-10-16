module Foo (main) where

data Peano = Z | S Peano

foo       :: Peano -> Int
foo Z     = 0
foo (S n) = let r = foo n
             in 1 + r

main :: Peano -> Int
main p = let q  = foo p
             q' = (1 + q)
          in div 100 q'
