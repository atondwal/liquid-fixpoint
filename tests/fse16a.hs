module FSE16a (b) where
{-
{-@ g :: x:Int -> {n:Int | x<n} -> Int -> {v : _ | fst v == snd v } @-}
g n x z = f n x z

f :: Int -> Int -> Int -> (Int,Int)
f n x z = if x<n
            then if z>x then f n (x+1) z else f n x (z+1)
            else (x,z)
-}

{-@ b :: x:Int -> y:Int -> {v : _ | x <= y => snd v = y && y <= x => fst v = x && fst v == snd v } @-}
b :: Int -> Int -> (Int,Int)
b x y = if x /= y
        then if x < y then b (x + 1) y else b x (y + 1)
        else (x, y)
