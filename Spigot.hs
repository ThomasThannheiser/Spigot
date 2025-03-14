module Spigot where

import Data.Ratio ((%))

{-- a little bit of Haskell --}

square :: Num a => a -> a
square x = x * x

squares :: [Int]
squares = [square x | x <- [1 .. 5]]

-- >>> map square [1 .. 5]

three :: Integer -> Integer
three x = 3

infinity :: Integer
infinity = 1 + infinity

-- >>> three infinity

fibs :: [Integer]
fibs = f (0, 1)
  where
    f (a, b) = a : f (b, a + b)

{-- calculating Pi --}

piFraction :: Double
piFraction = 355 / 113

--- >>> 22 / 7

-- >>> piFraction

-- >>> pi

{-- some infinite series --}

piLeibniz :: Int -> Double
piLeibniz n =
  fromRational . (4 *) . sum . take n
    $ zipWith (*) (cycle [1, -1]) [1 % (2 * k - 1) | k <- [1 ..]]

piWallis :: Int -> Double
piWallis n = 
  fromRational . (2 *) . product
    $ take n [let m = 4 * k * k in m % (m - 1) | k <- [1 ..]]

{-- Spigot algorithm for e and Pi 
    
    The calculation of e to many significant digits, Arthur H. J. Sale, 1968
    A Spigot Algorithm for the Digits of Pi, Stanley Rabinowitz, Stan Wagon, 1995

    implemented in Python

--}

{-- Unbounded Spigot Algorithms for the Digits of Pi, Jeremy Gibbons, 2005 --}

{-- streaming algorithm --}

stream :: (b -> c) -> (b -> c -> Bool) -> (b -> c -> b) -> (b -> a -> b) -> b -> [a] -> [c]
stream next isSafe produce consume b (a : as) =
  let c = next b
   in if isSafe b c
        then c : stream next isSafe produce consume (produce b c) (a : as)
        else stream next isSafe produce consume (consume b a) as

{-- converting from an infinite digit sequence in base m to an infinite sequence in base n --}

convert :: (Integer, Integer) -> [Integer] -> [Integer]
convert (m, n) = stream next isSafe produce consume init
  where
    init = (0 % 1, 1 % 1)
    next (u, v) = floor (u * v * n')
    isSafe (u, v) y = y == floor ((u + 1) * v * n')
    produce (u, v) y = (u - (y % 1) / (v * n'), v * n')
    consume (u, v) x = ((x % 1) + u * m', v / m')
    (m', n') = (m % 1, n % 1)

{-- Linear Fractional Transformation (Möbius Transformation) --}

type LFT = (Integer, Integer, Integer, Integer)

extr :: LFT -> Integer -> Rational
extr (q, r, s, t) x = fromInteger (q * x + r) / fromInteger (s * x + t)

unit :: LFT
unit = (1, 0, 0, 1)

compose :: LFT -> LFT -> LFT
compose (q, r, s, t) (u, v, w, x) = (q * u + r * w, q * v + r * x, s * u + t * w, s * v + t * x)

{-- Pi --}

-- pi = (2 + 1/3 *) . (2 + 2/5 *) . (2 + 3/7 *) ... (2 + i/(2 * i + 1) *) ...

piEuler :: [Integer]
piEuler = stream next safe prod cons init lfts
  where
    init = unit
    lfts = [(k, 4 * k + 2, 0, 2 * k + 1) | k <- [1 ..]]
    next z = floor (extr z 3)
    safe z n = n == floor (extr z 4)
    prod z n = compose (10, -10 * n, 0, 1) z
    cons = compose

{-- some further examples from TT --}

{-- Eulers constant --}

-- e = (1 + 1/1 *) . (1 + 1/2 *) . (1 + 1/3 *) ... (1 + 1/i *) ...

eEuler :: [Integer]
eEuler = stream next safe prod cons init lfts
  where
    init = unit
    lfts = [(1, k, 0, k) | k <- [1 ..]]
    next z = floor (extr z 1)
    safe z n = n == floor (extr z 2)
    prod z n = compose (10, -10 * n, 0, 1) z
    cons = compose

{-- natural logarithm --}

-- ln 2 = (0 + 1/2 *) . (1 + 1/2 *) . (1/2 + 1/2 *) . (1/3 + 1/2 *) ... (1/k + 1/2 *) ...

ln2 :: [Integer]
ln2 = stream next safe prod cons init lfts
  where
    init = (1, 0, 0, 2)
    lfts = [(k, 2, 0, 2 * k) | k <- [1 ..]]
    next z = floor (extr z 0)
    safe z n = n == floor (extr z 1)
    prod z n = compose (10, -10 * n, 0, 1) z
    cons = compose

{-- spigots from continuous fractions --}

{-- golden ratio --}

-- phi = (1 + 1/) . (1 + 1/) ...

phi :: [Integer]
phi = stream next safe prod cons init lfts
  where
    init = unit
    lfts = repeat (1, 1, 1, 0)
    next z = floor (extr z 1)
    safe z n = n == floor (extr z 2)
    prod z n = compose (10, -10 * n, 0, 1) z
    cons = compose

-- sqrt 2 = (1 + 1/) . (2 + 1/) . (2 + 1/) ...
-- 1 + sqrt 2 = (2 + 1/) . (2 + 1/) ....

sqrt2 :: [Integer]
sqrt2 = stream next safe prod cons init lfts
  where
    init = (1, 1, 1, 0)
    lfts = repeat (2, 1, 1, 0)
    next z = floor (extr z 2)
    safe z n = n == floor (extr z 3)
    prod z n = compose (10, -10 * n, 0, 1) z
    cons = compose


{-- faster spigots for Pi --}

piLambert :: [Integer]
piLambert = stream next safe prod cons init lfts
  where
    init = ((0, 4, 1, 0), 1)
    lfts = [(2 * i - 1, i * i, 1, 0) | i <- [1 ..]]
    next ((q, r, s, t), i) =
      let x = 2 * i - 1
       in floor ((q * x + r) % (s * x + t))
    safe ((q, r, s, t), i) n =
      let x = 5 * i - 2
       in n == floor ((q * x + 2 * r) % (s * x + 2 * t))
    prod (z, i) n = (compose (10, -10 * n, 0, 1) z, i)
    cons (z, i) z' = (compose z z', i + 1)

piGosper :: [Integer]
piGosper = stream next safe prod cons init lfts
  where
    init = ((1, 0, 0, 1), 1)
    lfts =
      [ let j = 3 * (3 * i + 1) * (3 * i + 2)
         in (i * (2 * i - 1), j * (5 * i - 2), 0, j)
        | i <- [1 ..]
      ]
    next ((q, r, s, t), i) =
      let x = 27 * i - 12
       in div (q * x + 5 * r) (s * x + 5 * t)
    safe ((q, r, s, t), i) n =
      let x = 675 * i - 216
       in n == div (q * x + 125 * r) (s * x + 125 * t)
    prod (z, i) n = (compose (10, -10 * n, 0, 1) z, i)
    cons (z, i) z' = (compose z z', i + 1)

{-- possible optimisations --}

piG2 :: [Integer]
piG2 = process next prod cons init lfts
  where
    process next prod cons u (x : xs) =
      let v = cons u x
          y = next v
       in y : process next prod cons (prod v y) xs
    init = ((1, 0, 0, 1), 1)
    lfts =
      [ let j = 3 * (3 * i + 1) * (3 * i + 2)
         in (i * (2 * i - 1), j * (5 * i - 2), 0, j)
        | i <- [1 ..]
      ]
    next ((q, r, s, t), i) =
      let x = 27 * i - 12
       in div (q * x + 5 * r) (s * x + 5 * t)
    prod (z, i) n = (compose (10, -10 * n, 0, 1) z, i)
    cons (z, i) z' = (compose z z', i + 1)

piG3 :: [Integer]
piG3 = g (1, 180, 60, 2)
  where
    g (q, r, t, i) =
      let (u, y) = (3 * (3 * i + 1) * (3 * i + 2), div (q * (27 * i - 12) + 5 * r) (5 * t))
       in y : g (10 * q * i * (2 * i - 1), 10 * u * (q * (5 * i - 2) + r - y * t), t * u, i + 1)

{-- A Spigot-Algorithm for Square-Roots Explained and Extended, Mayer Goldberg, 27.12.2023 --}

sqrt' :: Integer -> [Integer]
sqrt' n = go 0 (5 * n, 5)
  where
    go n (x, y)
      | x < y = n : go 0 (100 * x, 10 * y - 45)
      | otherwise = go (n + 1) (x - y, y + 10)
