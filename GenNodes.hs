import Text.Printf

comment :: String
comment = "-- Generated by GenNodes.hs"

tpy :: String
tpy = "nodes :: Measured a v => Digit a -> Digit a -> Digit a -> Digit (Node v a)"

digitConstr :: Int -> String
digitConstr 1 = "One"
digitConstr 2 = "Two"
digitConstr 3 = "Three"
digitConstr 4 = "Four"

digit :: Int -> Int -> String
digit 0 _    = "Zero"
digit n pred = printf "(%s %s)" (digitConstr n) args
  where args = unwords [printf "a%d" i | i <- take n [pred..]]

pattern :: (Int, Int, Int) -> String
pattern (a, b, c) =
  printf "nodes %s %s %s" (digit a 0) (digit b a) (digit c (a + b))

partitions :: Int -> [Int]
partitions 2 = [2]
partitions 3 = [3]
partitions 4 = [2, 2]
partitions n = 3 : partitions (n - 3)

node :: Int -> Int -> String
node n pred = printf "(%s %s)" constr bs
  where constr | n == 2 = "node2"
               | n == 3 = "node3"

        bs = unwords [printf "a%d" i | i <- take n [pred..]]

nodes :: [Int] -> String
nodes ps = printf "%s %s" (digitConstr n) (unwords $ nodes' ps 0)
  where n = length ps

        nodes' [] _ = []
        nodes' (p : ps) pred = node p pred : nodes' ps (pred + p)

clause :: (Int, Int, Int) -> String
clause ds@(a, b, c) = printf "%s =\n  %s" (pattern ds) (nodes ps)
  where ps = partitions (a + b + c)

main :: IO ()
main = do
  putStrLn comment
  putStrLn tpy
  mapM_ putStrLn [clause (x, y, z) | x <- [1..4], y <- [0..4], z <- [1..4]]
