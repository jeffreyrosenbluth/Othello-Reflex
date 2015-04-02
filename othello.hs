{-# LANGUAGE RecursiveDo #-}

import           Control.Monad (mapM)
import           Data.Array
import           Data.Function (on)
import qualified Data.Map      as Map
import           Data.List     (foldl', maximumBy, minimumBy)
import           Data.Tree

import           Reflex
import           Reflex.Dom

type Position = (Int, Int)

data Input = BlackMove Position | WhiteMove

data Game = Game { piece :: Square, board :: Board }

squares :: [Position]
squares = [(x, y) | y <- [1..8], x <- [1..8]]

buttonAttr' :: MonadWidget t m => Dynamic t (Map.Map String String) -> m (Event t ())
buttonAttr' attrs = do
  (e, _) <- elDynAttr' "button" attrs (text "")
  return $ _el_clicked e

buttonAttr :: MonadWidget t m => String -> Map.Map String String -> m (Event t ())
buttonAttr s attrs = do
  (e, _) <- elAttr' "button" attrs (text s)
  return $ _el_clicked e

mkSquare :: (MonadWidget t m) => Dynamic t Game -> Position ->  m (Event t Input)
mkSquare game coords = do
  rec b <- buttonAttr' attrs
      attrs <- mapDyn (\r -> case ((board r) ! coords) of
        Empty -> mkStyle "green"
        Black -> mkStyle "black"
        White -> mkStyle "white") game
  return $ fmap (const (BlackMove coords)) b
    where
      mkStyle c = Map.fromList
        [ ("style", "background-color: " ++
          c ++ "; font-size: 40px; height: 85px; width: 85px") ]

mkRow :: (MonadWidget t m) => Dynamic t Game -> Int -> m [Event t Input]
mkRow g n = el "div" $
  mapM (mkSquare g) (take 8 . drop (8 * (n-1)) $ squares)

mkMove :: Input -> Game -> Game
mkMove (BlackMove x) g@(Game Black _) = move x g
mkMove WhiteMove     g@(Game White _) = aiMove 2 White g
mkMove _ g                            = g

setup :: (MonadWidget t m) => m ()
setup = el "div" $ do
  rec rows <- mapM (mkRow g) [1..8]
      b <- buttonAttr "Move White" $ Map.fromList
        [("style", "font-size: 2em; margin-left: 250px; margin-top: 20px")]
      let wm = fmap (const WhiteMove) b
      g    <- foldDyn mkMove newGame (leftmost (wm : concat rows))
  return ()

main = mainWidget $ do
  elAttr "div" (Map.fromList [("style", "font-size: 40px; margin-left: 280px")]) (text "Othello")
  setup

----------------------------------------------------------------------
-- Othello
----------------------------------------------------------------------

data Square = Empty | Black | White
  deriving (Show, Eq)

type Line = [Position]

type Board = Array Position Square

----------------------------------------------------------------------
-- Game Logic
----------------------------------------------------------------------

-- Memoize line calculations
line :: Array (Int, Int, Int) Line
line = array ((1, 1, 1), (8, 8, 8)) [((i, j, d), line' i j d) | i <- [1..8], j <- [1..8], d <- [1..8]]
  where
    line' :: Int -> Int -> Int -> Line
    line' x y 1 = [(x, y + h)     | h <- [1..8], y+h <= 8]
    line' x y 2 = [(x, y - h)     | h <- [1..8], y-h >= 1]
    line' x y 3 = [(x + h, y)     | h <- [1..8], x+h <= 8]
    line' x y 4 = [(x - h, y)     | h <- [1..8], x-h >= 1]
    line' x y 5 = [(x + h, y + h) | h <- [1..8], y+h <= 8, x+h <= 8]
    line' x y 6 = [(x + h, y - h) | h <- [1..8], y-h >= 1, x+h <= 8]
    line' x y 7 = [(x - h, y + h) | h <- [1..8], y+h <= 8, x-h >= 1]
    line' x y 8 = [(x - h, y - h) | h <- [1..8], y-h >= 1, x-h >= 1]
    line' _ _ _ = []

-- pieces brd = map (brd !)
pieces :: Board -> Line -> [Square]
pieces brd = map (\x -> brd ! x)
{-# INLINE pieces #-}

opposite :: Square -> Square
opposite Black = White
opposite White = Black
opposite Empty = Empty

newBoard :: Board
newBoard = emptyArray // [((4,4), White),((4,5), Black),((5,4), Black),((5,5), White)]
  where
    emptyArray = listArray ((1,1),(8,8)) (repeat Empty)

newGame :: Game
newGame = Game Black newBoard

setPosition :: Board -> Position -> Square -> Board
setPosition brd square p =
    if (brd ! square) /= Empty
    then error $ "square " ++ show square ++ " is not empty"
    else brd // [(square, p)]

toFlip :: Board -> Square -> Line -> Line
toFlip _ _ []   = []
toFlip _ _ ([_]) = []
toFlip b p l
  | b ! head l == p || b ! head l == Empty = [] -- short circuit for obvious cases.
  | zs /= [] && fst (head zs) == p = map snd ys
  | otherwise = []
  where
    (ys, zs) = span ((== opposite p) . fst) $ zip (pieces b l) l

toFlipAll :: Board -> Square -> Position -> [Position]
toFlipAll b p s = concat [toFlip b p l | l <- map ln [1..8]]
  where
    ln z = line ! (fst s, snd s, z)

flipBoard :: Board -> Square -> Position -> Board
flipBoard b p s = b // ((s, p) : zip flips (repeat p))
  where
    flips = toFlipAll b p s

isLegal :: Board -> Square -> Position -> Bool
isLegal b p s = b ! s == Empty && (not . null $ toFlipAll b p s)

legalPositions :: Game -> [Position]
legalPositions (Game p b) = filter (isLegal b p) squares

legalMoves :: Game -> [(Game, Position)]
legalMoves g@(Game p b) = zip gs ls
  where
    ls = filter (isLegal b p) squares
    gs = map (\s ->  move s g) ls

move :: Position -> Game -> Game
move square g@(Game p b)
  | null (legalMoves g) = Game (opposite p) b
  | not (isLegal b p square) = g
  | otherwise = Game (opposite p) (flipBoard b p square)

isOver :: Board -> Bool
isOver b = not (any (isLegal b Black) squares || any (isLegal b White) squares)

findWinner :: Board -> Square
findWinner b
  | isOver b = case compare black white of
      GT -> Black
      LT -> White
      EQ -> Empty -- We use Empty to indicate a draw.
  | otherwise = error "The game is not over"
  where
    black = length $ filter (\s -> b ! s == Black) squares
    white = length $ filter (\s -> b ! s == White) squares

--------------------------------------------------------------------------------------
-- AI
--------------------------------------------------------------------------------------

-- Order the moves tried to maximize the benefit of alpha-beta pruning.
abSquares :: [Position]
abSquares = reverse
            [ (1,1), (1,8), (8,1), (8,8)                             --  20
            , (3,1), (6,1), (1,3), (8,3), (1,6), (8,6), (3,8), (6,8) --  11
            , (4,1), (5,1), (1,4), (8,4), (1,5), (8,5), (4,8), (5,8) --   8
            , (3,3), (4,3), (5,3), (6,3), (3,4), (6,4)               --   2
            , (3,5), (6,5), (3,6), (4,6), (5,6), (6,6)               --   2
            , (4,2), (5,2), (2,4), (7,4), (2,5), (7,5), (4,7), (5,7) --   1
            , (2,1), (7,1), (1,2), (8,2), (1,7), (8,7), (2,8), (7,8) --  -3
            , (3,2), (6,2), (2,3), (7,3), (2,6), (7,6), (3,7), (6,7) --  -4
            , (2,2), (7,2), (2,7), (7,7)                             --  -7
            ]

children :: Game -> [Game]
children g@(Game p b) = map (\s -> move s g) (filter (isLegal b p) abSquares)

--------------------------------------------------------------------------------------
-- Minimax
--------------------------------------------------------------------------------------
type GameTree = Tree Game

alphaBeta :: GameTree -> Double
alphaBeta = go (-1/0) (1/0)
  where
    go :: Double -> Double -> GameTree -> Double
    go _ _ (Node g []) = heuristic (board g) (piece g)
    go a b (Node _ gs) = fst $ foldl' prune (a, b) gs
      where
        prune (a', b') n
          | b' < a' = (a', b')
          | otherwise = (max a (- go (-b') (-a') n), b')

gameTree :: Game -> GameTree
gameTree g = Node g (map gameTree (children g))

cutoff :: Int -> GameTree -> GameTree
cutoff 0 (Node g _) = Node g []
cutoff n (Node g gs) = Node g (map (cutoff (n - 1)) gs)

aiMove :: Int -> Square -> Game -> Game
aiMove n p g = move (snd best) g
  where
    gt = cutoff n . gameTree
    ms = legalMoves g
    scores = map (\(g', s) -> (alphaBeta . gt $ g', s)) ms
    best = minimumBy (compare `on` fst) scores

-------------------------------------------------------------------------------------
-- Heuristic, based on:
-- http://kartikkukreja.wordpress.com/2013/03/30/heuristic-function-for-reversiothello
--------------------------------------------------------------------------------------

-- Assign a score to a board based on the subsequent criteria.
-- See:
-- http://courses.cs.washington.edu/courses/cse573/04au/Project/mini1/RUSSIA/Final_Paper.pdf
heuristic :: Board -> Square -> Double
heuristic b p =  10.0   * parity b p
              + 801.724 * cornerOcc b p
              + 382.026 * cornerAdj b p
              +  78.922 * mobility b p
              +  74.396 * stability b p
              +  10.0   * squareValues b p

oneIfEq :: Eq a => a -> a -> Double
oneIfEq p q = if p == q then 1 else 0

-- Value for occupying more squares.
parity :: Board -> Square -> Double
parity b p
  | sup  > inf =  100 * sup / total
  | inf > sup  = -100 * inf / total
  | otherwise = 0
  where
    ps = elems b
    sups = map (oneIfEq p) ps
    infs = map (oneIfEq (opposite p)) ps
    (sup, inf) = (sum sups, sum infs)
    total = sup + inf

-- Values for occupying specific squares.
valueTable :: Array Position Double
valueTable = listArray ((1,1), (8,8)) valList
  where
    valList = [ 20, -3, 11,  8,  8, 11, -3, 20
              , -3, -7, -4,  1,  1, -4, -7, -3
              , 11, -4,  2,  2,  2,  2, -4, 11
              ,  8,  1,  2, -3, -3,  2,  1,  8
              ,  8,  1,  2, -3, -3,  2,  1,  8
              , 11, -4,  2,  2,  2,  2, -4, 11
              , -3, -7, -4,  1,  1, -4, -7, -3
              , 20, -3, 11,  8,  8, 11, -3, 20 ]

squareValue :: Board -> Square -> Position -> Double
squareValue b p s
  | q == p = valueTable ! s
  | q == opposite p = - (valueTable ! s)
  | otherwise = 0
  where
    q = b ! s

squareValues :: Board -> Square -> Double
squareValues b p = sum $ map (squareValue b p) abSquares

-- Index offsets to 8 adjacent squares.
frontierX :: Array Int Int
frontierX = listArray (1, 8) [-1, -1, 0, 1, 1, 1, 0, -1]

frontierY :: Array Int Int
frontierY = listArray (1, 8) [0, 1, 1, 1, 0, -1, -1, -1]

-- Measures the potential for a square to be flanked.
stable :: Board -> Square -> Position -> Double
stable b p s
  | b ! s == Empty = 0
  | otherwise = sum $ map (oneIfEq p . (b !)) goodSqs
  where
    (i, j) = s
    sqs = [(i + frontierX ! k, j + frontierY ! k) | k <- [1..8]]
    goodSqs = filter (\(x, y) -> x >= 1 && x <= 8 && y >= 1 && y <= 8) sqs

stability :: Board -> Square -> Double
stability b p
  | sup  > inf = -100 * sup  / total
  | inf > sup  =  100 * inf / total
  | otherwise = 0
  where
    sups       = map (stable b p) abSquares
    infs       = map (stable b (opposite p)) abSquares
    (sup, inf) = (sum sups, sum infs)
    total      = sup + sup

unitVal :: Square -> Square -> Double
unitVal p q
  | q == p = 1
  | q == opposite p = -1
  | otherwise = 0

-- Occupying a corner is very good.
cornerOcc :: Board -> Square -> Double
cornerOcc b p = (25 *) . sum $ map (unitVal p) corners
  where
    corners = [b ! (1,1), b ! (1,8), b ! (8,1), b ! (8,8)]

-- Occupying a square adjacent to a corner is bad.
cornerAdj :: Board -> Square -> Double
cornerAdj b p = ((-12.5) *) . sum
                     $ map (unitVal p) (concat [ll, lr, tr, tl])
  where
    ll = if b ! (1,1) == Empty
         then [b ! (1,2), b ! (2,2), b ! (2,1)]
         else []
    lr = if b ! (8,1) == Empty
         then [b ! (7,1), b ! (7,2), b ! (8,2)]
         else []
    tr = if b ! (8,8) == Empty
         then [b ! (8,7), b ! (7,7), b ! (7,8)]
         else []
    tl = if b ! (1,8) == Empty
         then [b ! (1,7), b ! (2,7), b ! (2,8)]
         else []

-- Measures how many move choice you have relative to your opponent.
mobility :: Board -> Square -> Double
mobility b p
  | sup > inf = 100 * sup / total
  | inf > sup = -100 * inf / total
  | otherwise = 0
  where
    sup  = fromIntegral . length $ legalPositions g
    inf = fromIntegral . length $ legalPositions h
    g = Game p b
    h = g { piece = opposite (piece g) }
    total = sup + inf
