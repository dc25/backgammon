import Haste.DOM
import Haste.Prim
import Control.Monad.IO.Class
import Data.String

-- javascript functionality
foreign import ccall jsCreateElemNS :: JSString -> JSString -> IO Elem

foreign import ccall setDropCheckerCallback_ffi :: Ptr (JSString -> Int -> Int -> IO ()) -> IO ()
foreign import ccall placeAlert_ffi :: JSString -> IO ()
foreign import ccall consoleLog_ffi :: JSString -> IO ()

-- | Create an element in a namespace.
newElemNS :: MonadIO m => String -> String -> m Elem
newElemNS ns tag = liftIO $ jsCreateElemNS  (toJSStr ns) (toJSStr tag)

data Color = Black|White|None deriving (Eq, Show)
data Point = Point Color Int
data Game = Game [Point] Color Color

checkerRadius = 6

setCheckerPosition :: Elem -> Int -> Int -> IO ()
setCheckerPosition circle pointIndex checkerIndex = do
    setAttr circle "cx" (show $ xBase + leftDelta)
    setAttr circle "cy" (show $ yBase + stackDelta)
    where 

      firstUpperLevel = 7
      firstLowerLevel = 203
      leftmostPoint = 10
      pointGap = 15
      barGap = 5

      pointOffset | pointIndex < 12 = 11 - pointIndex -- from lower leftmost point
                  | otherwise       = pointIndex - 12 -- from upper leftmost point

      barGapUsed | pointOffset < 6 = 0                -- left side of board
                 | otherwise       = barGap           -- right side of board

      leftDelta = barGapUsed + pointOffset * pointGap -- distance in horizonatal "board units"

      stackDirection | pointIndex < 12 = -1           -- stacking up
                     | otherwise       = 1            -- stacking down

      stackDelta = stackDirection*checkerIndex*2*checkerRadius -- distance in vertical "board units"

      xBase = leftmostPoint                           -- horizontal position on board

      yBase | pointIndex < 12 = firstLowerLevel       -- vertical position on board
            | otherwise       = firstUpperLevel

setCheckerClass :: Elem -> Color -> Int -> Int -> Color -> IO ()
setCheckerClass circle usersColor pointIndex checkerIndex color = 
    setAttr circle "class" (svgCheckerClass color usersColor pointIndex checkerIndex) 
    where 
      svgCheckerClass color usersColor pi ci = 
          (if (usersColor == color ) then "draggable " else "") -- can only move your own checkers
          ++ show color 
          ++ " pi" ++ show pi -- point index
          ++ " ci" ++ show ci -- checker index

drawChecker :: Color -> Int -> Int -> Color -> IO ()
drawChecker usersColor pointIndex checkerIndex color = do
    Just d <- elemById "board" 
    circle <- newElemNS "http://www.w3.org/2000/svg" "circle"
    setAttr circle "r" (show $ checkerRadius)
    setCheckerPosition circle pointIndex checkerIndex
    setCheckerClass circle usersColor pointIndex checkerIndex color 
    if (usersColor  == color) then (setAttr circle "onmousedown" "selectElement(evt)") else return ()
    addChild circle d

drawPoint :: Color -> Int -> Point -> IO ()
drawPoint usersColor pointIndex (Point color count) =
    sequence_ $ map (uncurry $ drawChecker usersColor pointIndex) (zip [0..] $ replicate count color) 

drawGame :: Game -> IO ()
drawGame (Game points usersColor _) = sequence_ $ map (uncurry (drawPoint usersColor)) $ zip [0..] points

whiteStart=    [Point White 2, 
                Point None 0,
                Point None 0,
                Point None 0,
                Point None 0,
                Point None 0,
                Point None 0,
                Point None 0,
                Point None 0,
                Point None 0,
                Point None 0,
                Point White 5,
                Point None 0,
                Point None 0,
                Point None 0,
                Point None 0,
                Point White 3,
                Point None 0,
                Point White 5,
                Point None 0,
                Point None 0,
                Point None 0,
                Point None 0,
                Point None 0 ]

blackStart = map whiteToBlack $ reverse whiteStart
             where whiteToBlack (Point White c) = Point Black c
                   whiteToBlack p = p

gameStart = zipWith whiteOrBlack whiteStart blackStart
             where whiteOrBlack p@(Point White c) _ = p
                   whiteOrBlack _ p = p

newGame :: Game
newGame = Game gameStart White White

dropCheckerCallback :: JSString -> Int -> Int -> IO ()
dropCheckerCallback className x y = do
    let logStr = fromJSStr className ++ " " ++ show x  ++ " " ++ show y
    consoleLog_ffi  $ toJSStr logStr
    let classes = words $ fromJSStr className
        piString = drop 2 $ classes !! 2    -- "piXX"
        ciString = drop 2 $ classes !! 3  -- "ciXX"
        pointIndex = read piString :: Int
        checkerIndex = read ciString :: Int
        logStr2 = show pointIndex  ++ " " ++ show checkerIndex
    consoleLog_ffi  $ toJSStr logStr2


main :: IO ()
main = let gameInPlay = newGame
       in do drawGame gameInPlay
             setDropCheckerCallback_ffi $ toPtr dropCheckerCallback
             -- setCallbacks gameInPlay 

