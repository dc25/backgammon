import Haste.DOM
import Haste.Prim
import Control.Monad.IO.Class

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
firstUpperLevel = 7
firstLowerLevel = 203
leftmostPoint = 10
pointGap = 15
barGap = 5

drawChecker :: Color -> Int -> Int -> Color -> IO ()
drawChecker usersColor pointIndex checkerIndex color = do
    Just d <- elemById "board" 
    circle <- newElemNS "http://www.w3.org/2000/svg" "circle"
    setAttr circle "cx" (show $ xBase + leftDelta)
    setAttr circle "cy" (show $ yBase + stackDelta)
    setAttr circle "r" (show $ checkerRadius)
    setAttr circle "class" (svgCheckerClass color usersColor pointIndex checkerIndex) 
    if (usersColor  == color) then (setAttr circle "onmousedown" "selectElement(evt)") else return ()
    addChild circle d
    where 
      svgCheckerClass color usersColor pi ci = (if (usersColor == color ) then "draggable " else "") ++ show color ++ " pi" ++ show pi ++ " ci" ++ show ci

      pointOffset | pointIndex < 12 = 11 - pointIndex
                  | otherwise       = pointIndex - 12

      barGapUsed | pointOffset < 6 = 0
                 | otherwise       = barGap

      leftDelta = barGapUsed + pointOffset * pointGap

      stackDirection | pointIndex < 12 = -1
                     | otherwise       = 1

      stackDelta = stackDirection*checkerIndex*2*checkerRadius

      xBase = leftmostPoint

      yBase | pointIndex < 12 = firstLowerLevel
            | otherwise       = firstUpperLevel

drawPoint :: Color -> Int -> Point -> IO ()
drawPoint usersColor pointIndex (Point color count) = 
    let drawAtPoint = drawChecker usersColor pointIndex
        uncurryDrawAtPoint = uncurry drawAtPoint
    in sequence_ $ map uncurryDrawAtPoint (zip [0..] $ replicate count color) 

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
dropCheckerCallback className x y = consoleLog_ffi  $ toJSStr logStr
    where logStr = fromJSStr className ++ " " ++ show x  ++ " " ++ show y

main :: IO ()
main = let gameInPlay = newGame
       in do drawGame gameInPlay
             setDropCheckerCallback_ffi $ toPtr dropCheckerCallback
             -- enableSelection gameInPlay 
             -- setCallbacks gameInPlay 

