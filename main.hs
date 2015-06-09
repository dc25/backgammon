import Haste.DOM
import Haste.Prim
import Control.Monad.IO.Class

foreign import ccall jsCreateElemNS :: JSString -> JSString -> IO Elem
foreign import ccall jsSetAttrNS :: Elem -> JSString -> JSString -> IO ()

-- | Create an element in a namespace.
newElemNS :: MonadIO m => String -> String -> m Elem
newElemNS ns tag = liftIO $ jsCreateElemNS  (toJSStr ns) (toJSStr tag)

-- | Set an attribute of the given element.
setAttrNS :: MonadIO m => Elem -> PropID -> String -> m ()
setAttrNS e prop val = liftIO $ jsSetAttrNS e (toJSStr prop) (toJSStr val)

data Color = Black|White|None
data Point = Point Color  Int
data Game = Game [Point]

checkerRadius = 6
firstUpperLevel = 7
firstLowerLevel = 203
leftmostPoint = 10
pointGap = 15
barGap = 5

drawChecker :: Int -> Int -> Color -> IO ()
drawChecker pointIndex checkerIndex color = do
    Just d <- elemById "fullboard" 
    circle <- newElemNS "http://www.w3.org/2000/svg" "circle"
    setAttrNS circle "cx" (show $ xBase + leftDelta)
    setAttrNS circle "cy" (show $ yBase + stackDelta)
    setAttrNS circle "r" (show $ checkerRadius)
    setAttrNS circle "class" (svgCheckerClass color)
    setAttrNS circle "onmousedown" "selectElement(evt)"
    addChild circle d
    where 
      svgCheckerClass White = "draggable whiteChecker"
      svgCheckerClass Black = "draggable blackChecker"

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

drawPoint :: (Int,Point) -> IO ()
drawPoint (pointIndex, Point color count) = 
    let drawAtPoint = drawChecker pointIndex
        uncurryDrawAtPoint = uncurry drawAtPoint
    in sequence_ $ map uncurryDrawAtPoint (zip [0..] $ replicate count color) 

drawGame :: Game -> IO ()
drawGame (Game points) = sequence_ $ map drawPoint $ zip [0..] points

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
newGame = Game [Point White 2, Point Black 1]

main :: IO ()
main = let gameInPlay = newGame
       in do drawGame gameInPlay
             -- enableSelection gameInPlay 
             -- setCallbacks gameInPlay 

