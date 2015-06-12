import Haste.DOM
import Haste.Prim
import Control.Monad.IO.Class
import Data.String
import Data.List
import Data.Maybe
import Control.Applicative

-- javascript functionality
foreign import ccall jsCreateElemNS :: JSString -> JSString -> IO Elem

foreign import ccall setDropCheckerCallback_ffi :: Ptr (JSString -> Float -> Float -> IO ()) -> IO ()
foreign import ccall placeAlert_ffi :: JSString -> IO ()
foreign import ccall consoleLog_ffi :: JSString -> IO ()

-- | Create an element in a namespace.
newElemNS :: MonadIO m => String -> String -> m Elem
newElemNS ns tag = liftIO $ jsCreateElemNS  (toJSStr ns) (toJSStr tag)

data Color = Black|White|None deriving (Eq, Show)
data Point = Point { checkerColor :: Color
                   , checkerCount ::  Int
                   } deriving (Show)

data Game = Game [Point] Color Color

checkerRadius = 6
firstUpperLevel = 7
firstLowerLevel = 203
leftmostPoint = 10
pointGap = 15
barGap = 5

pointXCoords = firstSix ++ secondSix where
    firstPastBar = leftmostPoint+6*pointGap+barGap
    firstSix = take 6 [leftmostPoint,leftmostPoint+pointGap..]
    secondSix = take 6 [firstPastBar,firstPastBar+pointGap..]

coordsToPointIndex :: Float -> Float -> Maybe Int
coordsToPointIndex x y = 
    let 
        -- get the offset in "point count" from the left.
        lp = findIndex (\px -> abs (fromIntegral px - x) < 7) pointXCoords

        midPoint = (firstUpperLevel + firstLowerLevel) `div` 2

        -- Adjustment to apply to get the actual point index.
        -- Depends on whether selection is on bottom or top of board
        adjustment = if (y > fromIntegral midPoint) then (11-) else (12+) 

    in fmap adjustment lp  -- fmap over Maybe


setCheckerPosition :: Elem -> Int -> Int -> IO ()
setCheckerPosition circle pointIndex checkerIndex = do
    setAttr circle "cx" (show $ xBase + leftDelta)
    setAttr circle "cy" (show $ yBase + stackDelta)
    where 

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

checkerPositionClass :: Int -> Int -> String 
checkerPositionClass pi ci = 
       " pi" ++ show pi -- point index
    ++ " ci" ++ show ci -- checker index

setCheckerClass :: Elem -> Color -> Int -> Int -> Color -> IO ()
setCheckerClass circle usersColor pointIndex checkerIndex color = 
    setAttr circle "class" (svgCheckerClass color usersColor pointIndex checkerIndex) 
    where 
      svgCheckerClass color usersColor pi ci = 
          (if (usersColor == color ) then "draggable " else "") -- can only move your own checkers
          ++ show color 
          ++ checkerPositionClass pi ci

getCheckerElement :: MonadIO m => Int -> Int -> m Elem

getCheckerElement pointIndex checkerIndex = do
    elems <- elemsByClass $ checkerPositionClass pointIndex checkerIndex 
    return (elems !! 0)

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

dropCheckerCallback :: Game -> JSString -> Float -> Float -> IO ()
dropCheckerCallback (Game points _ _) className x y = do
    let classes = words $ fromJSStr className

        -- extract point index and checker index from class string
        piString = drop 2 $ classes !! 2    -- "piXX"
        ciString = drop 2 $ classes !! 3    -- "ciXX"

        pointIndex = read piString :: Int
        checkerIndex = read ciString :: Int

        -- convert placement coords to newPointIndex and newCheckerIndex
        -- newPointIndex and newCheckerIndex are both: Maybe Int 
        newPointIndex = coordsToPointIndex x y
        newCheckerIndex = checkerCount <$> ((!!) points) <$> newPointIndex 

    checker <- getCheckerElement pointIndex checkerIndex
    case newCheckerIndex of
        Just c -> setCheckerPosition checker (fromMaybe 0 newPointIndex) c
        Nothing -> setCheckerPosition checker pointIndex checkerIndex



main :: IO ()
main = let gameInPlay = newGame
       in do drawGame gameInPlay
             setDropCheckerCallback_ffi $ toPtr (dropCheckerCallback gameInPlay)
             -- setCallbacks gameInPlay 

