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
foreign import ccall animateCircle_ffi :: Elem -> Int -> Int -> Int -> IO ()

-- | Create an element in a namespace.
newElemNS :: MonadIO m => String -> String -> m Elem
newElemNS ns tag = liftIO $ jsCreateElemNS  (toJSStr ns) (toJSStr tag)

-- | Slide a circle to the given location.  
jsAnimateCircle :: MonadIO m => Elem -> Int -> Int -> Int -> m ()
jsAnimateCircle e cx cy duration = liftIO $ animateCircle_ffi e cx cy duration


data Color = Black|White|None deriving (Eq, Show)
data Point = Point { checkerColor :: Color
                   , checkerCount ::  Int
                   } deriving (Show)

data Game = Game {
               gamePoints :: [Point] 
               , usersColor :: Color 
               , playersColor :: Color
            } deriving (Show)

checkerRadius = 6
firstUpperLevel = 7
firstLowerLevel = 203
leftmostPoint = 10
pointGap = 15
barGap = 5

-- List of x coordinates of points relative to lhs.
pointXCoords = firstSix ++ secondSix where
    firstPastBar = leftmostPoint+6*pointGap+barGap
    firstSix = take 6 [leftmostPoint,leftmostPoint+pointGap..]
    secondSix = take 6 [firstPastBar,firstPastBar+pointGap..]

-- Used to determine which point a checker was dropped on.
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

-- Convert from point/checker indieces to appropriate center placement
checkerPosition :: Int -> Int -> (Int,Int)
checkerPosition pointIndex checkerIndex = 
    let pointOffset | pointIndex < 12 = 11 - pointIndex -- from lower leftmost point
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
  
        cx = xBase + leftDelta
        cy = yBase + stackDelta
    in (cx,cy)

-- Given a checker element, move it to the spot specified
-- by the pointIndex and checkerIndex.
setCheckerPosition :: MonadIO m => Elem -> Int -> Int -> m ()
setCheckerPosition circle pointIndex checkerIndex = do
    let (cx,cy) = checkerPosition pointIndex checkerIndex
    setAttr circle "cx" $ show cx
    setAttr circle "cy" $ show cy

-- Given a checker element, move it to the spot specified
-- by the pointIndex and checkerIndex.
animateToCheckerPosition :: MonadIO m => Elem -> Int -> Int -> m ()
animateToCheckerPosition circle pointIndex checkerIndex = do
    let (cx,cy) = checkerPosition pointIndex checkerIndex
    jsAnimateCircle circle cx cy 300

checkerPositionClass :: Int -> Int -> String 
checkerPositionClass pi ci = " pi" ++ show pi ++ " ci" ++ show ci 

setCheckerClass :: MonadIO m => Elem -> Color -> Int -> Int -> Color -> m ()
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

-- Create and place a single checker on specified point
drawChecker :: Color -> Int -> Int -> Color -> IO ()
drawChecker usersColor pointIndex checkerIndex color = do
    Just d <- elemById "board" 
    circle <- newElemNS "http://www.w3.org/2000/svg" "circle"
    setAttr circle "r" (show $ checkerRadius)
    setCheckerPosition circle pointIndex checkerIndex
    setCheckerClass circle usersColor pointIndex checkerIndex color 
    if (usersColor  == color) then (setAttr circle "onmousedown" "selectElement(evt)") else return ()
    addChild circle d

-- Create and draw all the checkers for a given point.
drawPoint :: Color -> Int -> Point -> IO ()
drawPoint usersColor pointIndex (Point color count) =
    sequence_ $ map (uncurry $ drawChecker usersColor pointIndex) (zip [0..] $ replicate count color) 

-- Create and draw all the checkers for all the points for a game.
drawGame :: Game -> IO ()
drawGame (Game points usersColor _) = sequence_ $ map (uncurry (drawPoint usersColor)) $ zip [0..] points

-- Given a game and a move, create the resulting new game.
updateGame :: Game -> Int -> Int -> Game
updateGame g@(Game points _ _) iFrom iTo = 
    -- could this be improved with lens?
    let fromColor = checkerColor $ points !! iFrom
        doMove f t (i,pt)
          | (i == f) = Point (checkerColor pt) (checkerCount pt -1)
          | (i == t)   = Point fromColor (checkerCount pt +1)
          | otherwise    = pt
                
    in g {gamePoints = (map (doMove iFrom iTo) (zip [0..] points)) }

-- Given a game and a move, create the resulting new game.
moveChecker :: MonadIO m => Int -> Int -> Int -> Int -> Color -> m ()
moveChecker oldPoint oldChecker newPoint newChecker color = do
    checker <- getCheckerElement oldPoint oldChecker
    animateToCheckerPosition checker newPoint newChecker  
    setCheckerClass checker color newPoint newChecker color

-- slide all of the checkers at a given point together.
fixCheckersAtPoint :: MonadIO m => Game -> Int -> Int -> m ()
fixCheckersAtPoint (Game points userColor _ ) pointIndex missingCheckerIndex = do
    let moveIndices = drop 1 [missingCheckerIndex .. checkerCount (points !! pointIndex)]
    sequence_ [moveChecker pointIndex i pointIndex (i-1) userColor | i <- moveIndices ]

dropCheckerCallback :: Game -> JSString -> Float -> Float -> IO ()
dropCheckerCallback g@(Game points usersColor _) className x y = do
    let classes = words $ fromJSStr className

        -- extract point index and checker index from class string
        piString = drop 2 $ classes !! 2    -- "piXX"
        ciString = drop 2 $ classes !! 3    -- "ciXX"

        oldPoint = read piString :: Int
        oldChecker = read ciString :: Int

        -- convert placement coords to maybeNewPoint and maybeNewChecker
        -- maybeNewPoint and maybeNewChecker are both: Maybe Int 
        maybeNewPoint = coordsToPointIndex x y
        maybeNewChecker = checkerCount <$> ((!!) points) <$> maybeNewPoint 

    case (maybeNewPoint,maybeNewChecker) of
        (Just newPoint, Just newChecker) -> do 

            let newColor = checkerColor $ points !! newPoint
                oldColor = checkerColor $ points !! oldPoint
                newCount = checkerCount $ points !! newPoint
                legalMove = newPoint > oldPoint && (newColor == oldColor || newCount < 2)

            if legalMove then do
                let newGame = updateGame g oldPoint newPoint
                moveChecker oldPoint oldChecker newPoint newChecker usersColor
                fixCheckersAtPoint newGame oldPoint oldChecker
                setCallbacks newGame
            else moveChecker oldPoint oldChecker oldPoint oldChecker usersColor
        _ -> moveChecker oldPoint oldChecker oldPoint oldChecker usersColor

setCallbacks :: Game -> IO ()
setCallbacks g = setDropCheckerCallback_ffi $ toPtr (dropCheckerCallback g)

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

main :: IO ()
main = do drawGame newGame
          setCallbacks newGame

