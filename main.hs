import Haste.DOM
import Haste.Prim
import Control.Monad.IO.Class
import Data.String
import Data.List
import Data.Maybe
import Control.Applicative

-- javascript functionality

-- debugging
foreign import ccall placeAlert_ffi :: JSString -> IO ()
foreign import ccall consoleLog_ffi :: JSString -> IO ()

-- | Create an element in a namespace.
foreign import ccall jsCreateElemNS :: JSString -> JSString -> IO Elem
newElemNS :: MonadIO m => String -> String -> m Elem
newElemNS ns tag = liftIO $ jsCreateElemNS  (toJSStr ns) (toJSStr tag)

-- | Slide a circle to the given location.  
foreign import ccall animateCircle_ffi :: Elem -> Int -> Int -> Int -> IO ()
jsAnimateCircle :: MonadIO m => Elem -> Int -> Int -> Int -> m ()
jsAnimateCircle e cx cy duration = liftIO $ animateCircle_ffi e cx cy duration

foreign import ccall setDropCheckerCallback_ffi :: Ptr (JSString -> Float -> Float -> IO ()) -> IO ()

data Placement =     PointPlacement { pointIndex :: Int, onPointIndex :: Int } 
                   | BarPlacement { onBarIndex :: Int }
                   | SidePlacement  { onSideIndex :: Int } deriving Show

data Color = Black|White deriving (Eq, Show)
data Point = Point { checkerColor :: Color
                   , checkerCount ::  Int
                   } deriving (Show)

data Game = Game {
                 gamePoints :: [Point] 
               , whiteOffTable :: Int
               , blackOffTable :: Int
               , whiteOnBar :: Int
               , blackOnBar :: Int
               , usersColor :: Color 
               , playersColor :: Color
            } deriving (Show)

checkerRadius = 6
firstUpperLevel = 7
firstLowerLevel = 203
leftmostPoint = 25
pointGap = 15
barGap = 5+15

-- List of x coordinates of points relative to lhs.
pointXCoords = firstSix ++ secondSix where
    firstPastBar = leftmostPoint+6*pointGap+barGap
    firstSix = take 6 [leftmostPoint,leftmostPoint+pointGap..]
    secondSix = take 6 [firstPastBar,firstPastBar+pointGap..]

-- Used to determine where on the board a checker was dropped
coordsToPointIndex :: Float -> Float -> Maybe Int
coordsToPointIndex x y = 
    let 
        -- get the offset in "point count" from the left.
        lp = findIndex (\px -> abs (fromIntegral px - x) < 7) pointXCoords

        midPoint = (firstUpperLevel + firstLowerLevel) `div` 2

        -- Adjustment to apply to get the actual point index.
        -- Depends on whether selection is on bottom or top of board
        adjustment = if (y > fromIntegral midPoint) then (23-) else (0+) 

    in fmap adjustment lp  -- fmap over Maybe

-- Convert from point/checker indices to appropriate center placement
checkerPosition :: Placement -> (Int,Int)
checkerPosition (PointPlacement pointIndex checkerIndex) = 
    let pointOffset | pointIndex < 12 =      pointIndex -- from lower leftmost point
                    | otherwise       = 23 - pointIndex  -- from upper leftmost point
  
        barGapUsed | pointOffset < 6 = 0                -- left side of board
                   | otherwise       = barGap           -- right side of board
  
        leftDelta = barGapUsed + pointOffset * pointGap -- distance in horizonatal "board units"
  
        stackDirection | pointIndex < 12 = 1           -- stacking up
                       | otherwise       = -1            -- stacking down
  
        stackDelta = stackDirection*checkerIndex*2*checkerRadius -- distance in vertical "board units"
  
        xBase = leftmostPoint                           -- horizontal position on board
  
        yBase | pointIndex < 12 = firstUpperLevel       -- vertical position on board
              | otherwise       = firstLowerLevel
  
        cx = xBase + leftDelta
        cy = yBase + stackDelta
    in (cx,cy)

-- Given a checker element, move it to the spot specified
-- by the pointIndex and checkerIndex.
setCheckerPosition :: MonadIO m => Elem -> Placement -> m ()
setCheckerPosition circle placement = do
    let (cx,cy) = checkerPosition placement
    setAttr circle "cx" $ show cx
    setAttr circle "cy" $ show cy

-- Given a checker element, move it to the spot specified
-- by the pointIndex and checkerIndex.
animateToCheckerPosition :: MonadIO m => Elem -> Placement -> m ()
animateToCheckerPosition circle placement = do
    let (cx,cy) = checkerPosition placement
    jsAnimateCircle circle cx cy 300

checkerPositionClass :: Placement -> String 
checkerPositionClass (PointPlacement pi ci) = " pi" ++ show pi ++ " ci" ++ show ci 

setCheckerClass :: MonadIO m => Elem -> Color -> Placement -> Color -> m ()
setCheckerClass circle usersColor placement color = 
    setAttr circle "class" (svgCheckerClass color usersColor placement) 
    where 
      svgCheckerClass color usersColor pl = 
          (if (usersColor == color ) then "draggable " else "") -- can only move your own checkers
          ++ show color 
          ++ checkerPositionClass pl

getCheckerElement :: MonadIO m => Placement -> m Elem
getCheckerElement pl = do
    elems <- elemsByClass $ checkerPositionClass pl
    return (elems !! 0)

-- Create and place a single checker on specified point
drawChecker :: Color -> Color -> Placement -> IO ()
drawChecker usersColor color pl = do
    Just d <- elemById "board" 
    circle <- newElemNS "http://www.w3.org/2000/svg" "circle"
    setAttr circle "r" (show $ checkerRadius)
    setCheckerPosition circle pl
    setCheckerClass circle usersColor pl color 
    addChild circle d

-- Create and draw all the checkers for a given point.
drawPoint :: Color -> Int -> Point -> IO ()
drawPoint usersColor pointIndex (Point color count) =
    sequence_ $ [drawChecker usersColor color (PointPlacement pointIndex checkerIndex) | checkerIndex <- take count [0..]]

-- Create and draw all the checkers for a given side.
-- Side is identified by color - white checkers go on left.
drawBar :: Color -> Color -> Int -> IO ()
drawBar color usersColor count  =
    sequence_ [drawChecker usersColor color (SidePlacement i) | i <- take count [0..]]

-- Create and draw all the checkers sitting on both sides for a game.
drawGame :: Game -> IO ()
drawGame (Game points wos bos wob bob usersColor _) = do
        sequence_ $ map (uncurry (drawPoint usersColor)) $ zip [0..] points
        -- drawBar White usersColor wos 
        -- drawBar Black usersColor bos 

-- Given a game and a move, create the resulting new game.
updateGame :: Game -> Int -> Int -> Game
updateGame g@(Game points wos bos wob bob _ _) iFrom iTo = 
    -- could this be improved with lens?
    let fromColor = checkerColor $ points !! iFrom
        doMove f t (i,pt)
          | (i == f) = Point (checkerColor pt) (checkerCount pt -1)
          | (i == t)   = Point fromColor (checkerCount pt +1)
          | otherwise    = pt
                
    in g {gamePoints = (map (doMove iFrom iTo) (zip [0..] points)) }

-- Given a game and a move, create the resulting new game.
moveChecker :: MonadIO m => Placement -> Placement -> Color -> m ()
moveChecker oldPlacement newPlacement color = do
    checker <- getCheckerElement oldPlacement
    animateToCheckerPosition checker newPlacement
    setCheckerClass checker color newPlacement color

-- slide all of the checkers at a given point together.
fixCheckersAtPoint :: MonadIO m => Game -> Int -> Int -> m ()
fixCheckersAtPoint (Game points wos bos wob bob userColor _ ) pointIndex missingCheckerIndex = do
    let moveIndices = drop 1 [missingCheckerIndex .. checkerCount (points !! pointIndex)]
    sequence_ [moveChecker (PointPlacement pointIndex i) (PointPlacement pointIndex (i-1)) userColor | i <- moveIndices ]

dropCheckerCallback :: Game -> JSString -> Float -> Float -> IO ()
dropCheckerCallback g@(Game points wos bos wob bob usersColor _) className x y = do
    let classes = words $ fromJSStr className

        -- extract point index and checker index from class string
        piString = drop 2 $ classes !! 2    -- "piXX"
        ciString = drop 2 $ classes !! 3    -- "ciXX"

        oldPoint = read piString :: Int
        oldChecker = read ciString :: Int
        oldPlacement = PointPlacement oldPoint oldChecker

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
                newPlacement = PointPlacement newPoint newChecker

            if legalMove then do
                let newGame = updateGame g oldPoint newPoint
                moveChecker oldPlacement newPlacement usersColor
                fixCheckersAtPoint newGame oldPoint oldChecker
                setCallbacks newGame
            else moveChecker oldPlacement oldPlacement usersColor
        _ -> moveChecker oldPlacement oldPlacement usersColor
        where 

setCallbacks :: Game -> IO ()
setCallbacks g = setDropCheckerCallback_ffi $ toPtr (dropCheckerCallback g)

whiteStart = [ Point White sc | sc <- [2,0,0,0,0,0,0,0,0,0,0,5,0,0,0,0,3,0,5,0,0,0,0,0]]

blackStart = map whiteToBlack $ reverse whiteStart
             where whiteToBlack (Point White c) = Point Black c
                   whiteToBlack p = p

gameStart = zipWith whiteOrBlack whiteStart blackStart
             where whiteOrBlack (Point White 0) b = b
                   whiteOrBlack w@(Point White _) _ = w
newGame :: Game
newGame = Game gameStart 0 0 0 0 White White

main :: IO ()
main = do drawGame newGame
          setCallbacks newGame

