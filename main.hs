{-# LANGUAGE OverloadedStrings #-}
import Haste
import Haste.DOM
import Haste.Prim
import Haste.Foreign
import Haste.Events
import Control.Monad.IO.Class
import Data.String
import Data.List
import Data.Maybe
import Control.Applicative

import P2P

-- javascript functionality

-- debugging
showAlertFFI :: String-> IO ()
showAlertFFI = ffi "(function (msg) { alert(msg); })"

consoleLogFFI :: String-> IO ()
consoleLogFFI = ffi "(function (msg) { console.log(msg); })"

-- | Create an element in a namespace.
newElemNS :: String -> String -> IO Elem
newElemNS = ffi "(function (ns,tag) {return document.createElementNS(ns, tag);})"

-- | Slide a circle to the given location.  
animateCircleFFI :: Elem -> Int -> Int -> Int -> IO ()
animateCircleFFI = ffi "(function (elem, cx, cy, duration) {$(elem).velocity({ cx: cx, cy: cy }, { duration: duration });})"

setDropCheckerCallbackFFI :: (String -> Float -> Float -> IO ()) -> IO ()
setDropCheckerCallbackFFI = ffi "(function (cb) {setDropCheckerCallback_ffi(cb);})"

data Placement =     PointPlacement { pointIndex :: Int, onPointIndex :: Int } 
                   | BarPlacement { onBarIndex :: Int }
                   | LeftSidePlacement  { onSideIndex :: Int } 
                   | RightSidePlacement  { onSideIndex :: Int } deriving (Show,Read)

data Color = Black|White deriving (Eq, Show, Read)
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
sideWidth = 15
leftmostPoint = sideWidth + 10
barWidth = 15
pointWidth = 15
barGap = 5 + barWidth

-- List of x coordinates of points relative to lhs.
pointXCoords = firstSix ++ secondSix where
    firstPastBar = leftmostPoint+6*pointWidth+barGap
    firstSix = take 6 [leftmostPoint,leftmostPoint+pointWidth..]
    secondSix = take 6 [firstPastBar,firstPastBar+pointWidth..]

-- Used to determine where on the board a checker was dropped
coordsToPlacement :: Game -> Float -> Float -> Maybe Placement
coordsToPlacement (Game points _ _ _ _ _ _) x y =
    let 
        -- get the offset in "point count" from the left.
        lp = findIndex (\px -> abs (fromIntegral px - x) < 7) pointXCoords

        midPoint = (firstUpperLevel + firstLowerLevel) `div` 2

        -- Adjustment to apply to get the actual point index.
        -- Depends on whether selection is on bottom or top of board
        adjustment = if y > fromIntegral midPoint then (23-) else (0+) 

        maybePointIndex = fmap adjustment lp  -- fmap over Maybe
        maybeCheckerIndex = checkerCount <$> (points !! ) <$> maybePointIndex

    in case (maybePointIndex, maybeCheckerIndex) of  -- is there a better way to do this?
        (Just pointIndex, Just checkerIndex) -> Just $ PointPlacement pointIndex checkerIndex
        _ -> Nothing

-- Convert from point/checker indices to appropriate center placement
checkerPosition :: Placement -> (Int,Int)
checkerPosition (PointPlacement pointIndex checkerIndex) = 
    let pointOffset | pointIndex < 12 =      pointIndex -- from lower leftmost point
                    | otherwise       = 23 - pointIndex  -- from upper leftmost point
  
        barGapUsed | pointOffset < 6 = 0                -- left side of board
                   | otherwise       = barGap           -- right side of board
  
        leftDelta = barGapUsed + pointOffset * pointWidth -- distance in horizonatal "board units"
  
        stackDirection | pointIndex < 12 = 1           -- stacking up
                       | otherwise       = -1            -- stacking down
  
        stackDelta = stackDirection*checkerIndex*2*checkerRadius -- distance in vertical "board units"
  
        xBase = leftmostPoint                           -- horizontal position on board
  
        yBase | pointIndex < 12 = firstUpperLevel       -- vertical position on board
              | otherwise       = firstLowerLevel
  
        cx = xBase + leftDelta
        cy = yBase + stackDelta
    in (cx,cy)

checkerPosition (LeftSidePlacement checkerIndex) = 
        (sideWidth `div` 2,firstLowerLevel -checkerIndex*2*checkerRadius )

checkerPosition (RightSidePlacement checkerIndex) = 
        (sideWidth+2*(5+(6*pointWidth))+barWidth+(sideWidth `div` 2),firstLowerLevel -checkerIndex*2*checkerRadius )

-- Given a checker element, move it to the spot specified
-- by the pointIndex and checkerIndex.
setCheckerPosition :: Elem -> Placement -> IO ()
setCheckerPosition circle placement = do
    let (cx,cy) = checkerPosition placement
    setAttr circle "cx" $ show cx
    setAttr circle "cy" $ show cy

-- Given a checker element, move it to the spot specified
-- by the pointIndex and checkerIndex.
animateToCheckerPosition :: Elem -> Placement -> IO ()
animateToCheckerPosition circle placement = do
    let (cx,cy) = checkerPosition placement
    animateCircleFFI circle cx cy 300

checkerPositionClass :: Placement -> String 
checkerPositionClass pl = map (\c -> if c==' ' then '_'; else c) $ show pl

setCheckerClass :: Elem -> Color -> Bool -> Placement -> IO ()
setCheckerClass circle color draggable placement = 
    setAttr circle "class" (svgCheckerClass color usersColor placement) 
    where 
      svgCheckerClass color usersColor pl = 
          (if draggable then "draggable " else "") 
          ++ show color ++ " "
          ++ checkerPositionClass pl

getCheckerElement :: Placement -> IO Elem
getCheckerElement pl = do
    elems <- elemsByClass $ checkerPositionClass pl
    return $ head elems

-- Create and place a single checker on specified point
drawChecker :: Color -> Bool -> Placement -> IO ()
drawChecker color draggable pl = do
    Just d <- elemById "board" 
    circle <- newElemNS "http://www.w3.org/2000/svg" "circle"
    setAttr circle "r" (show checkerRadius)
    setCheckerPosition circle pl
    setCheckerClass circle color draggable pl
    appendChild d circle 

-- Create and draw all the checkers for a given point.
drawPoint :: Color -> Int -> Point -> IO ()
drawPoint usersColor pointIndex (Point pointColor pointCount) =
    let draggable = usersColor == pointColor
    in sequence_ [drawChecker pointColor draggable (PointPlacement pointIndex checkerIndex) | checkerIndex <- take pointCount [0..]]

-- Create and draw all the checkers for a given side.
-- Side is identified by color - white checkers go on left.
drawSide :: Color -> Color -> Int -> IO ()
drawSide color usersColor count  =
    let pl = if color == White then LeftSidePlacement else RightSidePlacement
    in sequence_ [drawChecker color True (pl i) | i <- take count [0..]]

-- Create and draw all the checkers sitting on both sides for a game.
drawGame :: Game -> IO ()
drawGame (Game points wos bos wob bob usersColor _) = do
        -- sequence_ $ zipWith (drawPoint usersColor) [0 ..] points
        drawSide White usersColor wos 
        drawSide Black usersColor bos 

-- Given a game and a move, create the resulting new game.
updateGame :: Game -> Int -> Int -> Game
updateGame g@(Game points wos bos wob bob _ _) iFrom iTo = 
    -- could this be improved with lens?
    let fromColor = checkerColor $ points !! iFrom
        doMove f t (i,pt)
          | (i == f) = Point (checkerColor pt) (checkerCount pt -1)
          | (i == t)   = Point fromColor (checkerCount pt +1)
          | otherwise    = pt
                
    in g {gamePoints = map (doMove iFrom iTo) (zip [0..] points) }

-- Given a game and a move, create the resulting new game.
moveChecker :: Placement -> Placement -> Color -> IO ()
moveChecker oldPlacement newPlacement color = do
    checker <- getCheckerElement oldPlacement
    animateToCheckerPosition checker newPlacement
    setCheckerClass checker color True newPlacement 

-- slide all of the checkers at a given point together.
fixCheckersAtPoint :: Game -> Int -> Int -> IO ()
fixCheckersAtPoint (Game points wos bos wob bob userColor _ ) pointIndex missingCheckerIndex = do
    let moveIndices = drop 1 [missingCheckerIndex .. checkerCount (points !! pointIndex)]
    sequence_ [moveChecker (PointPlacement pointIndex i) (PointPlacement pointIndex (i-1)) userColor | i <- moveIndices ]

dropCheckerCallback :: Game -> String -> Float -> Float -> IO ()
dropCheckerCallback g@(Game points wos bos wob bob usersColor _) className x y = do
    let classes = words className

        -- extract placement from classes
        placementString =  map (\c -> if c=='_' then ' '; else c) (classes !! 2) 
        oldPlacement = read placementString :: Placement

        -- extract color from classes
        oldColor =  read (classes !! 1) :: Color

        -- Get new placement from mouse pick coords
        maybeNewPlacement = coordsToPlacement g x y

    case (oldPlacement, maybeNewPlacement) of
        (PointPlacement oldPoint oldChecker, Just newPlacement@(PointPlacement newPoint newChecker)) -> do 

            let newColor = checkerColor $ points !! newPoint
                newCount = checkerCount $ points !! newPoint
                legalMove = newPoint > oldPoint && (newColor == oldColor || newCount < 2)

            if legalMove then do
                let newGame = updateGame g oldPoint newPoint
                moveChecker oldPlacement newPlacement oldColor
                fixCheckersAtPoint newGame oldPoint oldChecker
                setCallbacks newGame
            else moveChecker oldPlacement oldPlacement oldColor
        _ -> moveChecker oldPlacement oldPlacement oldColor

clickedJoin :: MonadEvent m => EventData MouseEvent -> m ()
clickedJoin _ = do
        Just skelem <- elemById "sharedKey" 
        Just sk <- getValue skelem
        liftIO $ showAlertFFI $ fromJSStr sk

setCallbacks :: Game -> IO ()
setCallbacks g = do
        Just el <- elemById "joinGame" 
        onEvent el Click clickedJoin
        setDropCheckerCallbackFFI $ dropCheckerCallback g

initialPointCounts = [2,0,0,0,0,0,0,0,0,0,0,5,0,0,0,0,3,0,5,0,0,0,0,0]
whiteStart = [ Point White sc | sc <- initialPointCounts ]

blackStart = map whiteToBlack $ reverse whiteStart
             where whiteToBlack (Point White c) = Point Black c
                   whiteToBlack p = p

gameStart = zipWith whiteOrBlack whiteStart blackStart
             where whiteOrBlack (Point White 0) b = b
                   whiteOrBlack w@(Point White _) _ = w
newGame :: Game
newGame = let checkerCount = sum initialPointCounts
          in Game gameStart checkerCount checkerCount 0 0 White White

setHint :: String -> IO ()
setHint s = do
        Just el <- elemById "HintText"
        setProp el "innerHTML" s

main :: IO ()
main = do setHint "You have not joined a game (yet)."
          drawGame newGame
          setCallbacks newGame

