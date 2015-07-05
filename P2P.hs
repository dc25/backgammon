{-# LANGUAGE ForeignFunctionInterface, OverloadedStrings, 
             GeneralizedNewtypeDeriving #-}
module P2P (
    P2P 
  ) where

import Haste.Prim
import Control.Monad.IO.Class

newtype P2P = P2P JSAny

type ConnectionID = String

-- Create and access a P2P connection specified by ID
foreign import ccall jsConnect :: JSString -> IO (Ptr (Maybe P2P))
connect :: MonadIO m => ConnectionID -> m (Maybe P2P)
connect cid = liftIO $ fromPtr `fmap` (jsConnect $ toJSStr cid)

