{-# LANGUAGE MultiWayIf #-}

module Main (main) where

import Control.Applicative
import Control.Monad
import Control.Monad.List
import Data.List
import System.Directory
import System.FilePath
import Test.DocTest

main :: IO ()
main = do
  sources <- findSources "src"
  doctest ("-isrc" : sources)

findSources :: FilePath -> IO [FilePath]
findSources dir = runListT (goDir dir)
  where
    goItem :: FilePath -> FilePath -> ListT IO FilePath
    goItem _ ('.':_) = empty
    goItem parent name = do
      let path = parent </> name
      isDir  <- liftIO (doesDirectoryExist path)
      isFile <- liftIO (doesFileExist path)
      if | isDir     -> goDir  path
         | isFile    -> goFile path
         | otherwise -> empty

    goDir  path = goItem path =<< ListT (getDirectoryContents path)
    goFile path = path <$ guard (".hs" `isSuffixOf` path)
