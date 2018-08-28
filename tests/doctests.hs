{-# LANGUAGE MultiWayIf #-}

module Main (main) where

import Control.Applicative (empty)
import Control.Monad (guard)
import Control.Monad.List (ListT (ListT), liftIO,  runListT)
import Data.List (isSuffixOf)
import System.Directory (doesDirectoryExist, doesFileExist,
  getDirectoryContents)
import System.FilePath ((</>))
import Test.DocTest (doctest)

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
