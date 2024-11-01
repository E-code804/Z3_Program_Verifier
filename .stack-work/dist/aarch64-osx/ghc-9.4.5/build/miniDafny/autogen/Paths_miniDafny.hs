{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module Paths_miniDafny (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where


import qualified Control.Exception as Exception
import qualified Data.List as List
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude


#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir `joinFileName` name)

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath



bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath
bindir     = "/Users/erikpfeffer/Desktop/CS/UMD_CS/FinalProject/.stack-work/install/aarch64-osx/552a87bc517b0998c7c7bb2922ac58674e460efd270f056f3973db259977e9aa/9.4.5/bin"
libdir     = "/Users/erikpfeffer/Desktop/CS/UMD_CS/FinalProject/.stack-work/install/aarch64-osx/552a87bc517b0998c7c7bb2922ac58674e460efd270f056f3973db259977e9aa/9.4.5/lib/aarch64-osx-ghc-9.4.5/miniDafny-0.1.0.0-9IMdsoJkxyABj3qCm1OGSP-miniDafny"
dynlibdir  = "/Users/erikpfeffer/Desktop/CS/UMD_CS/FinalProject/.stack-work/install/aarch64-osx/552a87bc517b0998c7c7bb2922ac58674e460efd270f056f3973db259977e9aa/9.4.5/lib/aarch64-osx-ghc-9.4.5"
datadir    = "/Users/erikpfeffer/Desktop/CS/UMD_CS/FinalProject/.stack-work/install/aarch64-osx/552a87bc517b0998c7c7bb2922ac58674e460efd270f056f3973db259977e9aa/9.4.5/share/aarch64-osx-ghc-9.4.5/miniDafny-0.1.0.0"
libexecdir = "/Users/erikpfeffer/Desktop/CS/UMD_CS/FinalProject/.stack-work/install/aarch64-osx/552a87bc517b0998c7c7bb2922ac58674e460efd270f056f3973db259977e9aa/9.4.5/libexec/aarch64-osx-ghc-9.4.5/miniDafny-0.1.0.0"
sysconfdir = "/Users/erikpfeffer/Desktop/CS/UMD_CS/FinalProject/.stack-work/install/aarch64-osx/552a87bc517b0998c7c7bb2922ac58674e460efd270f056f3973db259977e9aa/9.4.5/etc"

getBinDir     = catchIO (getEnv "miniDafny_bindir")     (\_ -> return bindir)
getLibDir     = catchIO (getEnv "miniDafny_libdir")     (\_ -> return libdir)
getDynLibDir  = catchIO (getEnv "miniDafny_dynlibdir")  (\_ -> return dynlibdir)
getDataDir    = catchIO (getEnv "miniDafny_datadir")    (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "miniDafny_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "miniDafny_sysconfdir") (\_ -> return sysconfdir)




joinFileName :: String -> String -> FilePath
joinFileName ""  fname = fname
joinFileName "." fname = fname
joinFileName dir ""    = dir
joinFileName dir fname
  | isPathSeparator (List.last dir) = dir ++ fname
  | otherwise                       = dir ++ pathSeparator : fname

pathSeparator :: Char
pathSeparator = '/'

isPathSeparator :: Char -> Bool
isPathSeparator c = c == '/'
