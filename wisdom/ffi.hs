-- Calling C functions from Haskell using the Foreign Function Interface (FFI).
-- See: https://downloads.haskell.org/~ghc/8.6.5/docs/html/users_guide/ffi-chap.html#extension-ForeignFunctionInterface
-- See: https://www.haskell.org/definition/haskell2010.pdf (Chapter 8, "Foreign Function Interface")

-- If you have GHC and a C compiler, build with:
--  $ cc -c ffi-helper.c -o ffi-helper.o
--  $ ghc --make ffi.hs ffi-helper.o -o ffi

-- FFI is enabled by default in GHC, but using an explicit language pragma
-- doesn't hurt!
{-# LANGUAGE ForeignFunctionInterface #-}

module Main (main) where

import System.Posix (Fd(..), openFd, closeFd, OpenMode(ReadOnly), defaultFileFlags, fileSynchronise, mkstemp, fdWrite, handleToFd, fileExist)
import Foreign.C (CInt(..), CChar(..))
import Foreign.C.String (CString, withCString)
import Foreign.C.Error (throwErrno)
import System.FilePath (pathSeparator)
import Data.List (elemIndex)

-- Currently the `unix` module (which exports System.Posix) does not include
-- the shiny new "*at" system calls.
foreign import ccall unsafe "linkat" c_linkat :: CInt -> CString -> CInt -> CString -> CInt -> IO CInt
foreign import ccall unsafe "unlinkat" c_unlinkat :: CInt -> CString -> CInt -> IO CInt
foreign import ccall unsafe "renameat" c_renameat :: CInt -> CString -> CInt -> CString -> IO CInt

-- This is defined in ffi-helper.c
foreign import ccall unsafe fizzbuzz :: CInt -> IO CInt

linkat :: Fd -> FilePath -> Fd -> FilePath -> IO ()
linkat (Fd srcDir) srcName (Fd dstDir) dstName =
  withCString srcName (\srcName' ->
    withCString dstName (\dstName' -> do
      res <- c_linkat srcDir srcName' dstDir dstName' 0
      case res of
        0 -> return ()
        _ -> throwErrno "linkat"))

unlinkat :: Fd -> FilePath -> IO ()
unlinkat (Fd dir) name =
  withCString name (\name' -> do
    res <- c_unlinkat dir name' 0
    case res of
      0 -> return ()
      _ -> throwErrno "unlinkat")

renameat :: Fd -> FilePath -> Fd -> FilePath -> IO ()
renameat (Fd srcDir) srcName (Fd dstDir) dstName =
  withCString srcName (\srcName' ->
    withCString dstName (\dstName' -> do
      res <- c_renameat srcDir srcName' dstDir dstName'
      case res of
        0 -> return ()
        _ -> throwErrno "renameat"))

lastIndexOf :: Eq a => a -> [a] -> Maybe Int
lastIndexOf x l = do
  i <- elemIndex x (reverse l)
  return (length l - i - 1)

splitDirAndName :: FilePath -> (FilePath, FilePath)
splitDirAndName p =
  case lastIndexOf pathSeparator p of
    Just i -> let (dir, name) = splitAt i p in (dir, tail name)
    Nothing -> (".", p)

dirname  = fst . splitDirAndName
basename = snd . splitDirAndName

data WriteMode = CreateOrOverwrite | CreateIfMissing

durablyWriteFile :: WriteMode -> FilePath -> (Fd -> IO a) -> IO a
durablyWriteFile mode path writeFunc = do
  -- optional preemptive existence check
  case mode of
    CreateOrOverwrite -> return ()
    CreateIfMissing -> do
      ex <- fileExist path
      if ex
        then error $ "already exists: " ++ path
        else return ()

  let (baseDirName, baseFileName) = splitDirAndName path
  (tmpPath, tmpHandle) <- mkstemp (baseDirName ++ "/")
  tmpFd <- handleToFd tmpHandle -- closes tmpHandle, opens tmpFd
  res <- writeFunc tmpFd

  -- ensure that the file contents are on disk
  fileSynchronise tmpFd
  closeFd tmpFd -- TODO: always do this, even if another call throws

  -- link into place and ensure that the link is on disk
  dirFd <- openFd baseDirName ReadOnly Nothing defaultFileFlags
  let tmpBaseName = basename tmpPath
  case mode of
    CreateOrOverwrite -> do
      renameat dirFd tmpBaseName dirFd baseFileName
    CreateIfMissing -> do
      linkat dirFd tmpBaseName dirFd baseFileName
      unlinkat dirFd tmpBaseName
  fileSynchronise dirFd
  closeFd dirFd -- TODO: always do this, even if another call throws

  return res

main = do
  _ <- fizzbuzz 10
  let path = "/tmp/x"
  durablyWriteFile CreateIfMissing path (\f ->
    fdWrite f "hello!\n")
  putStrLn $ "overwrote " ++ path
