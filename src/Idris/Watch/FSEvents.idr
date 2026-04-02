||| FSEvents-based file watching for macOS
|||
||| This module provides efficient file system monitoring using the macOS
||| FSEvents API. On non-macOS platforms, it falls back to polling.
module Idris.Watch.FSEvents

import Core.Core

import System.Info

%default covering

-- Helper functions for pointer comparison (defined first to avoid forward refs)
prim__eqAnyPtr : AnyPtr -> AnyPtr -> Int
prim__eqAnyPtr = believe_me

prim__nullAnyPtr : AnyPtr -> Bool
prim__nullAnyPtr p = prim__nullPtr (believe_me p) == 1

prim__eqStrPtr : Ptr String -> Ptr String -> Int
prim__eqStrPtr = believe_me

prim__nullStrPtr : Ptr String -> Bool
prim__nullStrPtr p = prim__nullPtr p == 1

prim__peekStrPtr : Ptr String -> PrimIO String
prim__peekStrPtr = believe_me

-- Opaque handle for the FSEvents watcher
data FSEventsWatcher : Type where

-- FFI imports for macOS FSEvents support
%foreign "C:idris_fsevents_init,libidris2_support"
prim__fseventsInit : PrimIO AnyPtr

%foreign "C:idris_fsevents_add_path,libidris2_support"
prim__fseventsAddPath : AnyPtr -> String -> PrimIO Int

%foreign "C:idris_fsevents_start,libidris2_support"
prim__fseventsStart : AnyPtr -> PrimIO Int

%foreign "C:idris_fsevents_stop,libidris2_support"
prim__fseventsStop : AnyPtr -> PrimIO ()

%foreign "C:idris_fsevents_get_changed,libidris2_support"
prim__fseventsGetChanged : AnyPtr -> PrimIO (Ptr String)

%foreign "C:idris_fsevents_cleanup,libidris2_support"
prim__fseventsCleanup : AnyPtr -> PrimIO ()

%foreign "C:free,libc"
prim__free : Ptr String -> PrimIO ()

||| Check if FSEvents is available on this platform
export
fseventsAvailable : Bool
fseventsAvailable = os == "darwin"

||| Initialize an FSEvents watcher
||| Returns Nothing on non-macOS platforms or if initialization fails
export
initFSEvents : Core (Maybe FSEventsWatcher)
initFSEvents =
  if not fseventsAvailable
    then pure Nothing
    else do
      ptr <- coreLift $ primIO prim__fseventsInit
      if prim__nullAnyPtr ptr
        then pure Nothing
        else pure (Just (MkWatcher ptr))
  where
    MkWatcher : AnyPtr -> FSEventsWatcher
    MkWatcher = believe_me

||| Add a path to watch
export
addPath : FSEventsWatcher -> String -> Core Bool
addPath watcher path = do
  let ptr = believe_me {b=AnyPtr} watcher
  res <- coreLift $ primIO (prim__fseventsAddPath ptr path)
  pure (res == 0)

||| Start watching for changes
export
startWatching : FSEventsWatcher -> Core Bool
startWatching watcher = do
  let ptr = believe_me {b=AnyPtr} watcher
  res <- coreLift $ primIO (prim__fseventsStart ptr)
  pure (res == 0)

||| Stop watching for changes
export
stopWatching : FSEventsWatcher -> Core ()
stopWatching watcher = do
  let ptr = believe_me {b=AnyPtr} watcher
  coreLift $ primIO (prim__fseventsStop ptr)

||| Get the next changed file path
||| Returns Nothing if no files have changed
export
getChangedFile : FSEventsWatcher -> Core (Maybe String)
getChangedFile watcher = do
  let ptr = believe_me {b=AnyPtr} watcher
  strPtr <- coreLift $ primIO (prim__fseventsGetChanged ptr)
  if prim__nullStrPtr strPtr
    then pure Nothing
    else do
      str <- coreLift $ primIO (prim__peekStrPtr strPtr)
      coreLift $ primIO (prim__free strPtr)
      pure (Just str)

||| Cleanup and free the watcher
export
cleanupWatcher : FSEventsWatcher -> Core ()
cleanupWatcher watcher = do
  let ptr = believe_me {b=AnyPtr} watcher
  coreLift $ primIO (prim__fseventsCleanup ptr)

||| Get all changed files (non-blocking)
||| Returns a list of all changed file paths since last check
export
getAllChangedFiles : FSEventsWatcher -> Core (List String)
getAllChangedFiles watcher = go []
  where
    go : List String -> Core (List String)
    go acc = do
      mfile <- getChangedFile watcher
      case mfile of
        Nothing => pure (reverse acc)
        Just f => go (f :: acc)
