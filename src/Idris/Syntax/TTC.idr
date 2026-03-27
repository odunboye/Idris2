module Idris.Syntax.TTC

import public Core.Binary
import public Core.TTC

import TTImp.TTImp
import TTImp.TTImp.TTC

import Idris.Syntax

import Data.SortedMap

import Libraries.Data.ANameMap
import Libraries.Data.NameMap
import Libraries.Data.NatSet

%default covering

export
TTC IFaceInfo where
  toBuf (MkIFaceInfo ic impps ps cs ms ds)
      = do toBuf ic
           toBuf impps
           toBuf ps
           toBuf cs
           toBuf ms
           toBuf ds

  fromBuf
      = do ic <- fromBuf
           impps <- fromBuf
           ps <- fromBuf
           cs <- fromBuf
           ms <- fromBuf
           ds <- fromBuf
           pure (MkIFaceInfo ic impps ps cs ms ds)

export
TTC Fixity where
  toBuf InfixL = tag 0
  toBuf InfixR = tag 1
  toBuf Infix = tag 2
  toBuf Prefix = tag 3

  fromBuf
      = case !getTag of
             0 => pure InfixL
             1 => pure InfixR
             2 => pure Infix
             3 => pure Prefix
             _ => corrupt "Fixity"

export
TTC ImportSpec where
  toBuf Unrestricted = tag 0
  toBuf (Hiding ns) = do tag 1; toBuf ns
  toBuf (Explicit ns) = do tag 2; toBuf ns

  fromBuf
    = case !getTag of
         0 => pure Unrestricted
         1 => do ns <- fromBuf; pure (Hiding ns)
         2 => do ns <- fromBuf; pure (Explicit ns)
         _ => corrupt "ImportSpec"

export
TTC Import where
  toBuf (MkImport loc reexport path nameAs spec)
    = do toBuf loc
         toBuf reexport
         toBuf path
         toBuf nameAs
         toBuf spec

  fromBuf
    = do loc <- fromBuf
         reexport <- fromBuf
         path <- fromBuf
         nameAs <- fromBuf
         spec <- fromBuf
         pure (MkImport loc reexport path nameAs spec)

export
TTC BindingModifier where
  toBuf NotBinding = tag 0
  toBuf Typebind = tag 1
  toBuf Autobind = tag 2
  fromBuf
      = case !getTag of
             0 => pure NotBinding
             1 => pure Typebind
             2 => pure Autobind
             _ => corrupt "binding"

export
TTC FixityInfo where
  toBuf fx
      = do toBuf fx.fc
           toBuf fx.vis
           toBuf fx.bindingInfo
           toBuf fx.fix
           toBuf fx.precedence
  fromBuf
      = do fc <- fromBuf
           vis <- fromBuf
           binding <- fromBuf
           fix <- fromBuf
           prec <- fromBuf
           pure $ MkFixityInfo fc vis binding fix prec


export
TTC PatSynInfo where
  toBuf psi
      = do toBuf psi.fc
           toBuf psi.vis
           toBuf psi.params
           toBuf psi.body
           toBuf psi.bidirectional
  fromBuf
      = do fc <- fromBuf
           vis <- fromBuf
           params <- fromBuf
           body <- fromBuf
           bidir <- fromBuf
           pure $ MkPatSynInfo fc vis params body bidir

export
TTC SyntaxInfo where
  toBuf syn
      = do toBuf (ANameMap.toList (fixities syn))
           toBuf (filter (\n => elemBy (==) (fst n) (saveMod syn))
                           (SortedMap.toList $ modDocstrings syn))
           toBuf (filter (\n => elemBy (==) (fst n) (saveMod syn))
                           (SortedMap.toList $ modDocexports syn))
           toBuf (filter (\n => fst n `elem` saveIFaces syn)
                           (ANameMap.toList (ifaces syn)))
           toBuf (filter (\n => isJust (lookup (fst n) (saveDocstrings syn)))
                           (ANameMap.toList (defDocstrings syn)))
           toBuf (bracketholes syn)
           toBuf (startExpr syn)
           toBuf (holeNames syn)
           toBuf (ANameMap.toList (patSyns syn))

  fromBuf
      = do fix <- fromBuf
           moddstr <- fromBuf
           modexpts <- fromBuf
           ifs <- fromBuf
           defdstrs <- fromBuf
           bhs <- fromBuf
           start <- fromBuf
           hnames <- fromBuf
           patsyns <- fromBuf
           pure $ MkSyntax (fromList fix)
                   [] (fromList moddstr) (fromList modexpts)
                   [] (fromList ifs)
                   empty (fromList defdstrs)
                   bhs
                   [] empty start
                   hnames
                   (fromList patsyns)
