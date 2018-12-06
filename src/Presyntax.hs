
module Presyntax where

import Common

type Ty' = Tm'
type Tm  = Posed Tm'
type Ty  = Posed Ty'

type Profiling = Bool

data TopEntry
  = TEPostulate  Profiling (Posed Name) {-# unpack #-} Ty
  | TEDefinition Profiling (Posed Name) {-# unpack #-} Ty {-# unpack #-} Tm
  deriving Show

type Program = [TopEntry]

data Tm'
  = Var Name
  | Let Name {-# unpack #-} Ty {-# unpack #-} Tm {-# unpack #-} Tm
  | App {-# unpack #-} Tm {-# unpack #-} Tm NameOrIcit
  | Lam Name NameOrIcit {-# unpack #-} Tm
  | Pi {-# unpack #-} (Named Icit) {-# unpack #-} Ty {-# unpack #-} Ty
  | U
  | StopMetaIns {-# unpack #-} Tm
  | Hole
  deriving Show
