
module Presyntax where

import Common

type Ty' = Tm'
type Tm  = Posed Tm'
type Ty  = Posed Ty'

data TopEntry
  = TEPostulate  (Posed Name) {-# unpack #-} Ty
  | TEDefinition (Posed Name) {-# unpack #-} Ty {-# unpack #-} Tm
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
