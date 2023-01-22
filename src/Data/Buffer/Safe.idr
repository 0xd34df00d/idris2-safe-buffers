module Data.Buffer.Safe

import Data.Buffer as B
import Data.Fin
import Data.Vect

import Data.Storable

%default total

-- * Safe buffer definition and operations

export
data SBuffer : (0 n : Nat) -> (0 ty : Type) -> Type where
  MkSB : (buf : Buffer) -> SBuffer n ty

%name SBuffer buf


%inline
toByteIdx : (0 ty : Type) ->
            Storable ty =>
            (idx : Fin n) ->
            Int
toByteIdx ty idx = cast (finToNat idx) * sizeofTy ty


export %inline
newBuffer : HasIO io =>
            Storable ty =>
            (n : Nat) ->
            io (Maybe (SBuffer n ty))
newBuffer n = map (map MkSB) $ B.newBuffer (cast n * sizeofTy ty)

export %inline
setAt : HasIO io =>
        Storable ty =>
        (buf : SBuffer n ty) ->
        (idx : Fin n) ->
        (value : ty) ->
        io ()
setAt (MkSB buf) = setAtByte buf . toByteIdx ty

export %inline
getAt : HasIO io =>
        Storable ty =>
        (buf : SBuffer n ty) ->
        (idx : Fin n) ->
        io ty
getAt (MkSB buf) = getAtByte buf . toByteIdx ty

export
toVect : HasIO io =>
         Storable ty =>
         {n : _} ->
         (buf : SBuffer n ty) ->
         io (Vect n ty)
toVect buf = traverse (getAt buf) range

export
fromVect : HasIO io =>
           Storable ty =>
           {n : _} ->
           (values : Vect n ty) ->
           io (Maybe (SBuffer n ty))
fromVect values = do
  Just buf <- newBuffer n
      | Nothing => pure Nothing
  traverse_ (uncurry $ setAt buf) (zip range values)
  pure $ Just buf
