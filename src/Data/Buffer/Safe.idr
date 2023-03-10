module Data.Buffer.Safe

import Data.Buffer as B
import Data.Fin
import Data.Vect

import Data.Storable

%default total

export
data SBuffer : (0 n : Nat) -> (0 ty : Type) -> Type where
  MkSB : (buf : Buffer) -> SBuffer n ty

%name SBuffer buf


%inline
toByteIdx : (0 ty : Type) ->
            Storable ty =>
            (idx : Fin n) ->
            Int
toByteIdx ty idx = cast $ finToNat idx * sizeofTy ty


export %inline
newBuffer : HasIO io =>
            Storable ty =>
            (n : Nat) ->
            io (Maybe (SBuffer n ty))
newBuffer n = map (map MkSB) $ B.newBuffer (cast $ n * sizeofTy ty)

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


export %inline
castBuffer : (Storable ty, Storable ty') =>
             {auto 0 sameSize : sizeofTy ty' * n' = sizeofTy ty * n} ->
             (buf : SBuffer n ty) ->
             SBuffer n' ty'
castBuffer (MkSB buf) = MkSB buf

export %inline
castToBytes : Storable ty =>
              (buf : SBuffer n ty) ->
              SBuffer (sizeofTy ty * n) Bits8
castToBytes = castBuffer {sameSize = multOneLeftNeutral _}

export
copyData : HasIO io =>
           Storable ty =>
           (elemCnt : Nat) ->
           (srcBuf : SBuffer (elemCnt + srcN) ty) ->
           (dstBuf : SBuffer (elemCnt + dstN) ty) ->
           (srcPos : Fin srcN) ->
           (dstPos : Fin dstN) ->
           io ()
copyData elemCnt (MkSB srcBuf) (MkSB dstBuf) srcPos dstPos =
  B.copyData
    srcBuf
    (toByteIdx ty srcPos)
    (cast $ elemCnt * sizeofTy ty)
    dstBuf
    (toByteIdx ty dstPos)


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
