module Data.Storable

import Data.Buffer

%default total

public export
interface Storable (0 ty : Type) where
  %inline
  sizeof : Int
  %inline
  setAtByte : HasIO io =>
              (buf : Buffer) ->
              (byteIdx : Int) ->
              (value : ty) ->
              io ()
  %inline
  getAtByte : HasIO io =>
              (buf : Buffer) ->
              (byteIdx : Int) ->
              io ty

export %inline
Storable Bits8  where sizeof = 1 ; setAtByte = setBits8  ; getAtByte = getBits8

export %inline
Storable Bits16 where sizeof = 2 ; setAtByte = setBits16 ; getAtByte = getBits16

export %inline
Storable Bits32 where sizeof = 4 ; setAtByte = setBits32 ; getAtByte = getBits32

export %inline
Storable Bits64 where sizeof = 8 ; setAtByte = setBits64 ; getAtByte = getBits64

export %inline
Storable Int where sizeof = 8 ; setAtByte = setInt ; getAtByte = getInt

export %inline
Storable Double where sizeof = 8 ; setAtByte = setDouble ; getAtByte = getDouble


public export %inline
sizeofTy : (0 ty : Type) -> Storable ty => Int
sizeofTy ty = sizeof {ty}
