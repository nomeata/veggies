module Ollvm_ast where

import qualified Prelude

data Coq_linkage =
   LINKAGE_Private
 | LINKAGE_Internal
 | LINKAGE_Available_externally
 | LINKAGE_Linkonce
 | LINKAGE_Weak
 | LINKAGE_Common
 | LINKAGE_Appending
 | LINKAGE_Extern_weak
 | LINKAGE_Linkonce_odr
 | LINKAGE_Weak_odr
 | LINKAGE_External

linkage_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 ->
                a1 -> Coq_linkage -> a1
linkage_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 l =
  case l of {
   LINKAGE_Private -> f;
   LINKAGE_Internal -> f0;
   LINKAGE_Available_externally -> f1;
   LINKAGE_Linkonce -> f2;
   LINKAGE_Weak -> f3;
   LINKAGE_Common -> f4;
   LINKAGE_Appending -> f5;
   LINKAGE_Extern_weak -> f6;
   LINKAGE_Linkonce_odr -> f7;
   LINKAGE_Weak_odr -> f8;
   LINKAGE_External -> f9}

linkage_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1
               -> Coq_linkage -> a1
linkage_rec =
  linkage_rect

data Coq_dll_storage =
   DLLSTORAGE_Dllimport
 | DLLSTORAGE_Dllexport

dll_storage_rect :: a1 -> a1 -> Coq_dll_storage -> a1
dll_storage_rect f f0 d =
  case d of {
   DLLSTORAGE_Dllimport -> f;
   DLLSTORAGE_Dllexport -> f0}

dll_storage_rec :: a1 -> a1 -> Coq_dll_storage -> a1
dll_storage_rec =
  dll_storage_rect

data Coq_visibility =
   VISIBILITY_Default
 | VISIBILITY_Hidden
 | VISIBILITY_Protected

visibility_rect :: a1 -> a1 -> a1 -> Coq_visibility -> a1
visibility_rect f f0 f1 v =
  case v of {
   VISIBILITY_Default -> f;
   VISIBILITY_Hidden -> f0;
   VISIBILITY_Protected -> f1}

visibility_rec :: a1 -> a1 -> a1 -> Coq_visibility -> a1
visibility_rec =
  visibility_rect

data Coq_cconv =
   CC_Ccc
 | CC_Fastcc
 | CC_Coldcc
 | CC_Cc Prelude.Int

cconv_rect :: a1 -> a1 -> a1 -> (Prelude.Int -> a1) -> Coq_cconv -> a1
cconv_rect f f0 f1 f2 c =
  case c of {
   CC_Ccc -> f;
   CC_Fastcc -> f0;
   CC_Coldcc -> f1;
   CC_Cc x -> f2 x}

cconv_rec :: a1 -> a1 -> a1 -> (Prelude.Int -> a1) -> Coq_cconv -> a1
cconv_rec =
  cconv_rect

data Coq_param_attr =
   PARAMATTR_Zeroext
 | PARAMATTR_Signext
 | PARAMATTR_Inreg
 | PARAMATTR_Byval
 | PARAMATTR_Inalloca
 | PARAMATTR_Sret
 | PARAMATTR_Align Prelude.Int
 | PARAMATTR_Noalias
 | PARAMATTR_Nocapture
 | PARAMATTR_Nest
 | PARAMATTR_Returned
 | PARAMATTR_Nonnull
 | PARAMATTR_Dereferenceable Prelude.Int

param_attr_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> (Prelude.Int -> a1) ->
                   a1 -> a1 -> a1 -> a1 -> a1 -> (Prelude.Int -> a1) ->
                   Coq_param_attr -> a1
param_attr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 p =
  case p of {
   PARAMATTR_Zeroext -> f;
   PARAMATTR_Signext -> f0;
   PARAMATTR_Inreg -> f1;
   PARAMATTR_Byval -> f2;
   PARAMATTR_Inalloca -> f3;
   PARAMATTR_Sret -> f4;
   PARAMATTR_Align x -> f5 x;
   PARAMATTR_Noalias -> f6;
   PARAMATTR_Nocapture -> f7;
   PARAMATTR_Nest -> f8;
   PARAMATTR_Returned -> f9;
   PARAMATTR_Nonnull -> f10;
   PARAMATTR_Dereferenceable x -> f11 x}

param_attr_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> (Prelude.Int -> a1) ->
                  a1 -> a1 -> a1 -> a1 -> a1 -> (Prelude.Int -> a1) ->
                  Coq_param_attr -> a1
param_attr_rec =
  param_attr_rect

data Coq_fn_attr =
   FNATTR_Alignstack Prelude.Int
 | FNATTR_Alwaysinline
 | FNATTR_Builtin
 | FNATTR_Cold
 | FNATTR_Inlinehint
 | FNATTR_Jumptable
 | FNATTR_Minsize
 | FNATTR_Naked
 | FNATTR_Nobuiltin
 | FNATTR_Noduplicate
 | FNATTR_Noimplicitfloat
 | FNATTR_Noinline
 | FNATTR_Nonlazybind
 | FNATTR_Noredzone
 | FNATTR_Noreturn
 | FNATTR_Nounwind
 | FNATTR_Optnone
 | FNATTR_Optsize
 | FNATTR_Readnone
 | FNATTR_Readonly
 | FNATTR_Returns_twice
 | FNATTR_Sanitize_address
 | FNATTR_Sanitize_memory
 | FNATTR_Sanitize_thread
 | FNATTR_Ssp
 | FNATTR_Sspreq
 | FNATTR_Sspstrong
 | FNATTR_Uwtable
 | FNATTR_String Prelude.String
 | FNATTR_Key_value ((,) Prelude.String Prelude.String)
 | FNATTR_Attr_grp Prelude.Int

fn_attr_rect :: (Prelude.Int -> a1) -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1
                -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1
                -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1
                -> (Prelude.String -> a1) -> (((,) Prelude.String
                Prelude.String) -> a1) -> (Prelude.Int -> a1) -> Coq_fn_attr
                -> a1
fn_attr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 =
  case f30 of {
   FNATTR_Alignstack x -> f x;
   FNATTR_Alwaysinline -> f0;
   FNATTR_Builtin -> f1;
   FNATTR_Cold -> f2;
   FNATTR_Inlinehint -> f3;
   FNATTR_Jumptable -> f4;
   FNATTR_Minsize -> f5;
   FNATTR_Naked -> f6;
   FNATTR_Nobuiltin -> f7;
   FNATTR_Noduplicate -> f8;
   FNATTR_Noimplicitfloat -> f9;
   FNATTR_Noinline -> f10;
   FNATTR_Nonlazybind -> f11;
   FNATTR_Noredzone -> f12;
   FNATTR_Noreturn -> f13;
   FNATTR_Nounwind -> f14;
   FNATTR_Optnone -> f15;
   FNATTR_Optsize -> f16;
   FNATTR_Readnone -> f17;
   FNATTR_Readonly -> f18;
   FNATTR_Returns_twice -> f19;
   FNATTR_Sanitize_address -> f20;
   FNATTR_Sanitize_memory -> f21;
   FNATTR_Sanitize_thread -> f22;
   FNATTR_Ssp -> f23;
   FNATTR_Sspreq -> f24;
   FNATTR_Sspstrong -> f25;
   FNATTR_Uwtable -> f26;
   FNATTR_String x -> f27 x;
   FNATTR_Key_value x -> f28 x;
   FNATTR_Attr_grp x -> f29 x}

fn_attr_rec :: (Prelude.Int -> a1) -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1
               -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 ->
               a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 ->
               (Prelude.String -> a1) -> (((,) Prelude.String Prelude.String)
               -> a1) -> (Prelude.Int -> a1) -> Coq_fn_attr -> a1
fn_attr_rec =
  fn_attr_rect

data Coq_raw_id =
   Name Prelude.String
 | Anon Prelude.Int

raw_id_rect :: (Prelude.String -> a1) -> (Prelude.Int -> a1) -> Coq_raw_id ->
               a1
raw_id_rect f f0 r =
  case r of {
   Name x -> f x;
   Anon x -> f0 x}

raw_id_rec :: (Prelude.String -> a1) -> (Prelude.Int -> a1) -> Coq_raw_id ->
              a1
raw_id_rec =
  raw_id_rect

data Coq_ident =
   ID_Global Coq_raw_id
 | ID_Local Coq_raw_id

ident_rect :: (Coq_raw_id -> a1) -> (Coq_raw_id -> a1) -> Coq_ident -> a1
ident_rect f f0 i =
  case i of {
   ID_Global x -> f x;
   ID_Local x -> f0 x}

ident_rec :: (Coq_raw_id -> a1) -> (Coq_raw_id -> a1) -> Coq_ident -> a1
ident_rec =
  ident_rect

type Coq_local_id = Coq_raw_id

type Coq_global_id = Coq_raw_id

type Coq_function_id = Coq_local_id

type Coq_block_id = Coq_local_id

data Coq_typ =
   TYPE_I Prelude.Int
 | TYPE_Pointer Coq_typ
 | TYPE_Void
 | TYPE_Half
 | TYPE_Float
 | TYPE_Double
 | TYPE_X86_fp80
 | TYPE_Fp128
 | TYPE_Ppc_fp128
 | TYPE_Label
 | TYPE_Metadata
 | TYPE_X86_mmx
 | TYPE_Array Prelude.Int Coq_typ
 | TYPE_Function Coq_typ ([] Coq_typ)
 | TYPE_Struct ([] Coq_typ)
 | TYPE_Packed_struct ([] Coq_typ)
 | TYPE_Opaque
 | TYPE_Vector Prelude.Int Coq_typ
 | TYPE_Identified Coq_ident

typ_rect :: (Prelude.Int -> a1) -> (Coq_typ -> a1 -> a1) -> a1 -> a1 -> a1 ->
            a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> (Prelude.Int -> Coq_typ
            -> a1 -> a1) -> (Coq_typ -> a1 -> ([] Coq_typ) -> a1) -> (([]
            Coq_typ) -> a1) -> (([] Coq_typ) -> a1) -> a1 -> (Prelude.Int ->
            Coq_typ -> a1 -> a1) -> (Coq_ident -> a1) -> Coq_typ -> a1
typ_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 t =
  case t of {
   TYPE_I sz -> f sz;
   TYPE_Pointer t0 ->
    f0 t0
      (typ_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 t0);
   TYPE_Void -> f1;
   TYPE_Half -> f2;
   TYPE_Float -> f3;
   TYPE_Double -> f4;
   TYPE_X86_fp80 -> f5;
   TYPE_Fp128 -> f6;
   TYPE_Ppc_fp128 -> f7;
   TYPE_Label -> f8;
   TYPE_Metadata -> f9;
   TYPE_X86_mmx -> f10;
   TYPE_Array sz t0 ->
    f11 sz t0
      (typ_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 t0);
   TYPE_Function ret args ->
    f12 ret
      (typ_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 ret) args;
   TYPE_Struct fields -> f13 fields;
   TYPE_Packed_struct fields -> f14 fields;
   TYPE_Opaque -> f15;
   TYPE_Vector sz t0 ->
    f16 sz t0
      (typ_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
        f17 t0);
   TYPE_Identified id -> f17 id}

typ_rec :: (Prelude.Int -> a1) -> (Coq_typ -> a1 -> a1) -> a1 -> a1 -> a1 ->
           a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> (Prelude.Int -> Coq_typ
           -> a1 -> a1) -> (Coq_typ -> a1 -> ([] Coq_typ) -> a1) -> (([]
           Coq_typ) -> a1) -> (([] Coq_typ) -> a1) -> a1 -> (Prelude.Int ->
           Coq_typ -> a1 -> a1) -> (Coq_ident -> a1) -> Coq_typ -> a1
typ_rec =
  typ_rect

data Coq_icmp =
   Eq
 | Ne
 | Ugt
 | Uge
 | Ult
 | Ule
 | Sgt
 | Sge
 | Slt
 | Sle

icmp_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 ->
             Coq_icmp -> a1
icmp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 i =
  case i of {
   Eq -> f;
   Ne -> f0;
   Ugt -> f1;
   Uge -> f2;
   Ult -> f3;
   Ule -> f4;
   Sgt -> f5;
   Sge -> f6;
   Slt -> f7;
   Sle -> f8}

icmp_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 ->
            Coq_icmp -> a1
icmp_rec =
  icmp_rect

data Coq_fcmp =
   FFalse
 | FOeq
 | FOgt
 | FOge
 | FOlt
 | FOle
 | FOne
 | FOrd
 | FUno
 | FUeq
 | FUgt
 | FUge
 | FUlt
 | FUle
 | FUne
 | FTrue

fcmp_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1
             -> a1 -> a1 -> a1 -> a1 -> a1 -> Coq_fcmp -> a1
fcmp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 =
  case f15 of {
   FFalse -> f;
   FOeq -> f0;
   FOgt -> f1;
   FOge -> f2;
   FOlt -> f3;
   FOle -> f4;
   FOne -> f5;
   FOrd -> f6;
   FUno -> f7;
   FUeq -> f8;
   FUgt -> f9;
   FUge -> f10;
   FUlt -> f11;
   FUle -> f12;
   FUne -> f13;
   FTrue -> f14}

fcmp_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 ->
            a1 -> a1 -> a1 -> a1 -> a1 -> Coq_fcmp -> a1
fcmp_rec =
  fcmp_rect

data Coq_ibinop =
   Add Prelude.Bool Prelude.Bool
 | Sub Prelude.Bool Prelude.Bool
 | Mul Prelude.Bool Prelude.Bool
 | Shl Prelude.Bool Prelude.Bool
 | UDiv Prelude.Bool
 | SDiv Prelude.Bool
 | LShr Prelude.Bool
 | AShr Prelude.Bool
 | URem
 | SRem
 | And
 | Or
 | Xor

ibinop_rect :: (Prelude.Bool -> Prelude.Bool -> a1) -> (Prelude.Bool ->
               Prelude.Bool -> a1) -> (Prelude.Bool -> Prelude.Bool -> a1) ->
               (Prelude.Bool -> Prelude.Bool -> a1) -> (Prelude.Bool -> a1)
               -> (Prelude.Bool -> a1) -> (Prelude.Bool -> a1) ->
               (Prelude.Bool -> a1) -> a1 -> a1 -> a1 -> a1 -> a1 ->
               Coq_ibinop -> a1
ibinop_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 i =
  case i of {
   Add x x0 -> f x x0;
   Sub x x0 -> f0 x x0;
   Mul x x0 -> f1 x x0;
   Shl x x0 -> f2 x x0;
   UDiv x -> f3 x;
   SDiv x -> f4 x;
   LShr x -> f5 x;
   AShr x -> f6 x;
   URem -> f7;
   SRem -> f8;
   And -> f9;
   Or -> f10;
   Xor -> f11}

ibinop_rec :: (Prelude.Bool -> Prelude.Bool -> a1) -> (Prelude.Bool ->
              Prelude.Bool -> a1) -> (Prelude.Bool -> Prelude.Bool -> a1) ->
              (Prelude.Bool -> Prelude.Bool -> a1) -> (Prelude.Bool -> a1) ->
              (Prelude.Bool -> a1) -> (Prelude.Bool -> a1) -> (Prelude.Bool
              -> a1) -> a1 -> a1 -> a1 -> a1 -> a1 -> Coq_ibinop -> a1
ibinop_rec =
  ibinop_rect

data Coq_fbinop =
   FAdd
 | FSub
 | FMul
 | FDiv
 | FRem

fbinop_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> Coq_fbinop -> a1
fbinop_rect f f0 f1 f2 f3 f4 =
  case f4 of {
   FAdd -> f;
   FSub -> f0;
   FMul -> f1;
   FDiv -> f2;
   FRem -> f3}

fbinop_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> Coq_fbinop -> a1
fbinop_rec =
  fbinop_rect

data Coq_fast_math =
   Nnan
 | Ninf
 | Nsz
 | Arcp
 | Fast

fast_math_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> Coq_fast_math -> a1
fast_math_rect f f0 f1 f2 f3 f4 =
  case f4 of {
   Nnan -> f;
   Ninf -> f0;
   Nsz -> f1;
   Arcp -> f2;
   Fast -> f3}

fast_math_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> Coq_fast_math -> a1
fast_math_rec =
  fast_math_rect

data Coq_conversion_type =
   Trunc
 | Zext
 | Sext
 | Fptrunc
 | Fpext
 | Uitofp
 | Sitofp
 | Fptoui
 | Fptosi
 | Inttoptr
 | Ptrtoint
 | Bitcast

conversion_type_rect :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 ->
                        a1 -> a1 -> a1 -> Coq_conversion_type -> a1
conversion_type_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 c =
  case c of {
   Trunc -> f;
   Zext -> f0;
   Sext -> f1;
   Fptrunc -> f2;
   Fpext -> f3;
   Uitofp -> f4;
   Sitofp -> f5;
   Fptoui -> f6;
   Fptosi -> f7;
   Inttoptr -> f8;
   Ptrtoint -> f9;
   Bitcast -> f10}

conversion_type_rec :: a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 -> a1 ->
                       a1 -> a1 -> a1 -> Coq_conversion_type -> a1
conversion_type_rec =
  conversion_type_rect

type Coq_tident = (,) Coq_typ Coq_ident

data Expr a =
   VALUE_Ident Coq_ident
 | VALUE_Integer Prelude.Int
 | VALUE_Float Prelude.Float
 | VALUE_Bool Prelude.Bool
 | VALUE_Null
 | VALUE_Zero_initializer
 | VALUE_Cstring Prelude.String
 | VALUE_None
 | VALUE_Undef
 | VALUE_Struct ([] ((,) Coq_typ a))
 | VALUE_Packed_struct ([] ((,) Coq_typ a))
 | VALUE_Array ([] ((,) Coq_typ a))
 | VALUE_Vector ([] ((,) Coq_typ a))
 | OP_IBinop Coq_ibinop Coq_typ a a
 | OP_ICmp Coq_icmp Coq_typ a a
 | OP_FBinop Coq_fbinop ([] Coq_fast_math) Coq_typ a a
 | OP_FCmp Coq_fcmp Coq_typ a a
 | OP_Conversion Coq_conversion_type Coq_typ a Coq_typ
 | OP_GetElementPtr Coq_typ ((,) Coq_typ a) ([] ((,) Coq_typ a))
 | OP_ExtractElement ((,) Coq_typ a) ((,) Coq_typ a)
 | OP_InsertElement ((,) Coq_typ a) ((,) Coq_typ a) ((,) Coq_typ a)
 | OP_ShuffleVector ((,) Coq_typ a) ((,) Coq_typ a) ((,) Coq_typ a)
 | OP_ExtractValue ((,) Coq_typ a) ([] Prelude.Int)
 | OP_InsertValue ((,) Coq_typ a) ((,) Coq_typ a) ([] Prelude.Int)
 | OP_Select ((,) Coq_typ a) ((,) Coq_typ a) ((,) Coq_typ a)

coq_Expr_rect :: (Coq_ident -> a2) -> (Prelude.Int -> a2) -> (Prelude.Float
                 -> a2) -> (Prelude.Bool -> a2) -> a2 -> a2 ->
                 (Prelude.String -> a2) -> a2 -> a2 -> (([] ((,) Coq_typ a1))
                 -> a2) -> (([] ((,) Coq_typ a1)) -> a2) -> (([]
                 ((,) Coq_typ a1)) -> a2) -> (([] ((,) Coq_typ a1)) -> a2) ->
                 (Coq_ibinop -> Coq_typ -> a1 -> a1 -> a2) -> (Coq_icmp ->
                 Coq_typ -> a1 -> a1 -> a2) -> (Coq_fbinop -> ([]
                 Coq_fast_math) -> Coq_typ -> a1 -> a1 -> a2) -> (Coq_fcmp ->
                 Coq_typ -> a1 -> a1 -> a2) -> (Coq_conversion_type ->
                 Coq_typ -> a1 -> Coq_typ -> a2) -> (Coq_typ -> ((,) 
                 Coq_typ a1) -> ([] ((,) Coq_typ a1)) -> a2) -> (((,) 
                 Coq_typ a1) -> ((,) Coq_typ a1) -> a2) -> (((,) Coq_typ 
                 a1) -> ((,) Coq_typ a1) -> ((,) Coq_typ a1) -> a2) -> (((,)
                 Coq_typ a1) -> ((,) Coq_typ a1) -> ((,) Coq_typ a1) -> a2)
                 -> (((,) Coq_typ a1) -> ([] Prelude.Int) -> a2) -> (((,)
                 Coq_typ a1) -> ((,) Coq_typ a1) -> ([] Prelude.Int) -> a2)
                 -> (((,) Coq_typ a1) -> ((,) Coq_typ a1) -> ((,) Coq_typ 
                 a1) -> a2) -> (Expr a1) -> a2
coq_Expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 e =
  case e of {
   VALUE_Ident x -> f x;
   VALUE_Integer x -> f0 x;
   VALUE_Float x -> f1 x;
   VALUE_Bool x -> f2 x;
   VALUE_Null -> f3;
   VALUE_Zero_initializer -> f4;
   VALUE_Cstring x -> f5 x;
   VALUE_None -> f6;
   VALUE_Undef -> f7;
   VALUE_Struct x -> f8 x;
   VALUE_Packed_struct x -> f9 x;
   VALUE_Array x -> f10 x;
   VALUE_Vector x -> f11 x;
   OP_IBinop x x0 x1 x2 -> f12 x x0 x1 x2;
   OP_ICmp x x0 x1 x2 -> f13 x x0 x1 x2;
   OP_FBinop x x0 x1 x2 x3 -> f14 x x0 x1 x2 x3;
   OP_FCmp x x0 x1 x2 -> f15 x x0 x1 x2;
   OP_Conversion x x0 x1 x2 -> f16 x x0 x1 x2;
   OP_GetElementPtr x x0 x1 -> f17 x x0 x1;
   OP_ExtractElement x x0 -> f18 x x0;
   OP_InsertElement x x0 x1 -> f19 x x0 x1;
   OP_ShuffleVector x x0 x1 -> f20 x x0 x1;
   OP_ExtractValue x x0 -> f21 x x0;
   OP_InsertValue x x0 x1 -> f22 x x0 x1;
   OP_Select x x0 x1 -> f23 x x0 x1}

coq_Expr_rec :: (Coq_ident -> a2) -> (Prelude.Int -> a2) -> (Prelude.Float ->
                a2) -> (Prelude.Bool -> a2) -> a2 -> a2 -> (Prelude.String ->
                a2) -> a2 -> a2 -> (([] ((,) Coq_typ a1)) -> a2) -> (([]
                ((,) Coq_typ a1)) -> a2) -> (([] ((,) Coq_typ a1)) -> a2) ->
                (([] ((,) Coq_typ a1)) -> a2) -> (Coq_ibinop -> Coq_typ -> a1
                -> a1 -> a2) -> (Coq_icmp -> Coq_typ -> a1 -> a1 -> a2) ->
                (Coq_fbinop -> ([] Coq_fast_math) -> Coq_typ -> a1 -> a1 ->
                a2) -> (Coq_fcmp -> Coq_typ -> a1 -> a1 -> a2) ->
                (Coq_conversion_type -> Coq_typ -> a1 -> Coq_typ -> a2) ->
                (Coq_typ -> ((,) Coq_typ a1) -> ([] ((,) Coq_typ a1)) -> a2)
                -> (((,) Coq_typ a1) -> ((,) Coq_typ a1) -> a2) -> (((,)
                Coq_typ a1) -> ((,) Coq_typ a1) -> ((,) Coq_typ a1) -> a2) ->
                (((,) Coq_typ a1) -> ((,) Coq_typ a1) -> ((,) Coq_typ 
                a1) -> a2) -> (((,) Coq_typ a1) -> ([] Prelude.Int) -> a2) ->
                (((,) Coq_typ a1) -> ((,) Coq_typ a1) -> ([] Prelude.Int) ->
                a2) -> (((,) Coq_typ a1) -> ((,) Coq_typ a1) -> ((,) 
                Coq_typ a1) -> a2) -> (Expr a1) -> a2
coq_Expr_rec =
  coq_Expr_rect

data Coq_value =
   SV (Expr Coq_value)

value_rect :: ((Expr Coq_value) -> a1) -> Coq_value -> a1
value_rect f v =
  case v of {
   SV x -> f x}

value_rec :: ((Expr Coq_value) -> a1) -> Coq_value -> a1
value_rec =
  value_rect

type Coq_tvalue = (,) Coq_typ Coq_value

data Coq_instr_id =
   IId Coq_raw_id
 | IVoid Prelude.Int

instr_id_rect :: (Coq_raw_id -> a1) -> (Prelude.Int -> a1) -> Coq_instr_id ->
                 a1
instr_id_rect f f0 i =
  case i of {
   IId x -> f x;
   IVoid x -> f0 x}

instr_id_rec :: (Coq_raw_id -> a1) -> (Prelude.Int -> a1) -> Coq_instr_id ->
                a1
instr_id_rec =
  instr_id_rect

data Coq_instr =
   INSTR_Op Coq_value
 | INSTR_Call Coq_tident ([] Coq_tvalue)
 | INSTR_Phi Coq_typ ([] ((,) Coq_ident Coq_value))
 | INSTR_Alloca Coq_typ (Prelude.Maybe Coq_tvalue) (Prelude.Maybe
                                                   Prelude.Int)
 | INSTR_Load Prelude.Bool Coq_typ Coq_tvalue (Prelude.Maybe Prelude.Int)
 | INSTR_Store Prelude.Bool Coq_tvalue Coq_tvalue (Prelude.Maybe Prelude.Int)
 | INSTR_Fence
 | INSTR_AtomicCmpXchg
 | INSTR_AtomicRMW
 | INSTR_Unreachable
 | INSTR_VAArg
 | INSTR_LandingPad

instr_rect :: (Coq_value -> a1) -> (Coq_tident -> ([] Coq_tvalue) -> a1) ->
              (Coq_typ -> ([] ((,) Coq_ident Coq_value)) -> a1) -> (Coq_typ
              -> (Prelude.Maybe Coq_tvalue) -> (Prelude.Maybe Prelude.Int) ->
              a1) -> (Prelude.Bool -> Coq_typ -> Coq_tvalue -> (Prelude.Maybe
              Prelude.Int) -> a1) -> (Prelude.Bool -> Coq_tvalue ->
              Coq_tvalue -> (Prelude.Maybe Prelude.Int) -> a1) -> a1 -> a1 ->
              a1 -> a1 -> a1 -> a1 -> Coq_instr -> a1
instr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 i =
  case i of {
   INSTR_Op x -> f x;
   INSTR_Call x x0 -> f0 x x0;
   INSTR_Phi x x0 -> f1 x x0;
   INSTR_Alloca x x0 x1 -> f2 x x0 x1;
   INSTR_Load x x0 x1 x2 -> f3 x x0 x1 x2;
   INSTR_Store x x0 x1 x2 -> f4 x x0 x1 x2;
   INSTR_Fence -> f5;
   INSTR_AtomicCmpXchg -> f6;
   INSTR_AtomicRMW -> f7;
   INSTR_Unreachable -> f8;
   INSTR_VAArg -> f9;
   INSTR_LandingPad -> f10}

instr_rec :: (Coq_value -> a1) -> (Coq_tident -> ([] Coq_tvalue) -> a1) ->
             (Coq_typ -> ([] ((,) Coq_ident Coq_value)) -> a1) -> (Coq_typ ->
             (Prelude.Maybe Coq_tvalue) -> (Prelude.Maybe Prelude.Int) -> a1)
             -> (Prelude.Bool -> Coq_typ -> Coq_tvalue -> (Prelude.Maybe
             Prelude.Int) -> a1) -> (Prelude.Bool -> Coq_tvalue -> Coq_tvalue
             -> (Prelude.Maybe Prelude.Int) -> a1) -> a1 -> a1 -> a1 -> a1 ->
             a1 -> a1 -> Coq_instr -> a1
instr_rec =
  instr_rect

data Coq_terminator =
   TERM_Ret Coq_tvalue
 | TERM_Ret_void
 | TERM_Br Coq_tvalue Coq_tident Coq_tident
 | TERM_Br_1 Coq_tident
 | TERM_Switch Coq_tvalue Coq_tident ([] ((,) Coq_tvalue Coq_tident))
 | TERM_IndirectBr Coq_tvalue ([] Coq_tident)
 | TERM_Resume Coq_tvalue
 | TERM_Invoke Coq_tident ([] Coq_tvalue) Coq_tident Coq_tident

terminator_rect :: (Coq_tvalue -> a1) -> a1 -> (Coq_tvalue -> Coq_tident ->
                   Coq_tident -> a1) -> (Coq_tident -> a1) -> (Coq_tvalue ->
                   Coq_tident -> ([] ((,) Coq_tvalue Coq_tident)) -> a1) ->
                   (Coq_tvalue -> ([] Coq_tident) -> a1) -> (Coq_tvalue ->
                   a1) -> (Coq_tident -> ([] Coq_tvalue) -> Coq_tident ->
                   Coq_tident -> a1) -> Coq_terminator -> a1
terminator_rect f f0 f1 f2 f3 f4 f5 f6 t =
  case t of {
   TERM_Ret x -> f x;
   TERM_Ret_void -> f0;
   TERM_Br x x0 x1 -> f1 x x0 x1;
   TERM_Br_1 x -> f2 x;
   TERM_Switch x x0 x1 -> f3 x x0 x1;
   TERM_IndirectBr x x0 -> f4 x x0;
   TERM_Resume x -> f5 x;
   TERM_Invoke x x0 x1 x2 -> f6 x x0 x1 x2}

terminator_rec :: (Coq_tvalue -> a1) -> a1 -> (Coq_tvalue -> Coq_tident ->
                  Coq_tident -> a1) -> (Coq_tident -> a1) -> (Coq_tvalue ->
                  Coq_tident -> ([] ((,) Coq_tvalue Coq_tident)) -> a1) ->
                  (Coq_tvalue -> ([] Coq_tident) -> a1) -> (Coq_tvalue -> a1)
                  -> (Coq_tident -> ([] Coq_tvalue) -> Coq_tident ->
                  Coq_tident -> a1) -> Coq_terminator -> a1
terminator_rec =
  terminator_rect

data Coq_thread_local_storage =
   TLS_Localdynamic
 | TLS_Initialexec
 | TLS_Localexec

thread_local_storage_rect :: a1 -> a1 -> a1 -> Coq_thread_local_storage -> a1
thread_local_storage_rect f f0 f1 t =
  case t of {
   TLS_Localdynamic -> f;
   TLS_Initialexec -> f0;
   TLS_Localexec -> f1}

thread_local_storage_rec :: a1 -> a1 -> a1 -> Coq_thread_local_storage -> a1
thread_local_storage_rec =
  thread_local_storage_rect

data Coq_global =
   Coq_mk_global Coq_global_id Coq_typ Prelude.Bool (Prelude.Maybe Coq_value) 
 (Prelude.Maybe Coq_linkage) (Prelude.Maybe Coq_visibility) (Prelude.Maybe
                                                            Coq_dll_storage) 
 (Prelude.Maybe Coq_thread_local_storage) Prelude.Bool (Prelude.Maybe
                                                       Prelude.Int) Prelude.Bool 
 (Prelude.Maybe Prelude.String) (Prelude.Maybe Prelude.Int)

g_ident :: Coq_global -> Coq_global_id
g_ident g =
  case g of {
   Coq_mk_global g_ident0 _ _ _ _ _ _ _ _ _ _ _ _ -> g_ident0}

g_typ :: Coq_global -> Coq_typ
g_typ g =
  case g of {
   Coq_mk_global _ g_typ0 _ _ _ _ _ _ _ _ _ _ _ -> g_typ0}

g_constant :: Coq_global -> Prelude.Bool
g_constant g =
  case g of {
   Coq_mk_global _ _ g_constant0 _ _ _ _ _ _ _ _ _ _ -> g_constant0}

g_value :: Coq_global -> Prelude.Maybe Coq_value
g_value g =
  case g of {
   Coq_mk_global _ _ _ g_value0 _ _ _ _ _ _ _ _ _ -> g_value0}

g_linkage :: Coq_global -> Prelude.Maybe Coq_linkage
g_linkage g =
  case g of {
   Coq_mk_global _ _ _ _ g_linkage0 _ _ _ _ _ _ _ _ -> g_linkage0}

g_visibility :: Coq_global -> Prelude.Maybe Coq_visibility
g_visibility g =
  case g of {
   Coq_mk_global _ _ _ _ _ g_visibility0 _ _ _ _ _ _ _ -> g_visibility0}

g_dll_storage :: Coq_global -> Prelude.Maybe Coq_dll_storage
g_dll_storage g =
  case g of {
   Coq_mk_global _ _ _ _ _ _ g_dll_storage0 _ _ _ _ _ _ -> g_dll_storage0}

g_thread_local :: Coq_global -> Prelude.Maybe Coq_thread_local_storage
g_thread_local g =
  case g of {
   Coq_mk_global _ _ _ _ _ _ _ g_thread_local0 _ _ _ _ _ -> g_thread_local0}

g_unnamed_addr :: Coq_global -> Prelude.Bool
g_unnamed_addr g =
  case g of {
   Coq_mk_global _ _ _ _ _ _ _ _ g_unnamed_addr0 _ _ _ _ -> g_unnamed_addr0}

g_addrspace :: Coq_global -> Prelude.Maybe Prelude.Int
g_addrspace g =
  case g of {
   Coq_mk_global _ _ _ _ _ _ _ _ _ g_addrspace0 _ _ _ -> g_addrspace0}

g_externally_initialized :: Coq_global -> Prelude.Bool
g_externally_initialized g =
  case g of {
   Coq_mk_global _ _ _ _ _ _ _ _ _ _ g_externally_initialized0 _ _ ->
    g_externally_initialized0}

g_section :: Coq_global -> Prelude.Maybe Prelude.String
g_section g =
  case g of {
   Coq_mk_global _ _ _ _ _ _ _ _ _ _ _ g_section0 _ -> g_section0}

g_align :: Coq_global -> Prelude.Maybe Prelude.Int
g_align g =
  case g of {
   Coq_mk_global _ _ _ _ _ _ _ _ _ _ _ _ g_align0 -> g_align0}

data Coq_declaration =
   Coq_mk_declaration Coq_function_id Coq_typ ((,) ([] Coq_param_attr)
                                              ([] ([] Coq_param_attr))) 
 (Prelude.Maybe Coq_linkage) (Prelude.Maybe Coq_visibility) (Prelude.Maybe
                                                            Coq_dll_storage) 
 (Prelude.Maybe Coq_cconv) ([] Coq_fn_attr) (Prelude.Maybe Prelude.String) 
 (Prelude.Maybe Prelude.Int) (Prelude.Maybe Prelude.String)

dc_name :: Coq_declaration -> Coq_function_id
dc_name d =
  case d of {
   Coq_mk_declaration dc_name0 _ _ _ _ _ _ _ _ _ _ -> dc_name0}

dc_type :: Coq_declaration -> Coq_typ
dc_type d =
  case d of {
   Coq_mk_declaration _ dc_type0 _ _ _ _ _ _ _ _ _ -> dc_type0}

dc_param_attrs :: Coq_declaration -> (,) ([] Coq_param_attr)
                  ([] ([] Coq_param_attr))
dc_param_attrs d =
  case d of {
   Coq_mk_declaration _ _ dc_param_attrs0 _ _ _ _ _ _ _ _ -> dc_param_attrs0}

dc_linkage :: Coq_declaration -> Prelude.Maybe Coq_linkage
dc_linkage d =
  case d of {
   Coq_mk_declaration _ _ _ dc_linkage0 _ _ _ _ _ _ _ -> dc_linkage0}

dc_visibility :: Coq_declaration -> Prelude.Maybe Coq_visibility
dc_visibility d =
  case d of {
   Coq_mk_declaration _ _ _ _ dc_visibility0 _ _ _ _ _ _ -> dc_visibility0}

dc_dll_storage :: Coq_declaration -> Prelude.Maybe Coq_dll_storage
dc_dll_storage d =
  case d of {
   Coq_mk_declaration _ _ _ _ _ dc_dll_storage0 _ _ _ _ _ -> dc_dll_storage0}

dc_cconv :: Coq_declaration -> Prelude.Maybe Coq_cconv
dc_cconv d =
  case d of {
   Coq_mk_declaration _ _ _ _ _ _ dc_cconv0 _ _ _ _ -> dc_cconv0}

dc_attrs :: Coq_declaration -> [] Coq_fn_attr
dc_attrs d =
  case d of {
   Coq_mk_declaration _ _ _ _ _ _ _ dc_attrs0 _ _ _ -> dc_attrs0}

dc_section :: Coq_declaration -> Prelude.Maybe Prelude.String
dc_section d =
  case d of {
   Coq_mk_declaration _ _ _ _ _ _ _ _ dc_section0 _ _ -> dc_section0}

dc_align :: Coq_declaration -> Prelude.Maybe Prelude.Int
dc_align d =
  case d of {
   Coq_mk_declaration _ _ _ _ _ _ _ _ _ dc_align0 _ -> dc_align0}

dc_gc :: Coq_declaration -> Prelude.Maybe Prelude.String
dc_gc d =
  case d of {
   Coq_mk_declaration _ _ _ _ _ _ _ _ _ _ dc_gc0 -> dc_gc0}

data Coq_type_decl =
   Coq_mk_type_decl Coq_local_id Coq_typ

tdc_name :: Coq_type_decl -> Coq_local_id
tdc_name t =
  case t of {
   Coq_mk_type_decl tdc_name0 _ -> tdc_name0}

tdc_type :: Coq_type_decl -> Coq_typ
tdc_type t =
  case t of {
   Coq_mk_type_decl _ tdc_type0 -> tdc_type0}

data Coq_block =
   Coq_mk_block Coq_block_id ([] ((,) Coq_instr_id Coq_instr)) Coq_terminator 
 Coq_instr_id

blk_id :: Coq_block -> Coq_block_id
blk_id b =
  case b of {
   Coq_mk_block blk_id0 _ _ _ -> blk_id0}

blk_instrs :: Coq_block -> [] ((,) Coq_instr_id Coq_instr)
blk_instrs b =
  case b of {
   Coq_mk_block _ blk_instrs0 _ _ -> blk_instrs0}

blk_term :: Coq_block -> Coq_terminator
blk_term b =
  case b of {
   Coq_mk_block _ _ blk_term0 _ -> blk_term0}

blk_term_id :: Coq_block -> Coq_instr_id
blk_term_id b =
  case b of {
   Coq_mk_block _ _ _ blk_term_id0 -> blk_term_id0}

data Coq_definition =
   Coq_mk_definition Coq_declaration ([] Coq_local_id) ([] Coq_block)

df_prototype :: Coq_definition -> Coq_declaration
df_prototype d =
  case d of {
   Coq_mk_definition df_prototype0 _ _ -> df_prototype0}

df_args :: Coq_definition -> [] Coq_local_id
df_args d =
  case d of {
   Coq_mk_definition _ df_args0 _ -> df_args0}

df_instrs :: Coq_definition -> [] Coq_block
df_instrs d =
  case d of {
   Coq_mk_definition _ _ df_instrs0 -> df_instrs0}

data Coq_metadata =
   METADATA_Const Coq_tvalue
 | METADATA_Null
 | METADATA_Id Coq_raw_id
 | METADATA_String Prelude.String
 | METADATA_Named ([] Prelude.String)
 | METADATA_Node ([] Coq_metadata)

metadata_rect :: (Coq_tvalue -> a1) -> a1 -> (Coq_raw_id -> a1) ->
                 (Prelude.String -> a1) -> (([] Prelude.String) -> a1) ->
                 (([] Coq_metadata) -> a1) -> Coq_metadata -> a1
metadata_rect f f0 f1 f2 f3 f4 m =
  case m of {
   METADATA_Const x -> f x;
   METADATA_Null -> f0;
   METADATA_Id x -> f1 x;
   METADATA_String x -> f2 x;
   METADATA_Named x -> f3 x;
   METADATA_Node x -> f4 x}

metadata_rec :: (Coq_tvalue -> a1) -> a1 -> (Coq_raw_id -> a1) ->
                (Prelude.String -> a1) -> (([] Prelude.String) -> a1) -> (([]
                Coq_metadata) -> a1) -> Coq_metadata -> a1
metadata_rec =
  metadata_rect

data Coq_toplevel_entity =
   TLE_Target Prelude.String
 | TLE_Datalayout Prelude.String
 | TLE_Declaration Coq_declaration
 | TLE_Definition Coq_definition
 | TLE_Type_decl Coq_ident Coq_typ
 | TLE_Source_filename Prelude.String
 | TLE_Global Coq_global
 | TLE_Metadata Coq_raw_id Coq_metadata
 | TLE_Attribute_group Prelude.Int ([] Coq_fn_attr)

toplevel_entity_rect :: (Prelude.String -> a1) -> (Prelude.String -> a1) ->
                        (Coq_declaration -> a1) -> (Coq_definition -> a1) ->
                        (Coq_ident -> Coq_typ -> a1) -> (Prelude.String ->
                        a1) -> (Coq_global -> a1) -> (Coq_raw_id ->
                        Coq_metadata -> a1) -> (Prelude.Int -> ([]
                        Coq_fn_attr) -> a1) -> Coq_toplevel_entity -> a1
toplevel_entity_rect f f0 f1 f2 f3 f4 f5 f6 f7 t =
  case t of {
   TLE_Target x -> f x;
   TLE_Datalayout x -> f0 x;
   TLE_Declaration x -> f1 x;
   TLE_Definition x -> f2 x;
   TLE_Type_decl x x0 -> f3 x x0;
   TLE_Source_filename x -> f4 x;
   TLE_Global x -> f5 x;
   TLE_Metadata x x0 -> f6 x x0;
   TLE_Attribute_group x x0 -> f7 x x0}

toplevel_entity_rec :: (Prelude.String -> a1) -> (Prelude.String -> a1) ->
                       (Coq_declaration -> a1) -> (Coq_definition -> a1) ->
                       (Coq_ident -> Coq_typ -> a1) -> (Prelude.String -> a1)
                       -> (Coq_global -> a1) -> (Coq_raw_id -> Coq_metadata
                       -> a1) -> (Prelude.Int -> ([] Coq_fn_attr) -> a1) ->
                       Coq_toplevel_entity -> a1
toplevel_entity_rec =
  toplevel_entity_rect

data Coq_modul =
   Coq_mk_modul Prelude.String Coq_toplevel_entity Coq_toplevel_entity 
 ([] ((,) Prelude.String Coq_global)) ([] ((,) Prelude.String Coq_type_decl)) 
 ([] ((,) Prelude.String Coq_declaration)) ([]
                                           ((,) Prelude.String
                                           Coq_definition))

m_name :: Coq_modul -> Prelude.String
m_name m =
  case m of {
   Coq_mk_modul m_name0 _ _ _ _ _ _ -> m_name0}

m_target :: Coq_modul -> Coq_toplevel_entity
m_target m =
  case m of {
   Coq_mk_modul _ m_target0 _ _ _ _ _ -> m_target0}

m_datalayout :: Coq_modul -> Coq_toplevel_entity
m_datalayout m =
  case m of {
   Coq_mk_modul _ _ m_datalayout0 _ _ _ _ -> m_datalayout0}

m_globals :: Coq_modul -> [] ((,) Prelude.String Coq_global)
m_globals m =
  case m of {
   Coq_mk_modul _ _ _ m_globals0 _ _ _ -> m_globals0}

m_type_decls :: Coq_modul -> [] ((,) Prelude.String Coq_type_decl)
m_type_decls m =
  case m of {
   Coq_mk_modul _ _ _ _ m_type_decls0 _ _ -> m_type_decls0}

m_declarations :: Coq_modul -> [] ((,) Prelude.String Coq_declaration)
m_declarations m =
  case m of {
   Coq_mk_modul _ _ _ _ _ m_declarations0 _ -> m_declarations0}

m_definitions :: Coq_modul -> [] ((,) Prelude.String Coq_definition)
m_definitions m =
  case m of {
   Coq_mk_modul _ _ _ _ _ _ m_definitions0 -> m_definitions0}

type Coq_toplevel_entities = [] Coq_toplevel_entity

