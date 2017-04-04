{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Ast2Ast (convModule) where

import Data.Char
import Data.Maybe
import Data.List

import qualified Ollvm_ast as O
import Ollvm_ast

import qualified LLVM.AST as A
import qualified LLVM.AST.IntegerPredicate as A
import LLVM.AST
import LLVM.AST.DataLayout
import LLVM.AST.Linkage
import LLVM.AST.Global
import LLVM.AST.Visibility
import LLVM.AST.ParameterAttribute
import LLVM.AST.Type
import LLVM.AST.AddrSpace
import LLVM.AST.Constant
import qualified LLVM.AST.Constant as AC
import qualified  LLVM.AST.CallingConvention as CC

convModule :: Coq_modul -> Module
convModule = conv

class Conv a b | a -> b where
    conv :: a -> b

instance Conv Coq_modul Module where
  conv m =
    Module { moduleName = m_name m
           , moduleSourceFileName = m_name m
           , moduleDataLayout = getDataLayout (m_datalayout m)
           , moduleTargetTriple = getTargetTriple (m_target m)
           , moduleDefinitions =
                sortOn defName $
                map (conv . snd) (m_globals m) ++
                map (conv . snd) (m_type_decls m) ++
                map (conv . snd) (m_declarations m) ++
                map (conv . snd) (m_definitions m) ++
                map (conv . snd) (m_aliases m)
           }

defName :: Definition -> Maybe Name
defName (GlobalDefinition g) = Just $ name g
defName (TypeDefinition n _) = Nothing -- need to go first
defName _ = Nothing

instance Conv Coq_param_attr ParameterAttribute

defAddrSpace = AddrSpace 0

instance Conv Coq_typ Type where
    conv (TYPE_I b)                      = IntegerType (fromIntegral b)
    conv (TYPE_Pointer t)                = PointerType (conv t) defAddrSpace
    conv TYPE_Void                       = VoidType
    conv TYPE_Half                       = half
    conv TYPE_Float                      = float
    conv TYPE_Double                     = double
    conv TYPE_X86_fp80                   = x86_fp80
    conv TYPE_Fp128                      = fp128
    conv TYPE_Ppc_fp128                  = ppc_fp128
    conv TYPE_Label                      = error "TYPE_Label"
    conv TYPE_Metadata                   = MetadataType
    conv TYPE_X86_mmx                    = error "TYPE_X86_mmx"
    conv (TYPE_Array n t)                = ArrayType (fromIntegral n) (conv t)
    conv (TYPE_Function r args)          = FunctionType (conv r) (map conv args) False
    conv (TYPE_Struct ts)                = StructureType False (map conv ts)
    conv (TYPE_Packed_struct ts)         = StructureType True (map conv ts)
    conv TYPE_Opaque                     = error "TYPE_Opaque"
    conv (TYPE_Vector n t)               = VectorType (fromIntegral n) (conv t)
    conv (TYPE_Identified (ID_Global n)) = NamedTypeReference (conv n)
    conv (TYPE_Identified (ID_Local n))  = NamedTypeReference (conv n)

instance Conv Coq_block_id Name where
    conv (O.Name n) = A.Name n
    conv (Anon n) = UnName (fromIntegral n)

instance Conv f t => Conv (Coq_instr_id, f) (Named t) where
    conv (IId n,t) = conv n := conv t
    conv (IVoid _,t) = Do (conv t)

instance Conv Coq_value (Type -> Constant) where
    conv (SV (VALUE_Ident (ID_Global n))) t = GlobalReference t (conv n)
    conv (SV (VALUE_Integer i))           t = AC.Int b (fromIntegral i)
        where IntegerType b = t
    conv (SV (VALUE_Float f))             t = error "VALUE_Float"
    conv (SV (VALUE_Bool b))              t = AC.Int 1 (if b then 1 else 0)
    conv (SV VALUE_Null)                  t = Null t
    conv (SV (VALUE_Struct elems))        _ = AC.Struct Nothing False elems'
        where elems' = [ conv e (conv t) | (t,e) <- elems ]
    conv (SV (VALUE_Array elems))         (ArrayType _ t)
                                          = AC.Array t elems'
        where elems' = [ conv e (conv t) | (t,e) <- elems ]
    conv (SV (OP_Conversion O.Bitcast ty1 o ty2)) _
        = AC.BitCast (conv o (conv ty1)) (conv ty2)
    conv (SV (VALUE_Cstring str))         _ = AC.Array (IntegerType 8) elems
        where elems = [ (AC.Int 8 (fromIntegral (ord c))) | c <- str ]

instance Conv (Expr Coq_value) (Type -> Operand) where
    conv (VALUE_Ident (ID_Local  n)) t = LocalReference t (conv n)
    conv v                           t = ConstantOperand (conv (SV v) t)


instance Conv Coq_tvalue Operand where
    conv (t,SV v) = conv v (conv t)
instance Conv Coq_tident Operand where
    conv (t,ID_Local n) = LocalReference (conv t) (conv n)
    conv (t,ID_Global n) = ConstantOperand (GlobalReference (conv t) (conv n))

instance Conv Coq_ibinop (Operand -> Operand -> Instruction) where
    conv (O.Add nsw usw) = \o1 o2 -> A.Add nsw usw o1 o2 []
    conv (O.Sub nsw usw) = \o1 o2 -> A.Sub nsw usw o1 o2 []
    conv (O.Mul nsw usw) = \o1 o2 -> A.Mul nsw usw o1 o2 []

instance Conv Coq_icmp A.IntegerPredicate where
    conv O.Eq = A.EQ
    conv O.Ne = A.NE
    conv O.Sle = A.SLE
    conv O.Slt = A.SLT
    conv O.Sgt = A.SGT
    conv O.Sge = A.SGE
    conv O.Ule = A.ULE
    conv O.Ult = A.ULT
    conv O.Ugt = A.UGT
    conv O.Uge = A.UGE

instance Conv Coq_instr Instruction where
    conv (INSTR_Op (SV (OP_IBinop op  t a1 a2)))
        = (conv op) (conv (t,a1)) (conv (t,a2))
    conv (INSTR_Op (SV (OP_ICmp   cmp t a1 a2)))
        = A.ICmp (conv cmp) (conv (t,a1)) (conv (t,a2)) []
    conv (INSTR_Op (SV (OP_GetElementPtr _ to path)))
        = A.GetElementPtr False (conv to) (map conv path) []
    conv (INSTR_Op (SV (OP_Conversion O.Bitcast ty1 o ty2)))
        = A.BitCast (conv (ty1, o)) (conv ty2) []
    conv (INSTR_Op (SV (OP_Conversion O.Ptrtoint ty1 o ty2)))
        = A.PtrToInt (conv (ty1, o)) (conv ty2) []
    conv (INSTR_Op (SV (OP_Conversion O.Zext ty1 o ty2)))
        = A.ZExt (conv (ty1, o)) (conv ty2) []
    conv (INSTR_Store volatile o1 o2 mbAlign)
        = A.Store volatile (conv o1) (conv o2) Nothing (maybe 0 fromIntegral mbAlign) []
    conv (INSTR_Load volatile _ o mbAlign)
        = A.Load volatile (conv o) Nothing (maybe 0 fromIntegral mbAlign) []
    conv (INSTR_Call (t,f) tos)
        = A.Call Nothing CC.C [] (Right (conv (TYPE_Pointer t,f))) [ (conv to, []) | to <- tos ] [] []
    conv (INSTR_Phi t preds )
        = A.Phi (conv t) [ (conv (t,o), conv l)
                         | (o,SV (VALUE_Ident (ID_Local l))) <- preds ] []
    {-
    conv (INSTR_Call Coq_tident ([] Coq_tvalue)
    conv (INSTR_Phi Coq_typ ([] ((,) Coq_ident Coq_value))
    conv (INSTR_Alloca Coq_typ (Prelude.Maybe Coq_tvalue) (Prelude.Maybe Prelude.Int)
    conv (INSTR_Load Prelude.Bool Coq_typ Coq_tvalue (Prelude.Maybe Prelude.Int)
    conv (INSTR_Store Prelude.Bool Coq_tvalue Coq_tvalue (Prelude.Maybe Prelude.Int)
    conv (INSTR_Fence
    conv (INSTR_AtomicCmpXchg
    conv (INSTR_AtomicRMW
    conv (INSTR_Unreachable
    conv (INSTR_VAArg
    conv (INSTR_LandingPad
    -}

instance Conv Coq_terminator Terminator where
    conv (TERM_Br_1 (TYPE_Label, ID_Local nt)) = Br (conv nt) []
    conv (TERM_Br (to, SV o) (TYPE_Label, ID_Local nt) (TYPE_Label, ID_Local ne)) = CondBr (conv o (conv to)) (conv nt) (conv ne) []
    conv (TERM_Ret (t, SV o)) = Ret (Just (conv o (conv t))) []
    conv (TERM_Switch o (TYPE_Label, ID_Local d) brs) =
        Switch (conv o) (conv d) [ (conv v (conv t), conv l) | ((t,v),(TYPE_Label, ID_Local l)) <- brs ] []

instance Conv Coq_block  BasicBlock  where
    conv (Coq_mk_block id instrs term term_id) =
        BasicBlock (conv id) (map conv instrs) (conv (term_id, term))

instance Conv Coq_linkage Linkage where
    conv LINKAGE_External = External
    conv LINKAGE_Private  = Private
    conv LINKAGE_Internal = Internal

instance Conv Coq_global Definition where
    conv (Coq_mk_global
        g_ident        -- global_id;
        g_typ          -- typ;
        g_constant     -- bool;
        g_value        -- option value;
        g_linkage      -- option linkage;
        g_visibility   -- option visibility;
        g_dll_storage  -- option dll_storage;
        g_thread_local -- option thread_local_storage;
        g_unnamed_addr -- bool;
        g_addrspace    -- option int;
        g_externally_initialized-- bool;
        g_section      -- option string;
        g_align        -- option int;
        ) = GlobalDefinition $ GlobalVariable
            (conv g_ident)
            (maybe External conv g_linkage)
            Default -- Visibility
            Nothing -- (Maybe StorageClass)
            Nothing -- (Maybe Model)
            defAddrSpace
            Nothing -- (Maybe UnnamedAddr)
            g_constant
            (conv g_typ)
            (fmap (\val -> conv val (conv g_typ)) g_value)
            g_section
            Nothing -- (Maybe String) comdat
            (maybe 0 fromIntegral g_align)

instance Conv Coq_alias Definition where
    conv (Coq_mk_alias
        a_ident        -- global_id;
        a_typ          -- typ;
        a_value        -- value;
        a_linkage      -- option linkage;
        a_visibility   -- option visibility;
        a_dll_storage  -- option dll_storage;
        a_thread_local -- option thread_local_storage;
        a_unnamed_addr -- bool;
        ) = GlobalDefinition $ GlobalAlias
            (conv a_ident)
            (maybe External conv a_linkage)
            Default -- Visibility
            Nothing -- (Maybe StorageClass)
            Nothing -- (Maybe Model)
            Nothing -- (Maybe UnnamedAddr)
            (conv (TYPE_Pointer a_typ))
            (conv a_value (conv (TYPE_Pointer a_typ)))




instance Conv Coq_type_decl   Definition where
    conv (Coq_mk_type_decl name TYPE_Opaque)
        = TypeDefinition (conv name) Nothing
    conv (Coq_mk_type_decl name typ)
        = TypeDefinition (conv name) (Just (conv typ))

instance Conv Coq_declaration Definition where
    conv (Coq_mk_declaration
        dc_name --  function_id;
        (TYPE_Function dc_ret_ty dc_args_ty) --  typ; (* INVARIANT--  should be TYPE_Function (ret_t * args_t) *)
        (dc_ret_attrs, dc_args_attrs) --  list param_attr * list (list param_attr); (* ret_attrs * args_attrs *)
        dc_linkage     --  option linkage;
        dc_visibility  --  option visibility;
        dc_dll_storage --  option dll_storage;
        dc_cconv       --  option cconv;
        dc_attrs       --  list fn_attr;
        dc_section     --  option string;
        dc_align       --  option int;
        dc_gc          --  option string;
        ) = GlobalDefinition $ Function
                (maybe External conv dc_linkage)
                Default -- Visibility
                Nothing -- (Maybe StorageClass)
                CC.C -- CallingConvention
                (map conv dc_ret_attrs) -- [ParameterAttribute]
                (conv dc_ret_ty) -- Type
                (conv dc_name) -- Name
                ([ Parameter (conv t) (UnName 0) (map conv pas)
                 | (t,pas) <- zip2Safe dc_args_ty dc_args_attrs
                 ]
                , False) -- ([Parameter], Bool), snd indicates varargs
                [] -- [Either GroupID FunctionAttribute]
                Nothing -- (Maybe String)
                Nothing -- (Maybe String)
                0 -- Word32
                Nothing -- (Maybe String)
                Nothing -- (Maybe Constant)
                [] -- no blocks
                Nothing -- (Maybe Constant)


instance Conv Coq_definition  Definition where
    conv (Coq_mk_definition
        (Coq_mk_declaration
            dc_name --  function_id;
            (TYPE_Function dc_ret_ty dc_args_ty) --  typ; (* INVARIANT--  should be TYPE_Function (ret_t * args_t) *)
            (dc_ret_attrs, dc_args_attrs) --  list param_attr * list (list param_attr); (* ret_attrs * args_attrs *)
            dc_linkage     --  option linkage;
            dc_visibility  --  option visibility;
            dc_dll_storage --  option dll_storage;
            dc_cconv       --  option cconv;
            dc_attrs       --  list fn_attr;
            dc_section     --  option string;
            dc_align       --  option int;
            dc_gc          --  option string;
        ) args blocks
        ) =
        GlobalDefinition $
        Function
            (maybe External conv dc_linkage)
            Default -- Visibility
            Nothing -- (Maybe StorageClass)
            CC.C -- CallingConvention
            (map conv dc_ret_attrs) -- [ParameterAttribute]
            (conv dc_ret_ty) -- Type
            (conv dc_name) -- Name
            ([ Parameter (conv t) (conv a) (map conv pas)
             | (t, a,pas) <- zip3Safe dc_args_ty args dc_args_attrs
             ]
            , False) -- ([Parameter], Bool), snd indicates varargs
            [] -- [Either GroupID FunctionAttribute]
            Nothing -- (Maybe String)
            Nothing -- (Maybe String)
            0 -- Word32
            Nothing -- (Maybe String)
            Nothing -- (Maybe Constant)
            (map conv blocks) -- [BasicBlock]
            Nothing -- (Maybe Constant)

getTargetTriple :: Coq_toplevel_entity -> Maybe String
getTargetTriple (TLE_Target target) = Just target
getTargetTriple _                   = Nothing

getDataLayout :: Coq_toplevel_entity -> Maybe DataLayout
getDataLayout (TLE_Datalayout datalayout) = Just (parseDataLayout datalayout)
getDataLayout _                           = Nothing

parseDataLayout = error "no datalayout parser yet" 

zip3Safe [] [] [] = []
zip3Safe (x:xs) (y:ys) (z:zs) = (x,y,z) : zip3Safe xs ys zs

zip2Safe [] [] = []
zip2Safe (x:xs) (y:ys) = (x,y) : zip2Safe xs ys
zip2Safe _ _  = error "zip3Safe"
