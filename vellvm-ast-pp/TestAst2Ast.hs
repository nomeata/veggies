import Ollvm_ast
import Ast2Ast
import Text.Groom
import Ast2Assembly

m1 = Coq_mk_modul
    "Test"
    (TLE_Target "x86_64-pc-linux")
    (TLE_Source_filename "no data layout here")
    [ ("foobar", test1)
    , ("foobar", test2)
    , ("foobar", test3)
    , ("foobar", test) ] -- globals
    -- %struct.Node = type { %struct.Node*, %struct.Node*, i64 }
    [("foobar", Coq_mk_type_decl
        (Name "struct.Node")
        (TYPE_Struct [ TYPE_Pointer nodeTy, TYPE_Pointer nodeTy, TYPE_I 64 ]))
    ]
    [] -- declarations
    [ ("foobar",sumTree)  -- definitions
    , ("foobar",main) ]
  where
    nodeTy :: Coq_typ
    nodeTy = TYPE_Identified (ID_Local (Name "struct.Node"))

    funTy :: Coq_typ
    funTy = TYPE_Function (TYPE_I 64) [TYPE_Pointer nodeTy]

    -- @test1 = global %struct.Node { %struct.Node* null, %struct.Node* null, i64 100 }
    test1 = Coq_mk_global
        (Name "test1")
        nodeTy
        True -- constant
        (Just (SV (VALUE_Struct
            [ (TYPE_Pointer nodeTy, SV VALUE_Null)
            , (TYPE_Pointer nodeTy, SV VALUE_Null)
            , (TYPE_I 64,           SV (VALUE_Integer 100))
            ])))
        Nothing Nothing Nothing Nothing False Nothing False Nothing Nothing
    -- @test2 = global %struct.Node { %struct.Node* @test1, %struct.Node* null, i64 10 }
    test2 = Coq_mk_global
        (Name "test2")
        nodeTy
        True -- constant
        (Just (SV (VALUE_Struct
            [ (TYPE_Pointer nodeTy, SV (VALUE_Ident (ID_Global (Name "test1"))))
            , (TYPE_Pointer nodeTy, SV VALUE_Null)
            , (TYPE_I 64,           SV (VALUE_Integer 10))
            ])))
        Nothing Nothing Nothing Nothing False Nothing False Nothing Nothing
    -- @test3 = global %struct.Node { %struct.Node* null, %struct.Node* null, i64 1 }
    test3 = Coq_mk_global
        (Name "test3")
        nodeTy
        True -- constant
        (Just (SV (VALUE_Struct
            [ (TYPE_Pointer nodeTy, SV VALUE_Null)
            , (TYPE_Pointer nodeTy, SV VALUE_Null)
            , (TYPE_I 64,           SV (VALUE_Integer 1))
            ])))
        Nothing Nothing Nothing Nothing False Nothing False Nothing Nothing
    -- @test = global %struct.Node { %struct.Node* @test2, %struct.Node* @test3, i64 5 }
    test = Coq_mk_global
        (Name "test")
        nodeTy
        True -- constant
        (Just (SV (VALUE_Struct
            [ (TYPE_Pointer nodeTy, SV (VALUE_Ident (ID_Global (Name "test2"))))
            , (TYPE_Pointer nodeTy, SV (VALUE_Ident (ID_Global (Name "test3"))))
            , (TYPE_I 64,           SV (VALUE_Integer 5))
            ])))
        Nothing Nothing Nothing Nothing False Nothing False Nothing Nothing


    main = Coq_mk_definition
        (Coq_mk_declaration
            (Name "main")
            (TYPE_Function (TYPE_I 64) [TYPE_I 64, TYPE_Pointer (TYPE_Pointer (TYPE_I 8))])
            ([],[[],[]])
            Nothing
            Nothing
            Nothing
            Nothing
            []
            Nothing
            Nothing
            Nothing)
        [ Name "argc", Name "argv" ]
        [ Coq_mk_block (Anon 0)
            [ (IId (Anon 1), INSTR_Call (TYPE_Pointer funTy, ID_Global (Name "sum_tree")) [(TYPE_Pointer nodeTy, SV (VALUE_Ident (ID_Global (Name "test"))))])
            ]
            -- br i1 %1, label %then, label %else
            (TERM_Ret (TYPE_I 64, SV (VALUE_Ident (ID_Local (Anon 1)))))
            (IVoid 1)
        ]

    sumTree = Coq_mk_definition
        (Coq_mk_declaration
            (Name "sum_tree")
            funTy
            ([],[[]])
            Nothing
            Nothing
            Nothing
            Nothing
            []
            Nothing
            Nothing
            Nothing)
        [ Name "t" ]
        [ Coq_mk_block (Anon 0)
            -- %1 = icmp eq %struct.Node* %t, null
            [ (IId (Anon 1), INSTR_Op (SV (OP_ICmp Eq (TYPE_Pointer nodeTy) (SV (VALUE_Ident (ID_Local (Name "t")))) (SV VALUE_Null))))
            ]
            -- br i1 %1, label %then, label %else
            (TERM_Br (TYPE_I 1,   SV (VALUE_Ident (ID_Local ((Anon 1)))))
                     (TYPE_Label, ID_Local (Name "then"))
                     (TYPE_Label, ID_Local (Name "else")))
            (IVoid 2)
        , Coq_mk_block (Name "then") []
            --  ret i64 0
            (TERM_Ret (TYPE_I 64, SV (VALUE_Integer 0)))
            (IVoid 3)
        , Coq_mk_block (Name "else")
            [
                --   %2 = getelementptr %struct.Node, %struct.Node* %t, i32 0, i32 2
              (IId (Anon 2), INSTR_Op (SV (OP_GetElementPtr nodeTy (TYPE_Pointer nodeTy, SV (VALUE_Ident (ID_Local (Name "t")))) [(TYPE_I 32, SV (VALUE_Integer 0)), (TYPE_I 32, SV (VALUE_Integer 2))])))
                --   %3 = load i64, i64* %2
            , (IId (Anon 3), INSTR_Load False (TYPE_I 64) (TYPE_Pointer (TYPE_I 64), SV (VALUE_Ident (ID_Local (Anon 2)))) Nothing)
                --   %4 = getelementptr %struct.Node, %struct.Node* %t, i32 0, i32 1
            , (IId (Anon 4), INSTR_Op (SV (OP_GetElementPtr nodeTy (TYPE_Pointer nodeTy, SV (VALUE_Ident (ID_Local (Name "t")))) [(TYPE_I 32, SV (VALUE_Integer 0)), (TYPE_I 32, SV (VALUE_Integer 1))])))
                --   %5 = load %struct.Node*, %struct.Node** %4
            , (IId (Anon 5), INSTR_Load False (TYPE_Pointer nodeTy) (TYPE_Pointer (TYPE_Pointer nodeTy), SV (VALUE_Ident (ID_Local (Anon 4)))) Nothing)
                --   %6 = call i64 @sum_tree(%struct.Node* %5)
            , (IId (Anon 6), INSTR_Call (TYPE_Pointer funTy, ID_Global (Name "sum_tree")) [(TYPE_Pointer nodeTy, SV (VALUE_Ident (ID_Local (Anon 5))))])
                --   %7 = add i64 %3, %6
            , (IId (Anon 7), INSTR_Op (SV (OP_IBinop (Add False False) (TYPE_I 64) (SV (VALUE_Ident (ID_Local (Anon 3)))) (SV (VALUE_Ident (ID_Local (Anon 6)))))))
                --   %8 = getelementptr %struct.Node, %struct.Node* %t, i32 0, i32 0
            , (IId (Anon 8), INSTR_Op (SV (OP_GetElementPtr nodeTy (TYPE_Pointer nodeTy, SV (VALUE_Ident (ID_Local (Name "t")))) [(TYPE_I 32, SV (VALUE_Integer 0)), (TYPE_I 32, SV (VALUE_Integer 0))])))
                --   %9 = load %struct.Node*, %struct.Node** %8
            , (IId (Anon 9), INSTR_Load False (TYPE_Pointer nodeTy) (TYPE_Pointer (TYPE_Pointer nodeTy), SV (VALUE_Ident (ID_Local (Anon 8)))) Nothing)
                --   %10 = call i64 @sum_tree(%struct.Node* %9)
            , (IId (Anon 10), INSTR_Call (TYPE_Pointer funTy, ID_Global (Name "sum_tree")) [(TYPE_Pointer nodeTy, SV (VALUE_Ident (ID_Local (Anon 9))))])
                --   %11 = add i64 %7, %10
            , (IId (Anon 11), INSTR_Op (SV (OP_IBinop (Add False False) (TYPE_I 64) (SV (VALUE_Ident (ID_Local (Anon 7)))) (SV (VALUE_Ident (ID_Local (Anon 10)))))))
            ]
            -- ret i64 %11
            (TERM_Ret (TYPE_I 64, SV (VALUE_Ident (ID_Local (Anon 11)))))
            (IVoid 4)
        ]


main = do
    -- putStrLn (groom (convModule m1))
    ast2Assembly (convModule m1) >>= putStr
