module Ast2Assembly where

import LLVM.AST
import LLVM.Module (withModuleFromAST, moduleLLVMAssembly )
import LLVM.Context (withContext)
import Control.Monad.Trans.Except

ast2Assembly :: Module -> IO String
ast2Assembly m =
    (either error id) <$>
    withContext (\c ->
        runExceptT (withModuleFromAST c m ( moduleLLVMAssembly )))

ast2AssemblyFile :: Module -> FilePath -> IO ()
ast2AssemblyFile mod path = ast2Assembly mod >>= writeFile path
