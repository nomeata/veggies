import LLVM.Module
import LLVM.Context
import Text.Groom
import Control.Monad.Trans.Except

main = do
    assembly <- getContents
    withContext $ \c ->
        fmap (either error id) $
        runExceptT $ do
            ast <- withModuleFromLLVMAssembly c assembly $ \mod -> do
                ast <- moduleAST mod
                putStrLn $ groom ast
                return ast

            withModuleFromAST c ast $ \assembly2 ->
                moduleLLVMAssembly assembly2 >>= putStrLn
            return ()
