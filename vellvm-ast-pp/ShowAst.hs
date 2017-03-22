import LLVM.Module
import LLVM.Context
import Text.Groom
import Control.Monad.Trans.Except

main = do
    assembly <- getContents
    withContext $ \c -> do
        runExceptT $ withModuleFromLLVMAssembly c assembly $ \mod -> do
            ast <- moduleAST mod
            putStrLn $ groom ast
            return ()
