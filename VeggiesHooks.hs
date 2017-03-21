{-# LANGUAGE CPP, GADTs, ScopedTypeVariables, ImpredicativeTypes, OverloadedStrings, TupleSections, StandaloneDeriving #-}
module VeggiesHooks where

import           CorePrep             (corePrepPgm)
-- import           Gen2.GHC.CorePrep    (corePrepPgm) -- customized to not float new toplevel binds
import           CoreToStg            (coreToStg)
import           DriverPipeline
import           DriverPhases
import           DynFlags
import           GHC
import           GhcMonad
import           Hooks
import           Panic
import qualified SysTools
import           SimplStg             (stg2stg)
import           HeaderInfo
import           HscTypes
import           Maybes               (expectJust)

import           Control.Concurrent.MVar
import           Control.Monad

import qualified Data.ByteString.Char8 as B
import qualified Data.Map             as M

import           System.Directory     (copyFile, createDirectoryIfMissing)
import           System.FilePath

import           System.IO.Error

import qualified GHC.LanguageExtensions as Ext

import Debug.Trace

--------------------------------------------------
-- One shot replacement (the oneShot in DriverPipeline
-- always uses the unhooked linker)

oneShot :: HscEnv -> Phase -> [(String, Maybe Phase)] -> IO ()
oneShot hsc_env stop_phase srcs = do
  o_files <- mapM (compileFile hsc_env stop_phase) srcs
  {-
  Gen2.veggiesDoLink (hsc_dflags hsc_env) stop_phase o_files
  -}
  return ()

--------------------------------------------------
-- Driver hooks

installDriverHooks :: DynFlags -> DynFlags
installDriverHooks df = df { hooks = hooks' }
  where hooks' = (hooks df) { runPhaseHook     = Just runVeggiesPhase
                            -- , ghcPrimIfaceHook = Just Gen2.ghcjsPrimIface
                            }

haveCpp :: DynFlags -> Bool
haveCpp dflags = xopt Ext.Cpp dflags

runVeggiesPhase :: PhasePlus -> FilePath -> DynFlags
              -> CompPipeline (PhasePlus, FilePath)

runVeggiesPhase (HscOut src_flavour mod_name result) _ dflags = do

        location <- getLocation src_flavour mod_name
        setModLocation location

        let o_file = ml_obj_file location -- The real object file
            hsc_lang = hscTarget dflags
            next_phase = hscPostBackendPhase dflags src_flavour hsc_lang

        case result of
            HscNotGeneratingCode ->
                return (RealPhase next_phase,
                        panic "No output filename from Hsc when no-code")
            HscUpToDate ->
                do liftIO $ touchObjectFile dflags o_file
                   -- The .o file must have a later modification date
                   -- than the source file (else we wouldn't get Nothing)
                   -- but we touch it anyway, to keep 'make' happy (we think).
                   return (RealPhase StopLn, o_file)
            HscUpdateBoot ->
                do -- In the case of hs-boot files, generate a dummy .o-boot
                   -- stamp file for the benefit of Make
                   liftIO $ touchObjectFile dflags o_file
                   return (RealPhase next_phase, o_file)
#if __GLASGOW_HASKELL__ >= 709
            HscUpdateSig ->
                do -- We need to create a REAL but empty .o file
                   -- because we are going to attempt to put it in a library
                   PipeState{hsc_env=hsc_env'} <- getPipeState
                   let input_fn = expectJust "runPhase" (ml_hs_file location)
                       basename = dropExtension input_fn
                   -- fixme do we need to create a js_o file here?
                   -- liftIO $ compileEmptyStub dflags hsc_env' basename location
                   return (RealPhase next_phase, o_file)
#endif
            HscRecomp cgguts mod_summary
              -> do output_fn <- phaseOutputFilename next_phase

                    PipeState{hsc_env=hsc_env'} <- getPipeState

                    outputFilename <- liftIO $
                      veggiesWriteModule hsc_env' cgguts mod_summary output_fn

                    return (RealPhase next_phase, outputFilename)
-- skip these, but copy the result
runVeggiesPhase (RealPhase ph) input _dflags
  | Just next <- lookup ph skipPhases = do
    output <- phaseOutputFilename next
    liftIO $ (createDirectoryIfMissing True (takeDirectory output) >>
              copyFile input output)
                `catchIOError` \_ -> return ()
    return (RealPhase next, output)
  where
    skipPhases = []
    -- skipPhases = [ (CmmCpp, Cmm), (Cmm, As False), (Cmm, As True), (As False, StopLn), (As True, StopLn) ]

-- otherwise use default
runVeggiesPhase p input dflags = runPhase p input dflags

touchObjectFile :: DynFlags -> FilePath -> IO ()
touchObjectFile dflags path = do
  createDirectoryIfMissing True $ takeDirectory path
  SysTools.touch dflags "Touching object file" path

veggiesWriteModule :: HscEnv      -- ^ Environment in which to compile the module
                   -> CgGuts
                   -> ModSummary
                   -> FilePath    -- ^ Output path
                   -> IO FilePath
veggiesWriteModule env core mod output = do
    b <- veggiesCompileModule env core mod
    createDirectoryIfMissing True (takeDirectory output)
    B.writeFile output b
    return output

veggiesCompileModule :: HscEnv      -- ^ Environment in which to compile the module
                     -> CgGuts
                     -> ModSummary
                     -> IO B.ByteString
-- dynamic-too will invoke this twice, cache results in VeggiesEnv
veggiesCompileModule env core mod = compile
  where
    mod'  = ms_mod mod
    dflags = hsc_dflags env
    compile = do
      core_binds <- corePrepPgm env mod' (ms_location mod) (cg_binds core) (cg_tycons core)
      -- print "Got Core!"
      return (B.pack "; woohoo")
      {-
      stg <- coreToStg dflags mod' core_binds
      (stg', cCCs) <- stg2stg dflags mod' stg
      return $ variantRender gen2Variant settings dflags mod' stg' cCCs
      -}

