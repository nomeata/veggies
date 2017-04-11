target triple = "x86_64-pc-linux-gnu"

%hs = type { %hs* (%hs*)* }
%ind = type { %hs* (%hs*)*, %hs* }
%printAndExitClosure = type { %hs* (%hs*)*, i8* }

; External declaration of the puts function
declare void @puts(i8* nocapture) nounwind
declare void @exit(i64) nounwind

define %hs* @rts_printAndExit(%hs* %clos) {
  %cast = bitcast %hs* %clos to %printAndExitClosure*
  %strP = getelementptr %printAndExitClosure, %printAndExitClosure* %cast, i32 0, i32 1
  %str = load i8*, i8** %strP
  call void @puts(i8* %str)
  call void @exit(i64 1)
  unreachable
}

; stubs, required by the GHC-generated main() function
@defaultRtsConfig = constant i8* null
@ZCMain_main_closure = constant i8* null

; some embedded things

define %hs* @rts_returnArg(%hs* %clos) {
  ret %hs* %clos
}

define %hs* @rts_indirection(%hs* %clos) {
  %cast = bitcast %hs* %clos to %ind*
  %indirecteeP = getelementptr %ind, %ind* %cast, i32 0, i32 1
  %indirectee = load %hs*, %hs** %indirecteeP

  %enterPtr = getelementptr %hs, %hs* %indirectee, i32 0, i32 0
  %enter = load %hs* (%hs*)*, %hs* (%hs*)** %enterPtr

  %ret = call %hs* %enter(%hs* %indirectee)
  ret %hs* %ret
}
