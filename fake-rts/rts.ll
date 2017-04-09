target triple = "x86_64-pc-linux-gnu"

%hs = type { %hs* (%hs*)* }
%ind = type { %hs* (%hs*)*, %hs* }
%dc = type { %hs* (%hs*)*, i64, [0 x %hs*]}
%printAndExitClosure = type { %hs* (%hs*)*, i8* }

; Declare the string constant as a global constant.
@.str1 = private unnamed_addr constant [13 x i8] c"hello world\0A\00"
@.str2 = private unnamed_addr constant [14 x i8] c"haskell done\0A\00"
@.str3 = private unnamed_addr constant [13 x i8] c"eval result\0A\00"
@.str4 = private unnamed_addr constant [15 x i8] c"evaled result\0A\00"
@.str5 = private unnamed_addr constant [10 x i8] c"all done\0A\00"


; External declaration of the puts function
declare void @puts(i8* nocapture) nounwind
declare void @exit(i64) nounwind



@bad_arity_str = private unnamed_addr constant [11 x i8] c"bad arity\0A\00"
define %hs* @rts_badArity() {
  %cast1 = getelementptr [11 x i8], [11 x i8]* @bad_arity_str, i64 0, i64 0
  call void @puts(i8* %cast1)
  call void @exit(i64 1)
  unreachable
}

define %hs* @rts_printAndExit(%hs* %clos) {
  %cast = bitcast %hs* %clos to %printAndExitClosure*
  %strP = getelementptr %printAndExitClosure, %printAndExitClosure* %cast, i32 0, i32 1
  %str = load i8*, i8** %strP
  call void @puts(i8* %str)
  call void @exit(i64 1)
  unreachable
}

; stubs
@defaultRtsConfig = constant i8* null
@ZCMain_main_closure = constant i8* null

; The real entry point
@ZCMain_main = external constant %hs

declare %hs* @rts_call(%hs*, i64, [0 x %hs*]*)

; Definition of main function
@GHCziPrim_realWorldzh = external constant %hs
define i64 @hs_main() {
  %enterPtr = getelementptr %hs, %hs* @ZCMain_main, i32 0, i32 0
  %enter = load %hs* (%hs*)*, %hs* (%hs*)** %enterPtr
  %evaledPayload = call %hs* %enter(%hs* @ZCMain_main)

  %args = alloca %hs*, i64 1
  %argsCasted = bitcast %hs** %args to [0 x %hs*]*
  %argPtr = getelementptr [0 x %hs*], [0 x %hs*]* %argsCasted, i32 0, i32 0
  store %hs* @GHCziPrim_realWorldzh, %hs** %argPtr
  call %hs* @rts_call(%hs* %evaledPayload, i64 1, [0 x %hs*]* %argsCasted)

  call void @exit(i64 0)
  unreachable
}

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
