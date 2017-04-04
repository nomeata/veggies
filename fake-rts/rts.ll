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


declare extern_weak %hs* @ZCMain_main_fun([0 x %hs*]* %clos, %hs* %eta_B1)

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

; Definition of main function
@GHCziPrim_realWorldzh = external constant %hs
define i64 @main() {   ; i32()*
  %ret = call %hs* @ZCMain_main_fun([0 x %hs*]* null, %hs* @GHCziPrim_realWorldzh)
  ret i64 0
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
