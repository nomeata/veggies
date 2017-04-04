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

@GHCziPrim_coercionTokenzh = constant %hs { %hs* (%hs*)* @rts_returnArg }

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



declare i8* @malloc(i64)

%fun_clos2 = type { %hs* (%hs*)*, %hs* ([0 x %hs*]*, %hs*, %hs*)*, i64, [0 x %hs*] }
%int = type { %hs* (%hs*)*, i64 }

@GHCziPrim_zpzh_tmp = private constant %fun_clos2 { %hs* (%hs*)* @rts_returnArg, %hs* ([0 x %hs*]*, %hs*, %hs*)* @GHCziPrim_zpzh_fun, i64 2, [0 x %hs*] zeroinitializer }
@GHCziPrim_zpzh = alias %hs, bitcast (%fun_clos2* @GHCziPrim_zpzh_tmp to %hs*)
@GHCziPrim_plusWordzh = alias %hs, %hs* @GHCziPrim_zpzh
define %hs* @GHCziPrim_zpzh_fun([0 x %hs*]* %clos, %hs* %a, %hs* %b) {
  %a_cast = bitcast %hs* %a to %int*
  %b_cast = bitcast %hs* %b to %int*
  %a_ptr = getelementptr %int, %int* %a_cast, i32 0, i32 1
  %b_ptr = getelementptr %int, %int* %b_cast, i32 0, i32 1
  %a_val = load i64, i64* %a_ptr
  %b_val = load i64, i64* %b_ptr
  %c_val = add i64 %a_val, %b_val
  %c_raw = call i8* @malloc(i64 ptrtoint (%int* getelementptr (%int, %int* null, i32 1) to i64))
  %c_ret = bitcast i8* %c_raw to %hs*
  %c_cast = bitcast %hs* %c_ret to %int*
  %returnPtr = getelementptr %int, %int* %c_cast, i32 0, i32 0
  store %hs* (%hs*)* @rts_returnArg, %hs* (%hs*)** %returnPtr
  %valPtr = getelementptr %int, %int* %c_cast, i32 0, i32 1
  store i64 %c_val, i64* %valPtr
  ret %hs* %c_ret
}


@GHCziPrim_zmzh_tmp = private constant %fun_clos2 { %hs* (%hs*)* @rts_returnArg, %hs* ([0 x %hs*]*, %hs*, %hs*)* @GHCziPrim_zmzh_fun, i64 2, [0 x %hs*] zeroinitializer }
@GHCziPrim_zmzh = alias %hs, bitcast (%fun_clos2* @GHCziPrim_zmzh_tmp to %hs*)
@GHCziPrim_minusWordzh = alias %hs, %hs* @GHCziPrim_zmzh
define %hs* @GHCziPrim_zmzh_fun([0 x %hs*]* %clos, %hs* %a, %hs* %b) {
  %a_cast = bitcast %hs* %a to %int*
  %b_cast = bitcast %hs* %b to %int*
  %a_ptr = getelementptr %int, %int* %a_cast, i32 0, i32 1
  %b_ptr = getelementptr %int, %int* %b_cast, i32 0, i32 1
  %a_val = load i64, i64* %a_ptr
  %b_val = load i64, i64* %b_ptr
  %c_val = sub i64 %a_val, %b_val
  %c_raw = call i8* @malloc(i64 ptrtoint (%int* getelementptr (%int, %int* null, i32 1) to i64))
  %c_ret = bitcast i8* %c_raw to %hs*
  %c_cast = bitcast %hs* %c_ret to %int*
  %returnPtr = getelementptr %int, %int* %c_cast, i32 0, i32 0
  store %hs* (%hs*)* @rts_returnArg, %hs* (%hs*)** %returnPtr
  %valPtr = getelementptr %int, %int* %c_cast, i32 0, i32 1
  store i64 %c_val, i64* %valPtr
  ret %hs* %c_ret
}


@GHCziPrim_ztzh_tmp = private constant %fun_clos2 { %hs* (%hs*)* @rts_returnArg, %hs* ([0 x %hs*]*, %hs*, %hs*)* @GHCziPrim_ztzh_fun, i64 2, [0 x %hs*] zeroinitializer }
@GHCziPrim_ztzh = alias %hs, bitcast (%fun_clos2* @GHCziPrim_ztzh_tmp to %hs*)
@GHCziPrim_timesWordzh = alias %hs, %hs* @GHCziPrim_ztzh
define %hs* @GHCziPrim_ztzh_fun([0 x %hs*]* %clos, %hs* %a, %hs* %b) {
  %a_cast = bitcast %hs* %a to %int*
  %b_cast = bitcast %hs* %b to %int*
  %a_ptr = getelementptr %int, %int* %a_cast, i32 0, i32 1
  %b_ptr = getelementptr %int, %int* %b_cast, i32 0, i32 1
  %a_val = load i64, i64* %a_ptr
  %b_val = load i64, i64* %b_ptr
  %c_val = mul i64 %a_val, %b_val
  %c_raw = call i8* @malloc(i64 ptrtoint (%int* getelementptr (%int, %int* null, i32 1) to i64))
  %c_ret = bitcast i8* %c_raw to %hs*
  %c_cast = bitcast %hs* %c_ret to %int*
  %returnPtr = getelementptr %int, %int* %c_cast, i32 0, i32 0
  store %hs* (%hs*)* @rts_returnArg, %hs* (%hs*)** %returnPtr
  %valPtr = getelementptr %int, %int* %c_cast, i32 0, i32 1
  store i64 %c_val, i64* %valPtr
  ret %hs* %c_ret
}



