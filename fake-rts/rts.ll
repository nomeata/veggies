target triple = "x86_64-pc-linux-gnu"

%hs = type { %hs* (%hs*)* }
%dc = type { %hs* (%hs*)*, i64, [0 x %hs*]}

; Declare the string constant as a global constant.
@.str1 = private unnamed_addr constant [13 x i8] c"hello world\0A\00"
@.str2 = private unnamed_addr constant [14 x i8] c"haskell done\0A\00"
@.str3 = private unnamed_addr constant [13 x i8] c"eval result\0A\00"
@.str4 = private unnamed_addr constant [15 x i8] c"evaled result\0A\00"
@.str5 = private unnamed_addr constant [10 x i8] c"all done\0A\00"

@state_token_str = private unnamed_addr constant [21 x i8] c"entered state token\0A\00"

; External declaration of the puts function
declare i32 @puts(i8* nocapture) nounwind
declare extern_weak %hs* @ZCMain_main_fun([0 x %hs*]* %clos, %hs* %eta_B1)

@state_token = private constant %hs { %hs*(%hs*)* @state_token_fun }
define private %hs* @state_token_fun(%hs* %clos) {
  %cast1 = getelementptr [21 x i8], [21 x i8]* @state_token_str, i64 0, i64 0
  call i32 @puts(i8* %cast1)
  ret %hs* null
}


; Definition of main function
define i64 @main() {   ; i32()*
  ; Convert [13 x i8]* to i8  *...
  %cast1 = getelementptr [13 x i8], [13 x i8]* @.str1, i64 0, i64 0

  ; Call puts function to write out the string to stdout.
  call i32 @puts(i8* %cast1)

  %ret = call %hs* @ZCMain_main_fun([0 x %hs*]* null, %hs* @state_token)

  %cast2 = getelementptr [14 x i8], [14 x i8]* @.str2, i64 0, i64 0
  call i32 @puts(i8* %cast2)

  %retCast = bitcast %hs* %ret to %dc*
  %payloadPtr = getelementptr %dc, %dc* %retCast, i32 0, i32 2, i32 1
  %payload = load %hs*, %hs** %payloadPtr

  %enterPtr = getelementptr %hs, %hs* %payload, i32 0, i32 0
  %enter = load %hs* (%hs*)*, %hs* (%hs*)** %enterPtr

  %cast3 = getelementptr [13 x i8], [13 x i8]* @.str3, i64 0, i64 0
  call i32 @puts(i8* %cast3)

  %evaledPayload = call %hs* %enter(%hs* %payload)

  %cast4 = getelementptr [15 x i8], [15 x i8]* @.str4, i64 0, i64 0
  call i32 @puts(i8* %cast4)

  %payloadDc = bitcast %hs* %evaledPayload to %dc*
  %tagPtr = getelementptr %dc, %dc* %payloadDc, i32 0, i32 1
  %tag = load i64, i64* %tagPtr

  %cast5 = getelementptr [10 x i8], [10 x i8]* @.str5, i64 0, i64 0
  call i32 @puts(i8* %cast5)

  ret i64 %tag
}

; some embedded things

@GHCziPrim_coercionTokenzh = constant %hs { %hs* (%hs*)* @rts_returnArg }

define %hs* @rts_returnArg(%hs* %clos) {
  ret %hs* %clos
}

