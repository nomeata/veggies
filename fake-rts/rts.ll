target triple = "x86_64-pc-linux-gnu"

; Declare the string constant as a global constant.
@.str = private unnamed_addr constant [13 x i8] c"hello world\0A\00"

; External declaration of the puts function
declare i32 @puts(i8* nocapture) nounwind
declare extern_weak i64 @ZCMain_main()

; Definition of main function
define i64 @main() {   ; i32()*
  ; Convert [13 x i8]* to i8  *...
  %cast210 = getelementptr [13 x i8], [13 x i8]* @.str, i64 0, i64 0

  ; Call puts function to write out the string to stdout.
  call i32 @puts(i8* %cast210)
  %ret = call i64 @ZCMain_main()
  ret i64 %ret
}

; Named metadata
!0 = !{i32 42, null, !"string"}
!foo = !{!0}
