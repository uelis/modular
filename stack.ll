; ModuleID = 'src/stack.c'
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct._IO_FILE = type { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, %struct._IO_marker*, %struct._IO_FILE*, i32, i32, i64, i16, i8, [1 x i8], i8*, i64, i8*, i8*, i8*, i8*, i64, i32, [20 x i8] }
%struct._IO_marker = type { %struct._IO_marker*, %struct._IO_FILE*, i32 }

@stack_top = global i32 1048575, align 4
@stderr = external global %struct._IO_FILE*
@.str = private unnamed_addr constant [16 x i8] c"stack overflow\0A\00", align 1
@stack = common global [1048576 x i8] zeroinitializer, align 16
@.str1 = private unnamed_addr constant [22 x i8] c"stack_top < 1024*1024\00", align 1
@.str2 = private unnamed_addr constant [12 x i8] c"src/stack.c\00", align 1
@__PRETTY_FUNCTION__.stack_pop = private unnamed_addr constant [24 x i8] c"void *stack_pop(size_t)\00", align 1

; Function Attrs: nounwind uwtable
define void @raise_stack_overflow() #0 {
  %1 = load %struct._IO_FILE** @stderr, align 8
  %2 = call i32 (%struct._IO_FILE*, i8*, ...)* @fprintf(%struct._IO_FILE* %1, i8* getelementptr inbounds ([16 x i8]* @.str, i32 0, i32 0))
  call void @exit(i32 -1) #4
  unreachable
                                                  ; No predecessors!
  ret void
}

declare i32 @fprintf(%struct._IO_FILE*, i8*, ...) #1

; Function Attrs: noreturn nounwind
declare void @exit(i32) #2

; Function Attrs: alwaysinline nounwind uwtable
define i8* @stack_alloc(i64 %size) #3 {
  %1 = alloca i64, align 8
  store i64 %size, i64* %1, align 8
  %2 = load i64* %1, align 8
  %3 = load i32* @stack_top, align 4
  %4 = sext i32 %3 to i64
  %5 = sub i64 %4, %2
  %6 = trunc i64 %5 to i32
  store i32 %6, i32* @stack_top, align 4
  %7 = load i32* @stack_top, align 4
  %8 = icmp slt i32 %7, 0
  br i1 %8, label %9, label %10

; <label>:9                                       ; preds = %0
  call void @raise_stack_overflow()
  br label %10

; <label>:10                                      ; preds = %9, %0
  %11 = load i32* @stack_top, align 4
  %12 = sext i32 %11 to i64
  %13 = getelementptr inbounds [1048576 x i8]* @stack, i32 0, i64 %12
  ret i8* %13
}

; Function Attrs: alwaysinline nounwind uwtable
define i8* @stack_pop(i64 %size) #3 {
  %1 = alloca i64, align 8
  %data = alloca i8*, align 8
  store i64 %size, i64* %1, align 8
  %2 = load i32* @stack_top, align 4
  %3 = sext i32 %2 to i64
  %4 = getelementptr inbounds [1048576 x i8]* @stack, i32 0, i64 %3
  store i8* %4, i8** %data, align 8
  %5 = load i64* %1, align 8
  %6 = load i32* @stack_top, align 4
  %7 = sext i32 %6 to i64
  %8 = add i64 %7, %5
  %9 = trunc i64 %8 to i32
  store i32 %9, i32* @stack_top, align 4
  %10 = load i32* @stack_top, align 4
  %11 = icmp slt i32 %10, 1048576
  br i1 %11, label %12, label %13

; <label>:12                                      ; preds = %0
  br label %15

; <label>:13                                      ; preds = %0
  call void @__assert_fail(i8* getelementptr inbounds ([22 x i8]* @.str1, i32 0, i32 0), i8* getelementptr inbounds ([12 x i8]* @.str2, i32 0, i32 0), i32 47, i8* getelementptr inbounds ([24 x i8]* @__PRETTY_FUNCTION__.stack_pop, i32 0, i32 0)) #4
  unreachable
                                                  ; No predecessors!
  br label %15

; <label>:15                                      ; preds = %14, %12
  %16 = load i8** %data, align 8
  ret i8* %16
}

; Function Attrs: noreturn nounwind
declare void @__assert_fail(i8*, i8*, i32, i8*) #2

attributes #0 = { nounwind uwtable "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { noreturn nounwind "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { alwaysinline nounwind uwtable "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { noreturn nounwind }

!llvm.ident = !{!0}

!0 = !{!"Ubuntu clang version 3.6.2-1 (tags/RELEASE_362/final) (based on LLVM 3.6.2)"}
