; ModuleID = 'src/gc.c'
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-redhat-linux-gnu"

%struct._IO_FILE = type { i32, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, i8*, %struct._IO_marker*, %struct._IO_FILE*, i32, i32, i64, i16, i8, [1 x i8], i8*, i64, i8*, i8*, i8*, i8*, i64, i32, [20 x i8] }
%struct._IO_marker = type { %struct._IO_marker*, %struct._IO_FILE*, i32 }
%struct.__va_list_tag = type { i32, i32, i8*, i8* }

@from_space_mem = internal global [10240 x i8] zeroinitializer, align 16
@from_space = global i8* getelementptr inbounds ([10240 x i8], [10240 x i8]* @from_space_mem, i32 0, i32 0), align 8
@to_space_mem = internal global [10240 x i8] zeroinitializer, align 16
@to_space = global i8* getelementptr inbounds ([10240 x i8], [10240 x i8]* @to_space_mem, i32 0, i32 0), align 8
@next_free = global i32 0, align 4
@stderr = external global %struct._IO_FILE*, align 8
@.str = private unnamed_addr constant [15 x i8] c"out of memory\0A\00", align 1
@.str.1 = private unnamed_addr constant [42 x i8] c"root != ((void*)0) && in_from_space(root)\00", align 1
@.str.2 = private unnamed_addr constant [9 x i8] c"src/gc.c\00", align 1
@__PRETTY_FUNCTION__.gc_collect = private unnamed_addr constant [38 x i8] c"void gc_collect(size_t, int64_t, ...)\00", align 1
@.str.3 = private unnamed_addr constant [22 x i8] c"in_from_space(record)\00", align 1
@__PRETTY_FUNCTION__.copy_record = private unnamed_addr constant [33 x i8] c"void copy_record(void *, void *)\00", align 1
@.str.4 = private unnamed_addr constant [18 x i8] c"in_to_space(next)\00", align 1

; Function Attrs: nounwind uwtable
define void @raise_out_of_memory() #0 {
  %1 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 8
  %2 = call i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %1, i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str, i32 0, i32 0))
  call void @exit(i32 -1) #6
  unreachable
                                                  ; No predecessors!
  ret void
}

declare i32 @fprintf(%struct._IO_FILE*, i8*, ...) #1

; Function Attrs: noreturn nounwind
declare void @exit(i32) #2

; Function Attrs: alwaysinline nounwind uwtable
define i8* @gc_alloc(i64 %size) #3 {
  %1 = alloca i64, align 8
  %chunk = alloca i8*, align 8
  store i64 %size, i64* %1, align 8
  %2 = load i8*, i8** @from_space, align 8
  %3 = load i32, i32* @next_free, align 4
  %4 = sext i32 %3 to i64
  %5 = getelementptr inbounds i8, i8* %2, i64 %4
  store i8* %5, i8** %chunk, align 8
  %6 = load i64, i64* %1, align 8
  %7 = load i32, i32* @next_free, align 4
  %8 = sext i32 %7 to i64
  %9 = add i64 %8, %6
  %10 = trunc i64 %9 to i32
  store i32 %10, i32* @next_free, align 4
  %11 = load i32, i32* @next_free, align 4
  %12 = icmp sge i32 %11, 10240
  br i1 %12, label %13, label %14

; <label>:13                                      ; preds = %0
  store i8* null, i8** %chunk, align 8
  br label %14

; <label>:14                                      ; preds = %13, %0
  %15 = load i8*, i8** %chunk, align 8
  ret i8* %15
}

; Function Attrs: nounwind uwtable
define void @gc_collect(i64 %bytes_needed, i64 %rootc, ...) #0 {
  %1 = alloca i64, align 8
  %2 = alloca i64, align 8
  %next = alloca i8*, align 8
  %roots = alloca [1 x %struct.__va_list_tag], align 16
  %i = alloca i32, align 4
  %root = alloca i8*, align 8
  %size = alloca i32, align 4
  %scan = alloca i8*, align 8
  %size1 = alloca i32, align 4
  %ptr_count = alloca i32, align 4
  %i2 = alloca i32, align 4
  %p = alloca i8*, align 8
  %p_size = alloca i32, align 4
  %tmp = alloca i8*, align 8
  store i64 %bytes_needed, i64* %1, align 8
  store i64 %rootc, i64* %2, align 8
  %3 = load i8*, i8** @to_space, align 8
  store i8* %3, i8** %next, align 8
  %4 = getelementptr inbounds [1 x %struct.__va_list_tag], [1 x %struct.__va_list_tag]* %roots, i32 0, i32 0
  %5 = bitcast %struct.__va_list_tag* %4 to i8*
  call void @llvm.va_start(i8* %5)
  store i32 0, i32* %i, align 4
  br label %6

; <label>:6                                       ; preds = %50, %0
  %7 = load i32, i32* %i, align 4
  %8 = sext i32 %7 to i64
  %9 = load i64, i64* %2, align 8
  %10 = icmp slt i64 %8, %9
  br i1 %10, label %11, label %53

; <label>:11                                      ; preds = %6
  %12 = getelementptr inbounds [1 x %struct.__va_list_tag], [1 x %struct.__va_list_tag]* %roots, i32 0, i32 0
  %13 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %12, i32 0, i32 0
  %14 = load i32, i32* %13
  %15 = icmp ule i32 %14, 40
  br i1 %15, label %16, label %22

; <label>:16                                      ; preds = %11
  %17 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %12, i32 0, i32 3
  %18 = load i8*, i8** %17
  %19 = getelementptr i8, i8* %18, i32 %14
  %20 = bitcast i8* %19 to i8**
  %21 = add i32 %14, 8
  store i32 %21, i32* %13
  br label %27

; <label>:22                                      ; preds = %11
  %23 = getelementptr inbounds %struct.__va_list_tag, %struct.__va_list_tag* %12, i32 0, i32 2
  %24 = load i8*, i8** %23
  %25 = bitcast i8* %24 to i8**
  %26 = getelementptr i8, i8* %24, i32 8
  store i8* %26, i8** %23
  br label %27

; <label>:27                                      ; preds = %22, %16
  %28 = phi i8** [ %20, %16 ], [ %25, %22 ]
  %29 = load i8*, i8** %28
  store i8* %29, i8** %root, align 8
  %30 = load i8*, i8** %root, align 8
  %31 = icmp ne i8* %30, null
  br i1 %31, label %32, label %36

; <label>:32                                      ; preds = %27
  %33 = load i8*, i8** %root, align 8
  %34 = call zeroext i1 @in_from_space(i8* %33)
  br i1 %34, label %35, label %36

; <label>:35                                      ; preds = %32
  br label %38

; <label>:36                                      ; preds = %32, %27
  call void @__assert_fail(i8* getelementptr inbounds ([42 x i8], [42 x i8]* @.str.1, i32 0, i32 0), i8* getelementptr inbounds ([9 x i8], [9 x i8]* @.str.2, i32 0, i32 0), i32 111, i8* getelementptr inbounds ([38 x i8], [38 x i8]* @__PRETTY_FUNCTION__.gc_collect, i32 0, i32 0)) #6
  unreachable
                                                  ; No predecessors!
  br label %38

; <label>:38                                      ; preds = %37, %35
  %39 = load i8*, i8** %root, align 8
  %40 = bitcast i8* %39 to i64*
  %41 = load i64, i64* %40, align 8
  %42 = ashr i64 %41, 32
  %43 = trunc i64 %42 to i32
  store i32 %43, i32* %size, align 4
  %44 = load i8*, i8** %root, align 8
  %45 = load i8*, i8** %next, align 8
  call void @copy_record(i8* %44, i8* %45)
  %46 = load i32, i32* %size, align 4
  %47 = load i8*, i8** %next, align 8
  %48 = sext i32 %46 to i64
  %49 = getelementptr inbounds i8, i8* %47, i64 %48
  store i8* %49, i8** %next, align 8
  br label %50

; <label>:50                                      ; preds = %38
  %51 = load i32, i32* %i, align 4
  %52 = add nsw i32 %51, 1
  store i32 %52, i32* %i, align 4
  br label %6

; <label>:53                                      ; preds = %6
  %54 = getelementptr inbounds [1 x %struct.__va_list_tag], [1 x %struct.__va_list_tag]* %roots, i32 0, i32 0
  %55 = bitcast %struct.__va_list_tag* %54 to i8*
  call void @llvm.va_end(i8* %55)
  %56 = load i8*, i8** @to_space, align 8
  store i8* %56, i8** %scan, align 8
  br label %57

; <label>:57                                      ; preds = %131, %53
  %58 = load i8*, i8** %scan, align 8
  %59 = load i8*, i8** %next, align 8
  %60 = icmp ult i8* %58, %59
  br i1 %60, label %61, label %136

; <label>:61                                      ; preds = %57
  %62 = load i8*, i8** %scan, align 8
  %63 = bitcast i8* %62 to i64*
  %64 = load i64, i64* %63, align 8
  %65 = ashr i64 %64, 32
  %66 = trunc i64 %65 to i32
  store i32 %66, i32* %size1, align 4
  %67 = load i8*, i8** %scan, align 8
  %68 = bitcast i8* %67 to i64*
  %69 = load i64, i64* %68, align 8
  %70 = and i64 %69, 4294967295
  %71 = ashr i64 %70, 1
  %72 = trunc i64 %71 to i32
  store i32 %72, i32* %ptr_count, align 4
  store i32 0, i32* %i2, align 4
  br label %73

; <label>:73                                      ; preds = %128, %61
  %74 = load i32, i32* %i2, align 4
  %75 = load i32, i32* %ptr_count, align 4
  %76 = icmp slt i32 %74, %75
  br i1 %76, label %77, label %131

; <label>:77                                      ; preds = %73
  %78 = load i8*, i8** %scan, align 8
  %79 = bitcast i8* %78 to i64*
  %80 = getelementptr inbounds i64, i64* %79, i64 1
  %81 = bitcast i64* %80 to i8**
  %82 = load i32, i32* %i2, align 4
  %83 = sext i32 %82 to i64
  %84 = getelementptr inbounds i8*, i8** %81, i64 %83
  %85 = load i8*, i8** %84, align 8
  store i8* %85, i8** %p, align 8
  %86 = load i8*, i8** %p, align 8
  %87 = icmp ne i8* %86, null
  br i1 %87, label %88, label %127

; <label>:88                                      ; preds = %77
  %89 = load i8*, i8** %p, align 8
  %90 = call zeroext i1 @in_from_space(i8* %89)
  br i1 %90, label %91, label %127

; <label>:91                                      ; preds = %88
  %92 = load i8*, i8** %p, align 8
  %93 = bitcast i8* %92 to i64*
  %94 = load i64, i64* %93, align 8
  %95 = and i64 %94, 1
  %96 = icmp ne i64 %95, 0
  br i1 %96, label %97, label %116

; <label>:97                                      ; preds = %91
  %98 = load i8*, i8** %p, align 8
  %99 = bitcast i8* %98 to i64*
  %100 = load i64, i64* %99, align 8
  %101 = ashr i64 %100, 32
  %102 = trunc i64 %101 to i32
  store i32 %102, i32* %p_size, align 4
  %103 = load i8*, i8** %next, align 8
  %104 = load i32, i32* %p_size, align 4
  %105 = sext i32 %104 to i64
  %106 = getelementptr inbounds i8, i8* %103, i64 %105
  %107 = call zeroext i1 @in_to_space(i8* %106)
  br i1 %107, label %109, label %108

; <label>:108                                     ; preds = %97
  call void @raise_out_of_memory()
  br label %109

; <label>:109                                     ; preds = %108, %97
  %110 = load i8*, i8** %p, align 8
  %111 = load i8*, i8** %next, align 8
  call void @copy_record(i8* %110, i8* %111)
  %112 = load i32, i32* %p_size, align 4
  %113 = load i8*, i8** %next, align 8
  %114 = sext i32 %112 to i64
  %115 = getelementptr inbounds i8, i8* %113, i64 %114
  store i8* %115, i8** %next, align 8
  br label %116

; <label>:116                                     ; preds = %109, %91
  %117 = load i8*, i8** %p, align 8
  %118 = bitcast i8* %117 to i8**
  %119 = load i8*, i8** %118, align 8
  %120 = load i8*, i8** %scan, align 8
  %121 = bitcast i8* %120 to i64*
  %122 = getelementptr inbounds i64, i64* %121, i64 1
  %123 = bitcast i64* %122 to i8**
  %124 = load i32, i32* %i2, align 4
  %125 = sext i32 %124 to i64
  %126 = getelementptr inbounds i8*, i8** %123, i64 %125
  store i8* %119, i8** %126, align 8
  br label %127

; <label>:127                                     ; preds = %116, %88, %77
  br label %128

; <label>:128                                     ; preds = %127
  %129 = load i32, i32* %i2, align 4
  %130 = add nsw i32 %129, 1
  store i32 %130, i32* %i2, align 4
  br label %73

; <label>:131                                     ; preds = %73
  %132 = load i32, i32* %size1, align 4
  %133 = load i8*, i8** %scan, align 8
  %134 = sext i32 %132 to i64
  %135 = getelementptr inbounds i8, i8* %133, i64 %134
  store i8* %135, i8** %scan, align 8
  br label %57

; <label>:136                                     ; preds = %57
  %137 = load i8*, i8** %next, align 8
  %138 = load i8*, i8** @to_space, align 8
  %139 = ptrtoint i8* %137 to i64
  %140 = ptrtoint i8* %138 to i64
  %141 = sub i64 %139, %140
  %142 = trunc i64 %141 to i32
  store i32 %142, i32* @next_free, align 4
  %143 = load i64, i64* %1, align 8
  %144 = load i32, i32* @next_free, align 4
  %145 = sub nsw i32 10240, %144
  %146 = sext i32 %145 to i64
  %147 = icmp ugt i64 %143, %146
  br i1 %147, label %148, label %149

; <label>:148                                     ; preds = %136
  call void @raise_out_of_memory()
  br label %149

; <label>:149                                     ; preds = %148, %136
  %150 = load i8*, i8** @from_space, align 8
  store i8* %150, i8** %tmp, align 8
  %151 = load i8*, i8** @to_space, align 8
  store i8* %151, i8** @from_space, align 8
  %152 = load i8*, i8** %tmp, align 8
  store i8* %152, i8** @to_space, align 8
  ret void
}

; Function Attrs: nounwind
declare void @llvm.va_start(i8*) #4

; Function Attrs: inlinehint nounwind uwtable
define internal zeroext i1 @in_from_space(i8* %p) #5 {
  %1 = alloca i8*, align 8
  store i8* %p, i8** %1, align 8
  %2 = load i8*, i8** @from_space, align 8
  %3 = load i8*, i8** %1, align 8
  %4 = icmp ule i8* %2, %3
  br i1 %4, label %5, label %10

; <label>:5                                       ; preds = %0
  %6 = load i8*, i8** %1, align 8
  %7 = load i8*, i8** @from_space, align 8
  %8 = getelementptr inbounds i8, i8* %7, i64 10240
  %9 = icmp ult i8* %6, %8
  br label %10

; <label>:10                                      ; preds = %5, %0
  %11 = phi i1 [ false, %0 ], [ %9, %5 ]
  ret i1 %11
}

; Function Attrs: noreturn nounwind
declare void @__assert_fail(i8*, i8*, i32, i8*) #2

; Function Attrs: nounwind uwtable
define internal void @copy_record(i8* %record, i8* %next) #0 {
  %1 = alloca i8*, align 8
  %2 = alloca i8*, align 8
  %size = alloca i32, align 4
  store i8* %record, i8** %1, align 8
  store i8* %next, i8** %2, align 8
  %3 = load i8*, i8** %1, align 8
  %4 = call zeroext i1 @in_from_space(i8* %3)
  br i1 %4, label %5, label %6

; <label>:5                                       ; preds = %0
  br label %8

; <label>:6                                       ; preds = %0
  call void @__assert_fail(i8* getelementptr inbounds ([22 x i8], [22 x i8]* @.str.3, i32 0, i32 0), i8* getelementptr inbounds ([9 x i8], [9 x i8]* @.str.2, i32 0, i32 0), i32 83, i8* getelementptr inbounds ([33 x i8], [33 x i8]* @__PRETTY_FUNCTION__.copy_record, i32 0, i32 0)) #6
  unreachable
                                                  ; No predecessors!
  br label %8

; <label>:8                                       ; preds = %7, %5
  %9 = load i8*, i8** %2, align 8
  %10 = call zeroext i1 @in_to_space(i8* %9)
  br i1 %10, label %11, label %12

; <label>:11                                      ; preds = %8
  br label %14

; <label>:12                                      ; preds = %8
  call void @__assert_fail(i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str.4, i32 0, i32 0), i8* getelementptr inbounds ([9 x i8], [9 x i8]* @.str.2, i32 0, i32 0), i32 84, i8* getelementptr inbounds ([33 x i8], [33 x i8]* @__PRETTY_FUNCTION__.copy_record, i32 0, i32 0)) #6
  unreachable
                                                  ; No predecessors!
  br label %14

; <label>:14                                      ; preds = %13, %11
  %15 = load i8*, i8** %1, align 8
  %16 = bitcast i8* %15 to i64*
  %17 = load i64, i64* %16, align 8
  %18 = ashr i64 %17, 32
  %19 = trunc i64 %18 to i32
  store i32 %19, i32* %size, align 4
  %20 = load i8*, i8** %2, align 8
  %21 = load i8*, i8** %1, align 8
  %22 = load i32, i32* %size, align 4
  %23 = sext i32 %22 to i64
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* %20, i8* %21, i64 %23, i32 1, i1 false)
  %24 = load i8*, i8** %1, align 8
  %25 = bitcast i8* %24 to i64*
  store i64 0, i64* %25, align 8
  %26 = load i8*, i8** %2, align 8
  %27 = load i8*, i8** %1, align 8
  %28 = bitcast i8* %27 to i8**
  store i8* %26, i8** %28, align 8
  ret void
}

; Function Attrs: nounwind
declare void @llvm.va_end(i8*) #4

; Function Attrs: inlinehint nounwind uwtable
define internal zeroext i1 @in_to_space(i8* %p) #5 {
  %1 = alloca i8*, align 8
  store i8* %p, i8** %1, align 8
  %2 = load i8*, i8** @to_space, align 8
  %3 = load i8*, i8** %1, align 8
  %4 = icmp ule i8* %2, %3
  br i1 %4, label %5, label %10

; <label>:5                                       ; preds = %0
  %6 = load i8*, i8** %1, align 8
  %7 = load i8*, i8** @to_space, align 8
  %8 = getelementptr inbounds i8, i8* %7, i64 10240
  %9 = icmp ult i8* %6, %8
  br label %10

; <label>:10                                      ; preds = %5, %0
  %11 = phi i1 [ false, %0 ], [ %9, %5 ]
  ret i1 %11
}

; Function Attrs: nounwind
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* nocapture, i8* nocapture readonly, i64, i32, i1) #4

attributes #0 = { nounwind uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { noreturn nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { alwaysinline nounwind uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nounwind }
attributes #5 = { inlinehint nounwind uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #6 = { noreturn nounwind }

!llvm.ident = !{!0}

!0 = !{!"clang version 3.7.0 (tags/RELEASE_370/final)"}
