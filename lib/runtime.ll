@.str = private unnamed_addr constant [3 x i8] c"%d\00", align 1
@.str.1 = private unnamed_addr constant [4 x i8] c"%ms\00", align 1
@.str.2 = private unnamed_addr constant [3 x i8] c"%s\00", align 1
@.str.3 = private unnamed_addr constant [14 x i8] c"runtime error\00", align 1
@.str.4 = private unnamed_addr constant [4 x i8] c"%d\0A\00", align 1

declare i64 @strlen(i8*)
declare i8* @malloc(i64)
declare i8* @strcpy(i8*, i8*)
declare i8* @strcat(i8*, i8*)
declare i32 @printf(i8*, ...)
declare i32 @strcmp(i8*, i8*)
declare i32 @puts(i8*)
declare i32 @scanf(i8*, ...)
declare void @exit(i32)


define i8* @_new(i32 %0) {
  %r1 = sext i32 %0 to i64
  %r2 = call i8* @malloc(i64 %r1)
  ret i8* %r2
}

define i8* @_strconcat(i8* %r0, i8* %r1) {
  %r2 = call i64 @strlen(i8* %r0) 
  %r3 = call i64 @strlen(i8* %r1)
  %r4 = add i64 %r2, %r3
  %r4.5 = add i64 %r4, 1
  %cond = icmp sge i64 %r4.5, 16
  br i1 %cond, label %L1, label %L2
  L1:
  br label %L3
  L2:
  br label %L3
  L3:
  %size = phi i64 [%r4.5, %L1], [16, %L2]
  %r5 = call i8* @malloc(i64 %r4.5)
  %r6 = call i8* @strcpy(i8* %r5, i8* %r0)
  %r7 = call i8* @strcat(i8* %r6, i8* %r1)
  ret i8* %r7
}

define i1 @_strle(i8* %r0, i8* %r1) {
  %r7 = call i32 @strcmp(i8* %r0, i8* %r1)
  %r8 = icmp sle i32 %r7, 0
  br i1 %r8, label %L1, label %L2
  L1:
  ret i1 1
  L2:
  ret i1 0
}

define i1 @_strlt(i8* %r0, i8* %r1) {
  %r7 = call i32 @strcmp(i8* %r0, i8* %r1)
  %r8 = icmp slt i32 %r7, 0
  br i1 %r8, label %L1, label %L2
  L1:
  ret i1 1
  L2:
  ret i1 0
}

define i1 @_strge(i8* %r0, i8* %r1) {
  %r7 = call i32 @strcmp(i8* %r0, i8* %r1)
  %r8 = icmp sge i32 %r7, 0
  br i1 %r8, label %L1, label %L2
  L1:
  ret i1 1
  L2:
  ret i1 0
}

define i1 @_strgt(i8* %r0, i8* %r1) {
  %r7 = call i32 @strcmp(i8* %r0, i8* %r1)
  %r8 = icmp sgt i32 %r7, 0
  br i1 %r8, label %L1, label %L2
  L1:
  ret i1 1
  L2:
  ret i1 0
}

define i1 @_streq(i8* %r0, i8* %r1) {
  %r7 = call i32 @strcmp(i8* %r0, i8* %r1)
  %r8 = icmp eq i32 %r7, 0
  br i1 %r8, label %L1, label %L2
  L1:
  ret i1 1
  L2:
  ret i1 0
}

define i1 @_strneq(i8* %r0, i8* %r1) {
  %r7 = call i32 @strcmp(i8* %r0, i8* %r1)
  %r8 = icmp ne i32 %r7, 0
  br i1 %r8, label %L1, label %L2
  L1:
  ret i1 1
  L2:
  ret i1 0
}

define void @printInt(i32 %r0){
  %r2 = alloca i32, align 4
  store i32 %r0, i32* %r2, align 4
  %r3 = load i32, i32* %r2, align 4
  %r4 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.4, i64 0, i64 0), i32 %r3)
  ret void
}

define void @printString(i8* %r0) {
  %r2 = alloca i8*, align 8
  store i8* %r0, i8** %r2, align 8
  %r3 = load i8*, i8** %r2, align 8
  %r4 = call i32 @puts(i8* %r3)
  ret void
}

define i8* @readString() {
  %r1 = alloca i8*, align 8
  %r2 = call i32 (i8*, ...) @scanf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.1, i64 0, i64 0), i8** %r1)
  %r3 = load i8*, i8** %r1, align 8
  ret i8* %r3
}


define dso_local i32 @readInt() {
  %r1 = alloca i32, align 4
  %r2 = call i32 (i8*, ...) @scanf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str, i64 0, i64 0), i32* %r1)
  %r3 = load i32, i32* %r1, align 4
  ret i32 %r3
}

define void @error() {
  %r1 = call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.2, i64 0, i64 0), i8* getelementptr inbounds ([14 x i8], [14 x i8]* @.str.3, i64 0, i64 0))
  call void @exit(i32 0)
  unreachable
}


