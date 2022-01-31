GHC        = ghc
HAPPY      = happy
HAPPY_OPTS = --array --info --ghc --coerce
ALEX       = alex
ALEX_OPTS  = --ghc

vpath %.hs src
vpath %.y src
vpath %.x src
vpath %.o build

objects = Latte/Abs.hs Latte/Lex.hs Latte/Par.hs IDefinition.hs Translator.hs CompilationError.hs VariableEnvironment.hs FCCompiler.hs FCCompilerTypes.hs Gsce.hs LLVMCompiler.hs DeadCodeRemoval.hs Translator/Definitions.hs Translator/TranslatorEnvironment.hs Translator/Translator.hs LLVMCompiler/Outputable.hs LLVMCompiler/FunctionTable.hs
compilers = Main.hs

.PHONY: clean execution

all: build build/Main lib/runtime.bc execution

build:
	mkdir build

src/Latte/Par.hs : src/Latte/Par.y
	${HAPPY} ${HAPPY_OPTS} $< -o $@

src/Latte/Lex.hs : src/Latte/Lex.x
	${ALEX} ${ALEX_OPTS} $< -o $@

build/Main: Main.hs $(objects) 
	${GHC} $< -O -isrc -odir build -o $@

lib/runtime.bc : lib/runtime.ll
	llvm-as $<

execution: latc_llvm
	chmod +x latc_llvm
clean:
	-rm -rf build
	-rm -f $(addprefix src/Latte/, Par.hs Lex.hs Par.info)
	-rm -f src/*.hi src/Latte/*.hi
