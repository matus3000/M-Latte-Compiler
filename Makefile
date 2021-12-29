GHC        = ghc
HAPPY      = happy
HAPPY_OPTS = --array --info --ghc --coerce
ALEX       = alex
ALEX_OPTS  = --ghc

vpath %.hs src
vpath %.y src
vpath %.x src
vpath %.o build

objects = Latte/Abs.hs Latte/Lex.hs Latte/Par.hs IDefinition.hs Translator.hs CompilationError.hs VariableEnvironment.hs LLVMCompiler.hs FCCompilerTypes.hs
compilers = Main.hs

.PHONY: clean

all: build build/Main

build:
	mkdir build

src/Latte/Par.hs : src/Latte/Par.y
	${HAPPY} ${HAPPY_OPTS} $< -o $@

src/Latte/Lex.hs : src/Latte/Lex.x
	${ALEX} ${ALEX_OPTS} $< -o $@

build/Main: Main.hs $(objects) 
	${GHC} $< -O -isrc -odir build -o $@

clean:
	-rm -rf build
	-rm -f $(addprefix src/Latte/, Par.hs Lex.hs Par.info)
	-rm -f src/*.hi src/Latte/*.hi
