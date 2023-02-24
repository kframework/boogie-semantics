all : boogie-llvm

BOOGIE_LLVM := .build/boogie-kompiled/timestamp
boogie-llvm : ${BOOGIE_LLVM}
.build/boogie-kompiled/timestamp : boogie.md helpers.md syntax.md quantification.md
	kompile $< \
	    --enable-search \
	    --output-definition .build/boogie-kompiled \
	    --backend llvm \
        --main-module BOOGIE \
        --syntax-module BOOGIE-PROGRAM-SYNTAX

test/%.bpl.test : test/%.bpl ${BOOGIE_LLVM}
	krun --definition .build/boogie-kompiled $<
