all : boogie-llvm test
.PHONY : all
.SECONDARY : # Keep all intermediates

BOOGIE_LLVM := .build/boogie-kompiled/timestamp
boogie-llvm : ${BOOGIE_LLVM}
.build/boogie-kompiled/timestamp : boogie.md helpers.md syntax.md quantification.md
	kompile $< \
	    --no-exc-wrap \
	    --warnings-to-errors \
	    --gen-bison-parser \
	    --enable-search \
	    --output-definition .build/boogie-kompiled \
	    --backend llvm \
        --main-module BOOGIE \
        --syntax-module BOOGIE-PROGRAM-SYNTAX

test_inputs := $(wildcard test/operational/control-flow/*.bpl)
test_targets := $(addsuffix .test,${test_inputs})
test: ${test_targets}
	echo $^

.build/test/%.bpl.out: test/%.bpl ${BOOGIE_LLVM}
	mkdir -p $(dir $@)
	krun --definition .build/boogie-kompiled --search-final --no-pattern $< > $@
.PHONY : test/%.bpl.test
test/%.bpl.test : .build/test/%.bpl.out test/%.bpl.opexpect
	bin/diff-kboogie $^
