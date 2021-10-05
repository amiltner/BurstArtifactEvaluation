TARGETS=BurstCmdLine.exe

GENERATE_DATA := python3 generate-data.py
GENERATE_GRAPHS := python3 transform-data.py
CREATE_DEFAULT_ANSWERS := python3 create-default-answers.py

.PHONY: all build clean %.exe

all: build link

build:
	dune build app/BurstCmdLine.exe --profile release # ignores warnings as errors

link: $(TARGETS)

%.exe:
	if [ ! -f $@ ]; then ln -s _build/default/app/$@ . ; fi

install:
	jbuilder install

clean:
	rm -rf _build *.install *.pdf $(TARGETS)

clean-data:
ifneq (,$(wildcard ./generated-data/io.csv))
	rm generated-data/io.csv
endif
ifneq (,$(wildcard ./generated-data/ref.csv))
	rm generated-data/ref.csv
endif
ifneq (,$(wildcard ./generated-data/logical.csv))
	rm generated-data/logical.csv
endif

clean-outs:
ifneq (,$(wildcard ./benchmarks/logical/*.out))
	rm benchmarks/logical/*.out
endif
ifneq (,$(wildcard ./benchmarks/io/*.out))
	rm benchmarks/io/*.out
endif

documentation:
	jbuilder build @docs

generate-data: all
	$(GENERATE_DATA) ./BurstCmdLine.exe benchmarks/ref benchmarks/logical benchmarks/io

generate-outs: all
	$(CREATE_DEFAULT_ANSWERS) ./BurstCmdLine.exe benchmarks/logical benchmarks/io

kick-the-tires: all
	./BurstCmdLine.exe benchmarks/logical/list_append.mls
