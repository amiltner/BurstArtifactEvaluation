.PHONY: all clean generate-outs generate-data clean-data regenerate-data hyper-clean clean-outs regenerate-outs

all:
	stack setup && stack build

clean:
	stack clean

generate-data: all
	python3 generate-data.py benchmarks/logical

generate-outs: all
	python3 generate-outs.py benchmarks/logical

clean-data:
ifneq (,$(wildcard ./generated-data/data.csv))
	rm generated-data/data.csv
endif

regenerate-data: clean-data generate-data

regenerate-outs: clean-outs generate-outs

clean-outs:
ifneq (,$(wildcard ./benchmarks/logical/*.out))
	rm benchmarks/logical/*.out
endif

hyper-clean: clean-data clean-outs clean

kick-the-tires: all
	stack exec -- synquid benchmarks/logical/list_append.sq
