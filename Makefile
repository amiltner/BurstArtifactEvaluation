.PHONY: all clean generate-data clean-data regenerate-data

all:
	make -C burst
	make -C synquid
	make -C leon

clean:
	make -C burst clean
	make -C synquid clean
	make -C leon clean

clean-data:
	make -C burst clean-data
	make -C synquid clean-data
	make -C leon clean-data

clean-outs:
	make -C burst clean-outs
	make -C synquid clean-outs
	make -C leon clean-outs

generate-outs:
	make -C burst generate-outs
	make -C synquid generate-outs
	make -C leon generate-outs

generate-data:
	make -C burst generate-data
	make -C synquid generate-data
	make -C leon generate-data

generate-all: all generate-data generate-outs

regenerate-data:
	make -C burst regenerate-data
	make -C synquid regenerate-data

graphs:
	python3 generate-graphs.py generated-data/examples.csv generated-data/equiv.csv generated-data/postconditional.csv

hyper-clean: clean-data clean-outs clean

kick-the-tires:
	make -C burst kick-the-tires
	make -C synquid kick-the-tires
	make -C leon kick-the-tires
	echo "Tires kicked successfully!"
