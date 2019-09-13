.PHONY: clean-tests

clean-tests:
	find tests -name "*.hi"     | xargs rm -f
	find tests -name "*.dyn_hi" | xargs rm -f
	find tests -name "*.o"      | xargs rm -f
	find tests -name "*.dyn_o"  | xargs rm -f
	find tests -name "*.actual" | xargs rm -f
	rm -f tests/compile-and-dump/GradingClient/Main
