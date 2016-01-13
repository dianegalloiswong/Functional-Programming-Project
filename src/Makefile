OCAMLBUILD= ocamlbuild -no-links -classic-display \
		-tags debug,annot

TARGET=byte
MAIN=Main

all:
	$(OCAMLBUILD) $(MAIN).$(TARGET)
	cp _build/$(MAIN).$(TARGET) $(MAIN)

clean:
	$(OCAMLBUILD) -clean
	rm -f $(MAIN)

realclean: clean
	rm -f *~

cleanall: realclean
