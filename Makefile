.PHONY: slides

all: slides

slides:
	pandoc -t beamer slides.md -o slides.pdf
