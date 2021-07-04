# Get path to the Makefile
MKFILE_PATH := $(abspath $(lastword $(MAKEFILE_LIST)))
MKFILE_DIR := $(dir $(MKFILE_PATH))

# Spec and model name should be set for the tlc target
SPEC_NAME ?= UNSET
MODEL_NAME ?= MC

.PHONY: pcal
pcal: ## Translate all the pluscal in the TLA files.
	@for f in $(shell ls ${MKFILE_DIR}/*.tla); do \
		echo "Translating: $${f}"; \
		pcal -nocfg $${f}; \
		rm -f "$${f%.tla}.old"; \
	done

.PHONY: pdf
pdf: ## Render PDFs for all the TLA files.
	@for f in $(shell ls ${MKFILE_DIR}/*.tla); do \
		tla2tex -shade $${f}; \
		pdflatex "$${f%.tla}.tex"; \
	done
	@rm *.{aux,dvi,log,ps,tex}

.PHONY: tlc
tlc: # Run TLC against a model specified by MODEL_NAME env var
	@cd ${MKFILE_DIR} && \
		tlc2 ./models/${SPEC_NAME}/${MODEL_NAME}.tla

# This is just a silly hack I was using before I setup all the CLI stuff.
# Keeping it for now cause some stuff is still in there. LOL.
.PHONY: mitchellh/copy
mitchellh/copy:
	cp /host/mitchellh/Dropbox\ \(Personal\)/TEMP/Radix/*.{tla,pdf} .
