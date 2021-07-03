# Get path to the Makefile
MKFILE_PATH := $(abspath $(lastword $(MAKEFILE_LIST)))
MKFILE_DIR := $(dir $(MKFILE_PATH))

.PHONY: pcal
pcal: ## Translate all the pluscal in the TLA files.
	@for f in $(shell ls ${MKFILE_DIR}/*.tla); do \
		echo "Translating: $${f}"; \
		pcal -nocfg $${f}; \
		rm -f "$${f%.tla}.old"; \
	done

# This is just a silly hack I was using before I setup all the CLI stuff.
# Keeping it for now cause some stuff is still in there. LOL.
.PHONY: mitchellh/copy
mitchellh/copy:
	cp /host/mitchellh/Dropbox\ \(Personal\)/TEMP/Radix/*.{tla,pdf} .
