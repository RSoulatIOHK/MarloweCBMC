CC := gcc
CFLAGS := -Wall -Wextra -Iinclude

# Source and object files
DOG := " _   _\n/(. .)\    )\n  (*)____/|\n  /       |\n /   |--\ |\n(_)(_)  (_)"
SRCDIR := src
INCDIR := include
SOURCES := $(wildcard $(SRCDIR)/*.c)
OBJECTS := $(patsubst $(SRCDIR)/%.c, $(SRCDIR)/%.o, $(SOURCES))
CBMC_OPT := --object-bits 10
GOTO_NAME := main.goto

# Output binary and build directory
BUILDDIR := build
OUTPUT := $(BUILDDIR)/marloweSwapMC
REPORTDIR := report

# Default target
all: $(OUTPUT)

# Linking the object files to create the binary
$(OUTPUT): $(OBJECTS)
	$(CC) $(CFLAGS) $(OBJECTS) -o $@

# Compiling the source files into object files
$(SRCDIR)/%.o: $(SRCDIR)/%.c
	$(CC) $(CFLAGS) -c $< -o $@

# Ensure the build directory exists before compiling
$(shell mkdir -p $(BUILDDIR))
$(shell mkdir -p $(REPORTDIR))

# Clean the generated files
clean:
	rm -rf $(OBJECTS) $(BUILDDIR) $(REPORTDIR)

.PHONY: all clean

# CBMC Analysis target
verify:
	@echo "-------------------------------------------"
	@echo "Marlowe Bounded Model Checking Analysis"
	@echo "Currently only for the Marlowe Swap contract"
	@echo "Author: Romain Soulat"
	@echo "version: 0.0.1"
	@echo "-------------------------------------------"
	@echo $(DOG) # Contribution by Aliénor
	@echo " "
	@echo "-------------------------------------------"
	@echo "Notice:"
	@echo "Model of the ledger is very "
	@echo "Compiling the C code to goto format for analysis:"
	@goto-cc -o $(BUILDDIR)/$(GOTO_NAME) $(SRCDIR)/*.c -I$(INCDIR)
	@echo "Running CBMC analysis:"
	@echo "  - Generating result file"
	-@cbmc $(BUILDDIR)/$(GOTO_NAME) $(CBMC_OPT) --trace --xml-ui > $(REPORTDIR)/result.xml
	@echo "  - Generating coverage file"
	@cbmc $(BUILDDIR)/$(GOTO_NAME) $(CBMC_OPT) --cover location -xml-ui > $(REPORTDIR)/coverage.xml
	@echo "  - Generating properties file"
	@cbmc $(BUILDDIR)/$(GOTO_NAME) $(CBMC_OPT) --show-properties --xml-ui > $(REPORTDIR)/properties.xml
	@echo "  - Generating HTML report:"
	@cbmc-viewer --goto $(BUILDDIR)/$(GOTO_NAME) --result $(REPORTDIR)/result.xml --coverage $(REPORTDIR)/coverage.xml --property $(REPORTDIR)/properties.xml --srcdir $(SRCDIR) 
	open $(REPORTDIR)/html/index.html
