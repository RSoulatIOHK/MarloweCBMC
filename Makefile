CC := gcc
CFLAGS := -Wall -Wextra -Iinclude

# Source and object files
SRCDIR := src
INCDIR := include
SOURCES := $(wildcard $(SRCDIR)/*.c)
OBJECTS := $(patsubst $(SRCDIR)/%.c, $(SRCDIR)/%.o, $(SOURCES))
CBMC_OPT := --object-bits 10

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
	goto-cc -o $(BUILDDIR)/main.goto $(SRCDIR)/*.c -I$(INCDIR)
	-cbmc $(BUILDDIR)/main.goto $(CBMC_OPT) --trace --xml-ui > $(REPORTDIR)/result.xml
	cbmc $(BUILDDIR)/main.goto $(CBMC_OPT) --cover location -xml-ui > $(REPORTDIR)/coverage.xml
	cbmc $(BUILDDIR)/main.goto $(CBMC_OPT) --show-properties --xml-ui > $(REPORTDIR)/properties.xml
	cbmc-viewer --goto $(BUILDDIR)/main.goto --result $(REPORTDIR)/result.xml --coverage $(REPORTDIR)/coverage.xml --property $(REPORTDIR)/properties.xml --srcdir $(SRCDIR) 
	open $(REPORTDIR)/html/index.html
