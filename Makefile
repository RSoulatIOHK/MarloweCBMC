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

# Clean the generated files
clean:
	rm -rf $(OBJECTS) $(BUILDDIR)

.PHONY: all clean

# CBMC Analysis target
verify:
	cbmc -I$(INCDIR) $(SOURCES) $(SRCDIR)/main.c $(CBMC_OPT) -DCBMC
