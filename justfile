default:
    @just --list

# Regenerate the makefile from the project manifest.
generate:
    @if command -v rocq >/dev/null 2>&1; then \
        rocq makefile -f _CoqProject -o CoqMakeFile; \
    else \
        coq_makefile -f _CoqProject -o CoqMakeFile; \
    fi

# Compile every file listed in _CoqProject.
build: generate
    make -f CoqMakeFile

# Remove generated Rocq build artifacts.
clean: generate
    make -f CoqMakeFile clean

# Clean and compile the entire project again.
rebuild:
    just clean
    just build
