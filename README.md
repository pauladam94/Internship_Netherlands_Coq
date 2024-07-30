# Internship_Netherlands_Coq
Prooving Some Borrow checking Propertie in Coq

## How to run

```rust
    coq_makefile -f _CoqProject *.v -o Makefile
    make
```

## Dependencie chain Language

Utils: None
Error: Utils
Language: Utils
Parse: Utils, Error, Language
Semantics: Utils, Language, Error, Parse
Typing: Not Done for now
