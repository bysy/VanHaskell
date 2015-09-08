# VanHaskell

## Description

This module defines the VH language and provides a C code generator.

## Status

Currently in the middle of a big refactoring. My earlier versions had a single monster monad, which while functional, made it hard to extend the code. So moving to a more modular design was my first priority; I'm happy with the new structure of the compiler, in particular the way different stages can be assembled. However the actual code generation is currently not included. *Ahem.*
