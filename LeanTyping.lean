-- This module serves as the root of the `LeanTyping` library.
-- Import modules here that should be built as part of the library.
import LeanTyping.Utils
import LeanTyping.Syntax

-- basic eval
import LeanTyping.BasicEval

-- norm eval
import LeanTyping.NormEval

-- typed eval
import LeanTyping.TypedEval

-- typed norm eval
import LeanTyping.TypedNormEval


open Typing.Untyped in
#eval Term.runProgramNorm []
 (program:
    def id := (λ x . x)
    id id
    def f := (λ x . λ y . y x)
    (λ x . λ y . x y) (λ x . x))

open Typing.Typed in
#eval Term.runProgram []
 (program:
    def id := (λ x . x)
    id id
    def f := (λ x . λ y . y x)
    (λ x . λ y . x y) (λ x . x))

