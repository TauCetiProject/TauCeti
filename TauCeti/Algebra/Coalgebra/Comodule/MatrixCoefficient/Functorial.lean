/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Transport

/-!
# Compatibility import for matrix coefficient transport

This module preserves the old
`TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Functorial` import path after the
transport-specific matrix-coefficient lemmas moved to
`TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Transport`.

Keeping this public re-export is intentional downstream compatibility for users that still
imported the old public module name when the declarations were moved.
-/
