/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# Trace of multiplication by a derivation value

The Leibniz rule identifies `[D, L_a]` with `L_{D a}` in any non-associative algebra.
Cyclicity of trace therefore implies `tr(L_{D a}) = 0`. This supplies the invariance of
the trace form for Jordan algebras, without any commutativity or dimension hypothesis here.
-/

public section

namespace TauCeti

section Derivation

variable {R A : Type*} [CommRing R] [NonUnitalNonAssocRing A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A]

/-- The trace of left multiplication by the value of a derivation vanishes. -/
theorem derivationLieAlgebra.trace_mulLeft_apply_eq_zero (D : derivationLieAlgebra R A)
    (a : A) : LinearMap.trace R A (LinearMap.mulLeft R ((D : Module.End R A) a)) = 0 := by
  rw [← derivationLieAlgebra.lie_mulLeft D a, LinearMap.trace_lie]

end Derivation

end TauCeti
