/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Norm.Quadratic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Quadratic norms over local rings

For a quadratic basis `(1, θ)` over a local ring, if the trace and norm of `θ` lie in the
maximal ideal, the norm reduces to the square of the first coordinate in the residue field.
Consequently the norm is a unit exactly when the first coordinate is a unit. This applies to
Eisenstein integral bases without any restriction on the residue characteristic.
-/

public section

namespace Module.Basis

variable {K L : Type*} [CommRing K] [CommRing L] [Algebra K L]

/-- When the trace and norm of the second basis vector lie in the maximal ideal, the residue
of the norm is the square of the residue of the first coordinate. -/
theorem residue_norm_eq_sq_of_mem_maximalIdeal [IsLocalRing K]
    (B : Module.Basis (Fin 2) K L) (hB : B 0 = 1)
    (hT : Algebra.trace K L (B 1) ∈ IsLocalRing.maximalIdeal K)
    (hN : Algebra.norm K (B 1) ∈ IsLocalRing.maximalIdeal K) (w : L) :
    IsLocalRing.residue K (Algebra.norm K w) =
      IsLocalRing.residue K (B.repr w 0) ^ 2 := by
  rw [B.norm_eq_of_apply_zero_eq_one hB]
  simp [(IsLocalRing.residue_eq_zero_iff _).mpr hT, (IsLocalRing.residue_eq_zero_iff _).mpr hN]

/-- In a quadratic basis `(1, θ)` whose second vector has trace and norm in the maximal ideal,
an element has unit norm exactly when its first coordinate is a unit. -/
theorem isUnit_norm_iff_repr_zero_of_mem_maximalIdeal [IsLocalRing K]
    (B : Module.Basis (Fin 2) K L) (hB : B 0 = 1)
    (hT : Algebra.trace K L (B 1) ∈ IsLocalRing.maximalIdeal K)
    (hN : Algebra.norm K (B 1) ∈ IsLocalRing.maximalIdeal K) (w : L) :
    IsUnit (Algebra.norm K w) ↔ IsUnit (B.repr w 0) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit,
    B.residue_norm_eq_sq_of_mem_maximalIdeal hB hT hN]
  simp

end Module.Basis
