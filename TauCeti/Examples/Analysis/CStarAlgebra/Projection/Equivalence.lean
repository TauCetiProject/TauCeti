/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Projection.Equivalence

import TauCeti.Algebra.Star.Projection.Basic

/-!
# Concrete checks for matrix Murray–von Neumann equivalence

Two concrete matrix checks exercising `TauCeti.Analysis.CStarAlgebra.Projection.Equivalence`:

* Unequal-size zero-padding equivalence `diag(1, 0) ∼ 1` between `M₂(ℂ)` and `M₁(ℂ)`.
* Explicit midpoint computation of the stabilized exponential unitary path for `p = q = 1` in
  `M₁(ℂ)` with `v = 1`.
-/

open scoped CStarAlgebra ComplexOrder Matrix Real

namespace CStarMatrix

/-- Unequal-size Murray–von Neumann equivalence: `diag(1, 0) : M₂(ℂ)` is equivalent to
`1 : M₁(ℂ)`. -/
example :
    MurrayVonNeumannEquiv
      (CStarMatrix.fromBlocks (1 : CStarMatrix (Fin 1) (Fin 1) ℂ) 0 0
        (0 : CStarMatrix (Fin 1) (Fin 1) ℂ))
      (1 : CStarMatrix (Fin 1) (Fin 1) ℂ) :=
  (MurrayVonNeumannEquiv.pad_zero (k := Fin 1)
    (IsStarProjection.one (R := CStarMatrix (Fin 1) (Fin 1) ℂ))).symm

/-- Midpoint of the stabilized exponential path for `p = q = 1` in `M₁(ℂ)` and `v = 1`:
`exp(i π r / 2) * diag(1, 0) * exp(-i π r / 2) = [[1 / 2, i / 2], [-i / 2, 1 / 2]]`. -/
example :
    let p : CStarMatrix (Fin 1) (Fin 1) ℂ := 1
    let w : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ := fromBlocks 0 1 1 0
    let r : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ := (2 : ℂ)⁻¹ • (1 - w)
    have hr : IsStarProjection r :=
      IsStarProjection.half_one_sub_of_mul_self_eq_one
        (by simp [w]) (by simp [w, isSelfAdjoint_iff])
    let u : unitary (CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) :=
      selfAdjoint.expUnitary ⟨((π / 2 : ℝ) : ℂ) • r,
        IsSelfAdjoint.smul (Complex.conj_ofReal (π / 2)) hr.isSelfAdjoint⟩
    (u : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) * fromBlocks p 0 0 0 *
        star (u : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) =
      fromBlocks ((1 / 2 : ℂ) • 1) ((Complex.I / 2 : ℂ) • 1)
        ((-(Complex.I / 2) : ℂ) • 1) ((1 / 2 : ℂ) • 1) := by
  intro p w r hr u
  have hexp : Complex.exp (Complex.I * ((π / 2 : ℝ) : ℂ)) = Complex.I := by
    rw [mul_comm, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]
  have hu : (u : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) =
      fromBlocks (((1 + Complex.I) / 2 : ℂ) • 1) (((1 - Complex.I) / 2 : ℂ) • 1)
        (((1 - Complex.I) / 2 : ℂ) • 1) (((1 + Complex.I) / 2 : ℂ) • 1) := by
    dsimp only [u]; rw [hr.coe_expUnitary_smul (π / 2), hexp]
    ext (i | i) (j | j) <;> simp [r, w, ← fromBlocks_one] <;> ring
  have hsu : star (u : CStarMatrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) =
      fromBlocks (((1 - Complex.I) / 2 : ℂ) • 1) (((1 + Complex.I) / 2 : ℂ) • 1)
        (((1 + Complex.I) / 2 : ℂ) • 1) (((1 - Complex.I) / 2 : ℂ) • 1) := by
    rw [hu, fromBlocks_star]; ext (i | i) (j | j) <;> simp [Complex.conj_I, sub_eq_add_neg]
  rw [hsu, hu]
  ext (i | i) (j | j) <;> simp [p, fromBlocks_mul] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

end CStarMatrix
