/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Polynomial.Norm
public import Mathlib.NumberTheory.NumberField.House
public import TauCeti.Analysis.Polynomial.L1Norm
public import TauCeti.Analysis.Polynomial.SupNorm.Basic

/-!
# The house of a polynomial expression in an algebraic number

If every complex conjugate of `γ` is, up to the factor `s ^ d`, the value of an integer polynomial
`P` of degree `d` at the corresponding conjugate of `g`, then the house of `γ` is bounded by the
coefficient sup norm of `P`, a bound on the conjugates of `g`, and `s`.

## Main results

* `NumberField.house_le_of_norm_embedding_eq`: the bound
  `house γ ≤ s ^ n * ((n + 1) * R ^ n) * H(P)`.
-/

public section

namespace NumberField

open Polynomial

/-- If every conjugate `σ γ` of `γ` has absolute value `s ^ d * ‖P(σ g)‖`, where `1 ≤ s` and `P` has
degree `d ≤ n`, and `max 1 ‖σ g‖ ≤ R` for every conjugate, then the house of `γ` is at most
`s ^ n * ((n + 1) * R ^ n) * H(P)`. -/
theorem house_le_of_norm_embedding_eq {F : Type*} [Field F] [NumberField F] {g γ : F}
    {R : ℝ} (hR : ∀ σ : F →+* ℂ, max 1 ‖σ g‖ ≤ R) {s : ℝ} (hs1 : 1 ≤ s) {n : ℕ}
    {P : ℤ[X]} (hP : P.natDegree ≤ n)
    (hγ : ∀ σ : F →+* ℂ, ‖σ γ‖ = s ^ P.natDegree * ‖aeval (σ g) P‖) :
    house γ ≤ s ^ n * ((n + 1) * R ^ n) * P.supNorm := by
  have hH := P.supNorm_nonneg
  obtain ⟨σ, -, hσ⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty fun φ : F →+* ℂ ↦ ‖φ γ‖₊
  rw [house_eq_sup', hσ, coe_nnnorm, hγ]
  calc s ^ P.natDegree * ‖aeval (σ g) P‖
      ≤ s ^ n * ((n + 1) * P.supNorm * max 1 ‖σ g‖ ^ n) := by
        gcongr
        rw [aeval_def, algebraMap_int_eq, ← eval_map, ← P.supNorm_map (Int.castRingHom ℂ)]
        exact norm_eval_le_add_one_mul_supNorm_mul (natDegree_map_le.trans hP) _
    _ ≤ s ^ n * ((n + 1) * P.supNorm * R ^ n) := by
        gcongr
        exact hR σ
    _ = s ^ n * ((n + 1) * R ^ n) * P.supNorm := by ring

end NumberField
