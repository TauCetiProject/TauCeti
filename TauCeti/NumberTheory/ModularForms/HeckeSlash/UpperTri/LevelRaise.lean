/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.UpperTri.QExpansion

/-!
# Upper-triangular slashes of a level-raise

For `g` slash-invariant under a group with `1` as a strict period, the level-raise
`V_p g = p^(1-k) • (g ∣[k] scaleGL p)` (the function `τ ↦ g (p τ)`) is slashed by the
upper-triangular matrix `!![1, b; 0, p]` back to `p⁻¹ • g`:
`(V_p g) ((τ + b) / p) = g (τ + b) = g τ`, by the period-`1` invariance of `g`. This is the
upper-triangular part of the descent of a level-raise (`Newforms/Descent/LevelRaise.lean`).

## Main results

* `TauCeti.smul_slash_scaleGL_slash_upperTriRep`: for `g` slash-invariant with period `1`,
  `(p^(1-k) • (g ∣[k] scaleGL p)) ∣[k] !![1, b; 0, p] = p⁻¹ • g`.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB> @ `eb9621e7bcb0ce220ad53983ec45d987cb5b9002`),
`projects/LeanModularForms/LeanModularForms/StrongMultiplicityOne/HeckeDescent.lean`
(`V_p_slash_upper_aux`). The source's `modularFormLevelRaise` is this repository's
`ModularForm.levelRaise`; the statement is re-proved on the underlying function, for any
group with `1` as a strict period.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GL2

open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti

variable {p : ℕ} [NeZero p] (k : ℤ)

/-- **An upper-triangular matrix slashes a level-raise back to the form**: for `g` slash-invariant
under a group `Γ` with `1` as a strict period and `V_p g = p^(1-k) • (g ∣[k] scaleGL p)`,
`(V_p g) ∣[k] !![1, b; 0, p] = p⁻¹ • g`. -/
theorem smul_slash_scaleGL_slash_upperTriRep {Γ : Subgroup (GL (Fin 2) ℝ)}
    (hper : (1 : ℝ) ∈ Γ.strictPeriods) {F : Type*} [FunLike F ℍ ℂ]
    [SlashInvariantFormClass F Γ k] (g : F) (b : Fin p) :
    ((p : ℂ) ^ (1 - k) • (⇑g ∣[k] scaleGL p)) ∣[k] (upperTriRep p b : GL (Fin 2) ℚ) =
      (p : ℂ)⁻¹ • ⇑g := by
  funext τ
  have hτ : scaleGL p • (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep p b) • τ) =
      ((b : ℝ) +ᵥ τ : ℍ) := by
    ext1
    rw [coe_scaleGL_smul, coe_upperTriRep_smul, UpperHalfPlane.coe_vadd]
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
    push_cast
    field_simp
    ring
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  rw [slash_upperTriRep_apply, Pi.smul_apply, smul_eq_mul, slash_scaleGL_apply, Pi.smul_apply,
    smul_eq_mul, hτ, SlashInvariantForm.vAdd_apply_of_mem_strictPeriods g τ
      (by simpa using AddSubgroup.nsmul_mem _ hper b.val),
    ← mul_assoc ((p : ℂ) ^ (1 - k)), ← zpow_add₀ hp0, sub_add_sub_cancel, sub_self, zpow_zero,
    one_mul]

end TauCeti
