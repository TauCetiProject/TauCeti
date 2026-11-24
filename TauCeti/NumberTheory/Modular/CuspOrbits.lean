/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
public import TauCeti.NumberTheory.Modular.ConjugateTranslation
public import TauCeti.NumberTheory.Modular.Invariants

/-!
# The cusps of a subgroup of `PSL(2, ℤ)` are its cusp orbits

Let `Γ' ≤ PSL(2, ℤ)` have a coset numbering `e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n`. Its number of cusps
`TauCeti.ModularGroup.cuspCount Γ' e` is defined combinatorially, as the number of cycles of the
permutation `σinf = permT Γ' e` by which `T` acts on the cosets. This file identifies it with the
number of cusp orbits of the full preimage `±Γ' = Γ'.liftSL` in `SL(2, ℤ)`, both for the effective
image of `±Γ'` in `PSL(2, ℝ)` (`Subgroup.CuspOrbit`) and for its image in `GL(2, ℝ)` (Mathlib's
`CuspOrbits`).

The coset `g Γ'` is sent to the cusp orbit of `g⁻¹ • ∞`
(`TauCeti.ModularGroup.cuspOrbitOfCoset`). Every cusp is a translate of `∞`, so this map is
surjective, and two cosets have the same image exactly when they lie in one orbit of the powers of
`T`: if `h g'⁻¹ • ∞ = g⁻¹ • ∞` with `h ∈ ±Γ'`, then `g h g'⁻¹` fixes `∞`, so it is `±Tʲ`, and
`g' Γ' = T⁻ʲ g Γ'`. The orbits of the powers of `T` on the cosets are the cycles of `σinf`, so
the cycles of `σinf` are in bijection with the cusp orbits.

## Main results

* `TauCeti.ModularGroup.sameCycle_permT_iff`: two cosets lie in one cycle of `σinf` exactly when
  a power of `T` carries one to the other.
* `TauCeti.ModularGroup.cuspOrbitOfCoset_eq_iff`: two cosets have the same cusp orbit exactly
  when a power of `T` carries one to the other.
* `TauCeti.ModularGroup.cuspCount_eq_card_cuspOrbit`: the number of cusps is the number of cusp
  orbits of the image of `±Γ'` in `PSL(2, ℝ)`.
* `TauCeti.ModularGroup.cuspCount_eq_card_cuspOrbits`: the number of cusps is the number of
  Mathlib's cusp orbits of the image of `±Γ'` in `GL(2, ℝ)`.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics 228,
  Springer 2005, §3.8.
* G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press 1971, §1.6.
-/

open Equiv
open scoped MatrixGroups

public section

namespace TauCeti.ModularGroup

open _root_.ModularGroup

variable {n : ℕ} (Γ' : Subgroup PSL(2, ℤ))

/-- **The cycles of `σinf` are the orbits of the powers of `T`**: the cosets numbered `e q` and
`e q'` lie in one cycle of `permT Γ' e` exactly when `Tʲ q = q'` for some integer `j`. -/
theorem sameCycle_permT_iff (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) (q q' : PSL(2, ℤ) ⧸ Γ') :
    (permT Γ' e).SameCycle (e q) (e q') ↔ ∃ j : ℤ, (T : PSL(2, ℤ)) ^ j • q = q' := by
  simp only [Perm.SameCycle, permT, modularTriple_σinf, ← map_zpow,
    Equiv.permutationRepresentation_apply, e.symm_apply_apply, e.apply_eq_iff_eq]

/-- Two cosets of `Γ'` represented by `γ, γ' ∈ SL(2, ℤ)` are carried to each other by a power of
`T` exactly when `γ h γ'⁻¹` fixes `∞`, that is has vanishing lower-left entry, for some
`h ∈ ±Γ'`. This is the criterion `Subgroup.cuspOrbitOfSL2Z_eq_iff` for the cusp orbits of
`γ⁻¹ • ∞` and `γ'⁻¹ • ∞` to agree. -/
private theorem exists_T_zpow_smul_eq_iff (γ γ' : SL(2, ℤ)) :
    (∃ j : ℤ, (T : PSL(2, ℤ)) ^ j • ((γ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ') = (γ' : PSL(2, ℤ))) ↔
      ∃ h ∈ Γ'.liftSL, (γ * h * γ'⁻¹) 1 0 = 0 := by
  simp only [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, Subgroup.mem_liftSL]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨γ⁻¹ * T ^ (-j) * γ', ?_, by simp [mul_assoc, ModularGroup.coe_T_zpow]⟩
    simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_zpow, mul_assoc] using hj
  · rintro ⟨h, hh, hc⟩
    -- `γ h γ'⁻¹` fixes `∞`, so it is `±Tᵐ`, and its image in `PSL(2, ℤ)` is that of `Tᵐ`.
    obtain ⟨m, hm⟩ : ∃ m : ℤ, ((γ * h * γ'⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)) = (T : PSL(2, ℤ)) ^ m := by
      generalize γ * h * γ'⁻¹ = g at hc ⊢
      rcases ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hc with hT | hT
      · exact ⟨g 0 1, by
          rw [← QuotientGroup.mk_zpow, Matrix.ProjectiveSpecialLinearGroup.mk_eq_mk_iff]
          exact .inl hT.symm⟩
      · exact ⟨-g 0 1, by
          rw [← QuotientGroup.mk_zpow, Matrix.ProjectiveSpecialLinearGroup.mk_eq_mk_iff]
          exact .inr (neg_eq_iff_eq_neg.mpr hT).symm⟩
    refine ⟨-m, ?_⟩
    have hh' : (h : PSL(2, ℤ)) = (γ : PSL(2, ℤ))⁻¹ * (T : PSL(2, ℤ)) ^ m * γ' := by
      rw [← hm, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      group
    rw [hh'] at hh
    simpa [mul_assoc] using hh

/-- **The cusp orbit of a coset**: the coset `g Γ'` goes to the cusp orbit of `g⁻¹ • ∞` for the
effective image of the full preimage `±Γ'` in `PSL(2, ℝ)`. It is read on representatives by
`TauCeti.ModularGroup.cuspOrbitOfCoset_mk`. -/
noncomputable def cuspOrbitOfCoset [Γ'.FiniteIndex] (q : PSL(2, ℤ) ⧸ Γ') :
    (Γ'.liftSL.map sl2zToPSL2R).CuspOrbit :=
  Γ'.liftSL.cuspOrbitOfSL2Z (Quotient.out (Quotient.out q))⁻¹

variable [Γ'.FiniteIndex]

/-- The coset of `γ ∈ SL(2, ℤ)` goes to the cusp orbit of `γ⁻¹ • ∞`. -/
@[simp]
theorem cuspOrbitOfCoset_mk (γ : SL(2, ℤ)) :
    cuspOrbitOfCoset Γ' ((γ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ') = Γ'.liftSL.cuspOrbitOfSL2Z γ⁻¹ := by
  rw [cuspOrbitOfCoset, Subgroup.cuspOrbitOfSL2Z_eq_iff, inv_inv, ← exists_T_zpow_smul_eq_iff]
  refine ⟨0, ?_⟩
  rw [zpow_zero, one_smul, QuotientGroup.out_eq', QuotientGroup.out_eq']

/-- **Two cosets have the same cusp orbit** exactly when a power of `T` carries one to the other. -/
theorem cuspOrbitOfCoset_eq_iff (q q' : PSL(2, ℤ) ⧸ Γ') :
    cuspOrbitOfCoset Γ' q = cuspOrbitOfCoset Γ' q' ↔ ∃ j : ℤ, (T : PSL(2, ℤ)) ^ j • q = q' := by
  induction q using QuotientGroup.induction_on with | H g =>
  induction q' using QuotientGroup.induction_on with | H g' =>
  induction g using QuotientGroup.induction_on with | H γ =>
  induction g' using QuotientGroup.induction_on with | H γ' =>
  rw [cuspOrbitOfCoset_mk, cuspOrbitOfCoset_mk, Subgroup.cuspOrbitOfSL2Z_eq_iff, inv_inv,
    ← exists_T_zpow_smul_eq_iff]

/-- Translating a coset by a power of `T` does not change its cusp orbit. -/
@[simp]
theorem cuspOrbitOfCoset_T_zpow_smul (j : ℤ) (q : PSL(2, ℤ) ⧸ Γ') :
    cuspOrbitOfCoset Γ' ((T : PSL(2, ℤ)) ^ j • q) = cuspOrbitOfCoset Γ' q :=
  (cuspOrbitOfCoset_eq_iff Γ' _ _).mpr ⟨-j, by rw [smul_smul, ← zpow_add, neg_add_cancel,
    zpow_zero, one_smul]⟩

/-- Every cusp orbit of `±Γ'` is the cusp orbit of a coset. -/
theorem cuspOrbitOfCoset_surjective : Function.Surjective (cuspOrbitOfCoset Γ') := fun C ↦
  (Γ'.liftSL.cuspOrbitOfSL2Z_surjective C).elim fun γ hγ ↦
    ⟨((γ⁻¹ : SL(2, ℤ)) : PSL(2, ℤ)), by rw [cuspOrbitOfCoset_mk, inv_inv, hγ]⟩

omit [Γ'.FiniteIndex]

/-- **The cusps are the cusp orbits.** The number of cusps of `Γ'`, the number of cycles of
`σinf`, is the number of cusp orbits of the effective image of `±Γ'` in `PSL(2, ℝ)`. -/
theorem cuspCount_eq_card_cuspOrbit (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspCount Γ' e = Nat.card (Γ'.liftSL.map sl2zToPSL2R).CuspOrbit := by
  have : Finite (PSL(2, ℤ) ⧸ Γ') := .of_equiv _ e.symm
  have : Γ'.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  rw [cuspCount_def, orbitCount_def, ← Nat.card_congr (Setoid.quotientKerEquivOfSurjective _
    ((cuspOrbitOfCoset_surjective Γ').comp e.symm.surjective))]
  refine Nat.card_congr (Quotient.congrRight fun i i' ↦ ?_)
  rw [Setoid.ker_def, Function.comp_apply, Function.comp_apply, cuspOrbitOfCoset_eq_iff,
    ← sameCycle_permT_iff, e.apply_symm_apply, e.apply_symm_apply]
  -- the relation of `Equiv.Perm.SameCycle.setoid` is `Equiv.Perm.SameCycle` by definition
  exact Iff.rfl

/-- **The cusps are Mathlib's cusp orbits.** The number of cusps of `Γ'`, the number of cycles of
`σinf`, is the number of cusp orbits `CuspOrbits` of the image of `±Γ'` in `GL(2, ℝ)`. -/
theorem cuspCount_eq_card_cuspOrbits (e : PSL(2, ℤ) ⧸ Γ' ≃ Fin n) :
    cuspCount Γ' e = Nat.card (CuspOrbits (Γ'.liftSL.map (Matrix.SpecialLinearGroup.mapGL ℝ))) := by
  have : Finite (PSL(2, ℤ) ⧸ Γ') := .of_equiv _ e.symm
  have : Γ'.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  rw [cuspCount_eq_card_cuspOrbit, Nat.card_congr Γ'.liftSL.cuspOrbitsEquivCuspOrbit]

end TauCeti.ModularGroup
