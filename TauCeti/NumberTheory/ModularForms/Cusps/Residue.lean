/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.ConstantTerm
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# The weight-two relation between cusp constant terms

The constant term of the level-one trace (`ModularForm.trace`) is the sum of the cusp
translation constant terms, each multiplied by the width of its orbit. Since there are no
level-one modular forms of weight two (`ModularForm.levelOne_weight_two_rank_zero`), this
weighted sum vanishes in weight two.

We use the existing `CuspTranslationOrbit` and its full-coset convention: when the level
is an integral subgroup containing `-I`, these are the ordinary cusps and their widths.
Otherwise a cusp of the integral intersection can appear twice, or its translation width
can be twice its projective width. No choice of projective
coset representatives is made. The relation holds for every subgroup of finite relative
index in `SL₂(ℤ)`, with the cusp-form criterion stated for arithmetic determinant-one levels.

Consequently, to test cuspidality in weight two it suffices to check all but one of the
cusp translation constant terms. This is the linear restriction on the boundary data in
the weight-two cusp–Eisenstein decomposition.

## Main results

The residue relation and cusp-form test are in `TauCeti.ModularForm`.

* `weight_two_sum_cuspTranslationOrbitWidth_mul_constantTermAtCuspTranslationOrbit_eq_zero`:
  width-weighted residue relation in weight two.
* `weight_two_mem_cuspFormSubmodule_iff_forall_ne_constantTermAtCuspTranslationOrbit_eq_zero`:
  a weight-two modular form is cuspidal if and only if its constant terms vanish at every
  cusp translation orbit except any one chosen orbit.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §§3.1 and 4.2.
-/

public noncomputable section

open UpperHalfPlane Filter Function SlashInvariantForm
open scoped MatrixGroups Topology ModularForm

namespace TauCeti.ModularForm

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex 𝒮ℒ]
variable {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}
variable [ModularFormClass F 𝒢 k]

/-- The constant term of the trace to level one is the width-weighted sum of the cusp
translation constant terms. -/
theorem valueAtInfty_trace_eq_sum_cuspTranslationOrbitWidth_mul_constantTermAtCuspTranslationOrbit
    (f : F) :
    valueAtInfty (_root_.ModularForm.trace 𝒮ℒ f) =
      ∑ c : CuspTranslationOrbit 𝒢,
        (cuspTranslationOrbitWidth c : ℂ) * constantTermAtCuspTranslationOrbit f c := by
  classical
  let _ : Fintype (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) := Fintype.ofFinite _
  have hlim := tendsto_finsetSum Finset.univ fun q _ ↦
    tendsto_quotientFunc_valueAtInfty f q
  have hsum : valueAtInfty (_root_.ModularForm.trace 𝒮ℒ f) =
      ∑ q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ, valueAtInfty (quotientFunc f q) := by
    rw [_root_.ModularForm.coe_trace]
    simpa only [valueAtInfty, Finset.sum_fn] using hlim.limUnder_eq
  rw [hsum, ← Equiv.sum_comp (Subgroup.quotientEquivSigmaZMod (𝒢.subgroupOf 𝒮ℒ) TSL).symm,
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  have hwc : cuspTranslationOrbitWidth c = minimalPeriod (TSL • ·) c.out := by
    simpa only [Quotient.out_eq] using cuspTranslationOrbitWidth_mk c.out
  simp only [Subgroup.quotientEquivSigmaZMod_symm_apply,
    valueAtInfty_quotientFunc_TSL_zpow_smul, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul, constantTermAtCuspTranslationOrbit_def,
    hwc]

end TauCeti.ModularForm

namespace TauCeti.ModularForm

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex 𝒮ℒ]
variable {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F 𝒢 2]

/-- **The weight-two residue relation**: the width-weighted sum of the constant terms at all
cusp translation orbits is zero. -/
theorem weight_two_sum_cuspTranslationOrbitWidth_mul_constantTermAtCuspTranslationOrbit_eq_zero
    (f : F) :
    ∑ c : CuspTranslationOrbit 𝒢,
      (cuspTranslationOrbitWidth c : ℂ) * constantTermAtCuspTranslationOrbit f c = 0 := by
  rw [← valueAtInfty_trace_eq_sum_cuspTranslationOrbitWidth_mul_constantTermAtCuspTranslationOrbit]
  have hzero : _root_.ModularForm.trace 𝒮ℒ f = 0 :=
    (rank_zero_iff_forall_zero.mp _root_.ModularForm.levelOne_weight_two_rank_zero) _
  rw [hzero]
  exact (tendsto_const_nhds : Tendsto (fun _ : ℍ ↦ (0 : ℂ)) atImInfty (𝓝 0)).limUnder_eq

/-- In weight two, vanishing of all other cusp translation constant terms forces vanishing at
the remaining orbit as well. -/
theorem weight_two_constantTermAtCuspTranslationOrbit_eq_zero_of_forall_ne (f : F)
    (c : CuspTranslationOrbit 𝒢)
    (h : ∀ c' ≠ c, constantTermAtCuspTranslationOrbit f c' = 0) :
    constantTermAtCuspTranslationOrbit f c = 0 := by
  classical
  have hsum :=
    weight_two_sum_cuspTranslationOrbitWidth_mul_constantTermAtCuspTranslationOrbit_eq_zero f
  rw [Finset.sum_eq_single c (fun c' _ hc' ↦ by rw [h c' hc', mul_zero])
    (by simp)] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left
    (Nat.cast_ne_zero.mpr (NeZero.ne (cuspTranslationOrbitWidth c)))

end TauCeti.ModularForm

namespace TauCeti.ModularForm

open _root_.ModularForm _root_.Matrix.SpecialLinearGroup

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] [𝒢.HasDetOne] {k : ℤ}

/-- **A weight-two cusp-form test with one cusp omitted.** Vanishing at any one cusp
translation orbit follows from vanishing at all the others. -/
theorem weight_two_mem_cuspFormSubmodule_iff_forall_ne_constantTermAtCuspTranslationOrbit_eq_zero
    {f : ModularForm 𝒢 2}
    (c : CuspTranslationOrbit 𝒢) :
    f ∈ cuspFormSubmodule 𝒢 2 ↔
      ∀ c' ≠ c, TauCeti.ModularForm.constantTermAtCuspTranslationOrbit f c' = 0 := by
  rw [mem_cuspFormSubmodule_iff_constantTermAtCuspTranslationOrbit_eq_zero]
  refine ⟨fun h c' _ ↦ h c', fun h c' ↦ ?_⟩
  by_cases hc' : c' = c
  · subst c'
    exact weight_two_constantTermAtCuspTranslationOrbit_eq_zero_of_forall_ne f c h
  · exact h c' hc'

end TauCeti.ModularForm
