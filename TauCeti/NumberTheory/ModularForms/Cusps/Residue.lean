/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Cusps.ConstantTerm
public import TauCeti.NumberTheory.ModularForms.Norm.Cusps
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# The weight-two relation between cusp constant terms

The constant term of a modular form at a cusp translation orbit is independent of the
representative coset. The constant term of its trace to level one is the sum of these
constant terms, each multiplied by the width of its orbit. Since there are no level-one
modular forms of weight two, this weighted sum vanishes in weight two.

We use the existing `CuspTranslationOrbit` and its full-coset convention: when the level
is an integral subgroup containing `-I`, these are the ordinary cusps and their widths.
Otherwise a cusp of the integral intersection can appear twice, or its translation width
can be twice its projective width. No choice of projective
coset representatives is made. The relation holds for every subgroup of finite relative
index in `SL₂(ℤ)`, with the cusp-form criterion stated for arithmetic determinant-one levels.

Consequently, to test cuspidality in weight two it suffices to check all but one of the
cusp translation constant terms. This is the linear restriction on the boundary data in
the weight-two cusp–Eisenstein decomposition.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, §§3.1 and 4.2.

The proof uses Mathlib's trace and `ModularForm.levelOne_weight_two_rank_zero`, together
with the cusp translation decomposition already used for the general-level valence formula.
-/

public noncomputable section

open UpperHalfPlane Filter Function SlashInvariantForm
open scoped MatrixGroups Topology ModularForm

namespace TauCeti.ModularForm

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex 𝒮ℒ]
variable {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}

section SlashInvariant

variable [SlashInvariantFormClass F 𝒢 k]

/-- The constant term at a cusp translation orbit, computed from any of its coset factors. -/
def constantTermAtCuspTranslationOrbit (f : F) (c : CuspTranslationOrbit 𝒢) : ℂ :=
  valueAtInfty (quotientFunc f c.out)

omit [𝒢.IsFiniteRelIndex 𝒮ℒ] in
/-- The defining expression for the constant term at a cusp translation orbit. -/
theorem constantTermAtCuspTranslationOrbit_def (f : F) (c : CuspTranslationOrbit 𝒢) :
    constantTermAtCuspTranslationOrbit f c = valueAtInfty (quotientFunc f c.out) := (rfl)

end SlashInvariant

variable [ModularFormClass F 𝒢 k]

/-- The constant term may be read at any coset representing the cusp translation orbit. -/
@[simp]
theorem constantTermAtCuspTranslationOrbit_mk (f : F)
    (q : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ) :
    constantTermAtCuspTranslationOrbit f (⟦q⟧ : CuspTranslationOrbit 𝒢) =
      valueAtInfty (quotientFunc f q) := by
  obtain ⟨h, hh⟩ := (MulAction.orbitRel_apply (G := Subgroup.zpowers TSL)).mp
    (Quotient.eq.mp (Quotient.out_eq (⟦q⟧ : CuspTranslationOrbit 𝒢)))
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h.2
  have heq : TSL ^ j • q = (⟦q⟧ : CuspTranslationOrbit 𝒢).out := by
    simpa only [hj, Subgroup.smul_def] using hh
  rw [constantTermAtCuspTranslationOrbit_def, ← heq]
  exact valueAtInfty_quotientFunc_TSL_zpow_smul f q j

/-- At the orbit representing infinity, the constant term is the value at infinity of `f`. -/
@[simp]
theorem constantTermAtCuspTranslationOrbit_mk_one (f : F) :
    constantTermAtCuspTranslationOrbit f
        (⟦(QuotientGroup.mk 1 : 𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)⟧ : CuspTranslationOrbit 𝒢) =
      valueAtInfty f := by
  simp [constantTermAtCuspTranslationOrbit_mk]

/-- The constant term is the zeroth coefficient in the orbit's own width parameter. -/
theorem constantTermAtCuspTranslationOrbit_eq_qExpansion_coeff_zero (f : F)
    (c : CuspTranslationOrbit 𝒢) :
    constantTermAtCuspTranslationOrbit f c =
      (qExpansion (cuspTranslationOrbitWidth c : ℝ) (quotientFunc f c.out)).coeff 0 := by
  have hw : (0 : ℝ) < cuspTranslationOrbitWidth c := by
    exact_mod_cast cuspTranslationOrbitWidth_pos c
  have hper := periodic_quotientFunc_out f c
  have hana := analyticAt_cuspFunction_zero hw hper
    (TauCeti.SlashInvariantForm.mdifferentiable_quotientFunc f c.out)
    (TauCeti.SlashInvariantForm.isBoundedAtImInfty_quotientFunc f c.out)
  rw [qExpansion_coeff_zero hw hana hper, constantTermAtCuspTranslationOrbit_def]

/-- The constant term of the trace to level one is the width-weighted sum of the cusp
translation constant terms. -/
theorem valueAtInfty_trace_eq_sum_width_mul_constantTerm (f : F) :
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
theorem sum_width_mul_constantTerm_eq_zero (f : F) :
    ∑ c : CuspTranslationOrbit 𝒢,
      (cuspTranslationOrbitWidth c : ℂ) * constantTermAtCuspTranslationOrbit f c = 0 := by
  rw [← valueAtInfty_trace_eq_sum_width_mul_constantTerm]
  have hzero : _root_.ModularForm.trace 𝒮ℒ f = 0 :=
    (rank_zero_iff_forall_zero.mp _root_.ModularForm.levelOne_weight_two_rank_zero) _
  rw [hzero]
  exact (tendsto_const_nhds : Tendsto (fun _ : ℍ ↦ (0 : ℂ)) atImInfty (𝓝 0)).limUnder_eq

/-- In weight two, vanishing of all other cusp translation constant terms forces vanishing at
the remaining orbit as well. -/
theorem constantTerm_eq_zero_of_forall_ne (f : F) (c : CuspTranslationOrbit 𝒢)
    (h : ∀ c' ≠ c, constantTermAtCuspTranslationOrbit f c' = 0) :
    constantTermAtCuspTranslationOrbit f c = 0 := by
  classical
  have hsum := sum_width_mul_constantTerm_eq_zero f
  rw [Finset.sum_eq_single c (fun c' _ hc' ↦ by rw [h c' hc', mul_zero])
    (by simp)] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left
    (Nat.cast_ne_zero.mpr (NeZero.ne (cuspTranslationOrbitWidth c)))

end TauCeti.ModularForm

namespace TauCeti.ModularForm

open _root_.ModularForm _root_.Matrix.SpecialLinearGroup

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] [𝒢.HasDetOne] {k : ℤ}

/-- The constant term at the orbit of an integral matrix coset is the constant term at the
cusp represented by its inverse. -/
@[simp]
theorem constantTermAtCuspTranslationOrbit_mk_mapGL (f : ModularForm 𝒢 k) (γ : SL(2, ℤ)) :
    TauCeti.ModularForm.constantTermAtCuspTranslationOrbit f
        (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ) :
          𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)⟧ : CuspTranslationOrbit 𝒢) = constantTermAt γ⁻¹ f := by
  rw [constantTermAtCuspTranslationOrbit_mk, quotientFunc_mk,
    constantTermAt_eq_valueAtInfty, _root_.ModularForm.coe_translate,
    MonoidHom.coe_rangeRestrict, map_inv]

/-- A modular form is cuspidal exactly when its constant terms at all cusp translation
orbits vanish. -/
theorem mem_cuspFormSubmodule_iff_constantTermAtCuspTranslationOrbit_eq_zero
    (f : ModularForm 𝒢 k) :
    f ∈ cuspFormSubmodule 𝒢 k ↔
      ∀ c : CuspTranslationOrbit 𝒢,
        TauCeti.ModularForm.constantTermAtCuspTranslationOrbit f c = 0 := by
  rw [mem_cuspFormSubmodule_iff_constantTermAt_eq_zero]
  constructor
  · intro hf c
    induction c using Quotient.inductionOn with
    | h q =>
      induction q using Quotient.inductionOn with
      | h x =>
        obtain ⟨γ, hγ⟩ := x.property
        have hx : x = (mapGL ℝ).rangeRestrict γ := Subtype.ext hγ.symm
        rw [hx, constantTermAtCuspTranslationOrbit_mk_mapGL]
        exact hf γ⁻¹
  · intro hf γ
    simpa only [constantTermAtCuspTranslationOrbit_mk_mapGL, inv_inv] using
      hf (⟦(QuotientGroup.mk ((mapGL ℝ).rangeRestrict γ⁻¹) :
        𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)⟧ : CuspTranslationOrbit 𝒢)

/-- **A weight-two cusp-form test with one cusp omitted.** Vanishing at any one cusp
translation orbit follows from vanishing at all the others. -/
theorem mem_cuspFormSubmodule_iff_forall_ne_constantTerm_eq_zero (f : ModularForm 𝒢 2)
    (c : CuspTranslationOrbit 𝒢) :
    f ∈ cuspFormSubmodule 𝒢 2 ↔
      ∀ c' ≠ c, TauCeti.ModularForm.constantTermAtCuspTranslationOrbit f c' = 0 := by
  rw [mem_cuspFormSubmodule_iff_constantTermAtCuspTranslationOrbit_eq_zero]
  refine ⟨fun h c' _ ↦ h c', fun h c' ↦ ?_⟩
  by_cases hc' : c' = c
  · subst c'
    exact constantTerm_eq_zero_of_forall_ne f c h
  · exact h c' hc'

end TauCeti.ModularForm
