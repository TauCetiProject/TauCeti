/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.DiamondOperators
public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# Constant terms at the cusps

For an arithmetic subgroup `Γ` of determinant one (that is, contained in `SL₂(ℝ)`) and
`γ ∈ SL₂(ℤ)`, the constant term of a modular form at the cusp
represented by `γ` is the constant coefficient of the q-expansion of `f ∣ γ`.  We package this as
a linear functional.  We index by every representative, avoiding a choice of cusp
representatives; the common vanishing condition is intrinsic.  Bundling all of them gives the
linear map `ModularForm.constantTerms` to `SL₂(ℤ) → ℂ`.

The common kernel of these functionals is exactly the cusp-form submodule.  Restricting this
statement to a nebentypus space identifies the image of `S_k(N, χ)` inside `M_k(N, χ)` with the
common kernel there.  This is the linear-algebraic interface used to compare cusp forms with
Eisenstein series through their constant terms.

## Main definitions

* `ModularForm.constantTermAt`: the constant-term functional attached to an element of
  `SL₂(ℤ)`.
* `ModularForm.constantTerms`: all constant terms at once, as a linear map to `SL₂(ℤ) → ℂ`.

## Main results

* `ModularForm.mem_cuspFormSubmodule_iff_constantTermAt_eq_zero`: a modular form is cuspidal if
  and only if every translated constant term vanishes.
* `ModularForm.ker_constantTerms`: the kernel of `constantTerms` is the cusp-form submodule.
* `TauCeti.mem_range_cuspToModFormCharSpace_iff_constantTermAt_eq_zero`: the same
  characterization inside a nebentypus space.
* `TauCeti.range_cuspToModFormCharSpace_eq_ker_constantTerms`: the image of `S_k(N, χ)` in
  `M_k(N, χ)` is the kernel of `constantTerms` restricted to `M_k(N, χ)`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §3.1.
-/

public section

noncomputable section

open Complex CongruenceSubgroup Filter Matrix Matrix.SpecialLinearGroup ModularForm OnePoint
  UpperHalfPlane
open scoped CongruenceSubgroup MatrixGroups Pointwise

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

private local instance isArithmeticConjMapGL [Γ.IsArithmetic] (γ : SL(2, ℤ)) :
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • Γ).IsArithmetic := by
  simpa [← (Rat.castHom ℝ).algebraMap_toAlgebra, map_inv, map_mapGL]
    using Subgroup.IsArithmetic.conj Γ (mapGL ℚ γ)⁻¹

variable [Γ.HasDetOne] [Γ.IsArithmetic]

/-- The constant term of `f` at the cusp represented by `γ ∈ SL₂(ℤ)`, as a linear functional.

It is the constant coefficient after translating by `γ`.  The q-expansion uses the canonical
strict width at infinity of the conjugated arithmetic subgroup. -/
def constantTermAt (γ : SL(2, ℤ)) : ModularForm Γ k →ₗ[ℂ] ℂ :=
  let Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • Γ
  (PowerSeries.coeff 0).comp
    ((TauCeti.ModularForm.qExpansionLinearMap
      (Γγ.strictWidthInfty_pos_iff.mpr Fact.out) Γγ.strictWidthInfty_mem_strictPeriods k).comp
      (translateₗ (mapGL ℝ γ) (by simp)))

/-- The constant-term functional evaluates to the constant coefficient of the translated
q-expansion. -/
@[simp]
lemma constantTermAt_apply (γ : SL(2, ℤ)) (f : ModularForm Γ k) :
    constantTermAt γ f =
      (qExpansion (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • Γ).strictWidthInfty
        (translate f (mapGL ℝ γ))).coeff 0 := by
  rw [constantTermAt, LinearMap.comp_apply, LinearMap.comp_apply,
    TauCeti.ModularForm.qExpansionLinearMap_apply, translateₗ_apply]

/-- The constant term is the value at infinity of the translated modular form. -/
lemma constantTermAt_eq_valueAtInfty (γ : SL(2, ℤ)) (f : ModularForm Γ k) :
    constantTermAt γ f = valueAtInfty (translate f (mapGL ℝ γ)) := by
  let Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • Γ
  have hw : 0 < Γγ.strictWidthInfty := Γγ.strictWidthInfty_pos_iff.mpr Fact.out
  rw [constantTermAt_apply, qExpansion_coeff_zero hw
    (ModularFormClass.analyticAt_cuspFunction_zero (translate f (mapGL ℝ γ)) hw
      Γγ.strictWidthInfty_mem_strictPeriods)
    (SlashInvariantFormClass.periodic_comp_ofComplex (translate f (mapGL ℝ γ))
      Γγ.strictWidthInfty_mem_strictPeriods)]

/-- A modular form is cuspidal exactly when its constant term vanishes after every
`SL₂(ℤ)`-translate. -/
theorem mem_cuspFormSubmodule_iff_constantTermAt_eq_zero (f : ModularForm Γ k) :
    f ∈ cuspFormSubmodule Γ k ↔ ∀ γ : SL(2, ℤ), constantTermAt γ f = 0 := by
  rw [mem_cuspFormSubmodule_iff, isCuspForm_iff]
  constructor
  · intro hf γ
    rw [constantTermAt_eq_valueAtInfty]
    have hcγ : IsCusp (mapGL ℝ γ • ∞) Γ :=
      (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z Γ).mpr <| by
        rw [isCusp_SL2Z_iff']
        exact ⟨γ, rfl⟩
    exact (hf hcγ (mapGL ℝ γ) rfl).valueAtInfty_eq_zero
  · intro h c hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z
      ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z Γ).mp hc)]
    intro γ _
    have hcoeff := h γ
    rw [constantTermAt_eq_valueAtInfty] at hcoeff
    rw [SL_slash, ← ModularForm.coe_translate]
    exact isZeroAtImInfty_of_valueAtInfty_eq_zero (translate f (mapGL ℝ γ)) hcoeff

/-- All constant terms at once: the linear map sending `f` to `γ ↦ constantTermAt γ f`. -/
def constantTerms : ModularForm Γ k →ₗ[ℂ] SL(2, ℤ) → ℂ :=
  LinearMap.pi constantTermAt

@[simp]
lemma constantTerms_apply (f : ModularForm Γ k) (γ : SL(2, ℤ)) :
    constantTerms f γ = constantTermAt γ f := by
  rw [constantTerms, LinearMap.pi_apply]

/-- The common kernel of the constant-term functionals is the cusp-form submodule. -/
theorem ker_constantTerms : LinearMap.ker (constantTerms (Γ := Γ) (k := k)) =
    cuspFormSubmodule Γ k := by
  ext f
  rw [LinearMap.mem_ker, mem_cuspFormSubmodule_iff_constantTermAt_eq_zero, funext_iff]
  simp only [constantTerms_apply, Pi.zero_apply]

end ModularForm

namespace TauCeti

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-- Inside `M_k(N, χ)`, the common kernel of the cusp constant terms is precisely the image of
`S_k(N, χ)`. -/
theorem mem_range_cuspToModFormCharSpace_iff_constantTermAt_eq_zero
    (f : modFormCharSpace k χ) :
    f ∈ LinearMap.range (cuspToModFormCharSpace k χ) ↔
      ∀ γ : SL(2, ℤ), ModularForm.constantTermAt
        (Γ := (Gamma1 N).map (mapGL ℝ)) γ (f : ModularForm _ k) = 0 := by
  rw [← ModularForm.mem_cuspFormSubmodule_iff_constantTermAt_eq_zero]
  constructor
  · rintro ⟨g, rfl⟩
    rw [coe_cuspToModFormCharSpace]
    exact CuspForm.isCuspForm_toModularFormₗ
      (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
  · intro hf
    obtain ⟨g, hg⟩ := hf
    have hgmem : (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
        modFormCharSpace k χ := by
      rw [← CuspForm.toModularFormₗ_eq_coe, hg]
      exact f.2
    refine ⟨⟨g, (coe_mem_modFormCharSpace_iff k χ g).mp hgmem⟩, ?_⟩
    apply Subtype.ext
    rw [coe_cuspToModFormCharSpace]
    exact hg

/-- The image of `S_k(N, χ)` in `M_k(N, χ)` is the kernel of the constant terms restricted to
`M_k(N, χ)`. -/
theorem range_cuspToModFormCharSpace_eq_ker_constantTerms :
    LinearMap.range (cuspToModFormCharSpace k χ) =
      LinearMap.ker (ModularForm.constantTerms.comp (modFormCharSpace k χ).subtype) := by
  ext f
  rw [mem_range_cuspToModFormCharSpace_iff_constantTermAt_eq_zero, LinearMap.mem_ker,
    funext_iff]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, ModularForm.constantTerms_apply,
    Pi.zero_apply]

end TauCeti
