/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.DiamondOperators
public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.QExpansion.BigO

/-!
# Constant terms at the cusps

For an arithmetic subgroup `Γ` of determinant one (that is, contained in `SL₂(ℝ)`) and
`γ ∈ SL₂(ℤ)`, the constant term of a modular form at the cusp
represented by `γ` is the constant coefficient of the q-expansion of `f ∣ γ`.  We package this as
a linear functional.  We index by every representative, avoiding a choice of cusp
representatives; the common vanishing condition is intrinsic.  Bundling all of them gives the
linear map `ModularForm.constantTerms` to `SL₂(ℤ) → ℂ`.

The constant term at `γ` depends only on the cusp `γ ∞` and on the sign of `γ`: it is unchanged
when `γ` is multiplied on the left by an element of `Γ` or on the right by a power of
`T = [1, 1; 0, 1]`, and replacing `γ` by `-γ` multiplies it by `(-1)^k`. When `Γ` contains the
principal congruence subgroup `Γ(N)`, which is normal in `SL₂(ℤ)`, it therefore depends only on
the bottom row of `γ⁻¹` modulo `N`: for `γ = [a, b; c, d]` this row is `(-c, a)`, which encodes
the cusp `a / c` modulo `N`.

The common kernel of these functionals is exactly the cusp-form submodule.  Restricting this
statement to a nebentypus space identifies the image of `S_k(N, χ)` inside `M_k(N, χ)` with the
common kernel there.  This is the linear-algebraic interface used to compare cusp forms with
Eisenstein series through their constant terms.

## Main definitions

* `ModularForm.constantTermAt`: the constant-term functional attached to an element of
  `SL₂(ℤ)`.
* `ModularForm.constantTerms`: all constant terms at once, as a linear map to `SL₂(ℤ) → ℂ`.

## Main results

* `ModularForm.tendsto_translate_constantTermAt`: `f ∣ γ` tends to the constant term at `i∞`.
* `ModularForm.constantTermAt_mul_left`, `ModularForm.constantTermAt_mul_T_zpow`,
  `ModularForm.constantTermAt_neg`: the dependence of the constant term on the representative.
* `ModularForm.constantTermAt_eq_of_vecMul_inv_eq`: on a group containing `Γ(N)`, the constant
  term at `γ` depends only on the bottom row of `γ⁻¹` modulo `N`.
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
open scoped CongruenceSubgroup MatrixGroups Pointwise Topology

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

/-- The translate `f ∣ γ` tends to the constant term of `f` at `γ` at `i∞`. -/
theorem tendsto_translate_constantTermAt (γ : SL(2, ℤ)) (f : ModularForm Γ k) :
    Tendsto (translate f (mapGL ℝ γ)) atImInfty (𝓝 (constantTermAt γ f)) := by
  let Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • Γ
  rw [constantTermAt_eq_valueAtInfty]
  exact TauCeti.ModularFormClass.tendsto_valueAtInfty _
    (Γγ.strictWidthInfty_pos_iff.mpr Fact.out) Γγ.strictWidthInfty_mem_strictPeriods

/-- Multiplying the representative on the left by an element of `Γ` does not change the
constant term. -/
theorem constantTermAt_mul_left {h : SL(2, ℤ)} (hh : mapGL ℝ h ∈ Γ) (γ : SL(2, ℤ))
    (f : ModularForm Γ k) : constantTermAt (h * γ) f = constantTermAt γ f := by
  rw [constantTermAt_eq_valueAtInfty, constantTermAt_eq_valueAtInfty, coe_translate,
    coe_translate, map_mul, SlashAction.slash_mul, SlashInvariantFormClass.slash_action_eq f _ hh]

/-- Multiplying the representative on the right by a power of `T` does not change the constant
term, since slashing by `T ^ j` is the translation `τ ↦ τ + j`. -/
theorem constantTermAt_mul_T_zpow (γ : SL(2, ℤ)) (j : ℤ) (f : ModularForm Γ k) :
    constantTermAt (γ * ModularGroup.T ^ j) f = constantTermAt γ f := by
  refine tendsto_nhds_unique (tendsto_translate_constantTermAt _ f) ?_
  have hT : Tendsto (fun τ : ℍ ↦ (j : ℝ) +ᵥ τ) atImInfty atImInfty := by
    simpa [atImInfty, tendsto_comap_iff, Function.comp_def] using tendsto_comap
  convert (tendsto_translate_constantTermAt γ f).comp hT using 1
  ext τ
  rw [coe_translate, map_mul, SlashAction.slash_mul, Function.comp_apply, coe_translate,
    TauCeti.ModularGroup.mapGL_T_zpow_eq_upperRightHom,
    TauCeti.ModularForm.slash_upperRightHom_apply]

/-- Negating the representative multiplies the constant term by `(-1)^k`. -/
theorem constantTermAt_neg (γ : SL(2, ℤ)) (f : ModularForm Γ k) :
    constantTermAt (-γ) f = (-1) ^ k * constantTermAt γ f := by
  refine tendsto_nhds_unique (tendsto_translate_constantTermAt _ f) ?_
  convert (tendsto_translate_constantTermAt γ f).const_mul ((-1 : ℂ) ^ k) using 1
  ext τ
  have hneg : mapGL ℝ (-γ) = mapGL ℝ γ * (-1) := by
    rw [← mapGL_neg_one (R := ℤ), ← map_mul, mul_neg_one]
  rw [coe_translate, coe_translate, hneg, SlashAction.slash_mul, ModularForm.slash_neg_one]
  rw [Pi.smul_apply, smul_eq_mul]

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

/-- If `Γ` contains `Γ(N)`, the constant term at `γ` depends only on the bottom row of `γ⁻¹`
modulo `N`. For `γ = [a, b; c, d]` that row is `(-c, a)`, so the constant term depends only on the
cusp `a / c` modulo `N`. -/
theorem constantTermAt_eq_of_vecMul_inv_eq {N : ℕ} (hΓ : (Γ(N) : Subgroup (GL (Fin 2) ℝ)) ≤ Γ)
    {γ₁ γ₂ : SL(2, ℤ)}
    (h : ((![0, 1] : Fin 2 → ZMod N) ᵥ* (γ₁⁻¹ : SL(2, ℤ)) : Fin 2 → ZMod N) =
      ![0, 1] ᵥ* (γ₂⁻¹ : SL(2, ℤ))) (f : ModularForm Γ k) :
    constantTermAt γ₁ f = constantTermAt γ₂ f := by
  -- `m = γ₂⁻¹ γ₁` is `[1, j; 0, 1]` modulo `N` for `j = m 0 1`, so `m T⁻ʲ ∈ Γ(N)` and
  -- `γ₁ = (γ₂ (m T⁻ʲ) γ₂⁻¹) γ₂ Tʲ` with `γ₂ (m T⁻ʲ) γ₂⁻¹ ∈ Γ(N)` by normality.
  obtain ⟨m, hm⟩ : ∃ m : SL(2, ℤ), m = γ₂⁻¹ * γ₁ := ⟨_, rfl⟩
  have hrow (j : Fin 2) :
      (((γ₁⁻¹ : SL(2, ℤ)) 1 j : ℤ) : ZMod N) = (((γ₂⁻¹ : SL(2, ℤ)) 1 j : ℤ) : ZMod N) := by
    have := congrFun h j
    simp only [vecMul, dotProduct, Fin.sum_univ_two, cons_val_zero, cons_val_one, zero_mul,
      one_mul, zero_add, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, eq_intCast] at this
    exact this
  have hentry (g : SL(2, ℤ)) (j : Fin 2) : (g⁻¹ * γ₁ : SL(2, ℤ)) 1 j =
      (g⁻¹ : SL(2, ℤ)) 1 0 * γ₁ 0 j + (g⁻¹ : SL(2, ℤ)) 1 1 * γ₁ 1 j := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, mul_apply, Fin.sum_univ_two]
  have hm1 (j : Fin 2) : ((m 1 j : ℤ) : ZMod N) = (((1 : SL(2, ℤ)) 1 j : ℤ) : ZMod N) := by
    rw [← inv_mul_cancel γ₁, hm, hentry, hentry]
    push_cast
    rw [hrow 0, hrow 1]
  have h10 : (m 1 0 : ZMod N) = 0 := by simpa using hm1 0
  have h11 : (m 1 1 : ZMod N) = 1 := by simpa using hm1 1
  have h00 : (m 0 0 : ZMod N) = 1 := by
    have hdet := congrArg (Int.cast : ℤ → ZMod N) (Matrix.SpecialLinearGroup.det_coe m)
    rw [Matrix.det_fin_two] at hdet
    push_cast at hdet
    rw [h10, h11] at hdet
    simpa using hdet
  have hg : m * ModularGroup.T ^ (-m 0 1) ∈ Γ(N) := by
    rw [Gamma_mem]
    simp only [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, mul_apply,
      Fin.sum_univ_two]
    simp [h00, h10, h11]
  have hγ : γ₁ = (γ₂ * (m * ModularGroup.T ^ (-m 0 1)) * γ₂⁻¹) * γ₂ *
      ModularGroup.T ^ (m 0 1) := by
    simp [hm, mul_assoc]
  rw [hγ, constantTermAt_mul_T_zpow, constantTermAt_mul_left]
  exact hΓ (Subgroup.mem_map_of_mem _ ((Gamma_normal N).conj_mem _ hg γ₂))

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
