/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import TauCeti.NumberTheory.ModularForms.Norm.Trace
public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# The Sturm bound for finite-index subgroups of `SL(2, ℤ)`

For `𝒢 ≤ GL(2, ℝ)` of finite relative index in `𝒮ℒ` with discrete strict periods and
`f : ModularForm 𝒢 k`, if the `q`-expansion of `f` at the cusp `∞` (with cusp width
`𝒢.strictWidthInfty`) has order strictly greater than `k · [𝒮ℒ : 𝒢 ⊓ 𝒮ℒ] / 12`, then
`f = 0`.

The proof lifts the level-one bound `ModularForm.sturm_bound_levelOne` through the norm map:
the norm of `f` vanishes exactly when `f` does, and the norm-order comparison
`TauCeti.ModularForm.qExpansion_order_le_qExpansion_norm_order`, derived from the
decomposition `TauCeti.ModularForm.qExpansion_one_norm_order_eq`, carries sufficient
vanishing of `f` at `∞` to the norm.

## Main declarations

* `ModularForm.sturm_bound_finiteIndex`: the Sturm bound for finite relative index.
* `ModularForm.sturm_bound_finiteIndex_SL2Z`: the classical form for finite-index
  subgroups of `SL(2, ℤ)`.
* `ModularForm.eq_of_sturm_bound`: forms agreeing up to the bound are equal.
* `TauCeti.finiteDimensional_modularForm_finiteIndex`: `ModularForm 𝒢 k` is
  finite-dimensional over `ℂ`.

## References

* [Mathlib PR #39000](https://github.com/leanprover-community/mathlib4/pull/39000)
  (Chris Birkbeck) — the upstream draft this file ports onto the current Mathlib pin.
-/

public noncomputable section

open UpperHalfPlane Complex Function SlashInvariantForm Periodic Subgroup

open scoped ModularForm Topology Filter Manifold MatrixGroups

namespace ModularForm

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex 𝒮ℒ] {k : ℤ} (f : ModularForm 𝒢 k)

/-- **Sturm bound for subgroups of `GL(2, ℝ)` of finite relative index in `SL(2, ℤ)`** with
discrete strict periods. A modular form of weight `k` whose `q`-expansion at the cusp `∞`
has order strictly greater than `k · [𝒮ℒ : 𝒢 ⊓ 𝒮ℒ] / 12` is identically zero. -/
theorem sturm_bound_finiteIndex [DiscreteTopology 𝒢.strictPeriods]
    (h : (↑((k * Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)).toNat / 12) : ℕ∞) <
      (qExpansion 𝒢.strictWidthInfty f).order) : f = 0 := by
  rw [← FunLike.coe_zero_iff, ← _root_.ModularForm.norm_eq_zero_iff (ℋ := 𝒮ℒ)]
  exact sturm_bound_levelOne <|
    h.trans_le (TauCeti.ModularForm.qExpansion_order_le_qExpansion_norm_order f)

/-- **Classical Sturm bound for finite-index subgroups of `SL(2, ℤ)`.** -/
theorem sturm_bound_finiteIndex_SL2Z {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    {k : ℤ} (f : ModularForm (Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    (h : (↑((k * Γ.index).toNat / 12) : ℕ∞) <
      (qExpansion (Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)).strictWidthInfty f).order) :
    f = 0 := by
  have h_index :
      Nat.card (𝒮ℒ ⧸ (Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)).subgroupOf 𝒮ℒ) = Γ.index := by
    rw [← Subgroup.index_eq_card, ← Subgroup.relIndex,
      MonoidHom.range_eq_map (Matrix.SpecialLinearGroup.mapGL ℝ), ← Subgroup.relIndex_comap,
      Subgroup.comap_map_eq_self_of_injective Matrix.SpecialLinearGroup.mapGL_injective,
      Subgroup.relIndex_top_right]
  exact sturm_bound_finiteIndex f (h_index ▸ h)

/-- **Modular forms agreeing up to the Sturm bound are equal**: two weight-`k` forms whose
`q`-expansions at `∞` agree in every coefficient up to `k · [𝒮ℒ : 𝒢 ⊓ 𝒮ℒ] / 12` coincide. -/
theorem eq_of_sturm_bound [DiscreteTopology 𝒢.strictPeriods]
    (g : ModularForm 𝒢 k)
    (h : ∀ i ≤ (k * Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)).toNat / 12,
      PowerSeries.coeff i (qExpansion 𝒢.strictWidthInfty f) =
        PowerSeries.coeff i (qExpansion 𝒢.strictWidthInfty g)) : f = g := by
  rw [← sub_eq_zero]
  refine sturm_bound_finiteIndex (f - g) (lt_of_lt_of_le
    (by exact_mod_cast Nat.lt_succ_self _) (PowerSeries.nat_le_order _ _ fun i hi ↦ ?_))
  rw [FunLike.coe_sub, _root_.ModularForm.qExpansion_sub
    TauCeti.Subgroup.strictWidthInfty_pos_of_finiteRelIndex 𝒢.strictWidthInfty_mem_strictPeriods,
    map_sub, sub_eq_zero]
  exact h i (Nat.lt_succ_iff.mp hi)

end ModularForm

namespace TauCeti

/-- **Finite-dimensionality of modular forms.** As a corollary of the Sturm bound, the space
`ModularForm 𝒢 k` is finite-dimensional over `ℂ` for any subgroup `𝒢 ≤ GL(2, ℝ)` of finite
relative index in `𝒮ℒ` with determinant-one elements and discrete strict periods. -/
instance finiteDimensional_modularForm_finiteIndex
    {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.HasDetOne] [𝒢.IsFiniteRelIndex 𝒮ℒ]
    [DiscreteTopology 𝒢.strictPeriods] {k : ℤ} :
    Module.Finite ℂ (ModularForm 𝒢 k) := by
  set N : ℕ := (k * Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ)).toNat / 12 + 1
  refine Module.Finite.of_injective
    (((PowerSeries.trunc N).comp (ModularForm.qExpansionLinearMap
        Subgroup.strictWidthInfty_pos_of_finiteRelIndex
        𝒢.strictWidthInfty_mem_strictPeriods k)).codRestrict
      (Polynomial.degreeLT ℂ N) fun f ↦
        Polynomial.mem_degreeLT.mpr (PowerSeries.degree_trunc_lt _ _))
    ((injective_iff_map_eq_zero _).mpr fun f hf ↦ ?_)
  refine ModularForm.sturm_bound_finiteIndex f (lt_of_lt_of_le
    (by exact_mod_cast Nat.lt_succ_self _) (PowerSeries.nat_le_order _ _ fun i hi ↦ ?_))
  have hval : PowerSeries.trunc N (qExpansion 𝒢.strictWidthInfty f) = 0 := by
    simpa using congrArg Subtype.val hf
  have hcoeff := congrArg (fun p ↦ Polynomial.coeff p i) hval
  rwa [PowerSeries.coeff_trunc, ite_eq_left hi, Polynomial.coeff_zero] at hcoeff

/-- **Finite-dimensionality of cusp forms.** A cusp form is a modular form, injectively, so this
is `TauCeti.finiteDimensional_modularForm_finiteIndex` transported along
`CuspForm.toModularFormₗ`, under exactly the same hypotheses.

It is stated here rather than at its use sites because cusp-form finite-dimensionality is a
standing hypothesis of the old/new theory, not a fact local to any one argument: before this,
the two proofs in `TauCeti/NumberTheory/ModularForms/Petersson/Orthogonal.lean` that need it
each built it inline. -/
instance finiteDimensional_cuspForm_finiteIndex
    {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.HasDetOne] [𝒢.IsFiniteRelIndex 𝒮ℒ]
    [DiscreteTopology 𝒢.strictPeriods] {k : ℤ} :
    Module.Finite ℂ (CuspForm 𝒢 k) :=
  Module.Finite.of_injective CuspForm.toModularFormₗ CuspForm.toModularFormₗ_injective

end TauCeti

end
