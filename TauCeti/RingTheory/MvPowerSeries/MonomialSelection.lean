/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.RingTheory.MvPowerSeries.Substitution
import TauCeti.RingTheory.MvPowerSeries.Order

/-!
# Monomial selection in ultrametric power series

A coefficient of `H(a) * F`, with `H` integral and the series `a i` of zero constant term,
is no larger in norm than the same coefficient of `a^e * F` for some monomial of degree at
most the coefficient index's total degree. This lets one replace integral multipliers in
products of theta jets by monomials without increasing the valuation.

The selection is used in `New.CMLattice.LeastValLE.exists_monomial` in
`grh/src/New/Derivatives/Sharpness/LeastValuation.lean` of lsernau/grh-lean (rev. `72fead1`).
-/

public section

open Finset

namespace MvPowerSeries

/-- For series `a i` of zero constant coefficient, one monomial in the `a i` attains at least the
norm of the `d`-th coefficient of `H(a) * F`. The chosen monomial has degree at most `d.degree`,
and only the coefficients of `H` through that degree are required to have norm at most one.
No norm bound on `F` or on the substituted series `a i` is required. -/
theorem exists_monomial_norm_coeff_subst_mul_le {σ τ R : Type*}
    [SeminormedCommRing R] [IsUltrametricDist R] {a : σ → MvPowerSeries τ R}
    (hsub : HasSubst a) (ha : ∀ i, constantCoeff (a i) = 0) (H : MvPowerSeries σ R)
    (F : MvPowerSeries τ R) (d : τ →₀ ℕ) (hH : ∀ e, e.degree ≤ d.degree → ‖coeff e H‖ ≤ 1) :
    ∃ e : σ →₀ ℕ, e.degree ≤ d.degree ∧
      ‖coeff d (substAlgHom hsub H * F)‖ ≤ ‖coeff d ((e.prod fun i k ↦ a i ^ k) * F)‖ := by
  classical
  let M (e : σ →₀ ℕ) := e.prod fun i k ↦ a i ^ k
  let S (b : τ →₀ ℕ) := (coeff_subst_finite hsub H b).toFinset
  -- Use one finite support for all substitution coefficients in the convolution.
  let T := (antidiagonal d).biUnion fun b ↦ S b.1
  have hcoeff (b : (τ →₀ ℕ) × (τ →₀ ℕ)) (hb : b ∈ antidiagonal d) :
      coeff b.1 (substAlgHom hsub H) = ∑ e ∈ T, coeff e H * coeff b.1 (M e) := by
    rw [substAlgHom_apply, coeff_subst hsub, finsum_eq_sum_of_support_subset (s := T)]
    · simp only [M, smul_eq_mul]
    · intro e he
      exact mem_biUnion.mpr ⟨b, hb, (Set.Finite.mem_toFinset _).2 he⟩
  have hsum : coeff d (substAlgHom hsub H * F) =
      ∑ e ∈ T, coeff e H * coeff d (M e * F) := by
    rw [coeff_mul]
    calc
      _ = ∑ b ∈ antidiagonal d, ∑ e ∈ T, coeff e H * (coeff b.1 (M e) * coeff b.2 F) := by
        refine sum_congr rfl fun b hb ↦ ?_
        rw [hcoeff b hb, sum_mul]
        simp only [mul_assoc]
      _ = _ := by rw [sum_comm]; simp only [coeff_mul, mul_sum]
  have hdeg (e : σ →₀ ℕ) (he : e ∈ T) : e.degree ≤ d.degree := by
    obtain ⟨b, hb, hb'⟩ := mem_biUnion.mp he
    have hs : coeff e H • coeff b.1 (M e) ≠ 0 := (Set.Finite.mem_toFinset _).1 hb'
    have hne : coeff b.1 (M e) ≠ 0 := right_ne_zero_of_smul hs
    have hdeg₁ : e.degree ≤ b.1.degree := by
      by_contra! hlt
      exact hne (coeff_of_lt_order ((Nat.cast_lt.mpr hlt).trans_le (degree_le_order_prod_pow ha e)))
    refine hdeg₁.trans (Finsupp.degree_mono ?_)
    rw [← mem_antidiagonal.mp hb]
    exact le_self_add
  rw [hsum]
  by_cases hT : T.Nonempty
  · obtain ⟨e, he, hmax⟩ := T.exists_max_image (fun e ↦ ‖coeff d (M e * F)‖) hT
    refine ⟨e, hdeg e he, IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (norm_nonneg _) fun x hx ↦ ?_⟩
    exact (norm_mul_le _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (hH x (hdeg x hx))).trans (hmax x hx))
  · rw [not_nonempty_iff_eq_empty.mp hT, sum_empty, norm_zero]
    exact ⟨0, by simp, norm_nonneg _⟩

/-- Replace each integral multiplier in a finite product of coefficient norms by a single
monomial. The total degrees of all selected monomials together do not exceed the sum of the
coefficient degrees. In valuation notation, the sum of the valuations does not increase. -/
theorem exists_monomials_prod_norm_coeff_subst_mul_le {ι σ τ R : Type*} [Fintype ι]
    [SeminormedCommRing R] [IsUltrametricDist R] {a : σ → MvPowerSeries τ R}
    (hsub : HasSubst a) (ha : ∀ i, constantCoeff (a i) = 0) (H : ι → MvPowerSeries σ R)
    (F : ι → MvPowerSeries τ R) (d : ι → τ →₀ ℕ)
    (hH : ∀ j e, e.degree ≤ (d j).degree → ‖coeff e (H j)‖ ≤ 1) :
    ∃ e : ι → σ →₀ ℕ, (∑ j, (e j).degree) ≤ (∑ j, d j).degree ∧
      (∏ j, ‖coeff (d j) (substAlgHom hsub (H j) * F j)‖) ≤
        ∏ j, ‖coeff (d j) (((e j).prod fun i k ↦ a i ^ k) * F j)‖ := by
  choose e hd he using fun j ↦
    exists_monomial_norm_coeff_subst_mul_le hsub ha (H j) (F j) (d j) (hH j)
  refine ⟨e, ?_, prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun j _ ↦ he j)⟩
  rw [map_sum]
  exact sum_le_sum fun j _ ↦ hd j

end MvPowerSeries
