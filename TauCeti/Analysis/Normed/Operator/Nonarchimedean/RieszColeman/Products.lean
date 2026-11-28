/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Idempotents
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszColeman.Basic

/-!
# Riesz–Coleman projections for polynomial products

Projections attached to polynomials with coprime reversals are orthogonal. If the reversals
multiply to the reversal of another spectral polynomial, the sum of the orthogonal projections
is the projection for that polynomial.
-/

public section

open Polynomial

namespace ContinuousLinearMap.IsRieszColemanProjection

variable {R M ι : Type*} [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  {u E : M →L[R] M} {Q : R[X]} {p : ι → R[X]} {e : ι → M →L[R] M}

/-- Riesz–Coleman projections for polynomials with pairwise coprime reversals are orthogonal. -/
theorem orthogonalIdempotents_of_pairwise_isCoprime_reverse
    (he : ∀ i, IsRieszColemanProjection u (p i) (e i))
    (hp : Pairwise fun i j ↦ IsCoprime (p i).reverse (p j).reverse) :
    OrthogonalIdempotents e := by
  refine ⟨fun i ↦ (he i).isIdempotentElem, fun i j hij ↦ ?_⟩
  obtain ⟨a, b, hab⟩ := hp hij
  have hi : aeval u (p i).reverse * (e i * e j) = 0 := by
    rw [← mul_assoc, (he i).aeval_reverse_mul_eq_zero, zero_mul]
  have hj : aeval u (p j).reverse * (e i * e j) = 0 := by
    rw [← mul_assoc, (he i).commute_aeval (p j).reverse |>.eq, mul_assoc,
      (he j).aeval_reverse_mul_eq_zero, mul_zero]
  calc
    e i * e j = aeval u (a * (p i).reverse + b * (p j).reverse) * (e i * e j) := by simp [hab]
    _ = 0 := by simp [add_mul, mul_assoc, hi, hj]

/-- When `Q.reverse` is a product of reversals with orthogonal Riesz–Coleman projections,
the projection for `Q` is their sum. -/
theorem sum_eq_of_prod_reverse_eq [Fintype ι] (hE : IsRieszColemanProjection u Q E)
    (he : ∀ i, IsRieszColemanProjection u (p i) (e i)) (ho : OrthogonalIdempotents e)
    (hp : ∏ i, (p i).reverse = Q.reverse) :
    ∑ i, e i = E := by
  have hfix (i : ι) : E * e i = e i := by
    apply ContinuousLinearMap.coe_injective
    have hidem := ContinuousLinearMap.IsIdempotentElem.toLinearMap hE.isIdempotentElem
    rw [mul_def, toLinearMap_comp, LinearMap.IsIdempotentElem.comp_eq_right_iff hidem]
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem (fun j ↦ (p j).reverse) (Finset.mem_univ i)
    rw [(he i).range_eq_ker, hE.range_eq_ker, toLinearMap_aeval, toLinearMap_aeval, ← hp, hq]
    exact le_sup_left.trans sup_ker_aeval_le_ker_aeval_mul
  let D := E - ∑ i, e i
  have heD (i : ι) : e i * D = 0 := by
    dsimp only [D]
    rw [mul_sub, (hE.commute_of_commute (he i).commute.symm).eq, hfix,
      ho.mul_sum_of_mem (Finset.mem_univ i), sub_self]
  have hED : E * D = D := by
    simp only [D, mul_sub, hE.isIdempotentElem.eq, Finset.mul_sum, hfix]
  -- On the common kernel of the small projections, each evaluated factor is injective.
  have eliminate (s : Finset ι) (hz : aeval u (∏ i ∈ s, (p i).reverse) * D = 0) : D = 0 := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using hz
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, map_mul, mul_assoc] at hz
      apply ih
      let A := aeval u (∏ j ∈ s, (p j).reverse)
      have hkill : e i * (A * D) = 0 := by
        rw [← mul_assoc, ← ((he i).commute_aeval _).eq, mul_assoc, heD, mul_zero]
      calc
        A * D = (1 - e i) * (A * D) := by rw [sub_mul, one_mul, hkill, sub_zero]
        _ = 0 := by rw [← (he i).inverse_mul_aeval_reverse, mul_assoc, hz, mul_zero]
  have hzero := eliminate Finset.univ (by
    rw [hp, ← hED, ← mul_assoc, hE.aeval_reverse_mul_eq_zero, zero_mul])
  exact (sub_eq_zero.mp hzero).symm

end ContinuousLinearMap.IsRieszColemanProjection
