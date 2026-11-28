/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ThetaLift.Direction.Congruences
public import TauCeti.RingTheory.Valuation.AddValuation
public import Mathlib.Basic.ENNReal.Inv
import TauCeti.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Simultaneous changes of theta directions

`TauCeti.exists_direction_matrices_with_dvd_frobenius_pairings` intersects the coefficient
submodules from `TauCeti.exists_colengthDvd_frobenius_pairing` to impose all nonexempt
congruences on one family of direction changes. Its weighted determinant divisibility
bound is used in the theta-jet substitution.
`AddValuation.exists_direction_matrices_with_det_valuation_le_frobenius_budget` converts
this divisibility to the normalized additive valuation budget.

The construction follows `New.exists_newDirection_dvd` in
`grh/src/New/Derivatives/Divisibility/NullFrames.lean` of
grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC)
at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Finset Matrix
open scoped ENNReal

namespace TauCeti

/-- For finitely many Frobenius exponents and a partner rule on finitely many places, one
matrix per place and block label suffices to make all nonexempt pairings divisible by `π`.
The label `none` denotes the distinguished size-one block. A `some` block of size one
follows the same exemption rule as any other `some` block. The function `a` gives column
multiplicities. The modulus `π` divides `p`. For each `i ∈ s`, the power `d i ^ (p ^ e i)` is
associated to `π`, and each coordinate of the partner's distinguished direction
`Y (partner i t) none 1` admits a `p ^ e i`-th root modulo `π`. The weighted product of matrix
determinants divides the product of the local congruence costs expressed in the modulus roots. -/
theorem exists_direction_matrices_with_dvd_frobenius_pairings
    {R ι n τ I : Type*} [CommRing R] [PreValuationRing R]
    [Fintype ι] [Fintype n] [Fintype τ] {height : ι → ℕ}
    {p : ℕ} (hp : p.Prime) {π : R} (hπ : π ∣ (p : R))
    (s : Finset I) (e : I → ℕ) (partner : I → τ → τ) (mark : τ → Bool)
    (a : τ → Option ι → ℕ)
    (Y : ∀ (_ : τ) (h : Option ι), (Fin (h.elim 1 height) → R) →ₗ[R] (n → R))
    (d : I → R) (hd : ∀ i ∈ s, Associated (d i ^ (p ^ e i)) π)
    (hroot : ∀ i ∈ s, ∀ t j, ∃ x : R, π ∣ Y (partner i t) none 1 j - x ^ (p ^ e i)) :
    ∃ g : ∀ (_ : τ) (h : Option ι), Matrix (Fin (h.elim 1 height)) (Fin (h.elim 1 height)) R,
      (∀ i ∈ s, ∀ t h j, ¬DirectionPairExempt (mark t) (mark (partner i t)) h j →
        ∀ k k', π ∣ (fun u ↦ (Y t h (g t h k) u) ^ (p ^ e i)) ⬝ᵥ
          Y (partner i t) j (g (partner i t) j k')) ∧
      (∏ t, ∏ h, (g t h).det ^ a t h) ∣
        ∏ i ∈ s, ∏ t, d i ^ directionDeductionCost height
          (a t) (a (partner i t)) (p ^ e i) (mark t) (mark (partner i t)) := by
  classical
  choose root hroot using hroot
  have hlocal (i : s) (t : τ) :=
    exists_colengthDvd_frobenius_pairing (e := e i) (d := d i) hp
      ((hd i i.property).dvd.trans hπ) (Y t) (Y (partner i t)) (root i i.property t)
      (fun j ↦ (hd i i.property).dvd_iff_dvd_left.mpr (hroot i i.property t j))
      (a t) (a (partner i t)) (mark t) (mark (partner i t))
  choose L M l r hL hM hcost hpair using hlocal
  let A (t : τ) (h : Option ι) (i : s) (u : τ) : Submodule R (Fin (h.elim 1 height) → R) :=
    (if t = u then L i u h else ⊤) ⊓ (if t = partner i u then M i u h else ⊤)
  let B (t : τ) (h : Option ι) (i : s) (u : τ) : R :=
    (if t = u then d i ^ l i u h else 1) *
      (if t = partner i u then (d i ^ (p ^ e i)) ^ r i u h else 1)
  have hA (t h i u) : (⊤ : Submodule R _).ColengthDvd (A t h i u) (B t h i u) := by
    dsimp only [A, B]
    apply Submodule.ColengthDvd.inf
    · split_ifs <;> first | exact hL i u h | exact Submodule.colengthDvd_self _ _
    · split_ifs <;> first | exact hM i u h | exact Submodule.colengthDvd_self _ _
  have hmatrix (t h) := (Submodule.ColengthDvd.iInf fun i ↦
    Submodule.ColengthDvd.iInf (hA t h i)).exists_matrix_row_mem
  choose g hg hrow using hmatrix
  refine ⟨g, ?_, ?_⟩
  · intro i hi t h j hj k k'
    have hmem (v) (b) (k) : g v b k ∈ A v b ⟨i, hi⟩ t :=
      (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp (hrow v b k) ⟨i, hi⟩) t
    refine (hd i hi).dvd_iff_dvd_left.mp (hpair ⟨i, hi⟩ t h j hj _ ?_ _ ?_)
    · simpa only [A, ite_true] using (Submodule.mem_inf.mp (hmem t h k)).1
    · simpa only [A, ite_true] using (Submodule.mem_inf.mp (hmem (partner i t) j k')).2
  refine (Finset.prod_dvd_prod_of_dvd _ _ fun t _ ↦ Finset.prod_dvd_prod_of_dvd _ _
    fun h _ ↦ pow_dvd_pow_of_dvd (hg t h) _).trans ?_
  rw [← Finset.prod_coe_sort s]
  suffices heq : (∏ t, ∏ h, (∏ i : s, ∏ u, B t h i u) ^ a t h) = _ by rw [heq]
  simp_rw [← Finset.prod_pow]
  calc
    _ = ∏ (i : s), ∏ u, ∏ t, ∏ h, B t h i u ^ a t h := by
      simpa only [← Finset.univ_product_univ, Finset.prod_product] using
        (Finset.prod_comm (s := (Finset.univ : Finset (τ × Option ι)))
          (t := (Finset.univ : Finset (s × τ)))
          (f := fun th iu ↦ B th.1 th.2 iu.1 iu.2 ^ a th.1 th.2))
    _ = _ := by
      refine Finset.prod_congr rfl fun i _ ↦ Finset.prod_congr rfl fun u _ ↦ ?_
      rw [← hcost i u, prod_prod_ite_mul_pow]
      simp only [mem_univ, ite_true]
      simp_rw [← pow_mul (d i ^ (p ^ e i)), Nat.mul_comm (r i u _) (a (partner i u) _),
        Finset.prod_pow_eq_pow_sum]
      simp_rw [← pow_mul, Nat.mul_comm (l i u _) (a u _), Finset.prod_pow_eq_pow_sum, ← pow_add]

end TauCeti

namespace AddValuation

open TauCeti (DirectionPairExempt directionDeductionCost
  exists_direction_matrices_with_dvd_frobenius_pairings)

/-- The direction changes satisfying all nonexempt congruences for `s` can be chosen
with total weighted determinant valuation at most `v π` times the normalized deduction.
The power `d i ^ (p ^ e i)` need only be associated to `π` for each `i ∈ s`. -/
theorem exists_direction_matrices_with_det_valuation_le_frobenius_budget
    {R ι n τ I : Type*} [CommRing R] [PreValuationRing R]
    [Fintype ι] [Fintype n] [Fintype τ] {height : ι → ℕ}
    (v : AddValuation R ℝ≥0∞) {p : ℕ} (hp : p.Prime) {π : R} (hπ : π ∣ (p : R))
    (s : Finset I) (e : I → ℕ) (partner : I → τ → τ) (mark : τ → Bool)
    (a : τ → Option ι → ℕ)
    (Y : ∀ (_ : τ) (h : Option ι), (Fin (h.elim 1 height) → R) →ₗ[R] (n → R))
    (d : I → R) (hd : ∀ i ∈ s, Associated (d i ^ (p ^ e i)) π)
    (hroot : ∀ i ∈ s, ∀ t j, ∃ x : R, π ∣ Y (partner i t) none 1 j - x ^ (p ^ e i)) :
    ∃ g : ∀ (_ : τ) (h : Option ι), Matrix (Fin (h.elim 1 height)) (Fin (h.elim 1 height)) R,
      (∀ i ∈ s, ∀ t h j, ¬DirectionPairExempt (mark t) (mark (partner i t)) h j →
        ∀ k k', π ∣ (fun u ↦ (Y t h (g t h k) u) ^ (p ^ e i)) ⬝ᵥ
          Y (partner i t) j (g (partner i t) j k')) ∧
      (∑ t, ∑ h, a t h • v (g t h).det) ≤ v π * ∑ i ∈ s, ∑ t,
        (directionDeductionCost height (a t) (a (partner i t)) (p ^ e i)
          (mark t) (mark (partner i t)) : ℝ≥0∞) / ↑(p ^ e i) := by
  obtain ⟨g, hg, hdvd⟩ :=
    exists_direction_matrices_with_dvd_frobenius_pairings hp hπ s e partner mark a Y d hd hroot
  refine ⟨g, hg, ?_⟩
  have hnonneg (x : R) : 0 ≤ v x := zero_le
  have hle := AddValuation.map_le_map_of_dvd hnonneg hdvd
  simp only [v.map_prod, v.map_pow] at hle
  refine hle.trans_eq ?_
  simp only [Finset.mul_sum, nsmul_eq_mul]
  refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun t _ ↦ ?_
  have hq : ((p ^ e i : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast pow_ne_zero _ hp.ne_zero
  have hv : v (d i ^ (p ^ e i)) = v π := le_antisymm
    (AddValuation.map_le_map_of_dvd hnonneg (hd i hi).dvd)
    (AddValuation.map_le_map_of_dvd hnonneg (hd i hi).dvd')
  rw [← hv, v.map_pow, nsmul_eq_mul, mul_right_comm _ (v (d i)),
    mul_comm (↑(p ^ e i) : ℝ≥0∞),
    ENNReal.div_mul_cancel hq (ENNReal.natCast_ne_top _)]

end AddValuation
