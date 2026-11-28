/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ThetaLift.DirectionCongruences.Basic
public import TauCeti.RingTheory.Valuation.AddValuation
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.WithTop

/-!
# Simultaneous changes of theta directions

Intersect the coefficient conditions from every outgoing and incoming pairing before choosing
one matrix of new directions at each place and height. The weighted product of determinants
divides the product of the local costs; this form of the bound does not require choosing a
normalization of the valuation.

The simultaneous change is the one in `New.exists_newDirection_dvd` in
[lsernau/grh-lean, `New/Derivatives/Divisibility/NullFrames.lean`][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/Derivatives/Divisibility/NullFrames.lean
-/

public section

open Finset Matrix

namespace TauCeti

/-- For a pairing with twist exponent `e`, compute the deduction in units of the valuation of
a `p^e`-th root of the pairing modulus. The weights `a` and `b` count columns by height block;
`none` is the distinguished height-one block. -/
def directionDeductionNumerator {ι : Type*} [Fintype ι] (height : ι → ℕ) (q : ℕ)
    (a b : Option ι → ℕ) (markL markR : Bool) : ℕ :=
  min (if markL then 0 else a none) (q * ((∑ i, b (some i)) + if markR then 0 else b none)) +
    (∑ i, a (some i)) + min (∑ i, a (some i) * height i) (q * (∑ i, b (some i) * height i))

/-- Dividing the integer numerator by `q` recovers the deduction in units of the valuation
of the pairing modulus. Marked places contribute no distinguished columns to the minima. -/
theorem directionDeductionNumerator_div {ι : Type*} [Fintype ι] (height : ι → ℕ) (q : ℕ)
    (a b : Option ι → ℕ) (markL markR : Bool) :
    (directionDeductionNumerator height q a b markL markR : ℝ) / q =
      min ((if markL then 0 else (a none : ℝ)) / q)
        ((∑ i, (b (some i) : ℝ)) + if markR then 0 else (b none : ℝ)) +
      (∑ i, (a (some i) : ℝ)) / q +
      min ((∑ i, (a (some i) : ℝ) * height i) / q) (∑ i, (b (some i) : ℝ) * height i) := by
  rcases q.eq_zero_or_pos with rfl | hq
  · have h₁ : 0 ≤ (∑ i, (b (some i) : ℝ)) + if markR then 0 else (b none : ℝ) := by
      exact add_nonneg (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (by split <;> positivity)
    have h₂ : 0 ≤ ∑ i, (b (some i) : ℝ) * height i :=
      Finset.sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    simp [min_eq_left h₁, min_eq_left h₂]
  have hq₀ : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  simp only [directionDeductionNumerator, Nat.cast_add, Nat.cast_min, Nat.cast_mul,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, add_div, ← min_div_div_right hq₀.le,
    mul_div_cancel_left₀ _ hq₀.ne']

/-- The column-weighted determinant cost of a single pairing can be charged to its source and
its partner, even if they are the same place. -/
private theorem prod_direction_pair_cost {R Φ ι : Type*} [CommMonoid R] [Fintype Φ] [Fintype ι]
    [DecidableEq Φ] (a : Φ → Option ι → ℕ) (t u : Φ) (d : R) (q : ℕ) (l r : Option ι → ℕ) :
    (∏ v, ∏ h : Option ι,
      ((if v = t then d ^ l h else 1) * (if v = u then (d ^ q) ^ r h else 1)) ^ a v h) =
      d ^ ((∑ h, a t h * l h) + q * (∑ h, a u h * r h)) := by
  simp only [mul_pow, Finset.prod_mul_distrib, ite_pow, one_pow]
  rw [Finset.prod_comm (f := fun v (h : Option ι) ↦ if v = t then (d ^ l h) ^ a v h else 1),
    Finset.prod_comm (f := fun v (h : Option ι) ↦ if v = u then ((d ^ q) ^ r h) ^ a v h else 1)]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true, ← pow_mul, Finset.prod_pow_eq_pow_sum,
    ← pow_add]
  congr 1
  rw [Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun h _ ↦ by ring

/-- Choose one integral direction matrix for each place and height block, making every
nonexempt Frobenius pairing divisible by `π`. The weighted product of their determinants
divides the product of the deductions for the displayed exponents and places. Each cost is
measured in powers of the specified `p^e`-th root `d` of `π`.

The `none` block has size one. A pair is exempt only when its first block is `none` and
its first place is marked, or its first block and its marked partner's block are both `none`.
Partners need not be distinct or form permutations. -/
theorem exists_direction_matrices_dvd {R Φ ι n E : Type*} [CommRing R] [PreValuationRing R]
    [Fintype Φ] [Fintype ι] [Fintype n] [Fintype E] {p : ℕ} (hp : p.Prime) {π : R}
    (hπ : π ∣ (p : R)) (e : E → ℕ) (pr : E → Φ → Φ) (d : E → R)
    (hd : ∀ j, d j ^ (p ^ e j) = π) (height : ι → ℕ) (a : Φ → Option ι → ℕ) (mark : Φ → Bool)
    (Y : Φ → ∀ h : Option ι, (Fin (h.elim 1 height) → R) →ₗ[R] (n → R))
    (root : E → Φ → n → R) (hroot : ∀ j t i, root j t i ^ (p ^ e j) = Y (pr j t) none 1 i) :
    ∃ g : Φ → ∀ h : Option ι, Matrix (Fin (h.elim 1 height)) (Fin (h.elim 1 height)) R,
      (∀ j t h h', ¬(h = none ∧ (mark t = true ∨ h' = none ∧ mark (pr j t) = true)) →
        ∀ k k', π ∣ (fun i ↦ Y t h (g t h k) i ^ (p ^ e j)) ⬝ᵥ Y (pr j t) h' (g (pr j t) h' k')) ∧
      (∏ t, ∏ h, (g t h).det ^ a t h) ∣
        ∏ j, ∏ t, d j ^ directionDeductionNumerator height (p ^ e j) (a t) (a (pr j t))
          (mark t) (mark (pr j t)) := by
  classical
  choose L M l r hL hM hcost hpair using fun (j : E) (t : Φ) ↦
    exists_colengthDvd_frobenius_pairing (e := e j) hp (by rw [hd]; exact hπ)
      (Y t) (Y (pr j t)) (root j t) (hroot j t) (a t) (a (pr j t))
      (mark t) (mark (pr j t))
  let N (t : Φ) (h : Option ι) (j : E × Φ) : Submodule R (Fin (h.elim 1 height) → R) :=
    (if t = j.2 then L j.1 j.2 h else ⊤) ⊓ (if t = pr j.1 j.2 then M j.1 j.2 h else ⊤)
  let z (t : Φ) (h : Option ι) (j : E × Φ) : R :=
    (if t = j.2 then d j.1 ^ l j.1 j.2 h else 1) *
      (if t = pr j.1 j.2 then (d j.1 ^ (p ^ e j.1)) ^ r j.1 j.2 h else 1)
  have hlocal (t : Φ) (h : Option ι) (j : E × Φ) : (⊤ : Submodule R _).ColengthDvd (N t h j)
      (z t h j) := by
    unfold N z
    apply Submodule.ColengthDvd.inf <;> split_ifs with ht
    · exact hL j.1 j.2 h
    · simp
    · exact hM j.1 j.2 h
    · simp
  have hmatrix (t : Φ) (h : Option ι) :
      ∃ A : Matrix (Fin (h.elim 1 height)) (Fin (h.elim 1 height)) R,
        A.det ∣ ∏ j, z t h j ∧ ∀ k, ∀ j, A k ∈ N t h j := by
    let I : Matrix (Fin (h.elim 1 height)) (Fin (h.elim 1 height)) R := 1
    obtain ⟨A, hdet, hrows⟩ := (Submodule.colengthDvd_iInf_finset univ (N t h) (z t h)
      (fun j _ ↦ hlocal t h j)).exists_matrix I (by simp)
    refine ⟨A, hdet, ?_⟩
    have hrow (i : Fin (h.elim 1 height)) :
        (∑ k, A i k • I k) = A i := by
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Matrix.mul_apply, I, mul_one]
    simpa only [hrow, Submodule.mem_iInf, Finset.mem_univ, forall_const] using hrows
  choose g hdet hrow using hmatrix
  refine ⟨g, ?_, ?_⟩
  · intro j t h h' hno k k'
    have hleft : g t h k ∈ L j t h := by
      simpa [N] using (Submodule.mem_inf.mp (hrow t h k (j, t))).1
    have hright : g (pr j t) h' k' ∈ M j t h' := by
      simpa [N] using (Submodule.mem_inf.mp (hrow (pr j t) h' k' (j, t))).2
    simpa only [hd j] using hpair j t h h' hno _ hleft _ hright
  · calc
      _ ∣ ∏ t, ∏ h, (∏ j, z t h j) ^ a t h :=
        Finset.prod_dvd_prod_of_dvd _ _ fun t _ ↦
          Finset.prod_dvd_prod_of_dvd _ _ fun h _ ↦ pow_dvd_pow_of_dvd (hdet t h) _
      _ = _ := by
        simp only [← Finset.prod_pow]
        rw [Finset.prod_comm_cycle]
        simp only [Fintype.prod_prod_type]
        refine Finset.prod_congr rfl fun j _ ↦ Finset.prod_congr rfl fun t _ ↦ ?_
        rw [directionDeductionNumerator, ← hcost j t]
        exact prod_direction_pair_cost a t (pr j t) (d j) (p ^ e j) (l j t) (r j t)

/-- The simultaneous direction changes have total column-weighted valuation at most `v(π)`
times the sum of the normalized deductions. The valuation is nonnegative on the coefficient
ring, and its value at the pairing modulus is finite. -/
theorem exists_direction_matrices_of_addValuation {R Φ ι n E : Type*} [CommRing R]
    [PreValuationRing R] [Fintype Φ] [Fintype ι] [Fintype n] [Fintype E]
    {p : ℕ} (hp : p.Prime) {π : R} (hπ : π ∣ (p : R)) (e : E → ℕ) (pr : E → Φ → Φ)
    (d : E → R) (hd : ∀ j, d j ^ (p ^ e j) = π) (height : ι → ℕ) (a : Φ → Option ι → ℕ)
    (mark : Φ → Bool) (Y : Φ → ∀ h : Option ι, (Fin (h.elim 1 height) → R) →ₗ[R] (n → R))
    (root : E → Φ → n → R) (hroot : ∀ j t i, root j t i ^ (p ^ e j) = Y (pr j t) none 1 i)
    (v : AddValuation R (WithTop ℝ)) (hv : ∀ x, 0 ≤ v x) {w : ℝ} (hw : v π = w) :
    ∃ g : Φ → ∀ h : Option ι, Matrix (Fin (h.elim 1 height)) (Fin (h.elim 1 height)) R,
      (∀ j t h h', ¬(h = none ∧ (mark t = true ∨ h' = none ∧ mark (pr j t) = true)) →
        ∀ k k', π ∣ (fun i ↦ Y t h (g t h k) i ^ (p ^ e j)) ⬝ᵥ Y (pr j t) h' (g (pr j t) h' k')) ∧
      (∑ t, ∑ h, a t h • v (g t h).det) ≤
        ↑(w * ∑ j, ∑ t, (directionDeductionNumerator height (p ^ e j) (a t) (a (pr j t))
          (mark t) (mark (pr j t)) : ℝ) / (p : ℝ) ^ e j) := by
  classical
  obtain ⟨g, hg, hdet⟩ := exists_direction_matrices_dvd hp hπ e pr d hd height a mark Y root hroot
  have hrootval (j : E) : v (d j) = ↑(w / (p : ℝ) ^ e j) := by
    have hpow := congrArg v (hd j)
    rw [v.map_pow, hw] at hpow
    cases h : v (d j) with
    | top =>
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (pow_ne_zero (e j) hp.ne_zero)
      simp [h, hk, succ_nsmul] at hpow
    | coe x =>
      rw [h, ← WithTop.coe_nsmul, WithTop.coe_eq_coe, nsmul_eq_mul, Nat.cast_pow] at hpow
      rw [WithTop.coe_eq_coe, eq_div_iff (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))]
      exact (mul_comm ..).trans hpow
  have hle := AddValuation.map_le_map_of_dvd (v := v) hv hdet
  simp_rw [AddValuation.map_prod, v.map_pow] at hle
  refine ⟨g, hg, hle.trans_eq ?_⟩
  simp_rw [hrootval, ← WithTop.coe_nsmul, ← WithTop.coe_sum, nsmul_eq_mul, Finset.mul_sum]
  exact congrArg (fun z : ℝ ↦ (z : WithTop ℝ)) <| Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun t _ ↦ by ring

end TauCeti
