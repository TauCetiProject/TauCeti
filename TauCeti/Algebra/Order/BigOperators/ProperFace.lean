/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Lattice.Fold
public import TauCeti.Algebra.BigOperators.ProperFace

/-!
# Bounds on proper-face sums and the saving at the smallest coordinate

For a finite index type `ι` and coefficients `c : Finset ι → R`, the *proper-face sum*
`B_c(x) = ∑_{s ⊊ ι} c_s ∏_{i ∈ s} x_i` (`TauCeti.properFaceSum`) is a multiaffine polynomial
in `x` whose top monomial `D(x) = ∏_i x_i` is missing. With nonnegative
coefficients such sums are the error terms in Weibo Fu's weight-aspect multiplicity estimates,
where weights `k : ι → ℕ` enter through `x = k + 1`, the dimension of
`⊠_i Sym^{k_i}` being `D(k + 1)`. Because one coordinate is missing from every monomial, these
errors save a factor against `D`: if `1 ≤ x_i` and `a ≤ x_i` for every `i`, then
`a · B_c(x) ≤ (∑_{s ⊊ ι} c_s) · D(x)`. Taking `a = min_i x_i` gives the saving by the smallest
coordinate, and on the diagonal `B_c(t, …, t) ≤ (∑_s c_s) t^(|ι| - 1)`.

## Main definitions

* `TauCeti.IsProperFaceBound c e`: the function `e` on weights `k : ι → ℕ` is controlled by
  `c`, i.e. `|e k| ≤ B_c(k + 1)` for every `k`.

## Main results

* `TauCeti.properFaceSum_nonneg`, `TauCeti.abs_properFaceSum_le`: nonnegativity and the
  absolute-value majorant.
* `TauCeti.mul_properFaceSum_le`, `TauCeti.properFaceSum_le_div_inf'`,
  `TauCeti.properFaceSum_const_le`: the saving at the smallest coordinate and on the diagonal.
* `TauCeti.IsProperFaceBound.add`, `TauCeti.IsProperFaceBound.sum`,
  `TauCeti.IsProperFaceBound.of_mem_sum`,
  `TauCeti.exists_isProperFaceBound_properFaceSum_natCast`:
  closure of the controlled class under sums, common bounds for finite families, and control
  of proper-face sums in the unshifted weights.

The definition and its order-free API are in `TauCeti.Algebra.BigOperators.ProperFace`, and the
corresponding `MvPolynomial`, `TauCeti.properFacePolynomial`, is in
`TauCeti.Algebra.MvPolynomial.ProperFace`.

## References

* Weibo Fu, *Sharp bounds for multiplicities of Bianchi modular forms*, Ann. of Math. 200
  (2024), 123–152; arXiv:2201.11190, Theorem 1.2, Theorem 1.4 and §§6–7.
-/

public section

namespace TauCeti

open Finset

variable {ι R : Type*} [Fintype ι] [DecidableEq ι]

section OrderedSemiring

variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {c d : Finset ι → R} {x : ι → R}

theorem properFaceSum_mono (hcd : ∀ s ⊂ univ, c s ≤ d s) (hx : ∀ i, 0 ≤ x i) :
    properFaceSum c x ≤ properFaceSum d x := by
  rw [properFaceSum_def, properFaceSum_def]
  exact sum_le_sum fun s hs ↦
    mul_le_mul_of_nonneg_right (hcd s (mem_ssubsets.1 hs)) (prod_nonneg fun i _ ↦ hx i)

theorem properFaceSum_nonneg (hc : ∀ s ⊂ univ, 0 ≤ c s) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ properFaceSum c x := by
  simpa using properFaceSum_mono (c := 0) hc hx

/-- The saving at a missing coordinate: for nonnegative coefficients `c`, if every `x_i ≥ 1` and
`a ≤ x_i` for every `i`, then `a · B_c(x) ≤ (∑_{s ⊊ ι} c_s) · ∏_i x_i`. -/
theorem mul_properFaceSum_le (hc : ∀ s ⊂ univ, 0 ≤ c s) (hx : ∀ i, 1 ≤ x i) {a : R}
    (ha : ∀ i, a ≤ x i) :
    a * properFaceSum c x ≤ (∑ s ∈ (univ : Finset ι).ssubsets, c s) * ∏ i, x i := by
  have hx₀ : ∀ i, 0 ≤ x i := fun i ↦ zero_le_one.trans (hx i)
  rw [properFaceSum_def, mul_sum, sum_mul]
  refine sum_le_sum fun s hs ↦ ?_
  obtain ⟨j, -, hj⟩ := exists_of_ssubset (mem_ssubsets.1 hs)
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (hc s (mem_ssubsets.1 hs))
  calc a * ∏ i ∈ s, x i ≤ x j * ∏ i ∈ s, x i :=
        mul_le_mul_of_nonneg_right (ha j) (prod_nonneg fun i _ ↦ hx₀ i)
    _ = ∏ i ∈ insert j s, x i := (prod_insert hj).symm
    _ ≤ ∏ i, x i :=
        prod_le_prod_of_subset_of_one_le₀ (subset_univ _) (fun i _ ↦ hx₀ i) fun i _ _ ↦ hx i

/-- On the diagonal `x = (t, …, t)` with `t ≥ 1`, a proper-face sum with nonnegative
coefficients `c` is at most `(∑_{s ⊊ ι} c_s) t^(|ι| - 1)`. -/
theorem properFaceSum_const_le (hc : ∀ s ⊂ univ, 0 ≤ c s) {t : R} (ht : 1 ≤ t) :
    properFaceSum c (fun _ ↦ t) ≤
      (∑ s ∈ (univ : Finset ι).ssubsets, c s) * t ^ (Fintype.card ι - 1) := by
  rw [properFaceSum_def, sum_mul]
  refine sum_le_sum fun s hs ↦ ?_
  have hcard : #s < Fintype.card ι := card_univ (α := ι) ▸ card_lt_card (mem_ssubsets.1 hs)
  rw [prod_const]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (by omega)) (hc s (mem_ssubsets.1 hs))

end OrderedSemiring

section Semifield

variable [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] {c : Finset ι → R} {x : ι → R}

/-- The saving at a missing coordinate in divided form: for nonnegative coefficients `c`, if
every `x_i ≥ 1` and `0 < a ≤ x_i` for every `i`, then `B_c(x) ≤ (∑_{s ⊊ ι} c_s) · ∏_i x_i / a`. -/
theorem properFaceSum_le_div (hc : ∀ s ⊂ univ, 0 ≤ c s) (hx : ∀ i, 1 ≤ x i) {a : R}
    (ha₀ : 0 < a) (ha : ∀ i, a ≤ x i) :
    properFaceSum c x ≤ (∑ s ∈ (univ : Finset ι).ssubsets, c s) * (∏ i, x i) / a := by
  rw [le_div_iff₀ ha₀, mul_comm]
  exact mul_properFaceSum_le hc hx ha

/-- The saving by the smallest coordinate: for nonnegative coefficients `c`, if every
`x_i ≥ 1`, then `B_c(x) ≤ (∑_{s ⊊ ι} c_s) · ∏_i x_i / min_i x_i`. -/
theorem properFaceSum_le_div_inf' [Nonempty ι] (hc : ∀ s ⊂ univ, 0 ≤ c s) (hx : ∀ i, 1 ≤ x i) :
    properFaceSum c x ≤
      (∑ s ∈ (univ : Finset ι).ssubsets, c s) * (∏ i, x i) / univ.inf' univ_nonempty x := by
  refine properFaceSum_le_div hc hx ?_ fun i ↦ inf'_le _ (mem_univ i)
  obtain ⟨i, -, hi⟩ := exists_mem_eq_inf' (univ_nonempty (α := ι)) x
  exact hi ▸ zero_lt_one.trans_le (hx i)

end Semifield

section Ring

variable [CommRing R] [LinearOrder R] [IsOrderedRing R]

/-- For nonnegative variables, replacing the coefficients by their absolute values majorizes the
absolute value of a proper-face sum. -/
theorem abs_properFaceSum_le (c : Finset ι → R) {x : ι → R} (hx : ∀ i, 0 ≤ x i) :
    |properFaceSum c x| ≤ properFaceSum (fun s ↦ |c s|) x := by
  rw [properFaceSum_def, properFaceSum_def]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s _ ↦ ?_)
  rw [abs_mul, abs_of_nonneg (prod_nonneg fun i _ ↦ hx i)]

end Ring

section Bound

variable [CommRing R] [LinearOrder R]

/-- A function `e` of weights `k : ι → ℕ` is controlled by the proper-face coefficients `c` when
`|e k| ≤ B_c(k + 1)` for every weight `k`. -/
def IsProperFaceBound (c : Finset ι → R) (e : (ι → ℕ) → R) : Prop :=
  ∀ k : ι → ℕ, |e k| ≤ properFaceSum c (fun i ↦ (k i : R) + 1)

theorem isProperFaceBound_iff {c : Finset ι → R} {e : (ι → ℕ) → R} :
    IsProperFaceBound c e ↔ ∀ k : ι → ℕ, |e k| ≤ properFaceSum c (fun i ↦ (k i : R) + 1) :=
  Iff.rfl

namespace IsProperFaceBound

variable {c d : Finset ι → R} {e f : (ι → ℕ) → R}

theorem abs_le (h : IsProperFaceBound c e) (k : ι → ℕ) :
    |e k| ≤ properFaceSum c (fun i ↦ (k i : R) + 1) :=
  h k

variable [IsOrderedRing R]

theorem add (hc : IsProperFaceBound c e) (hd : IsProperFaceBound d f) :
    IsProperFaceBound (c + d) (e + f) := fun k ↦ by
  rw [properFaceSum_add]
  exact (abs_add_le _ _).trans (add_le_add (hc k) (hd k))

theorem smul (h : IsProperFaceBound c e) {a : R} (ha : 0 ≤ a) :
    IsProperFaceBound (a • c) (a • e) := fun k ↦ by
  rw [properFaceSum_smul, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left (h k) ha

theorem sum {α : Type*} {t : Finset α} {c : α → Finset ι → R} {e : α → (ι → ℕ) → R}
    (h : ∀ j ∈ t, IsProperFaceBound (c j) (e j)) :
    IsProperFaceBound (∑ j ∈ t, c j) (∑ j ∈ t, e j) := fun k ↦ by
  rw [properFaceSum_sum, Finset.sum_apply]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj ↦ h j hj k)

theorem mono (h : IsProperFaceBound c e) (hcd : ∀ s ⊂ univ, c s ≤ d s) :
    IsProperFaceBound d e := fun k ↦
  (h k).trans (properFaceSum_mono hcd fun _ ↦ add_nonneg (Nat.cast_nonneg _) zero_le_one)

/-- In a finite family of controlled functions with nonnegative coefficients, the sum of the
coefficient vectors controls every member. -/
theorem of_mem_sum {α : Type*} {t : Finset α} {c : α → Finset ι → R} {e : α → (ι → ℕ) → R}
    (hc : ∀ j ∈ t, ∀ s ⊂ univ, 0 ≤ c j s) (h : ∀ j ∈ t, IsProperFaceBound (c j) (e j)) {j : α}
    (hj : j ∈ t) : IsProperFaceBound (∑ j ∈ t, c j) (e j) :=
  (h j hj).mono fun s hs ↦ by
    rw [Finset.sum_apply]
    exact single_le_sum (fun i hi ↦ hc i hi s hs) hj

/-- The saving at a missing coordinate for a controlled function: for nonnegative coefficients
`c` and `0 ≤ a` with `a ≤ k_i + 1` for every `i`,
`a · |e k| ≤ (∑_{s ⊊ ι} c_s) · ∏_i (k_i + 1)`. -/
theorem mul_abs_le (h : IsProperFaceBound c e) (hc : ∀ s ⊂ univ, 0 ≤ c s) {k : ι → ℕ} {a : R}
    (ha₀ : 0 ≤ a) (ha : ∀ i, a ≤ k i + 1) :
    a * |e k| ≤ (∑ s ∈ (univ : Finset ι).ssubsets, c s) * ∏ i, ((k i : R) + 1) :=
  (mul_le_mul_of_nonneg_left (h k) ha₀).trans
    (mul_properFaceSum_le hc (fun i ↦ by simp) ha)

/-- At parallel weights `k = (n, …, n)` a function controlled by nonnegative coefficients `c`
is at most
`(∑_{s ⊊ ι} c_s) (n + 1)^(|ι| - 1)`. -/
theorem abs_const_le (h : IsProperFaceBound c e) (hc : ∀ s ⊂ univ, 0 ≤ c s) (n : ℕ) :
    |e fun _ ↦ n| ≤
      (∑ s ∈ (univ : Finset ι).ssubsets, c s) * ((n : R) + 1) ^ (Fintype.card ι - 1) :=
  (h _).trans (properFaceSum_const_le hc (by simp))

end IsProperFaceBound

/-- For a nonempty index type, a constant function `b` is controlled by the single coefficient
`|b|` at the empty face. -/
theorem isProperFaceBound_const [Nonempty ι] (b : R) :
    IsProperFaceBound (Pi.single (∅ : Finset ι) |b|) fun _ ↦ b := fun _ ↦ by
  simp [properFaceSum_single, (univ_nonempty (α := ι)).ne_empty.symm]

variable [IsOrderedRing R]

theorem isProperFaceBound_zero : IsProperFaceBound (0 : Finset ι → R) 0 := fun _ ↦ by simp

/-- A proper-face sum evaluated at the unshifted weights `k`, with arbitrary signed coefficients,
is controlled by nonnegative proper-face coefficients in `k + 1`. -/
theorem exists_isProperFaceBound_properFaceSum_natCast (c : Finset ι → R) :
    ∃ d : Finset ι → R, (∀ s, 0 ≤ d s) ∧
      IsProperFaceBound d fun k ↦ properFaceSum c fun i ↦ (k i : R) := by
  refine ⟨fun t ↦ |∑ s ∈ (univ : Finset ι).ssubsets with t ⊆ s, c s * ∏ i ∈ s \ t, (-1 : R)|,
    fun _ ↦ abs_nonneg _, fun k ↦ ?_⟩
  have hk : (fun i ↦ (k i : R)) = (fun i ↦ (k i : R) + 1) + fun _ ↦ -1 := by
    ext; simp
  dsimp only
  rw [hk, properFaceSum_add_vec]
  exact abs_properFaceSum_le _ fun _ ↦ add_nonneg (Nat.cast_nonneg _) zero_le_one

end Bound

end TauCeti
