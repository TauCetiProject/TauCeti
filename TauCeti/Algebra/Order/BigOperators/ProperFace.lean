/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Proper-face polynomials and the saving at the smallest coordinate

For a finite index type `ι` and coefficients `c : Finset ι → R`, the *proper-face sum*

```text
B_c(x) = ∑_{s ⊊ ι} c_s ∏_{i ∈ s} x_i
```

runs over the proper subsets of `ι`: it is a multiaffine polynomial in `x` whose top monomial
`D(x) = ∏_i x_i` is missing (the coefficient `c univ` is never used). With nonnegative
coefficients such sums are the error terms in Weibo Fu's weight-aspect multiplicity estimates,
where weights `k : ι → ℕ` enter through `x = k + 1`, the dimension of
`⊠_i Sym^{k_i}` being `D(k + 1)`. Because one coordinate is missing from every monomial, these
errors save a factor against `D`: if `1 ≤ x_i` and `a ≤ x_i` for every `i`, then
`a · B_c(x) ≤ (∑_{s ⊊ ι} c_s) · D(x)`. Taking `a = min_i x_i` gives the saving by the smallest
coordinate, and on the diagonal `B_c(t, …, t) ≤ (∑_s c_s) t^(|ι| - 1)`.

## Main definitions

* `TauCeti.properFaceSum c x`: the proper-face sum `B_c(x)`.
* `TauCeti.properFacePolynomial c`: the corresponding `MvPolynomial`.
* `TauCeti.IsProperFaceBound c e`: the function `e` on weights `k : ι → ℕ` is controlled by
  `c`, i.e. `|e k| ≤ B_c(k + 1)` for every `k`.

## Main results

* `TauCeti.properFaceSum_add`, `TauCeti.properFaceSum_smul`, `TauCeti.properFaceSum_equiv`:
  linearity in the coefficients and invariance under reindexing.
* `TauCeti.properFaceSum_nonneg`, `TauCeti.abs_properFaceSum_le`: nonnegativity and the
  absolute-value majorant.
* `TauCeti.properFaceSum_add_vec`: translating `x` by a vector `a` gives a proper-face sum
  with explicit new coefficients.
* `TauCeti.mul_properFaceSum_le`, `TauCeti.properFaceSum_le_div_inf'`,
  `TauCeti.properFaceSum_const_le`: the saving at the smallest coordinate and on the diagonal.
* `TauCeti.totalDegree_properFacePolynomial_le`, `TauCeti.degreeOf_properFacePolynomial_le`:
  total degree at most `|ι| - 1` and degree at most one in each variable.
* `TauCeti.IsProperFaceBound.add`, `TauCeti.IsProperFaceBound.sum`,
  `TauCeti.IsProperFaceBound.of_mem_sum`, `TauCeti.isProperFaceBound_properFaceSum_natCast`:
  closure of the controlled class under sums, common bounds for finite families, and control
  of proper-face sums in the unshifted weights.

## References

* Weibo Fu, *Sharp bounds for multiplicities of Bianchi modular forms*, Ann. of Math. 200
  (2024), 123–152; arXiv:2201.11190, Theorem 1.2, Theorem 1.4 and §§6–7.
-/

public section

namespace TauCeti

open Finset

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι]

section CommSemiring

variable [CommSemiring R]

/-- The proper-face sum `B_c(x) = ∑_{s ⊊ ι} c_s ∏_{i ∈ s} x_i`: the multiaffine polynomial with
coefficients `c` in which the top monomial `∏_i x_i` is omitted. The value `c univ` is never
used. -/
def properFaceSum (c : Finset ι → R) (x : ι → R) : R :=
  ∑ s ∈ (univ : Finset ι).ssubsets, c s * ∏ i ∈ s, x i

theorem properFaceSum_def (c : Finset ι → R) (x : ι → R) :
    properFaceSum c x = ∑ s ∈ (univ : Finset ι).ssubsets, c s * ∏ i ∈ s, x i := by
  rw [properFaceSum]

@[simp]
theorem properFaceSum_zero (x : ι → R) : properFaceSum (0 : Finset ι → R) x = 0 := by
  simp [properFaceSum]

@[simp]
theorem properFaceSum_add (c d : Finset ι → R) (x : ι → R) :
    properFaceSum (c + d) x = properFaceSum c x + properFaceSum d x := by
  simp [properFaceSum, add_mul, sum_add_distrib]

@[simp]
theorem properFaceSum_smul (a : R) (c : Finset ι → R) (x : ι → R) :
    properFaceSum (a • c) x = a * properFaceSum c x := by
  simp [properFaceSum, mul_sum, mul_assoc]

@[simp]
theorem properFaceSum_sum {α : Type*} (t : Finset α) (c : α → Finset ι → R) (x : ι → R) :
    properFaceSum (∑ j ∈ t, c j) x = ∑ j ∈ t, properFaceSum (c j) x := by
  simp only [properFaceSum, Finset.sum_apply, sum_mul]
  exact sum_comm

/-- A single coefficient at a proper subset `s` contributes exactly `a ∏_{i ∈ s} x_i`; at the
full subset it contributes nothing. -/
theorem properFaceSum_single (s : Finset ι) (a : R) (x : ι → R) :
    properFaceSum (Pi.single s a) x = if s = univ then 0 else a * ∏ i ∈ s, x i := by
  rw [properFaceSum]
  split_ifs with hs
  · exact sum_eq_zero fun t ht ↦ by
      rw [Pi.single_eq_of_ne (hs ▸ (mem_ssubsets.1 ht).ne), zero_mul]
  · rw [sum_eq_single_of_mem s (mem_ssubsets.2 (ssubset_univ_iff.2 hs)) fun t _ hts ↦ by
      rw [Pi.single_eq_of_ne hts, zero_mul], Pi.single_eq_same]

/-- The coefficient at the full subset does not affect the proper-face sum. -/
@[simp]
theorem properFaceSum_update_univ (c : Finset ι → R) (a : R) (x : ι → R) :
    properFaceSum (Function.update c univ a) x = properFaceSum c x :=
  sum_congr rfl fun s hs ↦ by rw [Function.update_of_ne (mem_ssubsets.1 hs).ne]

/-- Transporting the coefficients and the variables along a bijection of index types does not
change the proper-face sum. -/
theorem properFaceSum_equiv [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (c : Finset κ → R)
    (x : κ → R) : properFaceSum (c ∘ e.finsetCongr) (x ∘ e) = properFaceSum c x := by
  refine sum_equiv e.finsetCongr (fun s ↦ ?_) fun s _ ↦ ?_
  · simp only [mem_ssubsets, Equiv.finsetCongr_apply]
    rw [← map_univ_equiv e, map_ssubset_map]
  · simp [Equiv.finsetCongr_apply, prod_map]

/-- Translating the variables by a vector `a` gives a proper-face sum again: the coefficient at
`t` is `∑_{t ⊆ s ⊊ ι} c_s ∏_{i ∈ s \ t} a_i`. -/
theorem properFaceSum_add_vec (c : Finset ι → R) (x a : ι → R) :
    properFaceSum c (x + a) =
      properFaceSum
        (fun t ↦ ∑ s ∈ (univ : Finset ι).ssubsets with t ⊆ s, c s * ∏ i ∈ s \ t, a i) x := by
  simp only [properFaceSum, Pi.add_apply, prod_add, mul_sum, sum_mul]
  refine sum_comm' (fun s t ↦ ?_) |>.trans (sum_congr rfl fun t _ ↦ sum_congr rfl fun s _ ↦ ?_)
  · simp only [mem_ssubsets, mem_powerset, mem_filter]
    exact ⟨fun h ↦ ⟨⟨h.1, h.2⟩, h.2.trans_ssubset h.1⟩, fun h ↦ ⟨h.1.1, h.1.2⟩⟩
  · ring

end CommSemiring

section OrderedSemiring

variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {c d : Finset ι → R} {x : ι → R}

theorem properFaceSum_mono (hcd : ∀ s ⊂ univ, c s ≤ d s) (hx : ∀ i, 0 ≤ x i) :
    properFaceSum c x ≤ properFaceSum d x :=
  sum_le_sum fun s hs ↦
    mul_le_mul_of_nonneg_right (hcd s (mem_ssubsets.1 hs)) (prod_nonneg fun i _ ↦ hx i)

theorem properFaceSum_nonneg (hc : ∀ s ⊂ univ, 0 ≤ c s) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ properFaceSum c x := by
  simpa using properFaceSum_mono (c := 0) hc hx

/-- The saving at a missing coordinate: if every `x_i ≥ 1` and `a ≤ x_i` for every `i`, then
`a · B_c(x) ≤ (∑_{s ⊊ ι} c_s) · ∏_i x_i`. -/
theorem mul_properFaceSum_le (hc : ∀ s ⊂ univ, 0 ≤ c s) (hx : ∀ i, 1 ≤ x i) {a : R}
    (ha : ∀ i, a ≤ x i) :
    a * properFaceSum c x ≤ (∑ s ∈ (univ : Finset ι).ssubsets, c s) * ∏ i, x i := by
  have hx₀ : ∀ i, 0 ≤ x i := fun i ↦ zero_le_one.trans (hx i)
  rw [properFaceSum, mul_sum, sum_mul]
  refine sum_le_sum fun s hs ↦ ?_
  obtain ⟨j, -, hj⟩ := exists_of_ssubset (mem_ssubsets.1 hs)
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (hc s (mem_ssubsets.1 hs))
  calc a * ∏ i ∈ s, x i ≤ x j * ∏ i ∈ s, x i :=
        mul_le_mul_of_nonneg_right (ha j) (prod_nonneg fun i _ ↦ hx₀ i)
    _ = ∏ i ∈ insert j s, x i := (prod_insert hj).symm
    _ ≤ ∏ i, x i :=
        prod_le_prod_of_subset_of_one_le₀ (subset_univ _) (fun i _ ↦ hx₀ i) fun i _ _ ↦ hx i

/-- On the diagonal `x = (t, …, t)` with `t ≥ 1`, a proper-face sum is at most
`(∑_{s ⊊ ι} c_s) t^(|ι| - 1)`. -/
theorem properFaceSum_const_le (hc : ∀ s ⊂ univ, 0 ≤ c s) {t : R} (ht : 1 ≤ t) :
    properFaceSum c (fun _ ↦ t) ≤
      (∑ s ∈ (univ : Finset ι).ssubsets, c s) * t ^ (Fintype.card ι - 1) := by
  rw [properFaceSum, sum_mul]
  refine sum_le_sum fun s hs ↦ ?_
  have hcard : #s < Fintype.card ι := card_univ (α := ι) ▸ card_lt_card (mem_ssubsets.1 hs)
  rw [prod_const]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (by omega)) (hc s (mem_ssubsets.1 hs))

end OrderedSemiring

section Semifield

variable [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] {c : Finset ι → R} {x : ι → R}

/-- The saving at a missing coordinate in divided form: if every `x_i ≥ 1` and `0 < a ≤ x_i` for
every `i`, then `B_c(x) ≤ (∑_{s ⊊ ι} c_s) · ∏_i x_i / a`. -/
theorem properFaceSum_le_div (hc : ∀ s ⊂ univ, 0 ≤ c s) (hx : ∀ i, 1 ≤ x i) {a : R}
    (ha₀ : 0 < a) (ha : ∀ i, a ≤ x i) :
    properFaceSum c x ≤ (∑ s ∈ (univ : Finset ι).ssubsets, c s) * (∏ i, x i) / a := by
  rw [le_div_iff₀ ha₀, mul_comm]
  exact mul_properFaceSum_le hc hx ha

/-- The saving by the smallest coordinate: if every `x_i ≥ 1`, then
`B_c(x) ≤ (∑_{s ⊊ ι} c_s) · ∏_i x_i / min_i x_i`. -/
theorem properFaceSum_le_div_inf' [Nonempty ι] (hc : ∀ s ⊂ univ, 0 ≤ c s) (hx : ∀ i, 1 ≤ x i) :
    properFaceSum c x ≤
      (∑ s ∈ (univ : Finset ι).ssubsets, c s) * (∏ i, x i) / univ.inf' univ_nonempty x := by
  refine properFaceSum_le_div hc hx ?_ fun i ↦ inf'_le _ (mem_univ i)
  obtain ⟨i, -, hi⟩ := exists_mem_eq_inf' (univ_nonempty (α := ι)) x
  exact hi ▸ zero_lt_one.trans_le (hx i)

end Semifield

section Ring

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- For nonnegative variables, replacing the coefficients by their absolute values majorizes the
absolute value of a proper-face sum. -/
theorem abs_properFaceSum_le (c : Finset ι → R) {x : ι → R} (hx : ∀ i, 0 ≤ x i) :
    |properFaceSum c x| ≤ properFaceSum (fun s ↦ |c s|) x := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s _ ↦ ?_)
  rw [abs_mul, abs_of_nonneg (prod_nonneg fun i _ ↦ hx i)]

end Ring

section MvPolynomial

open MvPolynomial

variable [CommSemiring R]

/-- The `MvPolynomial` `∑_{s ⊊ ι} C(c_s) ∏_{i ∈ s} X_i` whose evaluation is the proper-face sum
`properFaceSum c`. -/
noncomputable def properFacePolynomial (c : Finset ι → R) : MvPolynomial ι R :=
  ∑ s ∈ (univ : Finset ι).ssubsets, C (c s) * ∏ i ∈ s, X i

theorem properFacePolynomial_def (c : Finset ι → R) :
    properFacePolynomial c = ∑ s ∈ (univ : Finset ι).ssubsets, C (c s) * ∏ i ∈ s, X i := by
  rw [properFacePolynomial]

@[simp]
theorem eval_properFacePolynomial (c : Finset ι → R) (x : ι → R) :
    eval x (properFacePolynomial c) = properFaceSum c x := by
  simp [properFacePolynomial, properFaceSum]

/-- A proper-face polynomial has total degree at most `|ι| - 1`. -/
theorem totalDegree_properFacePolynomial_le (c : Finset ι → R) :
    (properFacePolynomial c).totalDegree ≤ Fintype.card ι - 1 := by
  rcases subsingleton_or_nontrivial R with _ | _
  · simp [Subsingleton.elim (properFacePolynomial c) 0]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs ↦ ?_)
  have hcard : #s < Fintype.card ι := card_univ (α := ι) ▸ card_lt_card (mem_ssubsets.1 hs)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  simp only [totalDegree_X, sum_const, smul_eq_mul, mul_one]
  omega

/-- A proper-face polynomial has degree at most one in each variable. -/
theorem degreeOf_properFacePolynomial_le (c : Finset ι → R) (i : ι) :
    (properFacePolynomial c).degreeOf i ≤ 1 := by
  rcases subsingleton_or_nontrivial R with _ | _
  · simp [Subsingleton.elim (properFacePolynomial c) 0]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun s _ ↦ ?_)
  refine (degreeOf_C_mul_le _ _ _).trans ((degreeOf_prod_le _ _ _).trans ?_)
  simp only [degreeOf_X]
  rw [sum_ite_eq]
  split_ifs <;> omega

end MvPolynomial

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

variable [IsStrictOrderedRing R]

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

/-- The saving at a missing coordinate for a controlled function: if `a ≤ k_i + 1` for every `i`,
then `a · |e k| ≤ (∑_{s ⊊ ι} c_s) · ∏_i (k_i + 1)`. -/
theorem mul_abs_le (h : IsProperFaceBound c e) (hc : ∀ s ⊂ univ, 0 ≤ c s) {k : ι → ℕ} {a : R}
    (ha₀ : 0 ≤ a) (ha : ∀ i, a ≤ k i + 1) :
    a * |e k| ≤ (∑ s ∈ (univ : Finset ι).ssubsets, c s) * ∏ i, ((k i : R) + 1) :=
  (mul_le_mul_of_nonneg_left (h k) ha₀).trans
    (mul_properFaceSum_le hc (fun i ↦ by simp) ha)

/-- At parallel weights `k = (n, …, n)` a controlled function is at most
`(∑_{s ⊊ ι} c_s) (n + 1)^(|ι| - 1)`. -/
theorem abs_le_const (h : IsProperFaceBound c e) (hc : ∀ s ⊂ univ, 0 ≤ c s) (n : ℕ) :
    |e fun _ ↦ n| ≤
      (∑ s ∈ (univ : Finset ι).ssubsets, c s) * ((n : R) + 1) ^ (Fintype.card ι - 1) :=
  (h _).trans (properFaceSum_const_le hc (by simp))

end IsProperFaceBound

/-- For a nonempty index type, a constant function `b` is controlled by the single coefficient
`|b|` at the empty face. -/
theorem isProperFaceBound_const [Nonempty ι] (b : R) :
    IsProperFaceBound (Pi.single (∅ : Finset ι) |b|) fun _ ↦ b := fun _ ↦ by
  simp [properFaceSum_single, (univ_nonempty (α := ι)).ne_empty.symm]

variable [IsStrictOrderedRing R]

theorem isProperFaceBound_zero : IsProperFaceBound (0 : Finset ι → R) 0 := fun _ ↦ by simp

/-- A proper-face sum evaluated at the unshifted weights `k`, with arbitrary signed coefficients,
is controlled by nonnegative proper-face coefficients in `k + 1`. -/
theorem isProperFaceBound_properFaceSum_natCast (c : Finset ι → R) :
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
