/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
public import TauCeti.RingTheory.PowerSeries.Rescale

/-!
# Elementary symmetric polynomials

This file develops the elementary symmetric polynomials `e_n`.  It defines the integer-indexed
extension `TauCeti.esymmInt`, whose negative degrees vanish, and proves the generating functions
`∑ₙ eₙ tⁿ = ∏ᵢ (1 + xᵢ t)` and `∑ₙ (-1)ⁿ eₙ tⁿ = ∏ᵢ (1 - xᵢ t)`.  The integer indexing is the one
determinantal formulas such as the dual (transpose) Jacobi--Trudi identity use.

The file also gives explicit formulas for elementary symmetric polynomials in small finite
alphabets.  Such expansions support explicit computations of symmetric orbit products; in
particular the four-variable formula is used to express the quartic `D₄` resolvent's orbit
product in elementary symmetric polynomials.

## Main results

* `Multiset.esymm_cons`: adjoining an element `a` to a multiset gives
  `e_{n+1}(a, s) = e_{n+1}(s) + a eₙ(s)`.
* `Multiset.esymm_cons_zero`: adjoining a zero gives `e_{n+1}(0, s) = e_{n+1}(s)`, and
  `Multiset.esymm_cons_zero_eq_snoc` lists `e₁, …, e_{n+1}` of `0 ::ₘ s` for `card s ≤ n`.
* `Multiset.esymm_replicate_zero`: the positive-degree elementary symmetric functions of a
  multiset of zeros vanish.
* `Multiset.esymm_one`: `e₁(s)` is the sum of `s`.
* `MvPolynomial.esymm_card`: `e_n(X₁, …, X_n)` is the product of the variables.
* `Multiset.esymm_map`: elementary symmetric functions commute with ring homomorphisms.
* `Multiset.esymm_nonneg`, `Multiset.esymm_eq_zero_of_le`: for a multiset of nonnegative elements
  of an ordered semiring, every `eₙ(s)` is nonnegative, and once one vanishes so do all those of
  higher degree.
* `Multiset.esymm_erase`: removing an element `a ∈ s` gives
  `eₙ(s ∖ a) = ∑_{k=0}^{n} (-1)ᵏ e_{n-k}(s) aᵏ`, and `Multiset.sum_map_mul_esymm_erase` sums it
  over `a ∈ s` against weights `w(a)`; `Multiset.sum_map_mul_esymm_erase_map_mul` scales that sum
  under `s ↦ c s`.
* `Multiset.esymm_card_eq_prod` and `Multiset.esymm_map_inv_mul_prod`: `e_{card s}(s) = ∏ s`
  and the reversal `e_j(s⁻¹) ∏ s = e_{card s - j}(s)` for `0 ∉ s`.
* `TauCeti.esymmInt`: the elementary symmetric polynomial `e_m` of an integer degree `m`, which
  is `0` for `m < 0`.
* `TauCeti.symmetricEsymm`: `e_k` as an element of `MvPolynomial.symmetricSubalgebra`.
* `TauCeti.coeff_prod_one_add_C_mul_X`: the coefficient of `tⁿ` in `∏ᵢ (1 + xᵢ t)`, as a sum
  over the `n`-element subsets of the variables.
* `TauCeti.mk_esymm_eq_prod_one_add_X`: the generating function of the `eₙ`.
* `TauCeti.mk_multiset_esymm_eq_prod_one_add_X`: the same for the `eₙ` of a family of elements.
* `TauCeti.prod_one_add_mul_eq_sum_esymm`: its evaluation at a family `μ`,
  `∏ᵢ (1 + t μᵢ) = ∑ₖ eₖ(μ) tᵏ`.
* `TauCeti.mk_neg_one_pow_mul_esymm_eq_prod_one_sub_X`: its signed version
  `∑ₙ (-1)ⁿ eₙ tⁿ = ∏ᵢ (1 - xᵢ t)`.
* `TauCeti.eval_add_smul_one_esymm`: the shift expansion
  `e_k(μ + t·(1, …, 1)) = ∑_{j ≤ k} binom(n - j, k - j) e_j(μ) t^(k - j)` in `n` variables.
* `TauCeti.aeval_update_zero_esymm`: `σ_{k;i}(μ)`, the value of `e_k` with the `i`-th entry of
  `μ` set to zero, is `e_k` of the entries other than the `i`-th.
* `TauCeti.aeval_esymm_succ_eq_mul_add`: `σ_{k+1} = μ_i σ_{k;i} + σ_{k+1;i}`, for values in any
  algebra; at `μ = X` it is the decomposition of `e_{k+1}` along `X_i`.
* `TauCeti.eval_add_smul_single_esymm_succ`: on the line `μ + t eᵢ`, `σ_{k+1}` is affine with
  slope `σ_{k;i}(μ)`.
* `TauCeti.sum_eval_update_zero_esymm`: `∑_i σ_{k;i}(μ) = (n - k) σ_k(μ)` in `n` variables.
* `TauCeti.esymm_fin_four`: the four elementary symmetric polynomials in four variables.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  (2.2) and (2.6').
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, §7.6.
-/

public section

open Finset

/-- Adjoining an element `a` to a multiset `s`: `e_{n+1}(a, s) = e_{n+1}(s) + a eₙ(s)`. -/
theorem Multiset.esymm_cons {R : Type*} [CommSemiring R] (a : R) (s : Multiset R) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]

/-- Adjoining a zero to a multiset `s` does not change its positive-degree elementary symmetric
values: `e_{n+1}(0, s) = e_{n+1}(s)`. -/
@[simp]
theorem Multiset.esymm_cons_zero {R : Type*} [CommSemiring R] (s : Multiset R) (n : ℕ) :
    (0 ::ₘ s).esymm (n + 1) = s.esymm (n + 1) := by
  simp [Multiset.esymm_cons]

/-- The positive-degree elementary symmetric functions of `n` zeros vanish:
`e_{j+1}(0, …, 0) = 0`. -/
@[simp]
theorem Multiset.esymm_replicate_zero {R : Type*} [CommSemiring R] (n j : ℕ) :
    (Multiset.replicate n (0 : R)).esymm (j + 1) = 0 := by
  induction n with
  | zero => exact Multiset.esymm_of_card_lt (by simp)
  | succ n ih => rw [Multiset.replicate_succ, Multiset.esymm_cons_zero, ih]

/-- Adjoining a zero to a multiset `s` of at most `n` elements appends `0` to its elementary
symmetric values: `e_{j+1}(0, s)` for `j < n + 1` is `e₁(s), …, eₙ(s), 0`. -/
theorem Multiset.esymm_cons_zero_eq_snoc {R : Type*} [CommSemiring R] {n : ℕ} (s : Multiset R)
    (hs : s.card ≤ n) :
    (fun j : Fin (n + 1) => (0 ::ₘ s).esymm (j + 1)) =
      Fin.snoc (α := fun _ => R) (fun j : Fin n => s.esymm (j + 1)) 0 := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.snoc_last, Fin.val_last, Multiset.esymm_cons_zero,
      Multiset.esymm_of_card_lt (by omega)]
  · rw [Fin.snoc_castSucc, Fin.val_castSucc, Multiset.esymm_cons_zero]

/-- The first elementary symmetric function of a multiset is its sum: `e₁(s) = ∑_{x ∈ s} x`. This
is the multiset counterpart of `MvPolynomial.esymm_one`. -/
theorem Multiset.esymm_one {R : Type*} [CommSemiring R] (s : Multiset R) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one]

/-- Elementary symmetric functions commute with ring homomorphisms:
`e_n(f(s)) = f(e_n(s))`. This is the multiset counterpart of `MvPolynomial.map_esymm`. -/
theorem Multiset.esymm_map {R S F : Type*} [CommSemiring R] [CommSemiring S] [FunLike F R S]
    [RingHomClass F R S] (f : F) (s : Multiset R) (n : ℕ) :
    (s.map f).esymm n = f (s.esymm n) := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, map_multiset_sum,
    Function.comp_def, map_multiset_prod]

/-- The elementary symmetric functions of a multiset of nonnegative elements of an ordered
semiring are nonnegative. -/
theorem Multiset.esymm_nonneg {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    {s : Multiset R} (hs : ∀ a ∈ s, 0 ≤ a) (n : ℕ) : 0 ≤ s.esymm n :=
  Multiset.sum_nonneg fun x hx ↦ by
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hx
    exact Multiset.prod_nonneg fun a ha ↦
      hs a (Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 ha)

/-- For a multiset of nonnegative elements of an ordered semiring, once an elementary symmetric
function vanishes, so do all those of higher degree: `e_j(s) = 0` and `j ≤ l` give `e_l(s) = 0`.
For nonnegative reals, `e_j(s) = 0` means that fewer than `j` elements of `s` are nonzero. -/
theorem Multiset.esymm_eq_zero_of_le {R : Type*} [CommSemiring R] [PartialOrder R]
    [IsOrderedRing R] {s : Multiset R} (hs : ∀ a ∈ s, 0 ≤ a) {j l : ℕ} (hj : s.esymm j = 0)
    (hjl : j ≤ l) : s.esymm l = 0 := by
  induction l, hjl using Nat.le_induction with
  | base => exact hj
  | succ l _ ih =>
    rcases l with _ | l
    · have : (1 : R) = 0 := by simpa using ih
      simpa using congrArg (s.esymm 1 * ·) this
    clear hj
    induction s using Multiset.induction_on with
    | empty => exact Multiset.esymm_of_card_lt (by simp)
    | cons a s ihs =>
      have hs' : ∀ b ∈ s, 0 ≤ b := fun b hb ↦ hs b (Multiset.mem_cons_of_mem hb)
      have ha : 0 ≤ a := hs a (Multiset.mem_cons_self a s)
      rw [Multiset.esymm_cons, add_eq_zero_iff_of_nonneg (Multiset.esymm_nonneg hs' _)
        (mul_nonneg ha (Multiset.esymm_nonneg hs' _))] at ih
      rw [Multiset.esymm_cons, ihs hs' ih.1, ih.1, mul_zero, add_zero]

/-- Removing an element `a` of a multiset `s` from it:
`e_n(s ∖ a) = ∑_{k=0}^{n} (-1)ᵏ e_{n-k}(s) aᵏ`. This is the coefficient form of
`∏_{x ∈ s ∖ a} (1 + x t) = ∏_{x ∈ s} (1 + x t) / (1 + a t)`. -/
theorem Multiset.esymm_erase {R : Type*} [CommRing R] [DecidableEq R] {s : Multiset R} {a : R}
    (ha : a ∈ s) (n : ℕ) :
    (s.erase a).esymm n = ∑ k ∈ Finset.range (n + 1), (-1) ^ k * s.esymm (n - k) * a ^ k := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
  rw [Multiset.erase_cons_head]
  induction n with
  | zero => simp
  | succ n ih =>
    have h : ∑ k ∈ Finset.range (n + 1),
        (-1) ^ (k + 1) * (a ::ₘ t).esymm (n + 1 - (k + 1)) * a ^ (k + 1) =
        -a * ∑ k ∈ Finset.range (n + 1), (-1) ^ k * (a ::ₘ t).esymm (n - k) * a ^ k := by
      rw [mul_sum]
      refine sum_congr rfl fun k _ ↦ ?_
      rw [Nat.add_sub_add_right]
      ring
    rw [sum_range_succ', h, ← ih, Nat.sub_zero, Multiset.esymm_cons]
    ring

/-- The sum over the elements `a` of a multiset `s` of `w(a) e_n(s ∖ a)`, expanded by
`Multiset.esymm_erase` as a combination of the elementary symmetric functions of `s` and the
weighted power sums `∑_{a ∈ s} aᵏ w(a)`. -/
theorem Multiset.sum_map_mul_esymm_erase {R : Type*} [CommRing R] [DecidableEq R]
    (s : Multiset R) (w : R → R) (n : ℕ) :
    (s.map fun a ↦ w a * (s.erase a).esymm n).sum =
      ∑ k ∈ Finset.range (n + 1), (-1) ^ k * s.esymm (n - k) *
        (s.map fun a ↦ a ^ k * w a).sum := by
  rw [Multiset.map_congr rfl fun a ha ↦ by rw [Multiset.esymm_erase ha, mul_sum]]
  simp only [Finset.sum_eq_multiset_sum]
  rw [Multiset.sum_map_sum_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun k _ ↦ ?_)
  rw [← Multiset.sum_map_mul_left]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun a _ ↦ by ring)

/-- Scaling a multiset `s` by `c`, with a weight `w` satisfying `w(c a) = d w(a)`, scales
`∑_{a ∈ s} w(a) eₙ(s ∖ a)` by `cⁿ d`. No condition on `c` is needed. -/
theorem Multiset.sum_map_mul_esymm_erase_map_mul {R : Type*} [CommRing R] [DecidableEq R]
    (s : Multiset R) {w : R → R} {c d : R} (hw : ∀ a, w (c * a) = d * w a) (n : ℕ) :
    ((s.map (c * ·)).map fun a ↦ w a * ((s.map (c * ·)).erase a).esymm n).sum =
      c ^ n * d * (s.map fun a ↦ w a * (s.erase a).esymm n).sum := by
  rw [Multiset.sum_map_mul_esymm_erase, Multiset.sum_map_mul_esymm_erase, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  have hesymm : (s.map (c * ·)).esymm (n - k) = c ^ (n - k) * s.esymm (n - k) := by
    simpa only [smul_eq_mul] using (Multiset.pow_smul_esymm c (n - k) s).symm
  have hsum : ((s.map (c * ·)).map fun a ↦ a ^ k * w a).sum =
      c ^ k * d * (s.map fun a ↦ a ^ k * w a).sum := by
    rw [Multiset.map_map, ← Multiset.sum_map_mul_left]
    exact congrArg Multiset.sum (Multiset.map_congr rfl fun a _ ↦ by
      simp only [Function.comp_apply, hw, mul_pow]; ring)
  rw [hesymm, hsum, ← pow_sub_mul_pow c hkn]
  ring

/-- The top elementary symmetric function of a multiset is its product: `e_{card s}(s) = ∏ s`. -/
@[simp]
theorem Multiset.esymm_card_eq_prod {R : Type*} [CommSemiring R] (s : Multiset R) :
    s.esymm (Multiset.card s) = s.prod := by
  simp [Multiset.esymm, Multiset.powersetCard_self]

/-- Reversal: the elementary symmetric functions of the inverses of a multiset `s` of nonzero
elements of a semifield are those of `s`, read backwards and divided by `e_{card s}(s) = ∏ s`. -/
theorem Multiset.esymm_map_inv_mul_prod {K : Type*} [Semifield K] (s : Multiset K)
    (hs : (0 : K) ∉ s) {j : ℕ} (hj : j ≤ Multiset.card s) :
    (s.map (·⁻¹)).esymm j * s.prod = s.esymm (Multiset.card s - j) := by
  induction s using Multiset.induction_on generalizing j with
  | empty =>
    obtain rfl : j = 0 := by simpa using hj
    simp
  | cons a t ih =>
    have ha : a ≠ 0 := fun h ↦ hs (h ▸ Multiset.mem_cons_self _ _)
    have ht : (0 : K) ∉ t := fun h ↦ hs (Multiset.mem_cons_of_mem h)
    -- The factor `a⁻¹` of the new term cancels against the factor `a` of the new product.
    have hinv (x : K) : a⁻¹ * x * (a * t.prod) = x * t.prod := by
      rw [mul_mul_mul_comm, inv_mul_cancel₀ ha, one_mul]
    rw [Multiset.card_cons] at hj ⊢
    rcases j with _ | i
    · rw [Multiset.esymm_zero, one_mul, Nat.sub_zero, ← Multiset.card_cons a t,
        Multiset.esymm_card_eq_prod]
    rw [Multiset.map_cons, Multiset.esymm_cons, Multiset.prod_cons, add_mul, hinv,
      ih ht (j := i) (by omega)]
    rcases Nat.lt_or_ge i (Multiset.card t) with hlt | hge
    · -- Both remaining indices are one more than `card t - (i + 1)`; expand by `esymm_cons`.
      have h1 : Multiset.card t - i = Multiset.card t - (i + 1) + 1 := by omega
      have h2 : Multiset.card t + 1 - (i + 1) = Multiset.card t - (i + 1) + 1 := by omega
      rw [h1, h2, Multiset.esymm_cons, ← ih ht hlt]
      ring
    · obtain rfl : i = Multiset.card t := by omega
      rw [Multiset.esymm_of_card_lt (by simp), zero_mul, zero_add, Nat.sub_self, Nat.sub_self,
        Multiset.esymm_zero, Multiset.esymm_zero]

/-- The elementary symmetric polynomial whose degree is the number of variables is the product of
all the variables: `e_n(X₁, …, X_n) = X₁ ⋯ X_n`. -/
theorem MvPolynomial.esymm_card (σ : Type*) [Fintype σ] (R : Type*) [CommSemiring R] :
    MvPolynomial.esymm σ R (Fintype.card σ) = ∏ i, MvPolynomial.X i := by
  rw [MvPolynomial.esymm, ← Finset.card_univ, Finset.powersetCard_self, Finset.sum_singleton]

namespace TauCeti

section esymmInt

variable (σ : Type*) [Fintype σ] (R : Type*) [CommSemiring R]

/-- The **elementary symmetric polynomial of integer degree** `m`: `e_m` for `m ≥ 0` and `0` for
`m < 0`.  This is the indexing determinantal formulas such as the dual Jacobi--Trudi identity
use. -/
noncomputable def esymmInt (m : ℤ) : MvPolynomial σ R :=
  if 0 ≤ m then MvPolynomial.esymm σ R m.toNat else 0

variable {σ R}

/-- In a nonnegative degree, `TauCeti.esymmInt` is `MvPolynomial.esymm`. -/
@[simp]
theorem esymmInt_of_nonneg {m : ℤ} (hm : 0 ≤ m) :
    esymmInt σ R m = MvPolynomial.esymm σ R m.toNat := by
  simp [esymmInt, hm]

/-- In a negative degree, `TauCeti.esymmInt` vanishes. -/
@[simp]
theorem esymmInt_of_neg {m : ℤ} (hm : m < 0) : esymmInt σ R m = 0 := by
  simp [esymmInt, not_le.mpr hm]

/-- In a natural-number degree, `TauCeti.esymmInt` is `MvPolynomial.esymm`. -/
theorem esymmInt_natCast (n : ℕ) : esymmInt σ R n = MvPolynomial.esymm σ R n := by
  simp [esymmInt]

/-- `e_0 = 1`. -/
theorem esymmInt_zero : esymmInt σ R 0 = 1 := by
  simp

/-- Changing the coefficients along a ring homomorphism preserves `TauCeti.esymmInt`. -/
@[simp]
theorem map_esymmInt {S : Type*} [CommSemiring S] (m : ℤ) (f : R →+* S) :
    MvPolynomial.map f (esymmInt σ R m) = esymmInt σ S m := by
  unfold esymmInt
  split_ifs <;> simp [MvPolynomial.map_esymm]

/-- Renaming the variables along a bijection preserves `TauCeti.esymmInt`. -/
@[simp]
theorem rename_esymmInt {τ : Type*} [Fintype τ] (m : ℤ) (e : σ ≃ τ) :
    MvPolynomial.rename e (esymmInt σ R m) = esymmInt τ R m := by
  unfold esymmInt
  split_ifs <;> simp [MvPolynomial.rename_esymm]

end esymmInt

section symmetricEsymm

variable (σ : Type*) [Fintype σ] (R : Type*) [CommSemiring R]

/-- The elementary symmetric polynomial `MvPolynomial.esymm σ R k`, as an element of
`MvPolynomial.symmetricSubalgebra`. -/
noncomputable def symmetricEsymm (k : ℕ) : MvPolynomial.symmetricSubalgebra σ R :=
  ⟨MvPolynomial.esymm σ R k, MvPolynomial.esymm_isSymmetric σ R k⟩

variable {σ R}

@[simp, norm_cast]
theorem coe_symmetricEsymm (k : ℕ) :
    (symmetricEsymm σ R k : MvPolynomial σ R) = MvPolynomial.esymm σ R k :=
  (rfl)

/-- The elementary symmetric polynomial `e_k` in the symmetric subalgebra vanishes when `k`
exceeds the number of variables. -/
theorem symmetricEsymm_eq_zero_of_lt {k : ℕ} (h : Fintype.card σ < k) :
    symmetricEsymm σ R k = 0 := by
  ext1
  rw [coe_symmetricEsymm, MvPolynomial.esymm_eq_multiset_esymm]
  exact Multiset.esymm_of_card_lt (by simpa using h)

end symmetricEsymm

section GeneratingFunction

variable {σ : Type*} [Fintype σ] (R : Type*) [CommSemiring R]

/-- **The coefficient of `tⁿ` in `∏ᵢ (1 + xᵢ t)`**: the sum, over the `n`-element subsets `s` of
the variables, of the product of the variables in `s`. -/
theorem coeff_prod_one_add_C_mul_X (n : ℕ) :
    (∏ i, (1 + PowerSeries.C (MvPolynomial.X i : MvPolynomial σ R) *
      PowerSeries.X)).coeff n =
      ∑ s ∈ Finset.powersetCard n (Finset.univ : Finset σ), ∏ i ∈ s, MvPolynomial.X i := by
  classical
  rw [Finset.prod_one_add, map_sum, Finset.powersetCard_eq_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h : ∏ i ∈ s, (PowerSeries.C (MvPolynomial.X i : MvPolynomial σ R) * PowerSeries.X) =
      PowerSeries.C (∏ i ∈ s, (MvPolynomial.X i : MvPolynomial σ R)) *
        PowerSeries.X ^ s.card := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← map_prod]
  rw [h, PowerSeries.coeff_C_mul_X_pow]
  by_cases hs : s.card = n
  · subst hs
    simp
  · have hnt : n ≠ s.card := fun h => hs h.symm
    simp [hs, hnt]

/-- **The generating function of the elementary symmetric polynomials**:
`∑ₙ eₙ tⁿ = ∏ᵢ (1 + xᵢ t)`. -/
theorem mk_esymm_eq_prod_one_add_X :
    PowerSeries.mk (fun n => MvPolynomial.esymm σ R n) =
      ∏ i, (1 + PowerSeries.C (MvPolynomial.X i : MvPolynomial σ R) * PowerSeries.X) := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_mk, coeff_prod_one_add_C_mul_X, MvPolynomial.esymm]

variable {R}

/-- **The generating function of the elementary symmetric functions of a family**:
`∑ₙ eₙ(w) tⁿ = ∏ᵢ (1 + wᵢ t)` for a finite family `w` of elements of a commutative semiring. -/
theorem mk_multiset_esymm_eq_prod_one_add_X (w : σ → R) :
    PowerSeries.mk (fun n => (Finset.univ.val.map w).esymm n) =
      ∏ i, (1 + PowerSeries.C (w i) * PowerSeries.X) := by
  have h := congrArg (PowerSeries.map (MvPolynomial.aeval w).toRingHom)
    (mk_esymm_eq_prod_one_add_X (σ := σ) R)
  rw [map_prod] at h
  simp only [map_add, map_one, map_mul, PowerSeries.map_C, PowerSeries.map_X,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X] at h
  rw [← h]
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk, RingHom.coe_coe,
    MvPolynomial.aeval_esymm_eq_multiset_esymm]

/-- **The evaluated generating function of the elementary symmetric polynomials**: for a finite
family `μ` of elements of a commutative semiring and any `t`,
`∏ᵢ (1 + t μᵢ) = ∑_{k ≤ |σ|} eₖ(μ) tᵏ`. -/
theorem prod_one_add_mul_eq_sum_esymm (μ : σ → R) (t : R) :
    ∏ i, (1 + t * μ i) =
      ∑ k ∈ Finset.range (Fintype.card σ + 1),
        MvPolynomial.eval μ (MvPolynomial.esymm σ R k) * t ^ k := by
  classical
  rw [Finset.prod_one_add, ← Finset.sum_fiberwise_of_maps_to (g := Finset.card)
    (t := Finset.range (Fintype.card σ + 1)) fun s _ ↦ by
      simpa [Nat.lt_succ_iff] using Finset.card_le_univ s]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← Finset.powersetCard_eq_filter]
  simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.eval_X, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp hs).2, mul_comm]

end GeneratingFunction

section SignedGeneratingFunction

variable {σ : Type*} [Fintype σ] (R : Type*) [CommRing R]

/-- **The signed generating function of the elementary symmetric polynomials**:
`∑ₙ (-1)ⁿ eₙ tⁿ = ∏ᵢ (1 - xᵢ t)`. -/
theorem mk_neg_one_pow_mul_esymm_eq_prod_one_sub_X :
    PowerSeries.mk (fun n => (-1 : MvPolynomial σ R) ^ n * MvPolynomial.esymm σ R n) =
      ∏ i, (1 - PowerSeries.C (MvPolynomial.X i : MvPolynomial σ R) * PowerSeries.X) := by
  rw [← PowerSeries.rescale_mk, mk_esymm_eq_prod_one_add_X (σ := σ) R, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [map_add, map_mul, map_neg, map_one, PowerSeries.rescale_X, PowerSeries.rescale_C]
  ring

end SignedGeneratingFunction

/-- **The elementary symmetric functions of a shifted family**: translating every entry of
`μ : σ → R` by `t`, with `n = |σ|`,
`e_k(μ + t·(1, …, 1)) = ∑_{j ≤ k} binom(n - j, k - j) e_j(μ) t^(k - j)`.
For `k > n` both sides vanish. -/
theorem eval_add_smul_one_esymm {σ R : Type*} [Fintype σ] [CommSemiring R] (μ : σ → R) (t : R)
    (k : ℕ) :
    MvPolynomial.eval (μ + t • 1) (MvPolynomial.esymm σ R k) =
      ∑ j ∈ range (k + 1), ((Fintype.card σ - j).choose (k - j) : R) *
        MvPolynomial.eval μ (MvPolynomial.esymm σ R j) * t ^ (k - j) := by
  classical
  simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.eval_X, Pi.add_apply,
    Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, mul_sum, sum_mul]
  calc ∑ s ∈ powersetCard k univ, ∏ i ∈ s, (μ i + t)
      = ∑ s ∈ powersetCard k univ, ∑ u ∈ s.powerset, (∏ i ∈ u, μ i) * t ^ (k - #u) := by
        refine sum_congr rfl fun s hs ↦ ?_
        rw [prod_add]
        refine sum_congr rfl fun u hu ↦ ?_
        rw [prod_const, card_sdiff_of_subset (mem_powerset.mp hu), (mem_powersetCard.mp hs).2]
    _ = ∑ u ∈ univ.powerset with #u ≤ k,
          ∑ s ∈ powersetCard k univ with u ⊆ s, (∏ i ∈ u, μ i) * t ^ (k - #u) := by
        refine sum_comm' fun s u ↦ ?_
        simp only [mem_powersetCard, mem_powerset, mem_filter, subset_univ, true_and]
        constructor
        · rintro ⟨hs, hu⟩
          exact ⟨⟨hs, hu⟩, hs ▸ card_le_card hu⟩
        · rintro ⟨⟨hs, hu⟩, -⟩
          exact ⟨hs, hu⟩
    _ = ∑ u ∈ univ.powerset with #u ≤ k,
          ((Fintype.card σ - #u).choose (k - #u) : R) * (∏ i ∈ u, μ i) * t ^ (k - #u) := by
        refine sum_congr rfl fun u hu ↦ ?_
        rw [sum_const, card_filter_powersetCard_subset u univ k (subset_univ u)
          (mem_filter.mp hu).2, card_univ, nsmul_eq_mul, mul_assoc]
    _ = _ := by
        rw [← sum_fiberwise_of_maps_to (g := card) (t := range (k + 1))
          fun u hu ↦ mem_range_succ_iff.mpr (mem_filter.mp hu).2]
        refine sum_congr rfl fun j hj ↦ ?_
        have hset : (univ : Finset σ).powerset.filter (fun u ↦ #u ≤ k ∧ #u = j) =
            powersetCard j univ := by
          ext u
          simp only [mem_filter, mem_powerset, mem_powersetCard, subset_univ, true_and]
          constructor
          · exact fun h ↦ h.2
          · exact fun h ↦ ⟨h ▸ mem_range_succ_iff.mp hj, h⟩
        rw [filter_filter, hset]
        refine sum_congr rfl fun u hu ↦ ?_
        rw [(mem_powersetCard.mp hu).2]

section DeletedEntry

open Function MvPolynomial

variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R]

/-- **`σ_{k;i}` is the elementary symmetric function of the other entries.** Setting the `i`-th
entry of a family `f` to zero and evaluating `e_k` gives `e_k` of the entries `f j`, `j ≠ i`. -/
theorem aeval_update_zero_esymm {S : Type*} [CommSemiring S] [Algebra R S] (f : σ → S) (i : σ)
    (k : ℕ) :
    aeval (update f i 0) (esymm σ R k) = ((univ.erase i).val.map f).esymm k := by
  have h : univ.val.map (update f i 0) = 0 ::ₘ (univ.erase i).val.map f := by
    rw [← Multiset.cons_erase (mem_univ i), Multiset.map_cons, update_self, erase_val]
    refine congrArg _ (Multiset.map_congr rfl fun j hj ↦ update_of_ne ?_ _ _)
    exact ((Multiset.Nodup.mem_erase_iff univ.nodup).mp hj).1
  rw [aeval_esymm_eq_multiset_esymm, h]
  cases k <;> simp

/-- **The recurrence of the elementary symmetric functions along one entry**:
`σ_{k+1}(f) = f_i σ_{k;i}(f) + σ_{k+1;i}(f)`, where `σ_{k;i}(f)` is the value of `e_k` with the
`i`-th entry of `f` set to zero. At `f = X` this decomposes `e_{k+1}` along the variable `X_i`. -/
theorem aeval_esymm_succ_eq_mul_add {S : Type*} [CommSemiring S] [Algebra R S] (f : σ → S)
    (i : σ) (k : ℕ) :
    aeval f (esymm σ R (k + 1)) =
      f i * aeval (update f i 0) (esymm σ R k) + aeval (update f i 0) (esymm σ R (k + 1)) := by
  rw [aeval_update_zero_esymm, aeval_update_zero_esymm, aeval_esymm_eq_multiset_esymm,
    ← Multiset.cons_erase (mem_univ i), Multiset.map_cons, erase_val, Multiset.esymm_cons,
    add_comm]

/-- **`σ_{k+1}` is affine along a coordinate line**: on the line `f + t eᵢ`,
`σ_{k+1}(f + t eᵢ) = (f_i + t) σ_{k;i}(f) + σ_{k+1;i}(f)`, so its slope is `σ_{k;i}(f)`. -/
theorem eval_add_smul_single_esymm_succ (f : σ → R) (i : σ) (k : ℕ) (t : R) :
    eval (f + t • Pi.single i 1) (esymm σ R (k + 1)) =
      (f i + t) * eval (update f i 0) (esymm σ R k) +
        eval (update f i 0) (esymm σ R (k + 1)) := by
  have hu : update (f + t • Pi.single i 1) i 0 = update f i 0 := by
    ext j
    by_cases hj : j = i <;> simp [hj, update_of_ne]
  have h := aeval_esymm_succ_eq_mul_add (R := R) (f + t • Pi.single i 1) i k
  simp only [hu] at h
  simpa using h

/-- **The sum of the elementary symmetric functions with one entry deleted**:
`∑_i σ_{k;i}(μ) = (n - k) σ_k(μ)` for `n` variables, where `σ_{k;i}(μ)` is the value of `e_k`
with the `i`-th entry of `μ` set to zero. Since `σ_{k;i} = ∂σ_{k+1}/∂μ_i`, this is the sum
`∑_i ∂σ_{k+1}/∂μ_i = (n - k) σ_k` of the partial derivatives. For `k > n` both sides vanish. -/
theorem sum_eval_update_zero_esymm (μ : σ → R) (k : ℕ) :
    ∑ i, eval (update μ i 0) (esymm σ R k) =
      ((Fintype.card σ - k : ℕ) : R) * eval μ (esymm σ R k) := by
  have h : ∀ i, eval (update μ i 0) (esymm σ R k) =
      ∑ s ∈ powersetCard k univ, if i ∉ s then ∏ j ∈ s, μ j else 0 := by
    intro i
    simp only [esymm, map_sum, map_prod, eval_X]
    refine sum_congr rfl fun s _ ↦ ?_
    split_ifs with hi
    · exact prod_eq_zero hi (update_self ..)
    · exact prod_congr rfl fun j hj ↦ update_of_ne (ne_of_mem_of_not_mem hj hi) _ _
  simp_rw [h]
  simp only [esymm, map_sum, map_prod, eval_X, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun s hs ↦ ?_
  rw [← sum_filter, sum_const, filter_notMem_eq_sdiff, card_sdiff_of_subset (subset_univ s),
    card_univ, (mem_powersetCard.mp hs).2, nsmul_eq_mul]

end DeletedEntry

/-- The elementary symmetric polynomials in four variables, written out explicitly. -/
theorem esymm_fin_four {R : Type*} [CommSemiring R] :
    MvPolynomial.esymm (Fin 4) R 1 =
        MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2 + MvPolynomial.X 3 ∧
      MvPolynomial.esymm (Fin 4) R 2 =
        MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.X 0 * MvPolynomial.X 2 +
          MvPolynomial.X 0 * MvPolynomial.X 3 + MvPolynomial.X 1 * MvPolynomial.X 2 +
          MvPolynomial.X 1 * MvPolynomial.X 3 + MvPolynomial.X 2 * MvPolynomial.X 3 ∧
      MvPolynomial.esymm (Fin 4) R 3 =
        MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 +
          MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 3 +
          MvPolynomial.X 0 * MvPolynomial.X 2 * MvPolynomial.X 3 +
          MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3 ∧
      MvPolynomial.esymm (Fin 4) R 4 =
        MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 * MvPolynomial.X 3 := by
  have h1 : Finset.powersetCard 1 (Finset.univ : Finset (Fin 4)) = {{0}, {1}, {2}, {3}} := by
    decide
  have h2 : Finset.powersetCard 2 (Finset.univ : Finset (Fin 4)) =
      {{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}} := by
    decide
  have h3 : Finset.powersetCard 3 (Finset.univ : Finset (Fin 4)) =
      {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}} := by
    decide
  have h4 : Finset.powersetCard 4 (Finset.univ : Finset (Fin 4)) = {{0, 1, 2, 3}} := by
    decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp (config := { decide := true }) only [MvPolynomial.esymm, h1, h2, h3, h4,
        Finset.sum_insert, Finset.prod_insert, Finset.sum_singleton, Finset.prod_singleton,
        Finset.mem_insert, Finset.mem_singleton, add_assoc, mul_assoc]

end TauCeti
