/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import TauCeti.RingTheory.PowerSeries.Rescale
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.LinearCombination

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
* `Multiset.esymm_one`: `e₁(s)` is the sum of `s`.
* `Multiset.esymm_erase`: removing an element `a ∈ s` gives
  `eₙ(s ∖ a) = ∑_{k=0}^{n} (-1)ᵏ e_{n-k}(s) aᵏ`, and `Multiset.sum_map_mul_esymm_erase` sums it
  over `a ∈ s` against weights `w(a)`.
* `Multiset.esymm_card_eq_prod`, `Multiset.esymm_map_inv_mul_prod` and
  `Multiset.esymm_map_add_const`: `e_{card s}(s) = ∏ s`, the reversal
  `e_j(s⁻¹) ∏ s = e_{card s - j}(s)` for `0 ∉ s`, and the shift expansion
  `e_k(s + t) = ∑_{j ≤ k} binom(card s - j, k - j) e_j(s) t^{k-j}`.
* `TauCeti.esymmInt`: the elementary symmetric polynomial `e_m` of an integer degree `m`, which
  is `0` for `m < 0`.
* `TauCeti.coeff_prod_one_add_C_mul_X`: the coefficient of `tⁿ` in `∏ᵢ (1 + xᵢ t)`, as a sum
  over the `n`-element subsets of the variables.
* `TauCeti.mk_esymm_eq_prod_one_add_X`: the generating function of the `eₙ`.
* `TauCeti.mk_multiset_esymm_eq_prod_one_add_X`: the same for the `eₙ` of a family of elements.
* `TauCeti.prod_one_add_mul_eq_sum_esymm`: its evaluation at a family `μ`,
  `∏ᵢ (1 + t μᵢ) = ∑ₖ eₖ(μ) tᵏ`.
* `TauCeti.mk_neg_one_pow_mul_esymm_eq_prod_one_sub_X`: its signed version
  `∑ₙ (-1)ⁿ eₙ tⁿ = ∏ᵢ (1 - xᵢ t)`.
* `TauCeti.esymm_fin_four`: the four elementary symmetric polynomials in four variables.
* `TauCeti.eval_esymm_succ`, `TauCeti.sum_mul_eval_update_zero_esymm`,
  `TauCeti.sum_eval_update_zero_esymm` and `TauCeti.eval_add_smul_one_esymm`: for `μ : ι → R`,
  `σ_{k+1} = μ_i σ_{k;i} + σ_{k+1;i}`, `∑_i μ_i σ_{k;i} = (k + 1) σ_{k+1}`,
  `∑_i σ_{k;i} = (n - k) σ_k` and `σ_k(μ + t e) = ∑_{j ≤ k} binom(n - j, k - j) σ_j(μ) t^{k-j}`,
  where `σ_k` is `MvPolynomial.esymm` evaluated at `μ`, `σ_{k;i}` its value at `μ` with
  `μ_i = 0`, `n` the cardinality of `ι` and `e = (1, …, 1)`.

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

/-- The top elementary symmetric function of a multiset is its product: `e_{card s}(s) = ∏ s`. -/
@[simp]
theorem Multiset.esymm_card_eq_prod {R : Type*} [CommSemiring R] (s : Multiset R) :
    s.esymm (Multiset.card s) = s.prod := by
  simp [Multiset.esymm, Multiset.powersetCard_self]

/-- Reversal: the elementary symmetric functions of the inverses of a multiset `s` of nonzero
elements of a field are those of `s`, read backwards and divided by `e_{card s}(s) = ∏ s`. -/
theorem Multiset.esymm_map_inv_mul_prod {K : Type*} [Field K] (s : Multiset K)
    (hs : (0 : K) ∉ s) {j : ℕ} (hj : j ≤ Multiset.card s) :
    (s.map (·⁻¹)).esymm j * s.prod = s.esymm (Multiset.card s - j) := by
  induction s using Multiset.induction_on generalizing j with
  | empty =>
    obtain rfl : j = 0 := by simpa using hj
    simp
  | cons a t ih =>
    have ha : a ≠ 0 := fun h ↦ hs (h ▸ Multiset.mem_cons_self _ _)
    have ht : (0 : K) ∉ t := fun h ↦ hs (Multiset.mem_cons_of_mem h)
    have hinv : a⁻¹ * a = 1 := inv_mul_cancel₀ ha
    rw [Multiset.card_cons] at hj ⊢
    rcases j with _ | i
    · rw [Multiset.esymm_zero, one_mul, Nat.sub_zero, ← Multiset.card_cons a t,
        Multiset.esymm_card_eq_prod]
    rw [Multiset.map_cons, Multiset.esymm_cons, Multiset.prod_cons]
    have e1 := ih ht (j := i) (by omega)
    rcases Nat.lt_or_ge i (Multiset.card t) with hlt | hge
    · have e2 := ih ht (j := i + 1) hlt
      rw [show Multiset.card t + 1 - (i + 1) = (Multiset.card t - (i + 1)) + 1 by omega,
        Multiset.esymm_cons]
      rw [show Multiset.card t - i = Multiset.card t - (i + 1) + 1 by omega] at e1
      linear_combination a * e2 + e1 + ((t.map (·⁻¹)).esymm i * t.prod) * hinv
    · obtain rfl : i = Multiset.card t := by omega
      rw [Multiset.esymm_of_card_lt (by simp), Nat.sub_self, Multiset.esymm_zero]
      rw [Nat.sub_self, Multiset.esymm_zero] at e1
      linear_combination e1 + ((t.map (·⁻¹)).esymm (Multiset.card t) * t.prod) * hinv

open Polynomial in
/-- Shifting every element of a multiset `s` by `t`:
`e_k(s + t) = ∑_{j=0}^{k} binom(card s - j, k - j) e_j(s) t^{k-j}`. -/
theorem Multiset.esymm_map_add_const {R : Type*} [CommSemiring R] (s : Multiset R) (t : R) (k : ℕ) :
    (s.map (· + t)).esymm k =
      ∑ j ∈ Finset.range (k + 1),
        ((Multiset.card s - j).choose (k - j) : R) * s.esymm j * t ^ (k - j) := by
  rcases le_or_gt k (Multiset.card s) with hkm | hkm
  · have hcomp : ((s.map (· + t)).map fun r ↦ Polynomial.X + Polynomial.C r).prod =
        (s.map fun r ↦ Polynomial.X + Polynomial.C r).prod.comp
          (Polynomial.X + Polynomial.C t) := by
      rw [Polynomial.multiset_prod_comp, Multiset.map_map, Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun r _ ↦ ?_
      simp only [Function.comp_apply, add_comp, X_comp, C_comp, _root_.map_add]
      ring
    have h := congrArg (fun p ↦ p.coeff (Multiset.card s - k)) hcomp
    rw [Multiset.prod_X_add_C_coeff _ (by simp), Multiset.card_map,
      Nat.sub_sub_self hkm, Multiset.prod_X_add_C_eq_sum_esymm, Polynomial.sum_comp] at h
    rw [h, Polynomial.finsetSum_coeff]
    simp_rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr (show k + 1 ≤ Multiset.card s + 1 by
      omega))]
    · refine Finset.sum_congr rfl fun j hj ↦ ?_
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [show Multiset.card s - j - (Multiset.card s - k) = k - j by omega,
        show Multiset.card s - k = (Multiset.card s - j) - (k - j) by omega,
        Nat.choose_symm (by omega)]
      ring
    · intro j hj hjk
      simp only [Finset.mem_range, not_lt] at hj hjk
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero, mul_zero]
  · rw [Multiset.esymm_of_card_lt (by simpa using hkm)]
    refine (Finset.sum_eq_zero fun j _ ↦ ?_).symm
    rcases le_or_gt j (Multiset.card s) with hj | hj
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_mul]
    · rw [Multiset.esymm_of_card_lt hj, mul_zero, zero_mul]

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

section EvalUpdate

open MvPolynomial Function

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- The evaluation of `MvPolynomial.esymm` at `μ` is the elementary symmetric function of the
multiset of values of `μ`. -/
theorem eval_esymm_eq_esymm_map (μ : ι → R) (k : ℕ) :
    eval μ (esymm ι R k) = (univ.val.map μ).esymm k :=
  aeval_esymm_eq_multiset_esymm ι R k μ

variable [DecidableEq ι]

private theorem eval_update_zero_esymm (μ : ι → R) (i : ι) (k : ℕ) :
    eval (update μ i 0) (esymm ι R k) = ((univ.erase i).val.map μ).esymm k := by
  rw [eval_esymm_eq_esymm_map, ← Multiset.cons_erase (Finset.mem_univ_val i), ← Finset.erase_val,
    Multiset.map_cons, update_self,
    Multiset.map_congr rfl fun j hj ↦
      update_of_ne (Finset.ne_of_mem_erase (Finset.mem_val.mp hj)) _ _]
  cases k with
  | zero => simp
  | succ k => exact Multiset.esymm_cons_zero _ _

/-- The expansion of `σ_{k+1}(λ)` along the coordinate `λ_i`:
`σ_{k+1}(λ) = λ_i σ_{k;i}(λ) + σ_{k+1;i}(λ)`, where `σ_{k;i}(λ) = σ_k(λ)|_{λ_i = 0}`. -/
theorem eval_esymm_succ (μ : ι → R) (i : ι) (k : ℕ) :
    eval μ (esymm ι R (k + 1)) =
      μ i * eval (update μ i 0) (esymm ι R k) + eval (update μ i 0) (esymm ι R (k + 1)) := by
  rw [eval_update_zero_esymm, eval_update_zero_esymm, eval_esymm_eq_esymm_map,
    ← Multiset.cons_erase (Finset.mem_univ_val i), ← Finset.erase_val, Multiset.map_cons,
    Multiset.esymm_cons, add_comm]

/-- `∑_i σ_{k;i}(λ) = (n - k) σ_k(λ)`, where `σ_{k;i}(λ) = σ_k(λ)|_{λ_i = 0}` and `n` is the
cardinality of `ι`. -/
theorem sum_eval_update_zero_esymm (μ : ι → R) (k : ℕ) :
    ∑ i, eval (update μ i 0) (esymm ι R k) =
      ((Fintype.card ι - k : ℕ) : R) * eval μ (esymm ι R k) := by
  simp_rw [eval_update_zero_esymm, eval_esymm_eq_esymm_map, Finset.esymm_map_val]
  have h : ∀ i, powersetCard k (univ.erase i) = {A ∈ powersetCard k (univ : Finset ι) | i ∉ A} := by
    intro i
    ext A
    simp [Finset.mem_powersetCard, Finset.subset_erase, and_comm]
  simp_rw [h, Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun A hA ↦ ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_univ_sdiff,
    (Finset.mem_powersetCard.mp hA).2]

/-- The Euler identity `∑_i λ_i σ_{k;i}(λ) = (k + 1) σ_{k+1}(λ)`, where
`σ_{k;i}(λ) = σ_k(λ)|_{λ_i = 0}`. -/
theorem sum_mul_eval_update_zero_esymm (μ : ι → R) (k : ℕ) :
    ∑ i, μ i * eval (update μ i 0) (esymm ι R k) = (k + 1) * eval μ (esymm ι R (k + 1)) := by
  simp_rw [eval_update_zero_esymm, eval_esymm_eq_esymm_map, Finset.esymm_map_val, Finset.mul_sum]
  have h : ∀ i, ∑ A ∈ powersetCard k (univ.erase i), μ i * ∏ j ∈ A, μ j =
      ∑ B ∈ powersetCard (k + 1) univ, if i ∈ B then ∏ j ∈ B, μ j else 0 := by
    intro i
    rw [← Finset.sum_filter]
    have hi : ∀ A ∈ powersetCard k (univ.erase i), i ∉ A := fun A hA h ↦ by
      simpa using (Finset.subset_erase.mp (Finset.mem_powersetCard.mp hA).1).2 h
    refine Finset.sum_nbij' (insert i) (fun B ↦ B.erase i) (fun A hA ↦ ?_) (fun B hB ↦ ?_)
      (fun A hA ↦ Finset.erase_insert (hi A hA)) (fun B hB ↦ ?_)
      (fun A hA ↦ (Finset.prod_insert (hi A hA)).symm)
    · have := Finset.mem_powersetCard.mp hA
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.subset_univ _, by rw [Finset.card_insert_of_notMem (hi A hA), this.2]⟩,
        Finset.mem_insert_self _ _⟩
    · simp only [Finset.mem_filter, Finset.mem_powersetCard] at hB ⊢
      exact ⟨Finset.erase_subset_erase _ (Finset.subset_univ _), by
        rw [Finset.card_erase_of_mem hB.2, hB.1.2]; rfl⟩
    · simp only [Finset.mem_filter] at hB
      exact Finset.insert_erase hB.2
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun B hB ↦ ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
    (Finset.mem_powersetCard.mp hB).2]
  push_cast
  ring

end EvalUpdate

section Shift

open MvPolynomial

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- The shift expansion
`σ_k(λ + t e) = ∑_{j=0}^{k} binom(n - j, k - j) σ_j(λ) t^{k-j}`, where `e = (1, …, 1)` and `n` is
the cardinality of `ι`. -/
theorem eval_add_smul_one_esymm (μ : ι → R) (t : R) (k : ℕ) :
    eval (μ + t • 1) (esymm ι R k) =
      ∑ j ∈ range (k + 1),
        ((Fintype.card ι - j).choose (k - j) : R) * eval μ (esymm ι R j) * t ^ (k - j) := by
  simp_rw [eval_esymm_eq_esymm_map]
  have h : (univ.val.map (μ + t • 1)) = (univ.val.map μ).map (· + t) := by
    rw [Multiset.map_map]
    exact Multiset.map_congr rfl fun i _ ↦ by simp
  rw [h, Multiset.esymm_map_add_const, Multiset.card_map, Finset.card_val, Finset.card_univ]

end Shift

end TauCeti
