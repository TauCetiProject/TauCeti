/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Polynomial.Derivative

/-! # Polynomial Rolle and mean value

`TauCeti.PolynomialRolle R` states that equal polynomial values at distinct endpoints give
an interior root of the formal derivative. From this explicit hypothesis,
`PolynomialRolle.exists_eval_sub_eq_derivative_eval_mul` derives polynomial mean value; over an
ordered field, `PolynomialRolle.monotoneOn`, `antitoneOn`, `strictMonoOn`, and `strictAntiOn`
derive the corresponding order properties from derivative signs.

Roots of the derivative separate the roots of the polynomial. A field with polynomial Rolle has
characteristic zero (`PolynomialRolle.charZero`), a polynomial is injective on every
order-connected set free of derivative roots (`PolynomialRolle.injOn_eval`), and the number of
roots of `p`, distinct or counted with multiplicity, is at most one more than the corresponding
number for `p.derivative` (`PolynomialRolle.card_roots_toFinset_le_derivative`,
`PolynomialRolle.card_roots_le_derivative`). These are the algebraic counterparts of the
real-analytic root counts in `Mathlib.Analysis.Calculus.LocalExtr.Polynomial`, whose proofs
(by Benjamin Davidson and Yury Kudryashov) they follow with polynomial Rolle in place of Rolle's
theorem for differentiable functions. Consequently the derivatives of a split polynomial split
(`PolynomialRolle.splits_derivative`, `PolynomialRolle.splits_iterate_derivative`).

`TauCeti.FieldTheory.RealClosure.AbstractRolle` supplies this hypothesis from `IsRealClosed`
as `TauCeti.RealClosure.polynomialRolle_of_isRealClosed`, and exports direct `Polynomial`
versions of the mean value and monotonicity results for real closed ordered fields. Over a
real closed field, the root counts are applied as, for instance,
`polynomialRolle_of_isRealClosed.card_roots_le_derivative`. The `IsRealClosed ℝ` instance
specializes those statements to the real numbers.
-/

public section

open Polynomial Set

namespace TauCeti

/-- Polynomial Rolle: whenever a polynomial takes equal values at `a < b`, its formal
derivative has a root in `Ioo a b`. -/
def PolynomialRolle (R : Type*) [Field R] [LinearOrder R] : Prop :=
  ∀ (p : R[X]) (a b : R), a < b → p.eval a = p.eval b →
    ∃ c ∈ Ioo a b, p.derivative.eval c = 0

variable {R : Type*} [Field R] [LinearOrder R]

/-- Construct the polynomial Rolle property from its quantified statement. -/
theorem PolynomialRolle.of_forall
    (h : ∀ (p : R[X]) (a b : R), a < b → p.eval a = p.eval b →
      ∃ c ∈ Ioo a b, p.derivative.eval c = 0) : PolynomialRolle R := h

/-- Equal polynomial values at distinct endpoints give an interior derivative root. -/
theorem PolynomialRolle.exists_derivative_root (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hab : a < b) (heq : p.eval a = p.eval b) :
    ∃ c ∈ Ioo a b, p.derivative.eval c = 0 := h p a b hab heq

/-- Polynomial Rolle implies the mean value equality
`p.eval b - p.eval a = p.derivative.eval c * (b - a)` at some point `c ∈ Ioo a b`. -/
theorem PolynomialRolle.exists_eval_sub_eq_derivative_eval_mul
    (h : PolynomialRolle R) (p : R[X]) {a b : R} (hab : a < b) :
    ∃ c ∈ Ioo a b, p.eval b - p.eval a = p.derivative.eval c * (b - a) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  set m := (p.eval b - p.eval a) / (b - a)
  have hm : m * (b - a) = p.eval b - p.eval a := div_mul_cancel₀ _ hba
  obtain ⟨c, hc, hd⟩ := h.exists_derivative_root (p - C m * X) hab (by
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    linear_combination hm)
  have hd' : p.derivative.eval c = m := by simpa [sub_eq_zero] using hd
  exact ⟨c, hc, by rw [hd', hm]⟩

/-- The mean value point for a subinterval lies in the surrounding open interval. -/
private theorem PolynomialRolle.exists_sub_eq (h : PolynomialRolle R) (p : R[X]) {a b u v : R}
    (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u < v) :
    ∃ c ∈ Ioo a b, p.eval v - p.eval u = p.derivative.eval c * (v - u) := by
  obtain ⟨c, hc, he⟩ := h.exists_eval_sub_eq_derivative_eval_mul p huv
  exact ⟨c, ⟨hu.1.trans_lt hc.1, hc.2.trans_le hv.2⟩, he⟩

/-! ### Root separation by derivative roots -/

/-- A field with polynomial Rolle has characteristic zero: if `(n : R) = 0` for some `n ≥ 1`,
then `X ^ n - X` vanishes at `0` and `1` while its derivative is the constant `-1`. -/
theorem PolynomialRolle.charZero (h : PolynomialRolle R) : CharZero R := by
  refine charZero_of_inj_zero fun n hn ↦ by_contra fun hn0 ↦ ?_
  have key {a b : R} (hab : a < b) (ha : a ^ n = a) (hb : b ^ n = b) : False := by
    obtain ⟨c, -, hc⟩ := h.exists_derivative_root (X ^ n - X) hab (by simp [ha, hb])
    simp [derivative_X_pow, hn] at hc
  rcases (zero_ne_one' R).lt_or_gt with hlt | hlt
  · exact key hlt (zero_pow hn0) (one_pow n)
  · exact key hlt (one_pow n) (zero_pow hn0)

/-- Roots of the derivative separate the values of a polynomial: on an order-connected set
containing no root of the derivative, the polynomial is injective. In particular such a set
contains at most one root of the polynomial. -/
theorem PolynomialRolle.injOn_eval (h : PolynomialRolle R) (p : R[X]) {s : Set R}
    (hs : s.OrdConnected) (hd : ∀ x ∈ s, p.derivative.eval x ≠ 0) : InjOn p.eval s := by
  have key {x y : R} (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) : p.eval x ≠ p.eval y := fun he ↦ by
    obtain ⟨c, hc, hc0⟩ := h.exists_derivative_root p hxy he
    exact hd c (hs.out hx hy (Ioo_subset_Icc_self hc)) hc0
  intro x hx y hy he
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key hx hy hlt he
  · exact key hy hx hlt he.symm

/-- Between two consecutive distinct roots of a polynomial lies a root of its derivative that is
not a root of the polynomial, so the number of distinct roots of `p` is at most one more than the
number of distinct roots of `p.derivative` that are not roots of `p`. -/
theorem PolynomialRolle.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ
    (h : PolynomialRolle R) (p : R[X]) :
    p.roots.toFinset.card ≤ (p.derivative.roots.toFinset \ p.roots.toFinset).card + 1 := by
  have := h.charZero
  rcases eq_or_ne p.derivative 0 with hp' | hp'
  · rw [eq_C_of_derivative_eq_zero hp']
    simp
  have hp : p ≠ 0 := ne_of_apply_ne derivative (by rwa [derivative_zero])
  refine Finset.card_le_sdiff_of_interleaved fun x hx y hy hxy hxy' ↦ ?_
  rw [Multiset.mem_toFinset, mem_roots hp] at hx hy
  obtain ⟨z, hz, hz0⟩ := h.exists_derivative_root p hxy (hx.trans hy.symm)
  exact ⟨z, by rwa [Multiset.mem_toFinset, mem_roots hp', IsRoot], hz⟩

/-- The number of distinct roots of a polynomial is at most one more than the number of distinct
roots of its derivative. -/
theorem PolynomialRolle.card_roots_toFinset_le_derivative (h : PolynomialRolle R) (p : R[X]) :
    p.roots.toFinset.card ≤ p.derivative.roots.toFinset.card + 1 :=
  (h.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ p).trans <| by
    grw [Finset.sdiff_subset]

/-- The number of roots of a polynomial counted with multiplicity is at most one more than the
number of roots of its derivative counted with multiplicity. -/
theorem PolynomialRolle.card_roots_le_derivative (h : PolynomialRolle R) (p : R[X]) :
    Multiset.card p.roots ≤ Multiset.card p.derivative.roots + 1 := by
  have := h.charZero
  -- At a root of `p` of multiplicity `m`, `p'` has root multiplicity at least `m - 1`; the
  -- remaining one per distinct root is paid for by the roots of `p'` that are not roots of `p`.
  -- Taking cardinalities, combine with the bound on distinct roots.
  have hcard := Multiset.card_le_card
    (roots_add_roots_derivative_sdiff_roots_le_roots_derivative_add_roots_toFinset p)
  simp only [Multiset.card_add, Finset.card_val] at hcard
  have := h.card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ p
  omega

/-- For a polynomial over a commutative ring `F` with an algebra map to `R`, the number of its
roots in `R` is at most one more than the number of roots in `R` of its derivative. -/
theorem PolynomialRolle.card_rootSet_le_derivative (h : PolynomialRolle R) {F : Type*}
    [CommRing F] [Algebra F R] (p : F[X]) :
    Fintype.card (p.rootSet R) ≤ Fintype.card (p.derivative.rootSet R) + 1 := by
  classical
  simpa only [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe, derivative_map] using
    h.card_roots_toFinset_le_derivative (p.map (algebraMap F R))

/-- With polynomial Rolle, the derivative of a split polynomial splits: a polynomial of degree `d`
with `d` roots counted with multiplicity has a derivative with at least `d - 1` roots. -/
theorem PolynomialRolle.splits_derivative (h : PolynomialRolle R) {p : R[X]} (hp : p.Splits) :
    p.derivative.Splits := by
  rw [splits_iff_card_roots] at hp ⊢
  have hroots := h.card_roots_le_derivative p
  have hdeg := natDegree_derivative_le p
  have hcard := card_roots' p.derivative
  omega

/-- With polynomial Rolle, every iterated derivative of a split polynomial splits. -/
theorem PolynomialRolle.splits_iterate_derivative (h : PolynomialRolle R) {p : R[X]}
    (hp : p.Splits) (k : ℕ) : (derivative^[k] p).Splits := by
  induction k with
  | zero => exact hp
  | succ k ih => exact Function.iterate_succ_apply' derivative k p ▸ h.splits_derivative ih

variable [IsStrictOrderedRing R]

/-- Polynomial Rolle implies monotonicity where the derivative is nonnegative. -/
theorem PolynomialRolle.monotoneOn (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, 0 ≤ p.derivative.eval x) : MonotoneOn p.eval (Icc a b) := by
  intro u hu v hv huv
  rcases huv.eq_or_lt with rfl | huv
  · exact le_rfl
  obtain ⟨c, hc, he⟩ := h.exists_sub_eq p hu hv huv
  rw [← sub_nonneg, he]
  exact mul_nonneg (hd c hc) (sub_pos.mpr huv).le

/-- Polynomial Rolle implies antitonicity where the derivative is nonpositive. -/
theorem PolynomialRolle.antitoneOn (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, p.derivative.eval x ≤ 0) : AntitoneOn p.eval (Icc a b) := by
  -- `-p` has the opposite derivative sign, so `monotoneOn` applies to it.
  have h' := h.monotoneOn (-p) fun x hx ↦ by
    simpa only [derivative_neg, eval_neg, neg_nonneg] using hd x hx
  simpa only [eval_neg, neg_neg] using h'.neg

/-- Strict positivity of the derivative gives strict monotonicity. -/
theorem PolynomialRolle.strictMonoOn (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, 0 < p.derivative.eval x) : StrictMonoOn p.eval (Icc a b) := by
  intro u hu v hv huv
  obtain ⟨c, hc, he⟩ := h.exists_sub_eq p hu hv huv
  rw [← sub_pos, he]
  exact mul_pos (hd c hc) (sub_pos.mpr huv)

/-- Strict negativity of the derivative gives strict antitonicity. -/
theorem PolynomialRolle.strictAntiOn (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, p.derivative.eval x < 0) : StrictAntiOn p.eval (Icc a b) := by
  -- `-p` has the opposite derivative sign, so `strictMonoOn` applies to it.
  have h' := h.strictMonoOn (-p) fun x hx ↦ by
    simpa only [derivative_neg, eval_neg, neg_pos] using hd x hx
  simpa only [eval_neg, neg_neg] using h'.neg

end TauCeti
