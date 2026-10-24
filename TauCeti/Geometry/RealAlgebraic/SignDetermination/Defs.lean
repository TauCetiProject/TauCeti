/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Data.Fintype.Fiber
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Basic.Sign.Defs
public import Mathlib.RingTheory.Polynomial.IntegralNormalization
import Mathlib.Algebra.Order.Group.Finset
import Mathlib.Basic.Sign.Basic
import TauCeti.Algebra.Polynomial.Eval.Sign

/-! # Polynomial sign counts and Tarski queries

`Finset.signCount` counts the points of a finite set realizing a given polynomial
sign condition. `Finset.signSum` sums a polynomial's signs on that set.
`Polynomial.tarskiQuery p q` specializes the sum to the distinct roots of `p`.
For nonzero `p` its cardinality characterization counts the actual zeros of `p`;
for `p = 0` the value is zero and does not describe the infinite zero set.

The definitions and their basic API are independent of matrix inversion.
Sign counts and sign sums are unchanged when the points and polynomials are mapped through a
strictly monotone ring homomorphism (`Finset.signCount_map_image`, `Finset.signSum_map_image`).
Over a field, `Polynomial.tarskiQuery_integralNormalization` clears the leading coefficient of
the root polynomial, so Tarski queries can always be computed at a monic root polynomial.

The algebraic laws of Tarski queries follow. In the queried polynomial, the query depends only on
signs at the roots (`Polynomial.tarskiQuery_congr`), so it is unchanged by adding multiples of the
root polynomial or reducing modulo it, changes sign under negation, is multiplied by the sign of a
constant factor, and for a square counts the roots at which the polynomial does not vanish. In
the root polynomial, it depends only on the set of distinct roots: it is unchanged under
associates and positive powers, and is additive over products of coprime factors.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapter 10, for sign conditions and Tarski queries.
-/

public section

open Polynomial SignType
open Function (occCount occCount_eq_card_filter)

namespace Finset

section Basic

variable {R : Type*} [Semiring R] [LinearOrder R]

/-- The number of points realizing a specified polynomial sign condition. -/
noncomputable def signCount {J : Type*}
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) : ℕ :=
  occCount (fun x : Z => fun j => sign ((Q j).eval x.val)) σ

/-- Polynomial sign counts are multiplicities in the finite family of pointwise signs. -/
theorem signCount_eq_occCount {J : Type*}
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) :
    signCount Z Q σ = occCount (fun x : Z => fun j => sign ((Q j).eval x.val)) σ := (rfl)

open scoped Classical in
/-- Sign counts are cardinalities of the realizing subset of the original finite set. -/
theorem signCount_eq_card_filter {J : Type*}
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) :
    signCount Z Q σ = (Z.filter fun x => ∀ j, sign ((Q j).eval x) = σ j).card := by
  classical
  simp only [signCount_eq_occCount, occCount_eq_card_filter, Finset.card_filter,
    funext_iff]
  exact Finset.sum_coe_sort Z
    (fun x : R => if ∀ j, sign ((Q j).eval x) = σ j then (1 : ℕ) else 0)

@[simp, grind =]
theorem signCount_empty {J : Type*}
    (Q : J → R[X]) (σ : J → SignType) : signCount ∅ Q σ = 0 := by
  simp [signCount_eq_card_filter]

/-- The sign conditions partition the original finite set of points. -/
theorem sum_signCount {J : Type*} [Fintype J] [DecidableEq J]
    (Z : Finset R) (Q : J → R[X]) : ∑ σ, signCount Z Q σ = Z.card := by
  classical
  simpa only [signCount_eq_occCount, Nat.card_eq_fintype_card, Fintype.card_coe] using
    Function.sum_occCount_eq_card (fun x : Z => fun j => sign ((Q j).eval x.val))
      (fun _ => Finset.mem_univ _)

/-- A positive sign count is equivalent to realization at a point of the finite set. -/
@[simp, grind =]
theorem signCount_pos {J : Type*}
    (Z : Finset R) (Q : J → R[X]) (σ : J → SignType) :
    0 < signCount Z Q σ ↔ ∃ x ∈ Z, ∀ j, sign ((Q j).eval x) = σ j := by
  classical
  simp [signCount_eq_card_filter, Finset.card_pos, Finset.Nonempty]

/-- The integer sum of signs at a specified finite set of points. -/
noncomputable def signSum (Z : Finset R) (p : R[X]) : ℤ := ∑ x : Z, (sign (p.eval x.val) : ℤ)

/-- Sign sums are integer sums of pointwise polynomial signs. -/
theorem signSum_eq_sum_subtype (Z : Finset R) (p : R[X]) :
    signSum Z p = ∑ x : Z, (sign (p.eval x.val) : ℤ) := (rfl)

/-- Sign sums expressed directly over the original finite set. -/
theorem signSum_eq_sum (Z : Finset R) (p : R[X]) :
    signSum Z p = ∑ x ∈ Z, (sign (p.eval x) : ℤ) := by
  rw [signSum_eq_sum_subtype, Finset.sum_coe_sort Z (fun x : R => (sign (p.eval x) : ℤ))]

@[simp, grind =]
theorem signSum_empty (p : R[X]) : signSum ∅ p = 0 := by
  simp [signSum_eq_sum]

@[simp, grind =]
theorem signSum_zero (Z : Finset R) : signSum Z 0 = 0 := by
  simp [signSum_eq_sum]

@[simp, grind =]
theorem signSum_one [ZeroLEOneClass R] [NeZero (1 : R)] (Z : Finset R) : signSum Z 1 = Z.card := by
  simp [signSum_eq_sum]

/-- A finite sign sum is the number of positive evaluations minus the number of negative ones. -/
theorem signSum_eq_card_sub_card (Z : Finset R) (p : R[X]) :
    signSum Z p = ((Z.filter (fun x => 0 < p.eval x)).card : ℤ) -
      (Z.filter (fun x => p.eval x < 0)).card := by
  classical
  rw [signSum_eq_sum]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hpos : 0 < p.eval x
  · have hneg : ¬ p.eval x < 0 := not_lt_of_ge hpos.le
    simp [hpos, hneg]
  · by_cases hneg : p.eval x < 0 <;> simp [sign_apply, hpos, hneg]

section Map

variable {S : Type*} [Semiring S] [LinearOrder S] [DecidableEq S] {f : R →+* S}

/-- Sign counts are preserved by mapping the points and the polynomials through a strictly
monotone ring homomorphism. -/
@[simp]
theorem signCount_map_image {J : Type*} (hf : StrictMono f) (Z : Finset R) (Q : J → R[X])
    (σ : J → SignType) :
    signCount (Z.image f) (fun j => (Q j).map f) σ = signCount Z Q σ := by
  classical
  rw [signCount_eq_card_filter, signCount_eq_card_filter, filter_image,
    card_image_of_injective _ hf.injective]
  simp only [sign_eval_map _ f hf]

/-- Sign sums are preserved by mapping the points and the polynomial through a strictly
monotone ring homomorphism. -/
@[simp]
theorem signSum_map_image (hf : StrictMono f) (Z : Finset R) (p : R[X]) :
    signSum (Z.image f) (p.map f) = signSum Z p := by
  rw [signSum_eq_sum, signSum_eq_sum, sum_image fun _ _ _ _ h => hf.injective h]
  simp only [sign_eval_map _ f hf]

end Map

end Basic

section OrderedRing

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Negating a polynomial negates its sign sum over a finite set of points. -/
@[simp]
theorem signSum_neg (Z : Finset R) (p : R[X]) : signSum Z (-p) = -signSum Z p := by
  simp [signSum_eq_sum, Left.sign_neg]

/-- Scaling a polynomial by a constant multiplies its sign sums by the sign of the constant. -/
@[simp]
theorem signSum_C_mul (Z : Finset R) (c : R) (p : R[X]) :
    signSum Z (C c * p) = sign c * signSum Z p := by
  simp [signSum_eq_sum, sign_mul, Finset.mul_sum]

end OrderedRing

section CommOrderedRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The sign sum of a square counts the points at which the polynomial does not vanish. -/
theorem signSum_sq (Z : Finset R) (p : R[X]) :
    signSum Z (p ^ 2) = (Z.filter fun x => p.eval x ≠ 0).card := by
  classical
  rw [signSum_eq_sum, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [eval_pow, sign_pow]
  rcases lt_trichotomy (p.eval x) 0 with h | h | h
  · simp [h, h.ne]
  · simp [h]
  · simp [h, h.ne']

end CommOrderedRing

end Finset

namespace Polynomial

open Finset

section Basic

variable {R : Type*} [CommRing R] [IsDomain R] [LinearOrder R]

/-- Sum of the signs of `q` at the distinct roots of `p`, with value zero when `p = 0`. -/
noncomputable def tarskiQuery (p q : R[X]) : ℤ := signSum p.roots.toFinset q

theorem tarskiQuery_eq_signSum (p q : R[X]) :
    tarskiQuery p q = signSum p.roots.toFinset q := (rfl)

/-- The Tarski query expressed as a sum over distinct polynomial roots. -/
theorem tarskiQuery_eq_sum (p q : R[X]) :
    tarskiQuery p q = ∑ x ∈ p.roots.toFinset, (sign (q.eval x) : ℤ) := by
  rw [tarskiQuery_eq_signSum, signSum_eq_sum]

/-- The number of distinct roots of `p` where `q` is positive minus the number
where `q` is negative. -/
theorem tarskiQuery_eq_card_sub_card (p q : R[X]) :
    tarskiQuery p q = ((p.roots.toFinset.filter (fun x => 0 < q.eval x)).card : ℤ) -
      (p.roots.toFinset.filter (fun x => q.eval x < 0)).card := by
  rw [tarskiQuery_eq_signSum, signSum_eq_card_sub_card]

/-- A Tarski query lies between minus the degree of its root polynomial and its degree. -/
theorem tarskiQuery_mem_Icc_natDegree (p q : R[X]) :
    tarskiQuery p q ∈ Set.Icc (-(p.natDegree : ℤ)) (p.natDegree : ℤ) := by
  rw [tarskiQuery_eq_card_sub_card]
  have hroots : p.roots.toFinset.card ≤ p.natDegree :=
    (Multiset.toFinset_card_le p.roots).trans (card_roots' p)
  have hpos := Finset.card_filter_le p.roots.toFinset (fun x => 0 < q.eval x)
  have hneg := Finset.card_filter_le p.roots.toFinset (fun x => q.eval x < 0)
  constructor <;> omega

@[simp, grind =]
theorem tarskiQuery_zero_left (q : R[X]) : tarskiQuery 0 q = 0 := by
  simp [tarskiQuery_eq_signSum]

@[simp, grind =]
theorem tarskiQuery_zero_right (p : R[X]) : tarskiQuery p 0 = 0 := by
  simp [tarskiQuery_eq_signSum]

@[simp, grind =]
theorem tarskiQuery_one_right [ZeroLEOneClass R] (p : R[X]) :
    tarskiQuery p 1 = p.roots.toFinset.card := by
  simp [tarskiQuery_eq_signSum]

/-- A Tarski query with a constant root polynomial is zero, including when the constant is zero. -/
@[simp, grind =]
theorem tarskiQuery_C_left (c : R) (q : R[X]) : tarskiQuery (C c) q = 0 := by
  simp [tarskiQuery_eq_signSum]

/-- A Tarski query depends only on the signs of the queried polynomial at the roots. -/
theorem tarskiQuery_congr {p q r : R[X]}
    (h : ∀ x ∈ p.roots, sign (q.eval x) = sign (r.eval x)) :
    tarskiQuery p q = tarskiQuery p r := by
  rw [tarskiQuery_eq_sum, tarskiQuery_eq_sum]
  exact Finset.sum_congr rfl fun x hx => by rw [h x (Multiset.mem_toFinset.mp hx)]

/-- Adding a multiple of `p` to the queried polynomial does not change the query, since it does
not change the values at the roots of `p`. -/
@[simp]
theorem tarskiQuery_add_mul (p q r : R[X]) : tarskiQuery p (q + p * r) = tarskiQuery p q :=
  tarskiQuery_congr fun x hx => by
    rw [eval_add, eval_mul, (isRoot_of_mem_roots hx).eq_zero, zero_mul, add_zero]

/-- Associated root polynomials have the same Tarski queries. -/
theorem _root_.Associated.tarskiQuery_eq {p s : R[X]} (h : Associated p s) (q : R[X]) :
    tarskiQuery p q = tarskiQuery s q := by
  rw [tarskiQuery_eq_signSum, tarskiQuery_eq_signSum, h.roots_eq]

/-- Multiplying the root polynomial by a nonzero constant leaves its Tarski queries unchanged. -/
@[simp]
theorem tarskiQuery_C_mul_left {c : R} (hc : c ≠ 0) (p q : R[X]) :
    tarskiQuery (C c * p) q = tarskiQuery p q := by
  rw [tarskiQuery_eq_signSum, tarskiQuery_eq_signSum, roots_C_mul _ hc]

/-- Negating the root polynomial leaves its Tarski queries unchanged. -/
@[simp]
theorem tarskiQuery_neg_left (p q : R[X]) : tarskiQuery (-p) q = tarskiQuery p q := by
  rw [tarskiQuery_eq_signSum, tarskiQuery_eq_signSum, roots_neg]

/-- A positive power of `p` has the same distinct roots as `p`, hence the same Tarski queries. -/
@[simp]
theorem tarskiQuery_pow_left (p q : R[X]) {n : ℕ} (hn : n ≠ 0) :
    tarskiQuery (p ^ n) q = tarskiQuery p q := by
  rw [tarskiQuery_eq_signSum, tarskiQuery_eq_signSum, roots_pow, Multiset.toFinset_nsmul _ _ hn]

/-- The query at the roots of a nonzero product of two polynomials without common roots is the
sum of the queries at the roots of the factors. -/
theorem tarskiQuery_mul_left_of_disjoint {p s : R[X]} (hps : p * s ≠ 0)
    (h : Disjoint p.roots.toFinset s.roots.toFinset) (q : R[X]) :
    tarskiQuery (p * s) q = tarskiQuery p q + tarskiQuery s q := by
  classical
  rw [tarskiQuery_eq_sum, tarskiQuery_eq_sum, tarskiQuery_eq_sum, roots_mul hps,
    Multiset.toFinset_add, Finset.sum_union h]

/-- The query at the roots of a product of coprime polynomials is the sum of the queries at the
roots of the factors. No nonvanishing hypothesis is needed: if one factor is zero, the other is
a unit and has no roots. -/
theorem tarskiQuery_mul_left_of_isCoprime {p s : R[X]} (h : IsCoprime p s) (q : R[X]) :
    tarskiQuery (p * s) q = tarskiQuery p q + tarskiQuery s q := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [tarskiQuery_eq_signSum,
      (associated_one_iff_isUnit.mpr (isCoprime_zero_left.mp h)).roots_eq]
  rcases eq_or_ne s 0 with rfl | hs
  · simp [tarskiQuery_eq_signSum,
      (associated_one_iff_isUnit.mpr (isCoprime_zero_right.mp h)).roots_eq]
  refine tarskiQuery_mul_left_of_disjoint (mul_ne_zero hp hs)
    (Finset.disjoint_left.mpr fun x hxp hxs => ?_) q
  obtain ⟨a, b, hab⟩ := h
  have := congr_arg (eval x) hab
  rw [eval_add, eval_mul, eval_mul,
    (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hxp)).eq_zero,
    (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hxs)).eq_zero, eval_one] at this
  simp at this

/-- Counts at the roots of a nonzero polynomial count exactly its realizing zeros. -/
theorem signCount_roots_eq_natCard {J : Type*} {p : R[X]} (hp : p ≠ 0)
    (Q : J → R[X]) (σ : J → SignType) :
    signCount p.roots.toFinset Q σ =
      Nat.card {x : R // p.eval x = 0 ∧ ∀ j, sign ((Q j).eval x) = σ j} := by
  classical
  rw [signCount_eq_card_filter, ← Nat.card_eq_finsetCard]
  simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hp, IsRoot.def]

/-- A Tarski query counts the zeros of `p` where `q` is positive, minus those
where `q` is negative. -/
theorem tarskiQuery_eq_sub {p : R[X]} (hp : p ≠ 0) (q : R[X]) :
    tarskiQuery p q = (Nat.card {x : R // p.eval x = 0 ∧ 0 < q.eval x} : ℤ) -
      Nat.card {x : R // p.eval x = 0 ∧ q.eval x < 0} := by
  classical
  rw [tarskiQuery_eq_card_sub_card]
  simp only [← Nat.card_eq_finsetCard, Finset.mem_filter, Multiset.mem_toFinset,
    mem_roots hp, IsRoot.def]

/-- A positive count at the roots of a nonzero polynomial is an actual realizable condition. -/
theorem signCount_roots_pos {J : Type*}
    {p : R[X]} (hp : p ≠ 0) (Q : J → R[X]) (σ : J → SignType) :
    0 < signCount p.roots.toFinset Q σ ↔
      ∃ x : R, p.eval x = 0 ∧ ∀ j, sign ((Q j).eval x) = σ j := by
  classical
  simp only [signCount_pos, Multiset.mem_toFinset, mem_roots hp, IsRoot.def]

end Basic

section OrderedRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Negating the queried polynomial negates the Tarski query. -/
@[simp]
theorem tarskiQuery_neg_right (p q : R[X]) : tarskiQuery p (-q) = -tarskiQuery p q :=
  signSum_neg _ _

/-- Scaling the queried polynomial by a constant multiplies the query by the sign of the
constant. -/
@[simp]
theorem tarskiQuery_C_mul_right (c : R) (p q : R[X]) :
    tarskiQuery p (C c * q) = sign c * tarskiQuery p q :=
  signSum_C_mul _ _ _

/-- The query of a square counts the distinct roots of `p` at which `q` does not vanish. -/
theorem tarskiQuery_sq_right (p q : R[X]) :
    tarskiQuery p (q ^ 2) = (p.roots.toFinset.filter fun x => q.eval x ≠ 0).card :=
  signSum_sq _ _

end OrderedRing

section Field

variable {R : Type*} [Field R] [LinearOrder R]

/-- **Clearing the leading coefficient of the root polynomial.** The distinct roots of the monic
polynomial `p.integralNormalization` are those of `p` multiplied by the leading coefficient `a`
of `p`. Hence a Tarski query of `p` equals one of `p.integralNormalization` against any `r`
whose sign at `a * x` agrees with the sign of `q` at each root `x` of `p`. -/
theorem tarskiQuery_integralNormalization {p q r : R[X]} (hp : p ≠ 0)
    (h : ∀ x, p.eval x = 0 → sign (r.eval (p.leadingCoeff * x)) = sign (q.eval x)) :
    tarskiQuery p.integralNormalization r = tarskiQuery p q := by
  classical
  have ha : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hroots : p.integralNormalization.roots = p.roots.map (p.leadingCoeff * ·) := by
    rw [← roots_C_mul _ ha, mul_comm, integralNormalization_mul_C_leadingCoeff,
      roots_scaleRoots _ (isUnit_iff_ne_zero.mpr ha)]
  rw [tarskiQuery_eq_sum, tarskiQuery_eq_sum, hroots, Multiset.toFinset_map,
    Finset.sum_image fun x _ y _ hxy => mul_left_cancel₀ ha hxy]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [h x (isRoot_of_mem_roots (Multiset.mem_toFinset.mp hx)).eq_zero]

/-- Reducing the queried polynomial modulo `p` does not change the query. -/
@[simp]
theorem tarskiQuery_mod (p q : R[X]) : tarskiQuery p (q % p) = tarskiQuery p q := by
  rw [EuclideanDomain.mod_eq_sub_mul_div, sub_eq_add_neg, ← mul_neg, tarskiQuery_add_mul]

end Field

end Polynomial
