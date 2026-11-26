/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.FieldTheory.Finite.Irreducible
public import TauCeti.FieldTheory.Finite.MinpolyOrbit
public import TauCeti.RingTheory.AdjoinRoot.Basic
public import TauCeti.RingTheory.Polynomial.Monic.Irreducible

import TauCeti.Data.Nat.Totient.LowerBound
import TauCeti.FieldTheory.Finite.RootsOfUnity
import TauCeti.RingTheory.Polynomial.DegreeLT

/-!
# Primitive polynomials over a finite field

Let `K` be a finite field with `q` elements. A monic polynomial `p` of degree `r` over `K` is
*primitive* if it is irreducible and has a root of multiplicative order `q ^ r - 1`. All roots of
an irreducible polynomial, in any nontrivial `K`-algebra, have the same multiplicative order as
the root `AdjoinRoot.root p` of `p` in `AdjoinRoot p`, so the condition does not depend on where
the root is taken (`Irreducible.orderOf_eq_orderOf_root`); we use `AdjoinRoot p` in the definition
and `Polynomial.isPrimitivePolynomial_iff_orderOf_eq` to pass to a root in any other algebra.

The roots of the primitive polynomials of degree `r` in an extension `L` of degree `r` are the
generators of the cyclic group `Lˣ`, of which there are `φ (q ^ r - 1)`, and each such polynomial
has exactly `r` of them, so `φ (q ^ r - 1) = r · #{primitive polynomials of degree r}`. With the
elementary lower bound `m ≤ φ(m) (2 log m + 1)` for the totient this shows that at most a share
`exp(-1 / (2r (2r log q + 1)))` of the monic polynomials of degree `r` are not primitive.

This is not Mathlib's `Polynomial.IsPrimitive`, which asks that the coefficients have no common
non-unit divisor.

## Main definitions

* `Polynomial.IsPrimitivePolynomial`: a monic irreducible polynomial over a finite field whose
  root has order `q ^ natDegree - 1`.

## Main results

* `Polynomial.isPrimitivePolynomial_iff_orderOf_eq`: primitivity read off at any root.
* `Polynomial.IsPrimitivePolynomial.coeff_zero_ne_zero`, `Polynomial.IsPrimitivePolynomial.ne_X`:
  over a finite field, a primitive polynomial has a nonzero constant term, so it is not `X`.
* `Polynomial.isPrimitivePolynomial_minpoly`: over a finite extension `L` of `K`, the minimal
  polynomial of an element of order `q ^ [L : K] - 1` is primitive of degree `[L : K]`.
* `Polynomial.totient_eq_finrank_mul_ncard_isPrimitivePolynomial`: for such an `L`,
  `φ (q ^ [L : K] - 1) = [L : K] · #{primitive polynomials of degree [L : K]}`.
* `Polynomial.totient_eq_mul_ncard_isPrimitivePolynomial`: for every `r`,
  `φ (q ^ r - 1) = r · #{primitive polynomials of degree r}`.
* `Polynomial.totient_le_mul_ncard_isPrimitivePolynomial`: the lower bound
  `φ (q ^ r - 1) ≤ r · #{primitive polynomials of degree r}`.
* `Polynomial.ncard_monic_not_isPrimitivePolynomial_div_le_exp`: the monic polynomials of degree
  `r` that are not primitive make up at most a share `exp(-1 / (2r (2r log q + 1)))` of all
  `q ^ r` of them.

## References

* R. Lidl and H. Niederreiter, *Finite Fields*, Encyclopedia of Mathematics and its Applications
  20, Addison-Wesley (1983), ch. 3 (primitive polynomials and their number).
* The lower bound and the share of non-primitive polynomials follow
  `New.totient_le_mul_card_isPrimitivePolynomial` and `New.card_not_primitive_mul_le` in
  `New/Spanning/MainTerm/BadTypes.lean` of the folder `grh` of
  https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207.
-/

public section

open Polynomial Finset
open scoped Nat

namespace Polynomial

variable {K : Type*} [Field K]

/-- A polynomial `p` over a finite field `K` with `q` elements is *primitive* if it is monic,
irreducible, and its root `AdjoinRoot.root p` in `AdjoinRoot p` (a field extension of `K` of
degree `p.natDegree`) has multiplicative order `q ^ p.natDegree - 1`, that is, generates the
multiplicative group of `AdjoinRoot p`.

By `Polynomial.isPrimitivePolynomial_iff_orderOf_eq`, the root may be taken in any nontrivial
commutative `K`-algebra, e.g. a fixed extension of degree `p.natDegree` or an algebraic closure.

The definition does not assume `K` finite: for an infinite field `Nat.card K = 0`, and the
condition says that the root has infinite order. It is meant for finite `K`.

Not to be confused with `Polynomial.IsPrimitive` (coefficients without common divisor). -/
def IsPrimitivePolynomial (p : K[X]) : Prop :=
  p.Monic ∧ Irreducible p ∧ orderOf (AdjoinRoot.root p) = Nat.card K ^ p.natDegree - 1

/-- Unfolding `Polynomial.IsPrimitivePolynomial`. -/
@[simp]
theorem isPrimitivePolynomial_iff {p : K[X]} :
    p.IsPrimitivePolynomial ↔
      p.Monic ∧ Irreducible p ∧ orderOf (AdjoinRoot.root p) = Nat.card K ^ p.natDegree - 1 :=
  Iff.rfl

/-- Primitivity of `p` can be read off at any root `x` of `p` in a nontrivial commutative
`K`-algebra: `p` is primitive iff it is monic, irreducible, and `x` has order
`q ^ p.natDegree - 1`. -/
theorem isPrimitivePolynomial_iff_orderOf_eq {L : Type*} [CommRing L] [Nontrivial L]
    [Algebra K L] {p : K[X]} {x : L} (hx : aeval x p = 0) :
    p.IsPrimitivePolynomial ↔
      p.Monic ∧ Irreducible p ∧ orderOf x = Nat.card K ^ p.natDegree - 1 :=
  and_congr_right fun _ ↦ and_congr_right fun hi ↦ by rw [hi.orderOf_eq_orderOf_root hx]

/-- A primitive polynomial is monic. -/
theorem IsPrimitivePolynomial.monic {p : K[X]} (hp : p.IsPrimitivePolynomial) : p.Monic :=
  hp.1

/-- A primitive polynomial is irreducible. -/
theorem IsPrimitivePolynomial.irreducible {p : K[X]} (hp : p.IsPrimitivePolynomial) :
    Irreducible p :=
  hp.2.1

/-- A primitive polynomial is irreducible and monic. -/
theorem IsPrimitivePolynomial.mem_monicIrreduciblesOfDegree {p : K[X]}
    (hp : p.IsPrimitivePolynomial) : p ∈ monicIrreduciblesOfDegree K p.natDegree :=
  mem_monicIrreduciblesOfDegree_iff.mpr ⟨hp.monic, hp.irreducible, rfl⟩

variable [Finite K]

/-- A primitive polynomial over a finite field has a nonzero constant term: otherwise `0` would be
a root, of order `0 ≠ q ^ natDegree - 1`. -/
theorem IsPrimitivePolynomial.coeff_zero_ne_zero {p : K[X]} (hp : p.IsPrimitivePolynomial) :
    p.coeff 0 ≠ 0 := by
  intro h0
  have h := ((isPrimitivePolynomial_iff_orderOf_eq (x := (0 : K))
    (by rwa [← coeff_zero_eq_aeval_zero])).mp hp).2.2
  rw [orderOf_zero] at h
  have := Nat.one_lt_pow hp.irreducible.natDegree_pos.ne' (Finite.one_lt_card (α := K))
  omega

/-- A primitive polynomial over a finite field is not `X`. -/
theorem IsPrimitivePolynomial.ne_X {p : K[X]} (hp : p.IsPrimitivePolynomial) : p ≠ X :=
  fun h ↦ hp.coeff_zero_ne_zero (by simp [h])

/-- Over a finite field there are finitely many primitive polynomials of each degree. -/
theorem finite_setOf_isPrimitivePolynomial (r : ℕ) :
    {p : K[X] | p.IsPrimitivePolynomial ∧ p.natDegree = r}.Finite :=
  (finite_monicIrreduciblesOfDegree K r).subset fun _ ⟨hp, hr⟩ ↦
    hr ▸ hp.mem_monicIrreduciblesOfDegree

/-- An element of order `q ^ [L : K] - 1` in a finite extension `L` of `K` has a minimal
polynomial of degree at least `[L : K]`: the element is fixed by `y ↦ y ^ (q ^ d)` with `d` that
degree, so its order divides `q ^ d - 1`. -/
private theorem finrank_le_natDegree_minpoly {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] {x : L} (hx : orderOf x = Nat.card K ^ Module.finrank K L - 1) :
    Module.finrank K L ≤ (minpoly K x).natDegree := by
  have hint : IsIntegral K x := .of_finite K x
  set d := (minpoly K x).natDegree
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hd : 0 < d := minpoly.natDegree_pos hint
  have hr : 1 < Nat.card K ^ Module.finrank K L := Nat.one_lt_pow Module.finrank_pos.ne' hq
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at hx
    omega
  have hfix : x ^ Nat.card K ^ d = x := by
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact TauCeti.FiniteField.pow_card_pow_natDegree_minpoly K hint
  have hpos : 0 < Nat.card K ^ d - 1 := by
    have := Nat.one_lt_pow hd.ne' hq
    omega
  have hone : x ^ (Nat.card K ^ d - 1) = 1 := by
    refine mul_right_cancel₀ hx0 ?_
    rw [pow_sub_one_mul (pow_pos (by omega) d).ne', hfix, one_mul]
  have hle := Nat.le_of_dvd hpos (hx ▸ orderOf_dvd_of_pow_eq_one hone)
  exact (Nat.pow_le_pow_iff_right hq).mp (by omega)

/-- Over a finite extension `L` of a finite field `K` with `q` elements, the minimal polynomial of
an element of multiplicative order `q ^ [L : K] - 1` (a generator of `Lˣ`) is primitive, of
degree `[L : K]`. -/
theorem isPrimitivePolynomial_minpoly {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    {x : L} (hx : orderOf x = Nat.card K ^ Module.finrank K L - 1) :
    (minpoly K x).IsPrimitivePolynomial ∧ (minpoly K x).natDegree = Module.finrank K L := by
  have hint : IsIntegral K x := .of_finite K x
  have hdeg : (minpoly K x).natDegree = Module.finrank K L :=
    le_antisymm (minpoly.natDegree_le x) (finrank_le_natDegree_minpoly hx)
  exact ⟨(isPrimitivePolynomial_iff_orderOf_eq (minpoly.aeval K x)).mpr
    ⟨minpoly.monic hint, minpoly.irreducible hint, by rw [hdeg, hx]⟩, hdeg⟩

open Module

/-- In a finite extension `L` of `K`, the elements of order `q ^ [L : K] - 1` with a given
minimal polynomial `minpoly K x₀` are the roots of `minpoly K x₀` in `L`, `[L : K]` of them. -/
private theorem card_filter_minpoly_eq {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    [DecidableEq K[X]] {x₀ : L} (hx₀ : orderOf x₀ = Nat.card K ^ finrank K L - 1) :
    #{x ∈ primitiveRoots (Nat.card K ^ finrank K L - 1) L | minpoly K x = minpoly K x₀} =
      finrank K L := by
  classical
  have : Finite L := Module.finite_of_finite K
  have hint : IsIntegral K x₀ := .of_finite K x₀
  have hpos : 0 < Nat.card K ^ finrank K L - 1 := by
    have := Nat.one_lt_pow (finrank_pos (R := K) (M := L)).ne' (Finite.one_lt_card (α := K))
    omega
  have hirr := minpoly.irreducible hint
  have hset : {x ∈ primitiveRoots (Nat.card K ^ finrank K L - 1) L |
      minpoly K x = minpoly K x₀} = ((minpoly K x₀).rootSet L).toFinset := by
    ext x
    simp only [Finset.mem_filter, mem_primitiveRoots hpos, IsPrimitiveRoot.iff_orderOf,
      Set.mem_toFinset, mem_rootSet, ne_eq, minpoly.ne_zero hint, not_false_eq_true, true_and]
    refine ⟨fun h ↦ h.2 ▸ minpoly.aeval K x, fun h ↦ ⟨?_, ?_⟩⟩
    · rw [hirr.orderOf_eq_orderOf_root h, ← hirr.orderOf_eq_orderOf_root (minpoly.aeval K x₀), hx₀]
    · exact (minpoly.eq_of_irreducible_of_monic hirr h (minpoly.monic hint)).symm
  rw [hset, Set.toFinset_card, ← (isPrimitivePolynomial_minpoly hx₀).2]
  exact card_rootSet_eq_natDegree (Algebra.IsSeparable.isSeparable K x₀)
    (Normal.splits inferInstance x₀)

/-- **The number of primitive polynomials, over an extension of the degree.** If `L` is an
extension of the finite field `K` (with `q` elements) of degree `r = [L : K]`, then
`φ (q ^ r - 1) = r · #{primitive polynomials of degree r over K}`: the roots of these
polynomials in `L` are the `φ (q ^ r - 1)` generators of the cyclic group `Lˣ`, `r` for each.
If `L` is infinite-dimensional over `K`, then `[L : K] = 0` and both sides vanish. -/
theorem totient_eq_finrank_mul_ncard_isPrimitivePolynomial (L : Type*) [Field L] [Algebra K L] :
    φ (Nat.card K ^ finrank K L - 1) =
      finrank K L * {p : K[X] | p.IsPrimitivePolynomial ∧ p.natDegree = finrank K L}.ncard := by
  classical
  by_cases hL : FiniteDimensional K L
  swap
  · simp [finrank_of_not_finite hL]
  have : Finite L := Module.finite_of_finite K
  set n := Nat.card K ^ finrank K L - 1
  obtain ⟨ζ, hζ⟩ := TauCeti.exists_isPrimitiveRoot_of_dvd_natCard_sub_one (F := L) (d := n)
    (by rw [Module.natCard_eq_pow_finrank (K := K)])
  have hpos : 0 < n := by
    have := Nat.one_lt_pow (finrank_pos (R := K) (M := L)).ne' (Finite.one_lt_card (α := K))
    omega
  have hmem : ∀ x : L, x ∈ primitiveRoots n L ↔ orderOf x = n := fun x ↦
    (mem_primitiveRoots hpos).trans IsPrimitiveRoot.iff_orderOf
  have himage : {p : K[X] | p.IsPrimitivePolynomial ∧ p.natDegree = finrank K L} =
      ((primitiveRoots n L).image (minpoly K) : Set K[X]) := by
    ext p
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe, hmem]
    refine ⟨fun ⟨hp, hr⟩ ↦ ?_, ?_⟩
    · obtain ⟨x, hx⟩ :=
        hp.irreducible.exists_aeval_eq_zero_of_natDegree_dvd_finrank (L := L) (hr ▸ dvd_rfl)
      refine ⟨x, ?_, (minpoly.eq_of_irreducible_of_monic hp.irreducible hx hp.monic).symm⟩
      rw [((isPrimitivePolynomial_iff_orderOf_eq hx).mp hp).2.2, hr]
    · rintro ⟨x, hx, rfl⟩
      exact isPrimitivePolynomial_minpoly hx
  rw [← hζ.card_primitiveRoots, himage, Set.ncard_coe_finset,
    Finset.card_eq_sum_card_image (minpoly K), mul_comm]
  refine (Finset.sum_congr rfl fun p hp ↦ ?_).trans (Finset.sum_const_nat fun _ _ ↦ rfl)
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hp
  exact card_filter_minpoly_eq ((hmem x₀).mp hx₀)

/-- **The number of primitive polynomials.** Over a finite field `K` with `q` elements,
`φ (q ^ r - 1) = r · #{primitive polynomials of degree r}` for every `r` (for `r = 0` both sides
vanish). -/
theorem totient_eq_mul_ncard_isPrimitivePolynomial (r : ℕ) :
    φ (Nat.card K ^ r - 1) = r * {p : K[X] | p.IsPrimitivePolynomial ∧ p.natDegree = r}.ncard := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  have : NeZero r := ⟨hr.ne'⟩
  simpa only [FiniteField.finrank_extension] using
    totient_eq_finrank_mul_ncard_isPrimitivePolynomial (K := K)
      (FiniteField.Extension K (ringChar K) r)

/-- **Lower bound for the number of primitive polynomials.** Over a finite field `K` with `q`
elements, `φ (q ^ r - 1) ≤ r · #{primitive polynomials of degree r}`; equality holds, see
`Polynomial.totient_eq_mul_ncard_isPrimitivePolynomial`. -/
theorem totient_le_mul_ncard_isPrimitivePolynomial (r : ℕ) :
    φ (Nat.card K ^ r - 1) ≤ r * {p : K[X] | p.IsPrimitivePolynomial ∧ p.natDegree = r}.ncard :=
  (totient_eq_mul_ncard_isPrimitivePolynomial r).le

/-- The monic polynomials of degree `r` are the primitive polynomials of degree `r` and the
others. -/
private lemma ncard_isPrimitivePolynomial_add (r : ℕ) :
    {p : K[X] | p.IsPrimitivePolynomial ∧ p.natDegree = r}.ncard +
      {p : K[X] | p.Monic ∧ p.natDegree = r ∧ ¬p.IsPrimitivePolynomial}.ncard =
        Nat.card K ^ r := by
  have hdisj : Disjoint {p : K[X] | p.IsPrimitivePolynomial ∧ p.natDegree = r}
      {p : K[X] | p.Monic ∧ p.natDegree = r ∧ ¬p.IsPrimitivePolynomial} :=
    Set.disjoint_left.mpr fun _ hp hp' ↦ hp'.2.2 hp.1
  have hP : {p : K[X] | p.IsPrimitivePolynomial ∧ p.natDegree = r}.Finite :=
    (finite_setOf_monic_natDegree_eq K r).subset fun _ hp ↦ ⟨hp.1.monic, hp.2⟩
  have hN : {p : K[X] | p.Monic ∧ p.natDegree = r ∧ ¬p.IsPrimitivePolynomial}.Finite :=
    (finite_setOf_monic_natDegree_eq K r).subset fun _ hp ↦ ⟨hp.1, hp.2.1⟩
  rw [← ncard_setOf_monic_natDegree_eq K r, ← Set.ncard_union_eq hdisj hP hN]
  congr 1
  ext p
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  refine ⟨?_, fun ⟨hm, hr⟩ ↦ (em p.IsPrimitivePolynomial).imp (⟨·, hr⟩) (⟨hm, hr, ·⟩)⟩
  rintro (⟨hp, hr⟩ | ⟨hm, hr, -⟩)
  exacts [⟨hp.monic, hr⟩, ⟨hm, hr⟩]

/-- **Few monic polynomials are not primitive.** Over a finite field with `q` elements, the monic
polynomials of degree `r` that are not primitive make up at most a share
`exp(-1 / (2r (2r log q + 1)))` of all `q ^ r` monic polynomials of degree `r`. This combines
`φ (q ^ r - 1) ≤ r · #{primitive polynomials of degree r}` with
`TauCeti.Nat.one_sub_totient_pow_sub_one_div_le_exp`. For `r = 0` both sides are `1`. -/
theorem ncard_monic_not_isPrimitivePolynomial_div_le_exp (r : ℕ) :
    ({p : K[X] | p.Monic ∧ p.natDegree = r ∧ ¬p.IsPrimitivePolynomial}.ncard : ℝ) /
        (Nat.card K : ℝ) ^ r ≤
      Real.exp (-(1 / (2 * r * (2 * r * Real.log (Nat.card K) + 1)))) := by
  set P := {p : K[X] | p.IsPrimitivePolynomial ∧ p.natDegree = r}.ncard
  set N := {p : K[X] | p.Monic ∧ p.natDegree = r ∧ ¬p.IsPrimitivePolynomial}.ncard
  have hPN : (P : ℝ) + N = (Nat.card K : ℝ) ^ r := by
    exact_mod_cast ncard_isPrimitivePolynomial_add (K := K) r
  have hφ : (φ (Nat.card K ^ r - 1) : ℝ) ≤ r * P := by
    exact_mod_cast totient_le_mul_ncard_isPrimitivePolynomial r
  have hqr : (0 : ℝ) < (Nat.card K : ℝ) ^ r := pow_pos (Nat.cast_pos.mpr Nat.card_pos) r
  have hN : (N : ℝ) / (Nat.card K : ℝ) ^ r = 1 - P / (Nat.card K : ℝ) ^ r := by
    rw [eq_sub_iff_add_eq, ← add_div, add_comm, hPN, div_self hqr.ne']
  have hP : (φ (Nat.card K ^ r - 1) : ℝ) / (r * (Nat.card K : ℝ) ^ r) ≤
      P / (Nat.card K : ℝ) ^ r := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    rw [← div_div]
    gcongr
    rw [div_le_iff₀ (Nat.cast_pos.mpr hr)]
    linarith
  rw [hN]
  exact (sub_le_sub_left hP 1).trans
    (TauCeti.Nat.one_sub_totient_pow_sub_one_div_le_exp Finite.one_lt_card r)

end Polynomial
