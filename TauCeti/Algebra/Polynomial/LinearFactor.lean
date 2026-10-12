/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ring

/-!
# The linear factor `X - C x`, and its reverse

Linear factors, scalar factorizations, and the full power of a root factor.
Over an ordered field, a polynomial of degree at most one has constant sign on a root-free interval.

The *reversed* factor `C x - X` — the shape that arises as `x - θ` in `AdjoinRoot f` — has degree
`1`, like `X - C x` itself, which is the form Mathlib states.

A polynomial of degree at most one with root `x` is `C γ * (X - C x)` for a single scalar `γ`.
Writing it as `C a * X + C b`, the root condition gives `a * x + b = 0`, which identifies the
constant term and factors the polynomial. This works over noncommutative rings, with the scalar
factor on the left.

Factoring out the full multiplicity of a root of a nonzero polynomial leaves a cofactor
that does not vanish at the root.

## Main results

* `Polynomial.natDegree_C_sub_X`: the reversed linear factor `C x - X` has degree `1`.
* `Polynomial.exists_eq_C_mul_X_sub_C_of_natDegree_le_one`: a polynomial of `natDegree ≤ 1` with
  root `x` is `C γ * (X - C x)` for some `γ`.
* `Polynomial.eval_mul_pos_of_natDegree_le_one_of_no_roots`: constant nonzero sign on a root-free
  closed interval for polynomials of degree at most one.
* `Polynomial.derivative_root_factors`: factor the derivative of a polynomial with two root powers.
* `Polynomial.IsRoot.exists_eq_pow_succ_mul`: factor out a positive power of `X - C x`, leaving a
  cofactor nonzero at `x`.
* `Polynomial.rootMultiplicity_add_eq_left_of_dvd`: adding a multiple of a higher power of
  `X - C x` leaves the root multiplicity at `x` unchanged.

## Provenance

The statement of `exists_eq_C_mul_X_sub_C_of_natDegree_le_one` generalizes the commutative-ring
result adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, revision `66889eada51a`),
`EllipticCurves/Mathlib/Basic.lean`.
Its consumer is the `x - T` descent map of
`TauCeti/AlgebraicGeometry/EllipticCurve/MordellWeil/XSubT.lean`, where it pins down the line
through a `2`-torsion point.
-/

public section

namespace Polynomial

variable {R : Type*} [Ring R]

/-- The reversed linear polynomial `C x - X` has degree `1`, like `X - C x`. -/
@[simp]
theorem natDegree_C_sub_X {R : Type*} [Ring R] [Nontrivial R] (x : R) :
    (C x - X).natDegree = 1 := by
  rw [natDegree_sub, natDegree_X_sub_C]

/-- A polynomial of degree at most one with prescribed root `x` is a left scalar multiple of
`X - C x`, over any ring. -/
lemma exists_eq_C_mul_X_sub_C_of_natDegree_le_one {p : R[X]} (hdeg : p.natDegree ≤ 1)
    {x : R} (hx : p.IsRoot x) :
    ∃ γ, p = C γ * (X - C x) := by
  obtain ⟨a, b, hp⟩ := exists_eq_X_add_C_of_natDegree_le_one hdeg
  have hx' : a * x + b = 0 := by
    simpa only [IsRoot, hp, eval_add, eval_C_mul, eval_C, eval_X] using hx
  refine ⟨a, ?_⟩
  rw [hp, mul_sub, ← C_mul, eq_neg_of_add_eq_zero_right hx', map_neg, sub_eq_add_neg]

/-- A root of a nonzero polynomial factors out with positive multiplicity and a cofactor
that does not vanish at the root. -/
theorem IsRoot.exists_eq_pow_succ_mul {A : Type*} [CommRing A] {p : A[X]} {a : A}
    (ha : p.IsRoot a) (hp : p ≠ 0) :
    ∃ m : ℕ, ∃ q : A[X], p = (X - C a) ^ (m + 1) * q ∧ q.eval a ≠ 0 := by
  obtain ⟨q, hq, hn⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp a
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero ((rootMultiplicity_pos hp).mpr ha).ne'
  exact ⟨m, q, by simpa only [hm] using hq, fun h => hn (dvd_iff_isRoot.mpr h)⟩

/-- Adding a multiple of a higher power of `X - C a` does not change the root multiplicity
at `a` of a nonzero polynomial. -/
theorem rootMultiplicity_add_eq_left_of_dvd {A : Type*} [Ring A] {p q : A[X]} {a : A}
    (hp : p ≠ 0) (hq : (X - C a) ^ (p.rootMultiplicity a + 1) ∣ q) :
    (p + q).rootMultiplicity a = p.rootMultiplicity a := by
  have hpq : p + q ≠ 0 := by
    intro h
    rw [eq_neg_of_add_eq_zero_right h, dvd_neg] at hq
    exact pow_rootMultiplicity_not_dvd hp a hq
  refine le_antisymm ?_ ?_
  · rw [rootMultiplicity_le_iff hpq]
    intro h
    exact pow_rootMultiplicity_not_dvd hp a (by simpa using dvd_sub h hq)
  · apply (le_rootMultiplicity_iff hpq).mpr
    exact dvd_add (pow_rootMultiplicity_dvd p a) ((pow_dvd_pow _ (Nat.le_succ _)).trans hq)

/-- A polynomial of degree at most one has constant nonzero sign on an interval without a root. -/
theorem eval_mul_pos_of_natDegree_le_one_of_no_roots {R : Type*} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] {p : R[X]} (hdeg : p.natDegree ≤ 1) {a b : R}
    (hab : a ≤ b) (hroot : ∀ x ∈ Set.Icc a b, p.eval x ≠ 0) :
    0 < p.eval a * p.eval b := by
  by_cases hd0 : p.natDegree = 0
  · have hs : p.eval b = p.eval a := by rw [eq_C_of_natDegree_eq_zero hd0]; simp
    rw [hs]
    exact mul_self_pos.mpr (hroot a ⟨le_rfl, hab⟩)
  have hd1 : p.natDegree = 1 := by omega
  have hd : p.degree = 1 := (degree_eq_iff_natDegree_eq_of_pos (by decide)).mpr hd1
  obtain ⟨r, hr⟩ := exists_root_of_degree_eq_one hd
  obtain ⟨c, hc⟩ := exists_eq_C_mul_X_sub_C_of_natDegree_le_one hdeg hr
  have hcne : c ≠ 0 := by
    intro hz
    apply hroot a ⟨le_rfl, hab⟩
    simp [hc, hz]
  have hprod : 0 < (a - r) * (b - r) := by
    rcases lt_or_ge r a with h | h
    · exact mul_pos (sub_pos.mpr h) (sub_pos.mpr (h.trans_le hab))
    · have hb : b < r := by
        by_contra! hb
        exact hroot r ⟨h, hb⟩ hr
      exact mul_pos_of_neg_of_neg (sub_neg.mpr (hab.trans_lt hb)) (sub_neg.mpr hb)
  simp only [hc, eval_mul, eval_C, eval_sub, eval_X]
  convert mul_pos (mul_self_pos.mpr hcne) hprod using 1
  ring

/-- Factor the derivative after removing the powers contributed by two roots. -/
theorem derivative_root_factors {A : Type*} [CommRing A] (a b : A) (m n : ℕ) (r : A[X]) :
    ((X - C a) ^ (m + 1) * ((X - C b) ^ (n + 1) * r)).derivative =
      (X - C a) ^ m * (X - C b) ^ n *
        (C ((m : A) + 1) * (X - C b) * r + C ((n : A) + 1) * (X - C a) * r +
          (X - C a) * (X - C b) * r.derivative) := by
  simp only [derivative_mul, derivative_pow_succ, derivative_sub, derivative_X,
    derivative_C, sub_zero, mul_one]
  simp only [pow_succ]
  ring

end Polynomial

end
