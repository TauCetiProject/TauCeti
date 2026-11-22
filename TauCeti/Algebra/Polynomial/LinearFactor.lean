/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.HasseDeriv
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

Over any semiring, the Hasse derivative of order `k + 1` of `a * g`, for a polynomial `a` of degree
at most one, is `a` times that of `g` plus `derivative a` times the Hasse derivative of `g` of order
`k`. For `a = X - C r` over a ring the second term is the Hasse derivative of `g` of order `k`.
Consequently a Hasse derivative of order `k`
lowers the power of `X - C r` that is a left factor of a polynomial by at most `k`.

## Main results

* `Polynomial.modByMonic_X_sub_C_eq_zero`: division by a central linear factor has zero
  remainder at a root.
* `Polynomial.natDegree_C_sub_X`: the reversed linear factor `C x - X` has degree `1`.
* `Polynomial.exists_eq_C_mul_X_sub_C_of_natDegree_le_one`: a polynomial of `natDegree ≤ 1` with
  root `x` is `C γ * (X - C x)` for some `γ`.
* `Polynomial.eval_mul_pos_of_natDegree_le_one_of_no_roots`: constant nonzero sign on a root-free
  closed interval for polynomials of degree at most one.
* `Polynomial.derivative_root_factors`: factor the derivative of a polynomial with two root powers.
* `Polynomial.hasseDeriv_succ_mul_of_natDegree_le_one`, `Polynomial.hasseDeriv_succ_X_sub_C_mul`:
  the Leibniz rule for Hasse derivatives of a polynomial with a left factor of degree at most one,
  over any semiring, and of a polynomial with left factor `X - C r`, over any ring.
* `Polynomial.pow_sub_dvd_hasseDeriv_of_pow_dvd`: if `(X - C r) ^ n` is a left factor of `p`, then
  `(X - C r) ^ (n - k)` is a left factor of its Hasse derivative of order `k`, over any ring.
* `Polynomial.IsRoot.exists_eq_pow_succ_mul`: factor out a positive power of `X - C x`, leaving a
  cofactor nonzero at `x`.
* `Polynomial.rootMultiplicity_add_eq_left_of_dvd`: adding a multiple of a higher power of
  `X - C x` leaves the root multiplicity at `x` unchanged.
* `Polynomial.rootMultiplicity_neg`: negating a polynomial leaves its root multiplicities
  unchanged.

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

/-- Division by `X - c` leaves no remainder at a root `c` that commutes with every coefficient. -/
theorem modByMonic_X_sub_C_eq_zero {B : Type*} [Ring B] {p : B[X]} {c : B}
    (hc : ∀ b, Commute c b) (hp : p.eval c = 0) : p %ₘ (Polynomial.X - C c) = 0 := by
  nontriviality B
  have hd := degree_modByMonic_lt p (monic_X_sub_C c)
  rw [degree_X_sub_C] at hd
  have hr := eq_C_of_degree_le_zero (Nat.WithBot.lt_one_iff_le_zero.mp hd)
  have he := congrArg (Polynomial.eval c) (modByMonic_add_div p (Polynomial.X - C c))
  rw [hr] at he
  simp only [eval_add, eval_C, sub_mul, Polynomial.X_mul, eval_sub, eval_mul_X,
    eval_C_mul, (hc _).eq, sub_self, add_zero, hp] at he
  rw [hr, he, C_0]

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

/-- Negating a polynomial does not change its root multiplicity at any point. -/
@[simp]
theorem rootMultiplicity_neg (p : R[X]) (a : R) :
    (-p).rootMultiplicity a = p.rootMultiplicity a := by
  classical
  simp [rootMultiplicity_eq_multiplicity, multiplicity_neg]

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

/-- The Leibniz rule for Hasse derivatives of a polynomial with a left factor `a` of degree at most
one: `D⁽ᵏ⁺¹⁾ (a * g) = a * D⁽ᵏ⁺¹⁾ g + a' * D⁽ᵏ⁾ g`. Only the Hasse derivatives of `a` of order at
most one contribute. -/
theorem hasseDeriv_succ_mul_of_natDegree_le_one {S : Type*} [Semiring S] {a : S[X]}
    (ha : a.natDegree ≤ 1) (k : ℕ) (g : S[X]) :
    hasseDeriv (k + 1) (a * g) = a * hasseDeriv (k + 1) g + derivative a * hasseDeriv k g := by
  rw [hasseDeriv_mul, Finset.Nat.sum_antidiagonal_succ, Finset.sum_eq_single (0, k)]
  · simp
  · rintro ⟨_ | i, j⟩ hij hne
    · simp_all
    · simp [hasseDeriv_eq_zero_of_lt_natDegree a (i + 1 + 1) (by omega)]
  · simp

/-- The Leibniz rule for Hasse derivatives of a polynomial with left factor `X - C r`:
`D⁽ᵏ⁺¹⁾ ((X - C r) * g) = (X - C r) * D⁽ᵏ⁺¹⁾ g + D⁽ᵏ⁾ g`. This is the polynomial analogue of
`PowerSeries.hasseDeriv_succ_X_sub_C_mul`. -/
theorem hasseDeriv_succ_X_sub_C_mul (k : ℕ) (r : R) (g : R[X]) :
    hasseDeriv (k + 1) ((X - C r) * g) = (X - C r) * hasseDeriv (k + 1) g + hasseDeriv k g := by
  simpa using hasseDeriv_succ_mul_of_natDegree_le_one (natDegree_X_sub_C_le r) k g

/-- If `(X - C r) ^ n` is a left factor of `p`, then `(X - C r) ^ (n - k)` is a left factor of the
Hasse derivative of `p` of order `k`. This is the analogue of
`Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd` for Hasse derivatives. That result only
gives the divisibility for `k !` times the Hasse derivative, and the factor `k !` cannot in general
be cancelled. -/
theorem pow_sub_dvd_hasseDeriv_of_pow_dvd {p : R[X]} {r : R} {n : ℕ} (k : ℕ)
    (h : (X - C r) ^ n ∣ p) : (X - C r) ^ (n - k) ∣ hasseDeriv k p := by
  obtain ⟨q, rfl⟩ := h
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [pow_succ', mul_assoc, hasseDeriv_succ_X_sub_C_mul]
      -- The first summand keeps one linear factor in front of a derivative of order `k + 1`.
      have hle : n + 1 - (k + 1) ≤ n - (k + 1) + 1 := by omega
      refine dvd_add ((pow_dvd_pow _ hle).trans ?_) (by simpa using ih k)
      rw [pow_succ']
      exact mul_dvd_mul_left _ (ih (k + 1))

end Polynomial

end
