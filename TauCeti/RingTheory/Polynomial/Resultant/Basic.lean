/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Resultant lemmas

Mathlib evaluates the resultant against the linear polynomial `X - C x` on either side
(`Polynomial.resultant_X_sub_C_left`, `Polynomial.resultant_X_sub_C_right`). This file records the
companion for the *reversed* polynomial `C x - X`, which is the shape that arises as `x - θ` in
`AdjoinRoot f`: the answer is `f.eval x`, with **no sign**.

The file also normalizes bounded resultants with a monic left argument. This makes the resultant
independent of the chosen valid right degree bound, as needed when comparing resultant-based
discriminant formulas that use different bounds.

That absence is the point. `C x - X` is `C (-1) * (X - C x)`, which contributes `(-1) ^ m`, and
`resultant_X_sub_C_right` contributes another `(-1) ^ m`, so the two cancel.

The resultant with `1 - t X` at a degree bound `n` for `f` is the value at `t` of the reversal
`reflect n f`, and the multiplicativity `Res(f₁ * f₂, g) = Res(f₁, g) * Res(f₂, g)` holds for
arbitrary valid degree bounds, the bounds adding. These are the identities behind Coleman's
spectral transform, whose rank is a specified degree bound rather than an actual degree.

Finally, resultants taken at the actual degrees commute with any coefficient map preserving both
degrees, the form of base change used when comparing a resultant with its specializations.

## Main results

* `Polynomial.resultant_C_sub_X_right`
* `Polynomial.natDegree_one_sub_C_mul_X_le`: `1 - t X` has degree at most one.
* `Polynomial.resultant_one_sub_C_mul_X_right`: `Res_(n,1)(f, 1 - t X) = (reflect n f)(t)`.
* `Polynomial.resultant_mul_left_of_natDegree_le`: multiplicativity in the left argument at
  arbitrary degree bounds.
* `Polynomial.resultant_map_of_natDegree_eq`: resultants at the actual degrees commute with a
  coefficient map that preserves both degrees.
* `Polynomial.Monic.resultant_of_le`: for a monic left argument, the resultant is independent of
  the valid degree bound supplied for the right argument.

## Provenance

`Polynomial.resultant_C_sub_X_right` is adapted from Michael Stoll's `EllipticCurves`
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0) at commit
`66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, `EllipticCurves/Mathlib/Basic.lean` line 615, where
it is a Mathlib-bound prerequisite of the explicit `2`-descent.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The resultant of `f` with the reversed linear polynomial `C x - X` is `f.eval x`. Note the
absence of a sign: `C x - X` is `-(X - C x)`, and the two signs cancel. -/
@[simp]
theorem resultant_C_sub_X_right (f : R[X]) (x : R) (m : ℕ) (hm : f.natDegree ≤ m) :
    f.resultant (C x - X) m 1 = f.eval x := by
  -- `C x - X` is `X - C x` scaled by the constant `-1`
  have hneg : C x - X = C (-1 : R) * (X - C x) := by simp
  rw [hneg, resultant_C_mul_right, resultant_X_sub_C_right f m x hm, ← mul_assoc, ← pow_add,
    ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- `Res(f₁ * f₂, g) = Res(f₁, g) * Res(f₂, g)` for arbitrary valid degree bounds: the bound for
the product is the sum of the bounds for the factors. -/
theorem resultant_mul_left_of_natDegree_le {f₁ f₂ g : R[X]} {m₁ m₂ n : ℕ}
    (hf₁ : f₁.natDegree ≤ m₁) (hf₂ : f₂.natDegree ≤ m₂) (hg : g.natDegree ≤ n) :
    (f₁ * f₂).resultant g (m₁ + m₂) n = f₁.resultant g m₁ n * f₂.resultant g m₂ n := by
  obtain ⟨k₁, rfl⟩ := Nat.exists_eq_add_of_le hf₁
  obtain ⟨k₂, rfl⟩ := Nat.exists_eq_add_of_le hf₂
  rw [Nat.add_add_add_comm, resultant_add_left_deg _ _ _ _ _ natDegree_mul_le,
    resultant_mul_left _ _ _ _ hg, resultant_add_left_deg _ _ _ _ _ le_rfl,
    resultant_add_left_deg _ _ _ _ _ le_rfl]
  ring

/-- The linear polynomial `1 - t X` has degree at most one. -/
theorem natDegree_one_sub_C_mul_X_le (t : R) : (1 - C t * X).natDegree ≤ 1 := by
  compute_degree

/-- The resultant of `f` with the linear polynomial `1 - t X`, at the degree bound `n` for `f`, is
the value at `t` of the reversal of `f` in degree `n`. When `f = ∏ (X - αᵢ)` has degree `n`, both
sides are `∏ (1 - αᵢ t)`. -/
theorem resultant_one_sub_C_mul_X_right (f : R[X]) (t : R) {n : ℕ} (hf : f.natDegree ≤ n) :
    f.resultant (1 - C t * X) n 1 = (f.reflect n).eval t := by
  set ℓ : R[X] := 1 - C t * X
  have hℓ : ℓ.natDegree ≤ 1 := natDegree_one_sub_C_mul_X_le t
  -- the value of the reversal, as a sum over the coefficients of `f`
  set c : R := ∑ j ∈ Finset.range (n + 1), f.coeff j * t ^ (n - j)
  have hc : (f.reflect n).eval t = c := by
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_reflect_le.trans (max_le le_rfl hf))),
      ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Nat.succ_sub_one, coeff_reflect, revAt_le (Nat.sub_le n j), Nat.sub_sub_self hj]
  rw [hc]
  obtain _ | n := n
  · rw [resultant_zero_left_deg]
    simp [c]
  -- modulo `ℓ`, `X ^ j` is congruent to `t ^ (n - j) * X ^ n`, through a polynomial of degree `< n`
  set p : R[X] := -∑ j ∈ Finset.range (n + 2), ∑ i ∈ Finset.range (n + 1 - j),
    C (f.coeff j * t ^ i) * X ^ (j + i)
  have hp : p.natDegree + 1 ≤ n + 1 := by
    refine Nat.succ_le_succ ((natDegree_neg _).le.trans (natDegree_sum_le_of_forall_le _ _
      fun j _ ↦ natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_))
    exact (natDegree_C_mul_X_pow_le _ _).trans (by simp at hi; lia)
  have hfp : f + ℓ * p = C c * X ^ (n + 1) := by
    have hgeom (j : ℕ) : ℓ * ∑ i ∈ Finset.range (n + 1 - j), C (f.coeff j * t ^ i) * X ^ (j + i)
        = C (f.coeff j) * X ^ j - C (f.coeff j) * X ^ j * (C t * X) ^ (n + 1 - j) := by
      rw [← mul_one_sub, ← mul_neg_geom_sum]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp only [ℓ, C_mul, C_pow]
      ring
    rw [as_sum_range_C_mul_X_pow' f (n := n + 2) (by lia), mul_neg, Finset.mul_sum,
      Finset.sum_congr rfl fun j _ ↦ hgeom j, Finset.sum_sub_distrib, neg_sub, add_sub_cancel]
    simp only [c, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj : j ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [← pow_mul_pow_sub X hj, C_mul, C_pow]
    ring
  rw [← resultant_add_mul_left f ℓ p (n + 1) 1 hp hℓ, hfp, resultant_C_mul_left,
    resultant_X_pow_left _ _ _ hℓ]
  simp [ℓ]

/-- Resultants at the actual degrees commute with a coefficient map that preserves both degrees,
for instance an injective one or one that does not kill the leading coefficients
(`Polynomial.natDegree_map_of_leadingCoeff_ne_zero`). Without this hypothesis the original
degrees must be kept as explicit bounds, as in `Polynomial.resultant_map_map`. -/
theorem resultant_map_of_natDegree_eq {S : Type*} [CommRing S] (φ : R →+* S) {f g : R[X]}
    (hf : (f.map φ).natDegree = f.natDegree) (hg : (g.map φ).natDegree = g.natDegree) :
    (f.map φ).resultant (g.map φ) = φ (f.resultant g) := by
  rw [hf, hg, resultant_map_map]

end Polynomial

namespace TauCeti

open Polynomial

variable {R : Type*} [CommRing R]

/-- For monic `f`, `f.resultant g` does not depend on which valid upper bound is supplied for the
degree of `g`. -/
theorem _root_.Polynomial.Monic.resultant_of_le {f g : R[X]} (hf : f.Monic) {n : ℕ}
    (hn : g.natDegree ≤ n) : f.resultant g f.natDegree n = f.resultant g := by
  have hn' : n = g.natDegree + (n - g.natDegree) :=
    (Nat.add_sub_cancel' hn).symm
  conv_lhs => rw [hn']
  rw [Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl, Polynomial.coeff_natDegree,
    hf.leadingCoeff, one_pow, one_mul]

end TauCeti
