/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.ComputeDegree

/-!
# Lifting nonsingular points over a Henselian local ring

Let `R` be a Henselian local ring with residue field `k`, and let `W` be a Weierstrass curve over
`R`. Every nonsingular affine point of the reduced curve `W_k` lifts to a nonsingular affine point
of `W` over `R`. One of the two partial derivatives of the Weierstrass polynomial is nonzero at the
residue point. Fixing the other coordinate turns the Weierstrass equation into a monic polynomial
in the remaining coordinate, of degree two in `y` or three in `x`, with a simple root over `k`, and
Hensel's lemma lifts that root.

This is the input to the right-exactness of the reduction sequence
`0 → E₁(K) → E₀(K) → W_k,ns(k) → 0` over a Henselian valued field (Silverman AEC VII.2.1).

## Main results

* `WeierstrassCurve.Affine.exists_nonsingular_residue_eq`: over a Henselian local ring, a
  nonsingular point of the reduced curve is the reduction of a nonsingular point.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2.1.
-/

public section

open IsLocalRing Polynomial

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] [HenselianLocalRing R] {W : Affine R}

/-- If `W_X` is a unit at `(x₁, y₁)` and the equation holds modulo the maximal ideal, fixing
`y = y₁` and lifting a simple root of the resulting monic cubic in `x` gives a nonsingular point
`(x, y₁)` with `x ≡ x₁`. -/
private theorem exists_nonsingular_residue_eq_of_isUnit_X {x₁ y₁ : R}
    (heq : residue R (y₁ ^ 2 + W.a₁ * x₁ * y₁ + W.a₃ * y₁ -
      (x₁ ^ 3 + W.a₂ * x₁ ^ 2 + W.a₄ * x₁ + W.a₆)) = 0)
    (hX : IsUnit (W.a₁ * y₁ - (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄))) :
    ∃ x : R, W.Nonsingular x y₁ ∧ residue R x = residue R x₁ := by
  set g : R[X] := X ^ 3 + C W.a₂ * X ^ 2 + C (W.a₄ - W.a₁ * y₁) * X +
    C (W.a₆ - y₁ ^ 2 - W.a₃ * y₁) with hg
  have hgm : g.Monic := by
    rw [hg]
    monicity!
  have hgeval (x : R) : g.eval x =
      -(y₁ ^ 2 + W.a₁ * x * y₁ + W.a₃ * y₁ - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) := by
    simp only [hg, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    ring
  have hgder : g.derivative.eval x₁ = -(W.a₁ * y₁ - (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄)) := by
    simp only [hg, derivative_add, derivative_mul, derivative_X_pow, derivative_C,
      derivative_X, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_zero, eval_one]
    push_cast
    ring
  obtain ⟨x, hx, hxx₁⟩ := HenselianLocalRing.is_henselian g hgm x₁
    (by rw [← residue_eq_zero_iff, hgeval, map_neg, heq, neg_zero])
    (by rwa [hgder, IsUnit.neg_iff])
  have hres : residue R x = residue R x₁ := by
    rwa [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  refine ⟨x, (nonsingular_iff' x y₁).mpr ⟨(equation_iff' x y₁).mpr ?_, .inl ?_⟩, hres⟩
  · rw [← neg_eq_zero, ← hgeval]
    exact hx
  · -- `W_X(x, y₁)` has the same residue as the unit `W_X(x₁, y₁)`
    rw [← residue_ne_zero_iff_isUnit] at hX
    intro h0
    apply hX
    simpa only [map_sub, map_add, map_mul, map_pow, map_zero, hres] using congrArg (residue R) h0

/-- If `W_Y` is a unit at `(x₁, y₁)` and the equation holds modulo the maximal ideal, fixing
`x = x₁` and lifting a simple root of the resulting monic quadratic in `y` gives a nonsingular point
`(x₁, y)` with `y ≡ y₁`. -/
private theorem exists_nonsingular_residue_eq_of_isUnit_Y {x₁ y₁ : R}
    (heq : residue R (y₁ ^ 2 + W.a₁ * x₁ * y₁ + W.a₃ * y₁ -
      (x₁ ^ 3 + W.a₂ * x₁ ^ 2 + W.a₄ * x₁ + W.a₆)) = 0)
    (hY : IsUnit (2 * y₁ + W.a₁ * x₁ + W.a₃)) :
    ∃ y : R, W.Nonsingular x₁ y ∧ residue R y = residue R y₁ := by
  set f : R[X] := X ^ 2 + C (W.a₁ * x₁ + W.a₃) * X -
    C (x₁ ^ 3 + W.a₂ * x₁ ^ 2 + W.a₄ * x₁ + W.a₆) with hf
  have hfm : f.Monic := by
    rw [hf]
    monicity!
  have hfeval (y : R) : f.eval y =
      y ^ 2 + W.a₁ * x₁ * y + W.a₃ * y - (x₁ ^ 3 + W.a₂ * x₁ ^ 2 + W.a₄ * x₁ + W.a₆) := by
    simp only [hf, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
    ring
  have hfder : f.derivative.eval y₁ = 2 * y₁ + W.a₁ * x₁ + W.a₃ := by
    simp only [hf, derivative_add, derivative_sub, derivative_mul, derivative_X_pow,
      derivative_C, derivative_X, eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X,
      eval_zero, eval_one]
    push_cast
    ring
  obtain ⟨y, hy, hyy₁⟩ := HenselianLocalRing.is_henselian f hfm y₁
    (by rwa [← residue_eq_zero_iff, hfeval]) (by rwa [hfder])
  have hres : residue R y = residue R y₁ := by
    rwa [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  refine ⟨y, (nonsingular_iff' x₁ y).mpr ⟨(equation_iff' x₁ y).mpr ?_, .inr ?_⟩, hres⟩
  · rw [← hfeval]
    exact hy
  · -- `W_Y(x₁, y)` has the same residue as the unit `W_Y(x₁, y₁)`
    rw [← residue_ne_zero_iff_isUnit] at hY
    intro h0
    apply hY
    simpa only [map_add, map_mul, map_ofNat, map_zero, hres] using congrArg (residue R) h0

/-- **Hensel lifting of nonsingular points.** Over a Henselian local ring `R`, every nonsingular
affine point `(x₀, y₀)` of the reduced curve `W_k` over the residue field is the reduction of a
nonsingular affine point `(x, y)` of `W` over `R`. -/
theorem exists_nonsingular_residue_eq {x₀ y₀ : ResidueField R}
    (h : (W.map (residue R)).toAffine.Nonsingular x₀ y₀) :
    ∃ x y : R, W.Nonsingular x y ∧ residue R x = x₀ ∧ residue R y = y₀ := by
  obtain ⟨x₁, rfl⟩ := residue_surjective x₀
  obtain ⟨y₁, rfl⟩ := residue_surjective y₀
  rw [nonsingular_iff', equation_iff'] at h
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at h
  obtain ⟨heq, hXY⟩ := h
  have heq' : residue R (y₁ ^ 2 + W.a₁ * x₁ * y₁ + W.a₃ * y₁ -
      (x₁ ^ 3 + W.a₂ * x₁ ^ 2 + W.a₄ * x₁ + W.a₆)) = 0 := by
    simpa only [map_sub, map_add, map_mul, map_pow] using heq
  rcases hXY with hX | hY
  · have hX' : IsUnit (W.a₁ * y₁ - (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄)) := by
      rw [← residue_ne_zero_iff_isUnit]
      simpa only [map_sub, map_add, map_mul, map_pow, map_ofNat] using hX
    obtain ⟨x, hx, hres⟩ := exists_nonsingular_residue_eq_of_isUnit_X heq' hX'
    exact ⟨x, y₁, hx, hres, rfl⟩
  · have hY' : IsUnit (2 * y₁ + W.a₁ * x₁ + W.a₃) := by
      rw [← residue_ne_zero_iff_isUnit]
      simpa only [map_add, map_mul, map_ofNat] using hY
    obtain ⟨y, hy, hres⟩ := exists_nonsingular_residue_eq_of_isUnit_Y heq' hY'
    exact ⟨x₁, y, hy, rfl, hres⟩

end WeierstrassCurve.Affine

end
