/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.Smooth.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Singular

import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Eval

/-!
# Singular points obstruct formal smoothness

If a Weierstrass model `W` over a commutative ring `R` has a singular point with coordinates in
some nontrivial `R`-algebra `B`, then its affine coordinate ring `R[W]` is not formally smooth
over `R`.

The obstruction is a tangent vector that does not lift. At a singular point `(x, y)` the equation
has no constant or linear terms: it reads
`(Y - y)² + a₁ (X - x) (Y - y) = (X - x)³ + (3 x + a₂) (X - x)²`. Over `C = B[t] ⧸ (t³)` the point
`(x, y + t)` is therefore a solution modulo the square-zero ideal `(t²)`, but every lift
`(x + c t², y + t + d t²)` to `C` would force `t² = 0`.

This is the algebraic input to the converse of `WeierstrassCurve.smooth_projModelOver`: a
Weierstrass model whose projective model is smooth over the base has unit discriminant.

## Main results

* `WeierstrassCurve.Affine.not_formallySmooth_coordinateRing_of_isSingular`: a singular point over
  a nontrivial algebra rules out formal smoothness of the coordinate ring.

## References

* Stacks Project, Tag 00TI (formal smoothness by infinitesimal lifting).
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1.
-/

public section

namespace WeierstrassCurve.Affine

open Polynomial

variable {R : Type*} [CommRing R] {W : WeierstrassCurve.Affine R}

/-- The lifting argument over an algebra containing `t` with `t³ = 0` and `t² ≠ 0`: the point
`(x, y + t)` modulo `(t²)` has no lift. -/
private theorem not_formallySmooth_coordinateRing_of_isSingular_of_pow_three_eq_zero
    {C : Type*} [CommRing C] [Algebra R C] {x y t : C} (h : (W⁄C).toAffine.IsSingular x y)
    (ht : t ^ 3 = 0) (ht' : t ^ 2 ≠ 0) :
    ¬ Algebra.FormallySmooth R W.CoordinateRing := by
  intro hW
  let I : Ideal C := Ideal.span {t ^ 2}
  have hI : I ^ 2 = ⊥ := by
    rw [Ideal.span_singleton_pow, ← pow_mul, Ideal.span_singleton_eq_bot]
    linear_combination t * ht
  have htI : (Ideal.Quotient.mk I t) ^ 2 = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  -- the tangent vector `(x, y + t)` is a point modulo `I`
  have hE : (W⁄(C ⧸ I)).toAffine.Equation (Ideal.Quotient.mk I x)
      (Ideal.Quotient.mk I y + Ideal.Quotient.mk I t) := by
    rw [equation_iff_of_isSingular (h.baseChange (IsScalarTower.toAlgHom R C (C ⧸ I)))]
    simp [htI]
  obtain ⟨ψ, hψ⟩ := Algebra.FormallySmooth.comp_surjective R W.CoordinateRing I hI
    (CoordinateRing.evalAlgHom hE)
  have hmem (z : W.CoordinateRing) (w : C)
      (hz : Ideal.Quotient.mk I (ψ z) = Ideal.Quotient.mk I w) : ∃ c, ψ z = w + c * t ^ 2 := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hz)
    exact ⟨c, by rw [hc]; ring⟩
  obtain ⟨c, hc⟩ := hmem (AdjoinRoot.of W.polynomial X) x <| by
    simpa using congr($hψ (AdjoinRoot.of W.polynomial X))
  obtain ⟨d, hd⟩ := hmem (AdjoinRoot.root W.polynomial) (y + t) <| by
    simpa using congr($hψ (AdjoinRoot.root W.polynomial))
  -- the lift `(x + c t², y + t + d t²)` satisfies the equation expanded at `(x, y)`
  have h0 := (equation_iff_of_isSingular h _ _).mp (CoordinateRing.equation_of_algHom ψ)
  rw [hc, hd] at h0
  exact ht' (by linear_combination h0 - (2 * d + d ^ 2 * t + (W⁄C).a₁ * c +
    (W⁄C).a₁ * c * d * t - c ^ 3 * t ^ 3 - (3 * x + (W⁄C).a₂) * c ^ 2 * t) * ht)

/-- **A singular point obstructs formal smoothness.** If the base change of `W` to a nontrivial
`R`-algebra `B` has a singular point, then the coordinate ring `R[W]` is not formally smooth
over `R`. -/
theorem not_formallySmooth_coordinateRing_of_isSingular {B : Type*} [CommRing B] [Nontrivial B]
    [Algebra R B] {x y : B} (h : (W⁄B).toAffine.IsSingular x y) :
    ¬ Algebra.FormallySmooth R W.CoordinateRing := by
  refine not_formallySmooth_coordinateRing_of_isSingular_of_pow_three_eq_zero
    (h.baseChange (IsScalarTower.toAlgHom R B (B[X] ⧸ Ideal.span {(X ^ 3 : B[X])})))
    (t := Ideal.Quotient.mk _ X) ?_ ?_
  · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  · rw [← map_pow, Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, X_pow_dvd_iff]
    intro h2
    simpa using h2 2 (by norm_num)

end WeierstrassCurve.Affine
