/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
import TauCeti.RingTheory.PowerSeries.Derivative
import TauCeti.RingTheory.PowerSeries.Hensel

/-!
# The coordinate series of a normalized cubic

On the cubic `y² + axy = x³ + x`, the coordinate `x` is a unique formal series in `y`
near `(0, 0)`, over any commutative coefficient ring. It begins with the term `y²`.
The construction commutes with passage to a larger coefficient ring and substitution of
any series with zero constant term. In particular, if `a` belongs to a valuation ring,
the formal coordinate `x` is an integral series in `y`.

This is the simple-root form of Hensel's lemma applied to the cubic in `x`. The coordinate
and its use for integral expansions of CM theta functions follow the statement of
`New.exists_isRoot_cubic_constantCoeff_eq_zero` in
`grh/src/Lib/CM/FormalGroup/IntegralParameter.lean`
of <https://github.com/lsernau/grh-lean> at revision `72fead1`.
-/

public section

open PowerSeries

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- Two solutions of `y² + axy = x³ + x` with zero constant term in `x` agree when
`y` also has zero constant term. No field or characteristic assumption is needed. -/
theorem eq_of_cubic_series {a : R} {x x' y : R⟦X⟧}
    (hx : constantCoeff x = 0) (hx' : constantCoeff x' = 0)
    (hy : constantCoeff y = 0)
    (h : y ^ 2 + C a * x * y = x ^ 3 + x)
    (h' : y ^ 2 + C a * x' * y = x' ^ 3 + x') : x = x' := by
  have hu : IsUnit (x ^ 2 + x * x' + x' ^ 2 + 1 - C a * y) := by
    apply isUnit_iff_constantCoeff.mpr
    simp [hx, hx', hy]
  have hz : (x - x') * (x ^ 2 + x * x' + x' ^ 2 + 1 - C a * y) = 0 := by
    linear_combination h' - h
  exact sub_eq_zero.mp ((hu.mul_left_eq_zero).mp hz)

/-- Over any commutative ring there is a unique series `x` with zero constant term
satisfying `X² + a x X = x³ + x`. Thus `y` is an integral formal parameter at `(0, 0)`
for this cubic, including in characteristics two and three. -/
theorem existsUnique_cubic_series (a : R) :
    ∃! x : R⟦X⟧, constantCoeff x = 0 ∧ X ^ 2 + C a * x * X = x ^ 3 + x := by
  let P : Polynomial R⟦X⟧ := Polynomial.X ^ 3 + Polynomial.X -
    Polynomial.C (C a * X) * Polynomial.X - Polynomial.C (X ^ 2)
  have hr : (P.map constantCoeff).IsRoot 0 := by simp [P, Polynomial.IsRoot]
  have hu : IsUnit ((P.map constantCoeff).derivative.eval 0) := by simp [P]
  obtain ⟨x, hx, _⟩ := Polynomial.existsUnique_isRoot_constantCoeff_eq P hr hu
  have he : X ^ 2 + C a * x * X = x ^ 3 + x := by
    have hp := hx.1
    simp only [Polynomial.IsRoot, P, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C] at hp
    linear_combination -hp
  exact ⟨x, ⟨hx.2, he⟩, fun x' hx' ↦ eq_of_cubic_series hx'.1 hx.2 (by simp) hx'.2 he⟩

/-- Every solution of the normalized cubic with zero constant coordinates is obtained by
substituting `y` into a series over the ring containing `a`. This expresses integrality
in the parameter `y` without requiring that `y` itself have integral coefficients. -/
theorem _root_.RingHom.exists_map_subst_eq_of_cubic_series {S : Type*} [CommRing S] (φ : R →+* S)
    (a : R) {x y : S⟦X⟧} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0)
    (h : y ^ 2 + C (φ a) * x * y = x ^ 3 + x) :
    ∃ f : R⟦X⟧, constantCoeff f = 0 ∧ X ^ 2 + C a * f * X = f ^ 3 + f ∧
      (f.map φ).subst y = x := by
  obtain ⟨f, ⟨hf, he⟩, _⟩ := existsUnique_cubic_series a
  have hs := HasSubst.of_constantCoeff_zero' hy
  have hm : X ^ 2 + C (φ a) * f.map φ * X = f.map φ ^ 3 + f.map φ := by
    simpa only [map_add, map_mul, map_pow, map_X, map_C] using congrArg (map φ) he
  have heq : y ^ 2 + C (φ a) * (f.map φ).subst y * y =
      (f.map φ).subst y ^ 3 + (f.map φ).subst y := by
    simpa only [subst_add hs, subst_mul hs, subst_pow hs, subst_X hs, subst_C, ← C_apply] using
      congrArg (fun g : S⟦X⟧ ↦ g.subst y) hm
  refine ⟨f, hf, he, eq_of_cubic_series ?_ hx hy heq h⟩
  rw [constantCoeff_eq]
  exact constantCoeff_subst_eq_zero hy _ (by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map,
      coeff_zero_eq_constantCoeff_apply, hf, map_zero])

/-- The linear coefficient of the `x` coordinate vanishes at the origin of the cubic. -/
theorem coeff_one_eq_zero_of_cubic_series {a : R} {x y : R⟦X⟧}
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0)
    (h : y ^ 2 + C a * x * y = x ^ 3 + x) : coeff 1 x = 0 := by
  have hc := congrArg (coeff 1) h
  simpa [pow_succ, coeff_one_mul, hx, hy] using hc.symm

/-- The quadratic coefficient of `x` is the square of the linear coefficient of `y`.
In particular `y = z + O(z²)` gives `x = z² + O(z³)`. -/
theorem coeff_two_eq_of_cubic_series {a : R} {x y : R⟦X⟧}
    (hx : constantCoeff x = 0) (hy : constantCoeff y = 0)
    (h : y ^ 2 + C a * x * y = x ^ 3 + x) : coeff 2 x = coeff 1 y ^ 2 := by
  have hx1 := coeff_one_eq_zero_of_cubic_series hx hy h
  have hc := congrArg (coeff 2) h
  simpa [pow_succ, coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_zero_eq_constantCoeff,
    hx, hy, hx1, coeff_one_mul, pow_two] using hc.symm

/-- If `x, y` satisfy the cubic and `y' = 1 + 3x² - ay`, differentiation preserves
series in `y` over the coefficient ring. This applies even if `y` has nonintegral
coefficients in the ambient ring. -/
theorem _root_.RingHom.exists_map_subst_derivative_of_cubic_series {S : Type*} [CommRing S]
    (φ : R →+* S) (a : R) {x y : S⟦X⟧} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) (h : y ^ 2 + C (φ a) * x * y = x ^ 3 + x)
    (hd : derivative y = 1 + 3 * x ^ 2 - C (φ a) * y) (f : R⟦X⟧) :
    ∃ g : R⟦X⟧, (g.map φ).subst y = derivative ((f.map φ).subst y) := by
  obtain ⟨F, _, _, hF⟩ := φ.exists_map_subst_eq_of_cubic_series a hx hy h
  have hs := HasSubst.of_constantCoeff_zero' hy
  refine ⟨derivative f * (1 + 3 * F ^ 2 - C a * X), ?_⟩
  rw [map_mul, subst_mul hs, derivative_subst hs, derivative_map]
  congr 1
  simp only [map_sub, map_add, map_one, map_ofNat, map_mul, map_pow, map_C, map_X,
    ← coe_substAlgHom hs, map_sub, map_add, map_one, map_ofNat, map_mul, map_pow,
    substAlgHom_X] at hF ⊢
  simpa [hF, C_eq_algebraMap] using hd.symm

end TauCeti
