/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.RiemannHurwitz
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Divisor
public import TauCeti.Analysis.Complex.RiemannSurface.PowerMap

/-!
# The degree of a canonical divisor

On a compact connected Riemann surface `X` any two canonical divisors are linearly equivalent
(`TauCeti.RiemannSurface.IsCanonicalDivisor.linearlyEquivalent`), and linearly equivalent divisors
have the same degree because principal divisors have degree zero
(`TauCeti.RiemannSurface.MeromorphicFunction.degree_eq_of_linearlyEquivalent`). So all canonical
divisors of `X` have the same degree (`TauCeti.RiemannSurface.IsCanonicalDivisor.degree_eq`).

Combined with the pullback formula `div(f*ω) = f*(div ω) + R_f`, this gives the canonical-divisor
form of Riemann–Hurwitz for every canonical divisor, not just for the pulled-back one: if
`f : X → Y` is a finite holomorphic map of compact connected Riemann surfaces and `K_X`, `K_Y` are
canonical divisors, then `deg K_X = deg f · deg K_Y + deg R_f`
(`TauCeti.RiemannSurface.IsCanonicalDivisor.degree_eq_degree_mul_add_ramificationDegree`).

Every canonical divisor of the Riemann sphere has degree `-2`, the degree of `div dz = -2[∞]`
(`TauCeti.RiemannSurface.IsCanonicalDivisor.degree_eq_neg_two_of_sphere`). Hence for a finite
holomorphic map `f : X → ℙ¹` every canonical divisor `K` of `X` has
`deg K = -2 deg f + deg R_f`
(`TauCeti.RiemannSurface.IsCanonicalDivisor.degree_eq_neg_two_mul_degree_add_ramificationDegree`),
so the right-hand side does not depend on `f`
(`TauCeti.RiemannSurface.FiniteHolomorphicMap.neg_two_mul_degree_add_ramificationDegree_eq`). For
a map `ℙ¹ → ℙ¹` it says `deg R_f = 2 deg f - 2`
(`TauCeti.RiemannSurface.FiniteHolomorphicMap.ramificationDegree_eq_two_mul_degree_sub_two`).

That the common degree is `2g - 2` for the analytic genus `g` needs Serre duality and is not
proved here.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §17 (the canonical divisor class and the Riemann–Hurwitz formula).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter IV §2 and Chapter V §1.
-/

public section

open OnePoint
open scoped Manifold

namespace TauCeti.RiemannSurface

open AlgebraicGeometry

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [ConnectedSpace X] [T2Space X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y] [CompactSpace Y]

namespace IsCanonicalDivisor

/-- **All canonical divisors have the same degree.** On a compact connected Riemann surface, any
two canonical divisors have equal degree. -/
theorem degree_eq {K K' : WeilDivisor X} (hK : IsCanonicalDivisor K)
    (hK' : IsCanonicalDivisor K') : WeilDivisor.degree K = WeilDivisor.degree K' :=
  MeromorphicFunction.degree_eq_of_linearlyEquivalent (hK.linearlyEquivalent hK')

/-- **Riemann–Hurwitz for canonical divisors.** If `f : X → Y` is a finite holomorphic map of
compact connected Riemann surfaces, then canonical divisors `K_X` of `X` and `K_Y` of `Y`
satisfy `deg K_X = deg f · deg K_Y + deg R_f`. -/
theorem degree_eq_degree_mul_add_ramificationDegree [T2Space Y] [ConnectedSpace Y]
    {KX : WeilDivisor X} {KY : WeilDivisor Y}
    (hKX : IsCanonicalDivisor KX) (hKY : IsCanonicalDivisor KY) (f : FiniteHolomorphicMap X Y) :
    WeilDivisor.degree KX = degree f * WeilDivisor.degree KY + ramificationDegree f := by
  rw [hKX.degree_eq (hKY.divisorPullback_add_ramificationDivisor f), map_add,
    degree_divisorPullback, degree_ramificationDivisor]

/-- **Every canonical divisor of the Riemann sphere has degree `-2`.** -/
theorem degree_eq_neg_two_of_sphere {K : WeilDivisor (OnePoint ℂ)} (hK : IsCanonicalDivisor K) :
    WeilDivisor.degree K = -2 := by
  rw [hK.degree_eq isCanonicalDivisor_neg_two_infty, map_zsmul, WeilDivisor.degree_ofPoint]
  rfl

/-- **Riemann–Hurwitz over the sphere.** If `f : X → ℙ¹` is a finite holomorphic map from a
compact connected Riemann surface, every canonical divisor `K` of `X` has degree
`-2 deg f + deg R_f`. -/
theorem degree_eq_neg_two_mul_degree_add_ramificationDegree {K : WeilDivisor X}
    (hK : IsCanonicalDivisor K) (f : FiniteHolomorphicMap X (OnePoint ℂ)) :
    WeilDivisor.degree K = -2 * (degree f : ℤ) + ramificationDegree f := by
  rw [hK.degree_eq_degree_mul_add_ramificationDegree isCanonicalDivisor_neg_two_infty f,
    map_zsmul, WeilDivisor.degree_ofPoint]
  ring

end IsCanonicalDivisor

namespace FiniteHolomorphicMap

/-- **The Riemann–Hurwitz count does not depend on the map.** For two finite holomorphic maps
`f g : X → ℙ¹` from a compact connected Riemann surface,
`-2 deg f + deg R_f = -2 deg g + deg R_g`. -/
theorem neg_two_mul_degree_add_ramificationDegree_eq (f g : FiniteHolomorphicMap X (OnePoint ℂ)) :
    -2 * (degree f : ℤ) + ramificationDegree f = -2 * (degree g : ℤ) + ramificationDegree g := by
  have hK := isCanonicalDivisor_neg_two_infty.divisorPullback_add_ramificationDivisor f
  rw [← hK.degree_eq_neg_two_mul_degree_add_ramificationDegree f,
    hK.degree_eq_neg_two_mul_degree_add_ramificationDegree g]

/-- **Riemann–Hurwitz for maps of the sphere.** A finite holomorphic map `f : ℙ¹ → ℙ¹` has
ramification degree `2 deg f - 2`. -/
theorem ramificationDegree_eq_two_mul_degree_sub_two
    (f : FiniteHolomorphicMap (OnePoint ℂ) (OnePoint ℂ)) :
    (ramificationDegree f : ℤ) = 2 * degree f - 2 := by
  have h := isCanonicalDivisor_neg_two_infty.degree_eq_neg_two_mul_degree_add_ramificationDegree f
  rw [isCanonicalDivisor_neg_two_infty.degree_eq_neg_two_of_sphere] at h
  linarith

/-- The power map `z ↦ z²` of the sphere has degree `2` and ramification degree `2`, matching
`-2 = -2 · 2 + 2` for the canonical divisor of the sphere. -/
example : -2 * (degree (spherePow two_ne_zero) : ℤ) + ramificationDegree (spherePow two_ne_zero) =
    -2 := by
  rw [coe_spherePow, ramificationDegree_onePointMap_pow two_ne_zero,
    degree_onePointMap_pow]
  norm_num

/-- The identity `z ↦ z ^ 1` of the sphere has degree `1` and ramification degree `0`, matching
`-2 = -2 · 1 + 0`. -/
example : -2 * (degree (spherePow one_ne_zero) : ℤ) + ramificationDegree (spherePow one_ne_zero) =
    -2 := by
  rw [coe_spherePow, ramificationDegree_onePointMap_pow one_ne_zero,
    degree_onePointMap_pow]
  norm_num

end FiniteHolomorphicMap

end TauCeti.RiemannSurface
