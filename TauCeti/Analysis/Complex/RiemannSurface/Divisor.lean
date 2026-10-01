/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.FiniteSum
public import TauCeti.Analysis.Complex.RiemannSurface.Degree

/-!
# Pullback of divisors on Riemann surfaces

A finite holomorphic map `f : X → Y` pulls a divisor on `Y` back to `X` by multiplying the
coefficient at `f x` by the local multiplicity of `f` at `x`. The resulting function on `X` has
finite support because `f` has finite fibres. This file packages the construction as the additive
homomorphism `TauCeti.RiemannSurface.divisorPullback` on the existing finite formal sums
`TauCeti.AlgebraicGeometry.WeilDivisor`.

Pullback is contravariantly functorial. On a point divisor it is the sum of the points in the
fibre, weighted by their local multiplicities, and therefore its divisor degree is the analytic
degree of the map. More generally, pullback multiplies divisor degree by the degree of the finite
holomorphic map. These formulas are the divisor-theoretic form of counting a fibre with
multiplicity and are used to construct ramification divisors.

## Main declarations

* `TauCeti.RiemannSurface.divisorPullback`: pullback of finite formal divisors by a finite
  holomorphic map.
* `TauCeti.RiemannSurface.coeff_divisorPullback`: the coefficient of the pullback at a point.
* `TauCeti.RiemannSurface.divisorPullback_comp`: pullback reverses composition.
* `TauCeti.RiemannSurface.degree_divisorPullback`: pullback multiplies divisor degree
  by the degree of the map.

## References

* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §4.
-/

public noncomputable section

open Function Set

open scoped Manifold

namespace TauCeti.RiemannSurface

open AlgebraicGeometry

variable {X Y Z : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
  [ChartedSpace ℂ Y]

/-- The support of the coefficient function defining divisor pullback is finite. -/
private theorem finite_support_divisor_pullback (f : FiniteHolomorphicMap X Y)
    (D : WeilDivisor Y) :
    (Function.support fun x ↦ (localMultiplicity f x : ℤ) * D (f x)).Finite := by
  refine (D.support.finite_toSet.preimage' fun y _ ↦ f.finite_fiber y).subset ?_
  intro x hx
  have hD : D (f x) ≠ 0 := by
    intro h
    exact hx (by simp [h])
  exact Finsupp.mem_support_iff.mpr hD

/-- Pullback of a divisor by a finite holomorphic map. The coefficient at `x` is the coefficient
at `f x`, multiplied by the local multiplicity of `f` at `x`. -/
def divisorPullback (f : FiniteHolomorphicMap X Y) : WeilDivisor Y →+ WeilDivisor X where
  toFun D := Finsupp.ofSupportFinite
    (fun x ↦ (localMultiplicity f x : ℤ) * D (f x))
    (finite_support_divisor_pullback f D)
  map_zero' := by
    apply Finsupp.ext
    intro x
    rfl
  map_add' D E := by
    apply Finsupp.ext
    intro x
    exact mul_add _ _ _

/-- The coefficient of a pulled-back divisor is the coefficient at the image point multiplied by
the local multiplicity. -/
@[simp]
theorem coeff_divisorPullback (f : FiniteHolomorphicMap X Y) (D : WeilDivisor Y) (x : X) :
    WeilDivisor.coeff (divisorPullback f D) x =
      (localMultiplicity f x : ℤ) * WeilDivisor.coeff D (f x) :=
  (rfl)

/-- Pullback preserves effective divisors. -/
theorem _root_.TauCeti.AlgebraicGeometry.WeilDivisor.IsEffective.divisorPullback
    {D : WeilDivisor Y}
    (hD : WeilDivisor.IsEffective D) (f : FiniteHolomorphicMap X Y) :
    WeilDivisor.IsEffective (divisorPullback f D) := by
  rw [WeilDivisor.isEffective_iff] at hD ⊢
  intro x
  rw [coeff_divisorPullback]
  exact mul_nonneg (Int.natCast_nonneg _) (hD (f x))

/-- Pulling back a point divisor gives the fibre, with each point weighted by its local
multiplicity. -/
@[simp]
theorem divisorPullback_ofPoint (f : FiniteHolomorphicMap X Y) (y : Y) :
    divisorPullback f (WeilDivisor.ofPoint y) =
      WeilDivisor.ofFinsetWithMultiplicity (f.finite_fiber y).toFinset
        (localMultiplicity f) := by
  classical
  apply WeilDivisor.ext
  intro x
  rw [coeff_divisorPullback, WeilDivisor.coeff_ofFinsetWithMultiplicity]
  by_cases hxy : f x = y
  · simp [hxy, f.finite_fiber y |>.mem_toFinset]
  · simp [hxy, WeilDivisor.coeff_ofPoint_of_ne hxy, f.finite_fiber y |>.mem_toFinset]

section Connected

variable [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y] [PreconnectedSpace X]

/-- The support of a pulled-back divisor is the preimage of the original support. -/
@[simp]
theorem support_divisorPullback (f : FiniteHolomorphicMap X Y) (D : WeilDivisor Y) :
    ↑(divisorPullback f D).support = f ⁻¹' (D.support : Set Y) := by
  ext x
  simp only [Finset.mem_coe, WeilDivisor.mem_support_iff, coeff_divisorPullback,
    mul_ne_zero_iff, Int.natCast_ne_zero, mem_preimage]
  exact and_iff_right (Nat.ne_zero_iff_zero_lt.mpr (localMultiplicity_pos f x))

section Compact

variable [CompactSpace X] [T2Space X] [T2Space Y] [PreconnectedSpace Y]

/-- Pullback of divisors reverses composition of finite holomorphic maps. -/
@[simp]
theorem divisorPullback_comp [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [IsManifold 𝓘(ℂ) 1 Z] (g : FiniteHolomorphicMap Y Z) (f : FiniteHolomorphicMap X Y) :
    divisorPullback (g.comp f) = (divisorPullback f).comp (divisorPullback g) := by
  apply AddMonoidHom.ext
  intro D
  apply WeilDivisor.ext
  intro x
  rw [coeff_divisorPullback, AddMonoidHom.comp_apply, coeff_divisorPullback,
    coeff_divisorPullback, localMultiplicity_comp]
  push_cast
  simp only [FiniteHolomorphicMap.coe_comp, Function.comp_apply]
  ring

/-- Pulling back a point divisor has divisor degree equal to the degree of the finite holomorphic
map. -/
theorem degree_divisorPullback_ofPoint (f : FiniteHolomorphicMap X Y) (y : Y) :
    WeilDivisor.degree (divisorPullback f (WeilDivisor.ofPoint y)) =
      (degree f : ℤ) := by
  rw [divisorPullback_ofPoint, WeilDivisor.degree_ofFinsetWithMultiplicity]
  exact_mod_cast (degree_eq_fiber_sum f y).symm

/-- Pullback multiplies the degree of a divisor by the degree of the finite holomorphic map. -/
@[simp]
theorem degree_divisorPullback (f : FiniteHolomorphicMap X Y)
    (D : WeilDivisor Y) :
    WeilDivisor.degree (divisorPullback f D) =
      (degree f : ℤ) * WeilDivisor.degree D := by
  classical
  induction D using Finsupp.induction with
  | zero => simp
  | @single_add y n D hy hn ih =>
      simp only [map_add, ih, WeilDivisor.single_eq_zsmul_ofPoint, map_zsmul,
        degree_divisorPullback_ofPoint, WeilDivisor.degree_ofPoint]
      ring

end Compact

end Connected

end TauCeti.RiemannSurface

end
