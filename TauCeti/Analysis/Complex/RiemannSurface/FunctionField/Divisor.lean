/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Order
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Comap
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Basic
public import TauCeti.Analysis.Complex.RiemannSurface.RationalFunction

/-!
# Degree of principal divisors on compact Riemann surfaces

The divisor of a pulled-back meromorphic function is the pullback of its divisor.
In particular, a nonconstant meromorphic function pulls the divisor `[0] - [∞]` of the
sphere coordinate back to its own principal divisor. The fibre-degree theorem then
shows that every principal divisor has degree zero: zeros and poles have the same
total multiplicity. Nonzero constants have zero divisor as well.

Consequently divisor degree is invariant under linear equivalence. This is the
well-definedness input for taking degrees of canonical divisor classes and for
Riemann–Roch on compact Riemann surfaces. No existence theorem for nonconstant
meromorphic functions is needed.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §§16–17 (principal divisors and degree).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Chapter II §4 (degree and
  multiplicities of meromorphic functions).
-/

public noncomputable section

open Function OnePoint Set
open scoped Manifold

namespace TauCeti.RiemannSurface.MeromorphicFunction

open AlgebraicGeometry WeilDivisor

/-- The sphere coordinate has a simple zero at zero. -/
@[simp]
theorem order_coordinate_zero : order ((0 : ℂ) : OnePoint ℂ) coordinate = 1 := by
  have h : coordinate.finitePart = (affineChart : OnePoint ℂ → ℂ) := by
    funext x
    simp [finitePart_def]
  rw [order_apply, h, meromorphicOrderAt_def]
  have hchart : (affineChart : OnePoint ℂ → ℂ) ∘ affineChart.symm = id := by
    funext z
    simp
  rw [chartAt_coe, affineChart_coe, hchart]
  exact _root_.meromorphicOrderAt_id

/-- The sphere coordinate has a simple pole at infinity. -/
@[simp]
theorem order_coordinate_infty : order (∞ : OnePoint ℂ) coordinate = -1 := by
  have h : coordinate.finitePart = (affineChart : OnePoint ℂ → ℂ) := by
    funext x
    simp [finitePart_def]
  rw [order_apply, h, meromorphicOrderAt_def, chartAt_infty,
    affineChart_comp_invChart_symm]
  rw [invChart_infty]
  simpa only [Pi.inv_def, id_eq, _root_.meromorphicOrderAt_id] using
    (_root_.meromorphicOrderAt_inv (f := (id : ℂ → ℂ)) (x := 0))

/-- The coordinate's principal divisor is `[0] - [∞]`. -/
theorem principalDivisor_coordinate (h : coordinate ≠ 0) :
    (orderSystem (OnePoint ℂ)).principalDivisor (Additive.ofMul (Units.mk0 coordinate h)) =
      ofPoint ((0 : ℂ) : OnePoint ℂ) - ofPoint (∞ : OnePoint ℂ) := by
  classical
  apply WeilDivisor.ext
  intro x
  apply WithTop.coe_injective
  rw [coe_coeff_principalDivisor_orderSystem]
  simp only [toMul_ofMul, Units.val_mk0, coeff_sub]
  by_cases hx0 : x = ((0 : ℂ) : OnePoint ℂ)
  · simp [hx0]
  by_cases hxi : x = ∞
  · simp [hxi]
  · have horder : order x coordinate = 0 := order_eq_zero_iff.2 (by simp [hx0, hxi])
    simp [hx0, hxi, coeff_ofPoint_of_ne, horder]

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X] [CompactSpace X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) 1 Y] [ConnectedSpace Y] [CompactSpace Y]

/-- Principal divisors commute with pullback along a finite holomorphic map. -/
theorem principalDivisor_comap (φ : FiniteHolomorphicMap X Y) (u : (MeromorphicFunction Y)ˣ) :
    (orderSystem X).principalDivisor
        (Additive.ofMul (Units.map (comapₐ φ φ.holomorphic φ.nonconstant).toMonoidHom u)) =
      divisorPullback φ ((orderSystem Y).principalDivisor (Additive.ofMul u)) := by
  apply WeilDivisor.ext
  intro x
  apply WithTop.coe_injective
  rw [coe_coeff_principalDivisor_orderSystem, coeff_divisorPullback, WithTop.coe_mul,
    coe_coeff_principalDivisor_orderSystem]
  simpa [order_apply, mul_comm] using
    meromorphicOrderAt_finitePart_comap φ φ.holomorphic φ.nonconstant
      (u : MeromorphicFunction Y) x

variable [T2Space X]

/-- Every principal divisor on a compact connected Riemann surface has degree zero. -/
@[simp]
theorem degree_principalDivisor (u : Additive (MeromorphicFunction X)ˣ) :
    WeilDivisor.degree ((orderSystem X).principalDivisor u) = 0 := by
  classical
  let f : MeromorphicFunction X := (u.toMul : MeromorphicFunction X)
  by_cases hc : f ∈ range (algebraMap ℂ (MeromorphicFunction X))
  · obtain ⟨c, hc⟩ := hc
    have hc0 : c ≠ 0 := by
      intro h
      apply u.toMul.ne_zero
      exact hc.symm.trans (by simp [h])
    have hdiv : (orderSystem X).principalDivisor u = 0 := by
      apply WeilDivisor.ext
      intro x
      apply WithTop.coe_injective
      rw [coe_coeff_principalDivisor_orderSystem]
      exact (congrArg (order x) hc.symm).trans (by simp [hc0])
    simp [hdiv]
  · let φ : FiniteHolomorphicMap X (OnePoint ℂ) :=
      .ofMDifferentiable f.mdifferentiable (f.exists_apply_ne_of_notMem_range_algebraMap hc)
    have hz : coordinate ≠ 0 := by
      intro h
      have := congrArg (fun g : MeromorphicFunction (OnePoint ℂ) ↦ g (1 : ℂ)) h
      simp at this
    have hcomp : Units.map (comapₐ φ φ.holomorphic φ.nonconstant).toMonoidHom
        (Units.mk0 coordinate hz) = u.toMul := by
      apply Units.ext
      apply MeromorphicFunction.ext
      intro x
      simp [φ, f, FiniteHolomorphicMap.coe_ofMDifferentiable]
    have hd := principalDivisor_comap φ (Units.mk0 coordinate hz)
    rw [hcomp, ofMul_toMul, principalDivisor_coordinate hz] at hd
    rw [hd, degree_divisorPullback]
    simp [map_sub, degree_ofPoint]

/-- The order system has degree-zero principal divisors, with unit weight at every point. -/
theorem orderSystem_isWeightedDegreeZero :
    (orderSystem X).IsWeightedDegreeZero (fun _ ↦ 1) := by
  intro u
  simpa only [weightedDegree_one_eq_degree] using degree_principalDivisor u

/-- Linearly equivalent divisors on a compact connected Riemann surface have equal degrees. -/
theorem degree_eq_of_linearlyEquivalent {D E : WeilDivisor X}
    (h : (orderSystem X).LinearlyEquivalent D E) :
    WeilDivisor.degree D = WeilDivisor.degree E := by
  simpa only [weightedDegree_one_eq_degree] using
    (orderSystem X).weightedDegree_eq_of_linearlyEquivalent (fun _ ↦ 1)
      orderSystem_isWeightedDegreeZero h

end TauCeti.RiemannSurface.MeromorphicFunction
