/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded

import TauCeti.Analysis.Complex.Conformal.UpperHalfPlane.LocallyConnectedBoundary
import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected

/-!
# Riemann maps of unbounded domains with locally connected inverted boundary

An unbounded domain with several accesses to infinity need not have Jordan frontier on the Riemann
sphere.  Inversion about an exterior point can nevertheless turn it into a bounded simply connected
domain with locally connected frontier.  Carathéodory's continuity theorem then gives a continuous
upper-half-plane map to the inverted domain.  Inverting its interior values back produces a
holomorphic bijection onto the original domain; the continuous inverted coordinate records all
finite boundary values and all accesses to infinity at once.

This is the form of boundary extension used for polygonal domains with several unbounded ends.
Unlike the Jordan-domain result, it does not assert continuity of the original map at boundary
parameters sent to infinity.

## Main statement

* `TauCeti.exists_bijOn_upperHalfPlaneSet_of_locallyConnectedSpace_frontier_image_inv_sub` -- an
  upper-half-plane Riemann map of an unbounded domain, together with its continuous inverted
  coordinate on the closed half-plane.

## References

* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer, 1992, Ch. 2.
-/

public section

open Bornology Complex Filter Function Metric Set Topology UpperHalfPlane

namespace TauCeti

/-- **A Riemann map of an unbounded domain in a continuous inverted coordinate.** Let `U` be an
unbounded simply connected open subset of `ℂ`, and let `q ∉ closure U`. If inversion about `q`
gives a domain with locally connected frontier, then there is a holomorphic bijection `f` from the
upper half-plane onto `U` whose inverted coordinate `g = (f - q)⁻¹` extends continuously to the
closed upper half-plane.

The real boundary values of `g` lie on the inverted frontier and, together with its limit `0` at
infinity, cover that frontier. The function `g` can vanish at several real parameters, recording
multiple accesses of `U` to infinity, so no continuity claim for `f` is made there. -/
theorem exists_bijOn_upperHalfPlaneSet_of_locallyConnectedSpace_frontier_image_inv_sub
    {U : Set ℂ} {q : ℂ} (hUo : IsOpen U) (hUs : IsSimplyConnected U)
    (hq : q ∉ closure U) (hUb : ¬IsBounded U)
    [LocallyConnectedSpace
      (frontier ((fun z : ℂ => (z - q)⁻¹) '' U))] :
    ∃ f g : ℂ → ℂ, DifferentiableOn ℂ f upperHalfPlaneSet ∧ BijOn f upperHalfPlaneSet U ∧
      ContinuousOn g {z | 0 ≤ z.im} ∧ DifferentiableOn ℂ g upperHalfPlaneSet ∧
      EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet ∧
      (∀ z ∈ upperHalfPlaneSet, g z ≠ 0) ∧
      insert 0 (g '' {z | 0 ≤ z.im}) =
        closure ((fun z : ℂ => (z - q)⁻¹) '' U) ∧
      insert 0 (g '' {z | z.im = 0}) =
        frontier ((fun z : ℂ => (z - q)⁻¹) '' U) ∧
      Tendsto g (cobounded ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (𝓝 0) := by
  have hqU : q ∉ U := fun h => hq (subset_closure h)
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => (z - q)⁻¹) U :=
    (differentiableOn_id.sub_const q).inv fun z hz => sub_ne_zero.mpr fun h => hqU (h ▸ hz)
  have hinj : InjOn (fun z : ℂ => (z - q)⁻¹) U :=
    (inv_injective.comp (sub_left_injective (b := q))).injOn
  have hVo : IsOpen ((fun z : ℂ => (z - q)⁻¹) '' U) := isOpen_image_inv_sub hUo hqU
  have hVs : IsSimplyConnected ((fun z : ℂ => (z - q)⁻¹) '' U) :=
    isSimplyConnected_image_of_differentiableOn_of_injOn hUo hUs hdiff hinj
  have hV0 : (0 : ℂ) ∈ frontier ((fun z : ℂ => (z - q)⁻¹) '' U) := by
    rw [frontier_image_inv_sub hUo hq hUb]
    exact mem_insert _ _
  obtain ⟨g, hgc, hgd, hgV, hgK, hgR, hg0⟩ :=
    exists_continuousOn_bijOn_upperHalfPlaneSet_of_locallyConnectedSpace_frontier hVo hVs
      (isBounded_image_inv_sub hq) hV0
  have hzero : (0 : ℂ) ∉ (fun z : ℂ => (z - q)⁻¹) '' U := by
    rintro ⟨z, hz, hzinv⟩
    exact hqU ((sub_eq_zero.mp (inv_eq_zero.mp hzinv)) ▸ hz)
  have hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0 := fun z hz hgz =>
    hzero (hgz ▸ hgV.mapsTo hz)
  have hκ : BijOn (fun w : ℂ => q + w⁻¹) ((fun z : ℂ => (z - q)⁻¹) '' U) U := by
    refine ⟨?_, ((add_right_injective q).comp inv_injective).injOn,
      fun z hz => ⟨_, ⟨z, hz, rfl⟩, by simp⟩⟩
    rintro _ ⟨z, hz, rfl⟩
    simpa using hz
  refine ⟨fun z => q + (g z)⁻¹, g,
    (differentiableOn_const q).add (hgd.inv hgne), hκ.comp hgV, hgc, hgd, ?_, hgne,
    hgK, hgR, hg0⟩
  intro z hz
  simp only [add_sub_cancel_left]
  simp

end TauCeti
