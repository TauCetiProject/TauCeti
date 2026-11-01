/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Complete

/-!
# Naturality of maximal flows under related maps

A differentiable map `f` relating vector fields `X` and `Y` sends each integral curve of `X`
to one of `Y`. Consequently the maximal interval through `x` is contained in the maximal
interval through `f x`. If `Y` has unique integral curves, the maximal flows intertwine
on the source flow domain. Surjectivity of `f` therefore lets completeness descend from
`X` to `Y`, without requiring an inverse or a submersion hypothesis.

Unlike the diffeomorphism case, the flow identity is only asserted on the source domain:
a related map can collapse an escaping trajectory to a stationary point, so the target
flow may exist longer. Outside the source domain its junk value need not intertwine.

The proofs use `IsMIntegralCurveOn.map_of_mfderiv_eq` and the witness and uniqueness
characterizations of `maximalIntegralCurve`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 9,
  Proposition 9.6 (naturality of integral curves).
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace MDifferentiable

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {f : M → M'} {X : (x : M) → TangentSpace I x} {Y : (y : M') → TangentSpace I' y}

/-- A differentiable map relating two vector fields can only enlarge the maximal interval
of existence. No uniqueness or regularity assumption on either field is needed. -/
theorem maximalIntegralCurveInterval_subset (hf : MDifferentiable I I' f)
    (hXY : ∀ x, mfderiv I I' f x (X x) = Y (f x)) (x : M) :
    maximalIntegralCurveInterval X x ⊆ maximalIntegralCurveInterval Y (f x) := by
  intro t ht
  obtain ⟨γ, a, b, hγ, hγ0, h0, hta, -⟩ :=
    exists_isMIntegralCurveOn_maximalIntegralCurve_eq ht
  exact (hγ.map_of_mfderiv_eq (fun s _ ↦ hf (γ s)) (fun s _ ↦ hXY (γ s))
    ).subset_maximalIntegralCurveInterval h0 (by rw [comp_apply, hγ0]) hta

/-- Completeness descends through any surjective differentiable map relating the fields.
The map need not be injective, proper, or a submersion. -/
theorem isCompleteVectorField_of_surjective (hf : MDifferentiable I I' f)
    (hsurj : Surjective f) (hXY : ∀ x, mfderiv I I' f x (X x) = Y (f x))
    (hX : IsCompleteVectorField X) : IsCompleteVectorField Y := by
  rw [isCompleteVectorField_iff_maximalIntegralCurveInterval]
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  apply Set.eq_univ_of_univ_subset
  rw [← hX.maximalIntegralCurveInterval_eq_univ x]
  exact hf.maximalIntegralCurveInterval_subset hXY x

variable [T2Space M'] [IsManifold I' 1 M'] [BoundarylessManifold I' M']

/-- A differentiable map relating `X` to a `C¹` field `Y` intertwines their maximal flows
at every time in the source flow domain. No smoothness of `X` is required. -/
theorem apply_flowOf (hf : MDifferentiable I I' f)
    (hY : CMDiff 1 (fun y ↦ (⟨y, Y y⟩ : TangentBundle I' M')))
    (hXY : ∀ x, mfderiv I I' f x (X x) = Y (f x)) {t : ℝ} {x : M}
    (ht : (t, x) ∈ flowDomain X) :
    f (flowOf X t x) = flowOf Y t (f x) := by
  rw [TauCeti.flowOf_apply, TauCeti.flowOf_apply]
  obtain ⟨γ, a, b, hγ, hγ0, h0, hta, heq⟩ :=
    exists_isMIntegralCurveOn_maximalIntegralCurve_eq (mem_flowDomain.mp ht)
  have hfγ := hγ.map_of_mfderiv_eq (fun s _ ↦ hf (γ s)) (fun s _ ↦ hXY (γ s))
  rw [heq]
  exact ((hfγ.eqOn_maximalIntegralCurve hY h0 (by rw [comp_apply, hγ0])) hta).symm

end MDifferentiable
