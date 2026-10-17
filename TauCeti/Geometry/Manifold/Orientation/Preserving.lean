/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Orientation behavior of manifold maps

This file records the pointwise interface for a map to preserve or reverse manifold orientations.
The differential is required to be represented by a continuous linear equivalence, and its induced
orientation must agree with the target orientation (or its opposite). These predicates are the local
input for pullback orientations and orientation-sensitive integration.
-/

public section

noncomputable section

open scoped Manifold Topology

namespace TauCeti.Manifold.Orientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M'] [FiniteDimensional ℝ E']
  {ι : Type*} [Fintype ι]

/-- A map preserves orientations at `x` when its manifold derivative is an equivalence that maps
`o`'s tangent orientation at `x` to `o'`'s tangent orientation at `f x`. -/
def IsOrientationPreservingAt [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) : Prop :=
  ∃ e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x),
    (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x ∧
      _root_.Orientation.map ι e.toLinearEquiv (o.orientationAt x) = o'.orientationAt (f x)

/-- A map reverses orientations at `x` when its manifold derivative is an equivalence that maps
`o`'s tangent orientation at `x` to the opposite of `o'`'s tangent orientation at `f x`. -/
def IsOrientationReversingAt [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) : Prop :=
  ∃ e : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x),
    (e : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x ∧
      _root_.Orientation.map ι e.toLinearEquiv (o.orientationAt x) = -(o'.orientationAt (f x))

/-- A map cannot preserve and reverse the same pair of orientations at one point. -/
theorem not_isOrientationPreservingAt_and_isOrientationReversingAt
    [IsManifold I 1 M] [IsManifold I' 1 M']
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation I' M' ι)
    (f : M → M') (x : M) :
    ¬(IsOrientationPreservingAt o o' f x ∧ IsOrientationReversingAt o o' f x) := by
  rintro ⟨⟨e, he, hpres⟩, ⟨e', he', hrev⟩⟩
  have heq : e = e' := by
    ext v
    exact congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I' (f x) => L v)
      (he.trans he'.symm)
  subst e'
  have h : o'.orientationAt (f x) = -(o'.orientationAt (f x)) := hpres.symm.trans hrev
  exact (Module.Ray.ne_neg_self _ h)

/-- The identity map preserves every manifold orientation. -/
theorem isOrientationPreservingAt_id [IsManifold I 1 M]
    (o : Manifold.Orientation I M ι) (x : M) :
    IsOrientationPreservingAt (I := I) (I' := I) (M' := M) o o id x := by
  refine ⟨ContinuousLinearEquiv.refl ℝ _, ?_, ?_⟩
  · rw [ContinuousLinearEquiv.coe_refl, mfderiv_id]
  · change _root_.Orientation.map ι (LinearEquiv.refl ℝ (TangentSpace I x))
      (o.orientationAt x) = o.orientationAt x
    rw [_root_.Orientation.map_refl]
    rfl

/-- The identity map reverses an orientation when its target is given the opposite orientation. -/
theorem isOrientationReversingAt_id_neg [IsManifold I 1 M]
    (o : Manifold.Orientation I M ι) (x : M) :
    IsOrientationReversingAt (I := I) (I' := I) (M' := M) o (-o) id x := by
  refine ⟨ContinuousLinearEquiv.refl ℝ _, ?_, ?_⟩
  · rw [ContinuousLinearEquiv.coe_refl, mfderiv_id]
  · change _root_.Orientation.map ι (LinearEquiv.refl ℝ (TangentSpace I x))
      (o.orientationAt x) = -(-o).orientationAt x
    rw [_root_.Orientation.map_refl]
    simp only [Equiv.refl_apply]
    rw [orientationAt_neg]
    exact (InvolutiveNeg.neg_neg (o.orientationAt x)).symm

end TauCeti.Manifold.Orientation
