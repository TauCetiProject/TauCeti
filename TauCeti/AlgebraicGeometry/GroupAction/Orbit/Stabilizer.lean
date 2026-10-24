/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Action
public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Flat
public import TauCeti.AlgebraicGeometry.GroupAction.Stabilizer
public import TauCeti.CategoryTheory.Monoidal.Cartesian.Stabilizer.KernelPair
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyReduced

/-!
# Smooth orbit maps and scheme-theoretic stabilizers

For a reduced finite-type group scheme over an algebraically closed field, the projection
onto an orbit scheme is smooth exactly when its scheme-theoretic stabilizer is smooth.
In characteristic zero an affine acting group has smooth stabilizers by Cartier's theorem,
so its orbit projections are smooth. The target here is the locally closed orbit scheme,
rather than the possibly larger ambient scheme.

The actual relation over the orbit is `G × Stab(x) ≅ G ×_O G`, with maps
`(g,h) ↦ g` and `(g,h) ↦ gh`. It is obtained from `stabilizer.isPullback_rightMul` by
cancelling the orbit immersion. The projection from this product is smooth when the
stabilizer is; smoothness descends along the faithfully flat orbit projection. Conversely,
the stabilizer is the fibre over the base point. All these squares are scheme-theoretic,
so the criterion retains infinitesimal stabilizers in positive characteristic.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f, orbits and homogeneous spaces.
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

namespace TauCeti.SchemeAction

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  (G : Over (Spec (.of k))) {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X]
  [LocallyOfFiniteType G.hom] [CompactSpace G.left]
  [LocallyOfFiniteType X.hom] [CompactSpace X.left]
  (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)

/-- The kernel pair of the orbit projection is right multiplication by the
scheme-theoretic stabilizer, on arbitrary test schemes. -/
theorem isPullback_toOrbit_rightMul :
    IsPullback (fst G (stabilizer G x)).left (stabilizer.rightMul G x).left
      (toOrbit G x) (toOrbit G x) := by
  have h := stabilizer.isPullback_rightMul G x
  have h' := PullbackCone.isLimitOfFactors _ _ (orbitInclusion G x)
    (orbitProjection G x) (orbitProjection G x)
    (orbitProjection_inclusion G x) (orbitProjection_inclusion G x) h.cone h.isLimit
  have hh : IsPullback (fst G (stabilizer G x)) (stabilizer.rightMul G x)
      (orbitProjection G x) (orbitProjection G x) :=
    IsPullback.of_isLimit' ⟨(cancel_mono (orbitInclusion G x)).mp (by
      simpa only [Category.assoc, orbitProjection_inclusion] using h.w)⟩ h'
  simpa only [Over.forget_map, orbitProjection_left] using hh.map (Over.forget _)

/-- The fibre of the orbit projection over its base point is the actual stabilizer. -/
theorem isPullback_toOrbit_stabilizer :
    IsPullback (stabilizer.incl G x).left (stabilizer G x).hom
      (toOrbit G x) (η[G] ≫ orbitProjection G x).left := by
  have h := orbitFiber.isPullback G x x
  have hx : (η[G] ≫ orbitProjection G x) ≫ orbitInclusion G x = x := by
    simp [orbitProjection_inclusion, MonObj.one_eq_one]
  have h' := PullbackCone.isLimitOfFactors _ _ (orbitInclusion G x)
    (orbitProjection G x) (η[G] ≫ orbitProjection G x)
    (orbitProjection_inclusion G x) hx h.cone h.isLimit
  have hh : IsPullback (stabilizer.incl G x) (toUnit (stabilizer G x))
      (orbitProjection G x) (η[G] ≫ orbitProjection G x) :=
    IsPullback.of_isLimit' ⟨(cancel_mono (orbitInclusion G x)).mp (by
      rw [Category.assoc, orbitProjection_inclusion, Category.assoc, hx]
      exact h.w)⟩ h'
  simpa only [Over.forget_map, Over.toUnit_left, orbitProjection_left] using
    hh.map (Over.forget _)

/-- Smoothness of the orbit projection implies smoothness of its scheme-theoretic stabilizer,
in every characteristic. -/
theorem smooth_stabilizer_of_smooth_toOrbit (h : Smooth (toOrbit G x)) :
    Smooth (stabilizer G x).hom :=
  MorphismProperty.of_isPullback (isPullback_toOrbit_stabilizer G x) h

/-- For a reduced group, the orbit projection is smooth exactly when its stabilizer is.
The stabilizer need not be reduced a priori. -/
theorem smooth_toOrbit_iff [IsReduced G.left] :
    Smooth (toOrbit G x) ↔ Smooth (stabilizer G x).hom := by
  refine ⟨smooth_stabilizer_of_smooth_toOrbit G x, fun hs ↦ ?_⟩
  let := hs
  have hp : Smooth (fst G (stabilizer G x)).left := by
    rw [Over.fst_left]
    infer_instance
  have hf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme)
      (toOrbit G x) := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (isPullback_toOrbit_rightMul G x) hf hp

/-- Orbit projections for affine finite-type groups in characteristic zero are smooth.
No connectedness or reducedness hypothesis on the acting group is needed. -/
instance smooth_toOrbit_of_charZero [CharZero k] [IsAffine G.left] :
    Smooth (toOrbit G x) := by
  have : Smooth G.hom := TauCeti.AlgebraicGeometry.smooth_of_grpObj_of_charZero G
  have : IsReduced G.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian G.hom
  exact (smooth_toOrbit_iff G x).mpr (smooth_stabilizer G x)

end TauCeti.SchemeAction
