/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import TauCeti.Topology.Compactification.OnePoint.Map
public import TauCeti.Topology.JordanCurve.Basic

/-!
# The one-point compactification of the real line as a Jordan curve

The real projective line, topologically the one-point compactification `OnePoint ℝ`, is a
circle.  This file records the resulting homeomorphism and the corresponding Jordan-curve fact.
They let maps on the extended real boundary be treated using the Jordan-curve API. In particular,
a proper injective parametrization by the real line extends to a continuous injection of
`OnePoint ℝ`, so its image together with infinity is a Jordan curve in the one-point
compactification of the ambient space.

The construction uses Mathlib's stereographic homeomorphism from the one-point compactification
of a finite-dimensional real vector space to a sphere.  The standard orthonormal basis
`![1, Complex.I]` then identifies the resulting two-dimensional Euclidean sphere with
`Circle`.

## Main definitions

* `TauCeti.onePointRealHomeomorphCircle` -- a homeomorphism from `OnePoint ℝ` to `Circle`.

## Main results

* `TauCeti.isJordanCurve_univ_onePoint_real` -- the whole real projective line is a Jordan curve.
* `TauCeti.isJordanCurve_insert_infty_range_of_isProperMap` -- a proper simple real curve
  becomes a Jordan curve after adding the point at infinity.
-/

public section

noncomputable section

open Metric Set

namespace TauCeti

/-- The one-point compactification of the real line is homeomorphic to the circle.

Mathlib's `onePointEquivSphereOfFinrankEq` realizes it as the unit sphere in two-dimensional
Euclidean space.  The standard orthonormal basis of `ℂ` carries that sphere isometrically onto
the unit sphere in `ℂ`, which is definitionally `Circle`. -/
noncomputable def onePointRealHomeomorphCircle : OnePoint ℝ ≃ₜ Circle := by
  let eL : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ :=
    Complex.orthonormalBasisOneI.repr.symm
  let e : EuclideanSpace ℝ (Fin 2) ≃ₜ ℂ := eL.toHomeomorph
  let es : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ sphere (0 : ℂ) 1 :=
    e.subtype fun x => by
      simp only [mem_sphere_zero_iff_norm, e]
      rw [LinearIsometryEquiv.coe_toHomeomorph, eL.norm_map]
  exact ((onePointEquivSphereOfFinrankEq (V := ℝ) (by norm_num)).trans es).trans
    (Homeomorph.refl _)

/-- The whole one-point compactification of the real line is a Jordan curve. -/
theorem isJordanCurve_univ_onePoint_real :
    IsJordanCurve (Set.univ : Set (OnePoint ℝ)) :=
  isJordanCurve_iff.mpr
    ⟨(Homeomorph.Set.univ (OnePoint ℝ)).trans onePointRealHomeomorphCircle⟩

/-- A proper injective parametrization by the real line becomes a Jordan curve in the one-point
compactification of its ambient space. Both ends of the curve meet at infinity, and properness
ensures continuity there. -/
theorem isJordanCurve_insert_infty_range_of_isProperMap
    {X : Type*} [TopologicalSpace X]
    {f : ℝ → X} (hf : IsProperMap f) (hinj : Function.Injective f) :
    IsJordanCurve (insert OnePoint.infty (((↑) : X → OnePoint X) '' range f)) := by
  rw [← range_onePointMap f, ← image_univ]
  have h := isClosedEmbedding_onePointMap
    (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      hf.continuous hinj hf.isClosedMap)
  obtain ⟨e⟩ := isJordanCurve_iff.mp isJordanCurve_univ_onePoint_real
  exact isJordanCurve_iff.mpr
    ⟨(h.isEmbedding.homeomorphImage Set.univ).symm.trans e⟩

end TauCeti
