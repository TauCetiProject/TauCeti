/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.Normed.Operator.CayleyEquation
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure

/-!
# The source-side Beltrami equation

For an almost complex structure `J` on the real manifold underlying a complex normed
space, `TauCeti.isPseudoholomorphicAt_iff_conjWirtingerDeriv_eq_comp_cayleyCoord`
characterizes pseudoholomorphic maps into a standard complex vector space by the equation
`dbar u = ∂u ∘ cayleyCoord i J`. It uses
`ContinuousLinearMap.complexAntilinearPart_eq_comp_cayleyCoord_iff` and the
Wirtinger decomposition of the real derivative. The basis version tests the equation on
complex coordinate directions.
`Module.Basis.isPseudoholomorphicOn_iff_conjWirtingerDeriv_eq_comp_cayleyCoord` gives the
corresponding first-order system on an open set.

The coordinate problem is the one in S. M. Webster, *A new proof of the
Newlander–Nirenberg theorem*, Math. Z. 201 (1989), 303–316.
-/

public section

open Complex Module
open scoped Manifold

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {u : V → W} {x : V}

/-- At a point where `i + J` is invertible, a map into a complex normed space with
its standard structure is pseudoholomorphic precisely when it is real differentiable
and solves the source-side Beltrami equation. -/
theorem isPseudoholomorphicAt_iff_conjWirtingerDeriv_eq_comp_cayleyCoord
    {J : SmoothAlmostComplexStructure 𝓘(ℝ, V) V}
    (hJ : IsUnit ((SmoothAlmostComplexStructure.ofComplexManifold V V).toEndomorphism x +
      J.toEndomorphism x)) :
    IsPseudoholomorphicAt J (SmoothAlmostComplexStructure.ofComplexManifold W W) u x ↔
      DifferentiableAt ℝ u x ∧
        ∀ v, conjWirtingerDeriv u x v =
          wirtingerDeriv u x (cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I)
            (J.toEndomorphism x) v) := by
  rw [isPseudoholomorphicAt_iff_mfderiv, mdifferentiableAt_iff_differentiableAt]
  refine and_congr_right fun hu ↦ ?_
  rw [(hu.hasFDerivAt.hasMFDerivAt).mfderiv]
  have htarget (v : W) :
      (SmoothAlmostComplexStructure.ofComplexManifold W W).toEndomorphism (u x) v = I • v :=
    SmoothAlmostComplexStructure.ofComplexManifold_apply (u x) v
  -- In the self models the tangent spaces are the model spaces. Read both equations there.
  change (∀ v : V, fderiv ℝ u x (J x v) =
    (SmoothAlmostComplexStructure.ofComplexManifold W W).toEndomorphism (u x) (fderiv ℝ u x v)) ↔ _
  simp only [htarget, conjWirtingerDeriv_eq_complexAntilinearPart,
    wirtingerDeriv_eq_complexLinearPart]
  have hstd : (SmoothAlmostComplexStructure.ofComplexManifold V V).toEndomorphism x =
      (ContinuousLinearMap.lsmul ℝ ℂ I : V →L[ℝ] V) :=
    ContinuousLinearMap.ext fun v ↦
      (SmoothAlmostComplexStructure.ofComplexManifold_apply (E := V) x v).trans
      (ContinuousLinearMap.lsmul_apply (E := V) ℝ ℂ I v).symm
  exact (ContinuousLinearMap.complexAntilinearPart_eq_comp_cayleyCoord_iff
    (L := fderiv ℝ u x) (hstd ▸ hJ)).symm

/-- The source-side Beltrami equation can be tested on the directions of any complex basis.
Both sides of the equation are conjugate-linear in the direction, since the Cayley
coordinate of an almost complex structure anticommutes with multiplication by `i`. -/
theorem _root_.Module.Basis.isPseudoholomorphicAt_iff_conjWirtingerDeriv_eq_comp_cayleyCoord
    {J : SmoothAlmostComplexStructure 𝓘(ℝ, V) V} {ι : Type*} (b : Basis ι ℂ V)
    (hJ : IsUnit ((SmoothAlmostComplexStructure.ofComplexManifold V V).toEndomorphism x +
      J.toEndomorphism x)) :
    IsPseudoholomorphicAt J (SmoothAlmostComplexStructure.ofComplexManifold W W) u x ↔
      DifferentiableAt ℝ u x ∧
        ∀ k, conjWirtingerDeriv u x (b k) =
          wirtingerDeriv u x (cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I)
            (J.toEndomorphism x) (b k)) := by
  rw [TauCeti.isPseudoholomorphicAt_iff_conjWirtingerDeriv_eq_comp_cayleyCoord hJ]
  refine and_congr_right fun _ ↦ ⟨fun h k ↦ h (b k), fun h v ↦ ?_⟩
  let A : V →L[ℝ] V := J.toEndomorphism x
  let C : V →L[ℝ] V := cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I) A
  have hA : A * A = -1 := J.square_neg x
  have hC_apply (w : V) : C.complexAntilinearPart w = C w := by
    exact ContinuousLinearMap.complexAntilinearPart_cayleyCoord_apply hA w
  have hmaps : (conjWirtingerDeriv u x).toLinearMap =
      ((wirtingerDeriv u x).comp C.complexAntilinearPart).toLinearMap := by
    apply b.ext
    intro k
    simpa only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, hC_apply] using h k
  simpa only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, hC_apply] using
    DFunLike.congr_fun hmaps v

/-- On an open set where the Cayley denominator `i + J` is invertible, a map into a
standard complex space is pseudoholomorphic exactly when it is real differentiable
and solves the source-side Beltrami equation in each complex basis direction. -/
theorem _root_.Module.Basis.isPseudoholomorphicOn_iff_conjWirtingerDeriv_eq_comp_cayleyCoord
    {J : SmoothAlmostComplexStructure 𝓘(ℝ, V) V} {ι : Type*} (b : Basis ι ℂ V)
    {s : Set V} (hs : IsOpen s)
    (hJ : ∀ x ∈ s, IsUnit ((SmoothAlmostComplexStructure.ofComplexManifold V V).toEndomorphism x +
      J.toEndomorphism x)) :
    IsPseudoholomorphicOn J (SmoothAlmostComplexStructure.ofComplexManifold W W) u s ↔
      DifferentiableOn ℝ u s ∧
        ∀ x ∈ s, ∀ k, conjWirtingerDeriv u x (b k) =
          wirtingerDeriv u x (cayleyCoord (ContinuousLinearMap.lsmul ℝ ℂ I)
            (J.toEndomorphism x) (b k)) := by
  rw [isPseudoholomorphicOn_iff]
  constructor
  · intro h
    have hp x hx := (b.isPseudoholomorphicAt_iff_conjWirtingerDeriv_eq_comp_cayleyCoord
      (hJ x hx)).1 ((h x hx).isPseudoholomorphicAt_of_mem_nhds (hs.mem_nhds hx))
    exact ⟨fun x hx ↦ (hp x hx).1.differentiableWithinAt, fun x hx ↦ (hp x hx).2⟩
  · rintro ⟨hu, he⟩ x hx
    have hp := (b.isPseudoholomorphicAt_iff_conjWirtingerDeriv_eq_comp_cayleyCoord
      (hJ x hx)).2 ⟨(hu x hx).differentiableAt (hs.mem_nhds hx), he x hx⟩
    exact hp.isPseudoholomorphicWithinAt

end TauCeti
