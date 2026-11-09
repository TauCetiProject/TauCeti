/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Adjoint
public import TauCeti.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Smooth horizontal and vertical projections

The orthogonal horizontal and vertical projections of a Riemannian submersion are regular
sections of the endomorphism bundle of its source tangent bundle. In particular, they send
regular vector fields to regular vector fields, by `ContMDiff.clm_bundle_apply`. This allows
covariant differentiation of the horizontal and vertical parts of a field, as needed in the
fundamental equations of a submersion.

The projections are the native `Submodule.starProjection` maps for the kernel of the
differential and its orthogonal complement, with the given Riemannian metric. There is no
auxiliary choice of splitting. Horizontal projection is computed by differentiating and then
horizontally lifting; vertical projection is its complement. The regularity proof uses
`ContMDiffAt.mfderiv_adjoint_apply`, so it takes account of both varying metrics.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, §1.
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 2.
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsManifold I 1 M] [IsManifold J 1 N]
  {n : ℕ∞ω} [IsManifold I (n + 1) M]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J n F (fun y : N ↦ TangentSpace J y)]
  {f : M → N} (h : IsRiemannianSubmersion I J f)

include h

/-- The horizontal orthogonal projections of a smooth Riemannian submersion form a `C^n`
endomorphism field when both metrics are `C^n`, for `n ≤ ∞`. -/
theorem contMDiff_starProjection_orthogonal_ker (hn : n + 1 ≤ ∞) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        x (mfderiv I J f x).kerᗮ.starProjection) := by
  -- At arbitrary n, this is a lemma, not a registered instance; it uses IsManifold I (n + 1) M.
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  intro a
  let e := trivializationAt E (TangentSpace I) a
  have hs := Manifold.contMDiffOn_hom_of_localFrame (I := I) (n := n) (e := e) (e' := e)
    (Module.finBasis ℝ E) (f := id) contMDiffOn_id
    (fun _ hx ↦ ⟨hx, hx⟩)
    (u := e.baseSet) (A := fun x ↦ (mfderiv I J f x).kerᗮ.starProjection) (by
      intro j x hx
      have hX := (e.contMDiffOn_localFrame_baseSet (I := I) n
        (Module.finBasis ℝ E) j).contMDiffAt
        (e.open_baseSet.mem_nhds hx)
      have hf := ((h.isSubmersion.contMDiff.of_le hn) x)
      have hdf : ContMDiffAt I (J.prod 𝓘(ℝ, F)) n
          (fun y ↦ TotalSpace.mk' F (f y)
            (mfderiv I J f y (e.localFrame (Module.finBasis ℝ E) j y))) x := by
        -- Express the tangent-map composition as the bundled differential applied to the frame.
        simpa only [Function.comp_def, tangentMap] using
          (hf.contMDiffAt_tangentMap le_rfl).comp x hX
      have hlift := hf.mfderiv_adjoint_apply
        (W := fun y ↦ mfderiv I J f y (e.localFrame (Module.finBasis ℝ E) j y)) hdf
      simpa only [Function.id_def, ← h.horizontalLift_apply, h.horizontalLift_mfderiv]
        using hlift.contMDiffWithinAt)
  exact hs.contMDiffAt (e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) a))

/-- The vertical orthogonal projections of a smooth Riemannian submersion form a `C^n`
endomorphism field when both metrics are `C^n`, for `n ≤ ∞`. -/
theorem contMDiff_starProjection_ker (hn : n + 1 ≤ ∞) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        x (mfderiv I J f x).ker.starProjection) := by
  -- Supply the arbitrary-order tangent-bundle instance from IsManifold I (n + 1) M, as above.
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  have hid : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        x (ContinuousLinearMap.id ℝ (TangentSpace I x))) :=
    (TauCeti.contMDiff_hom_bundle_iff _).mpr contMDiff_id
  refine (hid.sub_section (h.contMDiff_starProjection_orthogonal_ker hn)).congr fun x ↦ ?_
  simp only [Pi.sub_apply, Submodule.starProjection_orthogonal]
  congr 1
  abel

end TauCeti.IsRiemannianSubmersion
