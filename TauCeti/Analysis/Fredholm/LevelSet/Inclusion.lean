/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import TauCeti.Analysis.Fredholm.LevelSet.Manifold

import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# The inclusion of a regular level set

Let `f : E → F` be a map between Banach spaces which, along the level set `{x | f x = c}`, is
strictly differentiable with surjective Fredholm derivative `D x` of constant index `n`.
`TauCeti.levelSetChartedSpace` makes the level set a charted space modelled on `Fin n → 𝕜`, and
`TauCeti.isManifold_levelSet` makes it a `C^m` manifold when `f` is `C^m` along the level set.

This file proves that the inclusion of the level set into `E` is a `C^m` map for that atlas, and
computes its differential: at `z` it is the inclusion of `ker (D z)`, read in the model space
through `ContinuousLinearMap.kerModelEquiv`. In particular the inclusion is an immersion, and
its tangent space at `z` is `ker (D z)`. These are the facts needed to restrict functions on `E`
to the level set and to compare their differentials, for instance to pull back a function along
the inclusion and compute its critical points.

The proofs follow those of `TauCeti.contMDiffOn_coe_sectionZeroChartAt_symm` and
`TauCeti.hasMFDerivAt_coe_sectionZero` for zero sets of bundle sections, in the simpler setting of
a map defined on a Banach space.

## Main results

* `TauCeti.contMDiff_coe_levelSet`: the inclusion of a regular level set is `C^m`.
* `TauCeti.hasMFDerivAt_coe_levelSet`: its differential at `z` is the inclusion of `ker (D z)`.
* `TauCeti.injective_mfderiv_coe_levelSet` and `TauCeti.range_mfderiv_coe_levelSet`: the
  differential is injective, with range `ker (D z)`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Corollary 5.14 and
  Proposition 5.38, for regular level sets and their tangent spaces.
-/

public section

namespace TauCeti

open Set
open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {f : E → F} {c : F} {D : E → E →L[𝕜] F} {n : ℕ} {m : ℕ∞ω}
  (hf : ∀ x ∈ {x | f x = c}, HasStrictFDerivAt f (D x) x)
  (hFred : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.IsFredholm (D x))
  (hsurj : ∀ x ∈ {x | f x = c}, Function.Surjective (D x))
  (hindex : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.index (D x) = n)

/-- **The inclusion of a regular level set is smooth.** For the atlas
`TauCeti.levelSetChartedSpace`, the inclusion of the level set `{x | f x = c}` into `E` is as
smooth as `f` is along the level set. -/
theorem contMDiff_coe_levelSet (hsmooth : ∀ x ∈ {x | f x = c}, ContDiffAt 𝕜 m f x) :
    letI := levelSetChartedSpace hf hFred hsurj hindex
    ContMDiff 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, E) m (Subtype.val : ↥{x | f x = c} → E) := by
  let _ := levelSetChartedSpace hf hFred hsurj hindex
  have := isManifold_levelSet hf hFred hsurj hindex hsmooth
  intro z
  set χ := levelSetChartAt hf hFred hsurj hindex z
  have hχ : chartAt (Fin n → 𝕜) z = χ := levelSetChartedSpace_chartAt hf hFred hsurj hindex z
  -- Write the inclusion on the chart source as the inverse chart composed with the chart.
  have hsymm : ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, E) m
      (fun k ↦ ((χ.symm k : ↥{x | f x = c}) : E)) χ.target :=
    ContDiffOn.contMDiffOn (contDiffOn_coe_levelSetChartAt_symm hf hFred hsurj hindex hsmooth z)
  have hchart : ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, Fin n → 𝕜) m χ χ.source :=
    hχ ▸ contMDiffOn_chart
  have hval : ContMDiffOn 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, E) m
      (Subtype.val : ↥{x | f x = c} → E) χ.source :=
    ContMDiffOn.congr (hsymm.comp hchart fun _ hw ↦ χ.map_source hw) fun w hw ↦ by
      rw [Function.comp_apply, χ.left_inv hw]
  exact hval.contMDiffAt
    (χ.open_source.mem_nhds (mem_levelSetChartAt_source hf hFred hsurj hindex z))

/-- **The differential of the inclusion of a regular level set.** For the atlas
`TauCeti.levelSetChartedSpace`, the differential at `z` of the inclusion of the level set into
`E` is the inclusion of `ker (D z)`, read in the model space through
`ContinuousLinearMap.kerModelEquiv`. -/
theorem hasMFDerivAt_coe_levelSet (z : ↥{x | f x = c}) :
    letI := levelSetChartedSpace hf hFred hsurj hindex
    HasMFDerivAt 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, E) (Subtype.val : ↥{x | f x = c} → E) z
      ((D z.1).ker.subtypeL.comp
        (((D z.1).kerModelEquiv (hFred z.1 z.2).finite_ker
          ((ContinuousLinearMap.finrank_ker_eq_iff_index_eq (D z.1) (hsurj z.1 z.2)).2
            (hindex z.1 z.2))).symm : (Fin n → 𝕜) →L[𝕜] (D z.1).ker)) := by
  let _ := levelSetChartedSpace hf hFred hsurj hindex
  set K := (D z.1).kerModelEquiv (hFred z.1 z.2).finite_ker
    ((ContinuousLinearMap.finrank_ker_eq_iff_index_eq (D z.1) (hsurj z.1 z.2)).2
      (hindex z.1 z.2))
  set ψ := levelSetChart (hf z.1 z.2) (LinearMap.range_eq_top.2 (hsurj z.1 z.2))
    (hFred z.1 z.2).closedComplemented_ker z.2
  have hderiv : HasFDerivAt (fun k ↦ ((ψ.symm k : ↥{x | f x = c}) : E))
      (D z.1).ker.subtypeL (K.symm 0) := by
    simpa only [map_zero] using
      (hasStrictFDerivAt_coe_levelSetChart_symm (hf z.1 z.2) _ _ z.2).hasFDerivAt
  have hcoord : HasFDerivAt
      (fun k ↦ (((levelSetChartAt hf hFred hsurj hindex z).symm k : ↥{x | f x = c}) : E))
      ((D z.1).ker.subtypeL.comp (K.symm : (Fin n → 𝕜) →L[𝕜] (D z.1).ker)) 0 := by
    refine (hderiv.comp 0 K.symm.hasFDerivAt).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun k ↦ ?_)
    dsimp only [Function.comp_apply]
    rw [levelSetChartAt_symm_apply]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  -- The source chart is the preferred chart at `z`, the target chart is the identity of `E`,
  -- and both models are boundaryless, so the coordinate expression is the one in `hcoord`.
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, levelSetChartedSpace_chartAt, levelSetChartAt_apply_self,
    chartAt_self_eq, OpenPartialHomeomorph.refl_apply, Function.comp_def, Set.range_id, id_eq]
  exact hcoord.hasFDerivWithinAt

/-- The differential of the inclusion of a regular level set is injective: the inclusion is an
immersion. -/
theorem injective_mfderiv_coe_levelSet (z : ↥{x | f x = c}) :
    letI := levelSetChartedSpace hf hFred hsurj hindex
    Function.Injective
      (mfderiv 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, E) (Subtype.val : ↥{x | f x = c} → E) z) := by
  let _ := levelSetChartedSpace hf hFred hsurj hindex
  rw [(hasMFDerivAt_coe_levelSet hf hFred hsurj hindex z).mfderiv]
  exact Subtype.val_injective.comp (ContinuousLinearEquiv.injective _ :
    Function.Injective ((D z.1).kerModelEquiv (hFred z.1 z.2).finite_ker
      ((ContinuousLinearMap.finrank_ker_eq_iff_index_eq (D z.1) (hsurj z.1 z.2)).2
        (hindex z.1 z.2))).symm)

/-- **The tangent space of a regular level set is the kernel of the derivative.** The range of
the differential at `z` of the inclusion of a regular level set is `ker (D z)`. -/
theorem range_mfderiv_coe_levelSet (z : ↥{x | f x = c}) :
    letI := levelSetChartedSpace hf hFred hsurj hindex
    (mfderiv 𝓘(𝕜, Fin n → 𝕜) 𝓘(𝕜, E) (Subtype.val : ↥{x | f x = c} → E) z).range =
      (D z.1).ker := by
  let _ := levelSetChartedSpace hf hFred hsurj hindex
  set K := (D z.1).kerModelEquiv (hFred z.1 z.2).finite_ker
    ((ContinuousLinearMap.finrank_ker_eq_iff_index_eq (D z.1) (hsurj z.1 z.2)).2
      (hindex z.1 z.2))
  rw [(hasMFDerivAt_coe_levelSet hf hFred hsurj hindex z).mfderiv]
  ext v
  simp only [LinearMap.mem_range]
  -- The composite applied to `w` is, by definition of `ContinuousLinearMap.comp` and of the
  -- subtype inclusion, the underlying vector of `K.symm w`.
  constructor
  · rintro ⟨w, rfl⟩
    exact (K.symm w).2
  · intro hv
    exact ⟨K ⟨v, hv⟩, congrArg Subtype.val (K.symm_apply_apply ⟨v, hv⟩)⟩

end TauCeti
