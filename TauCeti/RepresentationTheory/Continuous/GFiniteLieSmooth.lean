/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector
public import TauCeti.RepresentationTheory.GFinite

import TauCeti.Geometry.Lie.Representation
import TauCeti.RepresentationTheory.Continuous.StronglyContinuous

/-!
# `G`-finite vectors are smooth

Let `π` be a strongly continuous representation of a finite-dimensional real Lie group `G` on a
normed space `V` over `ℝ` or `ℂ` (more generally over a normed field `𝕜` finite-dimensional over
`ℝ`). Every `G`-finite vector `v` of `π` is a smooth vector: the span `W` of its orbit is a
finite-dimensional invariant subspace, on which strong continuity is continuity in the operator
norm, so the restriction of `π` to `W` is a continuous finite-dimensional representation. That
restriction is smooth by automatic smoothness (`ContRepresentation.contMDiff_apply`), and the
orbit map of `v` is its orbit map read in `V`.

No compactness of `G` and no completeness of `V` is needed. For a compact Lie group `K` this is
the statement that `K`-finite vectors are smooth.

## Main results

* `Representation.IsGFinite.isLieSmoothVector`: a `G`-finite vector of a strongly continuous
  representation of a Lie group is smooth.
* `ContRepresentation.gFiniteSubmodule_le_lieSmoothVectors`: the `G`-finite vectors form a
  submodule of the smooth vectors.

## References

* Bernstein, Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, §2.
-/

public section

noncomputable section

open scoped ContDiff Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [FiniteDimensional ℝ 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]
  {π : ContRepresentation 𝕜 G V}

/-- **`G`-finite vectors are smooth.** Every `G`-finite vector of a strongly continuous
representation of a finite-dimensional real Lie group is a smooth vector. -/
theorem Representation.IsGFinite.isLieSmoothVector (hπ : ∀ v, Continuous fun g ↦ π g v) {v : V}
    (hv : π.toRepresentation.IsGFinite v) : π.IsLieSmoothVector I v := by
  let W : Submodule 𝕜 V := Submodule.span 𝕜 (Set.range fun g : G ↦ π g v)
  have : FiniteDimensional 𝕜 W := (π.toRepresentation.isGFinite_iff v).1 hv
  have hW : ∀ g, ∀ w ∈ W, π g w ∈ W := fun g _ hw ↦
    π.toRepresentation.apply_mem_span_range_apply v g hw
  let σ := π.subrepresentation W hW
  have hσ : Continuous σ := continuous_clm_apply.2 fun w ↦
    ContRepresentation.continuous_subrepresentation_apply hπ w
  let w₀ : W := ⟨v, Submodule.subset_span ⟨1, by simp⟩⟩
  have h : ContMDiff I 𝓘(ℝ, W) ∞ fun g ↦ σ g w₀ :=
    (σ.contMDiff_apply hσ).comp (contMDiff_id.prodMk contMDiff_const)
  have hfun : (fun g ↦ π g v) = (W.subtypeL.restrictScalars ℝ) ∘ fun g ↦ σ g w₀ := by
    funext g
    simp [σ, w₀]
  rw [π.isLieSmoothVector_iff I, hfun]
  exact (W.subtypeL.restrictScalars ℝ).contMDiff.comp h

/-- The `G`-finite vectors of a strongly continuous representation of a finite-dimensional real
Lie group are smooth vectors. -/
theorem ContRepresentation.gFiniteSubmodule_le_lieSmoothVectors
    (hπ : ∀ v, Continuous fun g ↦ π g v) :
    π.toRepresentation.gFiniteSubmodule ≤ π.lieSmoothVectors I := fun _ hv ↦
  (π.mem_lieSmoothVectors I).2
    ((π.toRepresentation.mem_gFiniteSubmodule.1 hv).isLieSmoothVector I hπ)
