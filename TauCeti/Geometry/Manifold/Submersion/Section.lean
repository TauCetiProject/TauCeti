/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import TauCeti.Geometry.Manifold.Submersion
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Right inverses and local sections of submersions

A `C^n` submersion `f : M → N` reads as a linear projection `u ↦ (L u).1` in suitable charts,
for a continuous linear equivalence `L : E ≃L[𝕜] E'' × F`. Two consequences of this normal form
are recorded here.

* Infinitesimally, for `n ≠ 0` the derivative of `f` at every point has a continuous linear right
  inverse (`Manifold.IsSubmersionAt.hasRightInverse_mfderiv`). This strengthens the surjectivity
  of the derivative, and is what lets a linear object on the tangent space of `N` be lifted to the
  tangent space of `M`.
* Locally, when `M` has no boundary, `f` has a `C^n` section through every point: a map `s`
  defined near `f x` with `s (f x) = x` and `f ∘ s = id` near `f x`
  (`Manifold.IsSubmersionAt.exists_contMDiffOn_rightInvOn`). In normal-form charts it is
  `a ↦ L⁻¹ (a, c)` for the second coordinate `c` of `x`.

Local sections are how data on `M` that is constant along the fibres of `f` is shown to come from
a smooth object on `N`: near `f x` such data is the pullback of its restriction along `s`.

## Main results

* `Manifold.IsSubmersionAtOfComplement.hasRightInverse_mfderiv`,
  `Manifold.IsSubmersionAt.hasRightInverse_mfderiv`,
  `Manifold.IsSubmersion.hasRightInverse_mfderiv`: the derivative of a submersion has a
  continuous linear right inverse.
* `Manifold.IsSubmersionAtOfComplement.exists_contMDiffOn_rightInvOn`,
  `Manifold.IsSubmersionAt.exists_contMDiffOn_rightInvOn`: smooth local sections of a submersion
  of a boundaryless manifold.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Theorem 4.26 (local section theorem).
-/

public section

namespace Manifold

open Function Set Filter
open scoped Manifold Topology ContDiff

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N} {x : M}

namespace IsSubmersionAtOfComplement

variable (h : IsSubmersionAtOfComplement F I J n f x)

include h in
/-- **The derivative of a submersion has a continuous linear right inverse.** In normal-form
charts `φ` and `ψ`, the derivative of `f` followed by the invertible derivative of `ψ` is the
projection `u ↦ (L u).1` precomposed with the invertible derivative of `φ`, and that projection
splits. -/
theorem hasRightInverse_mfderiv (hn : n ≠ 0) : (mfderiv I J f x).HasRightInverse := by
  have hψ : (mfderiv J 𝓘(𝕜, E'') (h.codChart.extend J) (f x)).IsInvertible :=
    isInvertible_mfderiv_extend (IsManifold.maximalAtlas_subset_of_le
      (ENat.one_le_iff_ne_zero_withTop.2 hn) h.codChart_mem_maximalAtlas) h.mem_codChart_source
  have hφ : (mfderiv I 𝓘(𝕜, E) (h.domChart.extend I) x).IsInvertible :=
    isInvertible_mfderiv_extend (IsManifold.maximalAtlas_subset_of_le
      (ENat.one_le_iff_ne_zero_withTop.2 hn) h.domChart_mem_maximalAtlas) h.mem_domChart_source
  -- The projection `u ↦ (L u).1` splits through `a ↦ L⁻¹ (a, 0)`.
  have hπ : h.projection.HasRightInverse :=
    ⟨(h.equiv.symm : E'' × F →L[𝕜] E).comp (ContinuousLinearMap.inl 𝕜 E'' F), fun a ↦ by simp⟩
  -- The derivative of `f` read through `ψ` is `(L ∘ dφ).1`, which has a right inverse `R`.
  obtain ⟨R, hR⟩ : ((mfderiv J 𝓘(𝕜, E'') (h.codChart.extend J) (f x)).comp
      (mfderiv I J f x)).HasRightInverse :=
    (hπ.comp (.of_isInvertible hφ)).congr
      (h.mfderiv_extend_comp_mfderiv hn h.mem_domChart_source)
  -- Since the derivative of `ψ` is injective, `R ∘ dψ` is a right inverse of the derivative of `f`.
  refine ⟨R.comp (mfderiv J 𝓘(𝕜, E'') (h.codChart.extend J) (f x)), fun v ↦ hψ.injective ?_⟩
  have hv := hR (mfderiv J 𝓘(𝕜, E'') (h.codChart.extend J) (f x) v)
  rw [ContinuousLinearMap.comp_apply] at hv
  rwa [ContinuousLinearMap.comp_apply]

include h in
/-- **Smooth local sections of a submersion.** If `f` is a `C^n` submersion at `x` and `M` has no
boundary, there is a map `s : N → M` with `s (f x) = x` which is `C^n` on an open neighbourhood `U`
of `f x` and satisfies `f (s y) = y` for `y ∈ U`. In normal-form charts `φ` and `ψ` it is
`y ↦ φ⁻¹ (L⁻¹ (ψ y, c))`, where `c` is the second coordinate of `L (φ x)`. -/
theorem exists_contMDiffOn_rightInvOn [I.Boundaryless] :
    ∃ U : Set N, ∃ s : N → M, IsOpen U ∧ f x ∈ U ∧ s (f x) = x ∧ ContMDiffOn J I n s U ∧
      RightInvOn s f U := by
  set φ := h.domChart.extend I with hφ
  set ψ := h.codChart.extend J with hψ
  have hφs : φ.source = h.domChart.source := by rw [hφ, OpenPartialHomeomorph.extend_source]
  have hψs : ψ.source = h.codChart.source := by rw [hψ, OpenPartialHomeomorph.extend_source]
  have hx : x ∈ φ.source := hφs ▸ h.mem_domChart_source
  -- The affine slice `a ↦ L⁻¹ (a, c)` through the chart image of `x`.
  set c : F := (h.equiv (φ x)).2
  set g : E'' → E := fun a ↦ h.equiv.symm (a, c)
  have hg : ContDiff 𝕜 n g :=
    h.equiv.symm.contDiff.comp ((contDiff_id).prodMk contDiff_const)
  have hψx : ψ (f x) = (h.equiv (φ x)).1 :=
    (h.codChart_extend_apply h.mem_domChart_source).trans (h.projection_apply _)
  have hgx : g (ψ (f x)) = φ x := by simp [g, c, hψx]
  set U : Set N := ψ.source ∩ ψ ⁻¹' (g ⁻¹' φ.target)
  have hU : IsOpen U :=
    h.codChart.continuousOn_extend.isOpen_inter_preimage (hψs ▸ h.codChart.open_source)
      (h.domChart.isOpen_extend_target.preimage hg.continuous)
  have hfxU : f x ∈ U := ⟨hψs ▸ h.mem_codChart_source, by simpa [hgx] using φ.map_source hx⟩
  refine ⟨U, φ.symm ∘ g ∘ ψ, hU, hfxU, by simp [hgx, φ.left_inv hx], ?_, fun y hy ↦ ?_⟩
  · refine (contMDiffOn_extend_symm h.domChart_mem_maximalAtlas).comp
      (hg.contMDiff.comp_contMDiffOn
        ((h.codChart.contMDiffOn_extend h.codChart_mem_maximalAtlas).mono ?_)) fun y hy ↦ ?_
    · exact hψs ▸ inter_subset_left
    · rw [← OpenPartialHomeomorph.extend_target']
      exact hy.2
  · -- On `U`, `f (s y)` and `y` have the same image under the injective chart `ψ`.
    have hgy : g (ψ y) ∈ φ.target := hy.2
    have hsy : φ.symm (g (ψ y)) ∈ h.domChart.source := hφs ▸ φ.map_target hgy
    have hfsy : f (φ.symm (g (ψ y))) ∈ ψ.source := hψs ▸ h.source_subset_preimage_source hsy
    refine ψ.injOn hfsy hy.1 ?_
    rw [h.codChart_extend_apply hsy, projection_apply, φ.right_inv hgy]
    simp [g]

end IsSubmersionAtOfComplement

/-- **The derivative of a submersion has a continuous linear right inverse.** -/
theorem IsSubmersionAt.hasRightInverse_mfderiv (h : IsSubmersionAt I J n f x) (hn : n ≠ 0) :
    (mfderiv I J f x).HasRightInverse :=
  h.isSubmersionAtOfComplement_complement.hasRightInverse_mfderiv hn

/-- **The derivative of a submersion has a continuous linear right inverse** at every point. -/
theorem IsSubmersion.hasRightInverse_mfderiv (h : IsSubmersion I J n f) (hn : n ≠ 0) (x : M) :
    (mfderiv I J f x).HasRightInverse :=
  (h.isSubmersionAt x).hasRightInverse_mfderiv hn

/-- **Smooth local sections of a submersion.** If `f` is a `C^n` submersion at `x` and `M` has no
boundary, there is a map `s : N → M` with `s (f x) = x` which is `C^n` on an open neighbourhood `U`
of `f x` and satisfies `f (s y) = y` for `y ∈ U`. -/
theorem IsSubmersionAt.exists_contMDiffOn_rightInvOn [I.Boundaryless]
    (h : IsSubmersionAt I J n f x) :
    ∃ U : Set N, ∃ s : N → M, IsOpen U ∧ f x ∈ U ∧ s (f x) = x ∧ ContMDiffOn J I n s U ∧
      RightInvOn s f U :=
  h.isSubmersionAtOfComplement_complement.exists_contMDiffOn_rightInvOn

end Manifold
