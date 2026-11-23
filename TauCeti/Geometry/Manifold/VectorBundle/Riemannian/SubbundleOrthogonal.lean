/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Frame.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
import TauCeti.Analysis.InnerProductSpace.RangeProjection
import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Synthesis

/-!
# Orthogonal complements of smooth subbundles

Let `V` be a finite-rank `C^n` vector bundle with a `C^n` Riemannian metric, and let `W x` be
subspaces of its fibres spanned near every point by `k` sections of class `C^n` forming a basis at
each point: a `C^n` subbundle of rank `k` in the sense of the local frame criterion
`TauCeti.HasLocalContMDiffSubbundleFrames`. Then the orthogonal complements `(W x)ᗮ` are again
spanned near every point by `rank V - k` sections of class `C^n` forming a basis at each point
(`TauCeti.IsSubbundleFrameOn.exists_isSubbundleFrameOn_orthogonal`), so they form a `C^n` subbundle
of rank `rank V - k`, the orthogonal complement of `W`
(`TauCeti.HasLocalContMDiffSubbundleFrames.orthogonal`).

The proof reads `W` in a `C^n` orthonormal local frame `ε` of `V`
(`TauCeti.exists_isLocalFrameOn_orthonormal`). The coordinates `⟪ε i x, X j x⟫` of a local frame
`X` of `W` define injective operators `c x : ℝᵏ → ℝᵈ` depending `C^n` on `x`, whose ranges are the
coordinate images of `W x`. The orthogonal projections onto the orthogonal complements of these
ranges are `C^n` (`ContDiffAt.starProjection_orthogonal_range`). The synthesis map of `ε` is a
linear isometry onto the fibre, so it carries these complements onto `(W x)ᗮ`, and projecting a
basis at the base point and synthesizing gives the local frame
(`TauCeti.exists_isSubbundleFrameOn_map_synthesisMap`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Lemma 10.32
  (the local frame criterion for smooth subbundles).
-/

public section

open Bundle InnerProductSpace Set Module Function
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V IB] [IsContMDiffRiemannianBundle IB n F V]
  {k : ℕ} {W : Π x, Submodule ℝ (V x)}

/-- **Orthogonal complements of smooth subbundles have smooth local frames.** Let `X` be a `C^n`
local frame of size `k` of the subspaces `W x` of the fibres of a finite-rank `C^n` Riemannian
bundle `V`, on an open set `U₀`. Near every point of `U₀`, the orthogonal complements `(W x)ᗮ` are
spanned by `rank V - k` sections of class `C^n` forming a basis at each point. -/
theorem IsSubbundleFrameOn.exists_isSubbundleFrameOn_orthogonal {X : Fin k → Π x, V x}
    {U₀ : Set B} (hU₀ : IsOpen U₀) (hX : IsSubbundleFrameOn F W X U₀)
    (hXn : ∀ j, CMDiff[U₀] n (T% (X j))) {x₀ : B} (hx₀ : x₀ ∈ U₀) :
    ∃ U ⊆ U₀, IsOpen U ∧ x₀ ∈ U ∧ ∃ Y : Fin (finrank ℝ F - k) → Π x, V x,
      IsSubbundleFrameOn F (fun x ↦ (W x)ᗮ) Y U ∧ ∀ i, CMDiff[U] n (T% (Y i)) := by
  -- Read `W` in a `C^n` orthonormal frame `ε` near `x₀`, on `U₂ = U₀ ∩ U₁`.
  obtain ⟨U₁, hU₁, hx₁, ε, hε, hεon⟩ := exists_isLocalFrameOn_orthonormal (I := IB) (n := n)
    (F := F) (V := V) x₀
  set U₂ := U₀ ∩ U₁
  have hεn (i : Fin (finrank ℝ F)) : CMDiff[U₂] n (T% (ε i)) :=
    (hε.contMDiffOn i).mono inter_subset_right
  set c := fun y ↦ (overlapOperator ℝ (ε · y) (X · y)).toContinuousLinearMap
  have hc := contMDiffOn_overlapOperator hεn fun j ↦ (hXn j).mono inter_subset_left
  -- The overlap operators are injective, since synthesizing against `ε` gives the frame `X`.
  have hinj (y : B) (hy : y ∈ U₂) : Injective (c y) := by
    have h := (linearIndependent_iff_injective_synthesisMap (𝕜 := ℝ) (X · y)).mp
      (hX.linearIndependent hy.1)
    rw [← (hεon y hy.2).synthesisMap_comp_overlapOperator (hε.generating hy.2),
      LinearMap.coe_comp] at h
    exact h.of_comp
  -- The orthogonal projections onto the complements of their ranges are `C^n`.
  have hP : ContMDiffOn IB 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ F)) →L[ℝ]
      EuclideanSpace ℝ (Fin (finrank ℝ F))) n (fun y ↦ (c y).rangeᗮ.starProjection) U₂ :=
    fun y hy ↦ (contDiffAt_id.starProjection_orthogonal_range
      (hinj y hy)).contMDiffAt.comp_contMDiffWithinAt y (hc y hy)
  have hr : finrank ℝ (c x₀).rangeᗮ = finrank ℝ F - k := by
    have hsum := Submodule.finrank_add_finrank_orthogonal (c x₀).range
    rw [LinearMap.finrank_range_of_inj (hinj x₀ ⟨hx₀, hx₁⟩), finrank_euclideanSpace_fin,
      finrank_euclideanSpace_fin] at hsum
    omega
  -- Project a basis at `x₀` and synthesize against `ε`.
  obtain ⟨U, hUU₂, hU, hxU, Y, hY, hYn⟩ := exists_isSubbundleFrameOn_map_synthesisMap
    (hU₀.inter hU₁) hεn (fun y hy ↦ hε.linearIndependent hy.2) hP ⟨hx₀, hx₁⟩ hr
  refine ⟨U, fun y hy ↦ (hUU₂ hy).1, hU, hxU, Y,
    ⟨hY.continuousOn, hY.linearIndependent, fun {y} hy ↦ (hY.span_eq hy).trans ?_⟩, hYn⟩
  rw [← hX.span_eq (hUU₂ hy).1]
  exact (hεon y (hUU₂ hy).2).map_orthogonal_range_overlapOperator (hε.generating (hUU₂ hy).2) _

/-- **The orthogonal complement of a smooth subbundle.** If the subspaces `W x` of the fibres of
a finite-rank `C^n` Riemannian bundle `V` satisfy the local frame criterion for a `C^n` subbundle
of rank `k`, then so do their orthogonal complements `(W x)ᗮ`, with rank `rank V - k`. -/
theorem HasLocalContMDiffSubbundleFrames.orthogonal
    (hW : HasLocalContMDiffSubbundleFrames IB n F (Fin k) W) :
    HasLocalContMDiffSubbundleFrames IB n F (Fin (finrank ℝ F - k)) fun x ↦ (W x)ᗮ :=
  hasLocalContMDiffSubbundleFrames_iff.mpr fun x₀ ↦ by
    obtain ⟨U₀, hU₀, hx₀, X, hX, hXn⟩ := hasLocalContMDiffSubbundleFrames_iff.mp hW x₀
    obtain ⟨U, -, hU, hxU, Y, hY, hYn⟩ := hX.exists_isSubbundleFrameOn_orthogonal hU₀ hXn hx₀
    exact ⟨U, hU, hxU, Y, hY, hYn⟩

end TauCeti
