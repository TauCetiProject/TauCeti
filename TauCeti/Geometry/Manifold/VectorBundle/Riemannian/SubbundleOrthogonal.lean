/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Frame
public import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt
public import TauCeti.Geometry.Manifold.VectorBundle.Subbundle
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
import TauCeti.Analysis.InnerProductSpace.RangeProjection

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

section Coordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d k : ℕ}

/-- The operator `ℝᵏ → ℝᵈ` sending the `j`-th basis vector to the coordinates `⟪ε i, X j⟫` of
`X j` in the family `ε`. -/
private abbrev coordOperator (ε : Fin d → E) (X : Fin k → E) :
    EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  synthesisMap ℝ fun j ↦ analysisMap ℝ ε (X j)

variable {ε : Fin d → E} (hon : Orthonormal ℝ ε) (hsp : ⊤ ≤ Submodule.span ℝ (range ε))
  (X : Fin k → E)
include hon hsp

/-- Synthesizing the coordinates of `X` in an orthonormal basis `ε` recovers `X`. -/
private theorem synthesisMap_comp_coordOperator :
    synthesisMap ℝ ε ∘ₗ coordOperator ε X = synthesisMap ℝ X := by
  have hid := (OrthonormalBasis.mk hon hsp).frameOperator_eq_id (𝕜 := ℝ)
  rw [OrthonormalBasis.coe_mk] at hid
  have hX (j : Fin k) : synthesisMap ℝ ε (analysisMap ℝ ε (X j)) = X j := by
    simpa only [frameOperator_def, LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun hid (X j)
  refine LinearMap.ext fun a ↦ ?_
  simp [map_sum, map_smul, hX]

/-- The synthesis map of an orthonormal basis `ε` carries the orthogonal complement of the range
of the coordinate operator of `X` onto the orthogonal complement of the span of `X`. -/
private theorem map_orthogonal_range_coordOperator :
    (LinearMap.range (coordOperator ε X))ᗮ.map (synthesisMap ℝ ε) =
      (Submodule.span ℝ (range X))ᗮ := by
  set S := Orthonormal.synthesisMapIsometry hon
  have hS : S.toLinearMap = synthesisMap ℝ ε := Orthonormal.synthesisMapIsometry_toLinearMap hon
  have hrange : LinearMap.range S.toLinearMap = ⊤ := by
    rw [hS, range_synthesisMap]
    exact top_unique hsp
  rw [← hS, Submodule.map_orthogonal, hrange, inf_top_eq, hS, ← LinearMap.range_comp,
    synthesisMap_comp_coordOperator hon hsp, range_synthesisMap]

end Coordinates

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V IB] [IsContMDiffRiemannianBundle IB n F V]
  {k : ℕ} {W : Π x, Submodule ℝ (V x)}

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle n F V IB] in
/-- The coordinate operators of `C^n` sections `X` in `C^n` sections `ε` depend `C^n` on the base
point. -/
private theorem contMDiffOn_coordOperator {d : ℕ} {ε : Fin d → Π x, V x} {X : Fin k → Π x, V x}
    {U : Set B} (hε : ∀ i, CMDiff[U] n (T% (ε i))) (hX : ∀ j, CMDiff[U] n (T% (X j))) :
    ContMDiffOn IB 𝓘(ℝ, EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin d)) n
      (fun y ↦ (coordOperator (ε · y) (X · y)).toContinuousLinearMap) U := by
  -- The coordinates `⟪ε i y, X j y⟫` are `C^n`.
  have hw (j : Fin k) : ContMDiffOn IB 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) n
      (fun y ↦ analysisMap ℝ (ε · y) (X j y)) U := by
    have hcoord : ContMDiffOn IB 𝓘(ℝ, Fin d → ℝ) n (fun y i ↦ ⟪ε i y, X j y⟫_ℝ) U :=
      contMDiffOn_pi_module_iff.2 fun i ↦ (hε i).inner_bundle (hX j)
    refine (((EuclideanSpace.equiv (Fin d) ℝ).symm.contDiff (n := n)).contMDiff.comp_contMDiffOn
      hcoord).congr fun y _ ↦ ?_
    ext i
    simp
  -- The coordinate operator is the sum of the rank-one maps `a ↦ a j • w j y`.
  have hsum : (fun y ↦ (coordOperator (ε · y) (X · y)).toContinuousLinearMap) = fun y ↦
      ∑ j, (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).smulRight
        (analysisMap ℝ (ε · y) (X j y)) := by
    ext y a : 2
    simp
  rw [hsum]
  exact contMDiffOn_finsetSum fun j _ ↦
    ((ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d))
      (EuclideanSpace.proj j)).contDiff (n := n)).contMDiff.comp_contMDiffOn (hw j)

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
  set c := fun y ↦ (coordOperator (ε · y) (X · y)).toContinuousLinearMap
  have hc := contMDiffOn_coordOperator hεn fun j ↦ (hXn j).mono inter_subset_left
  -- The coordinate operators are injective, since synthesizing against `ε` gives the frame `X`.
  have hinj (y : B) (hy : y ∈ U₂) : Injective (c y) := by
    have h := (linearIndependent_iff_injective_synthesisMap (𝕜 := ℝ) (X · y)).mp
      (hX.linearIndependent hy.1)
    rw [← synthesisMap_comp_coordOperator (hεon y hy.2) (hε.generating hy.2), LinearMap.coe_comp]
      at h
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
  exact map_orthogonal_range_coordOperator (hεon y (hUU₂ hy).2) (hε.generating (hUU₂ hy).2) _

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
