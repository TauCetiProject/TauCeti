/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# The open unit ball is diffeomorphic to the whole space

The open unit ball of a real inner product space `F` is an open subset of `F`, hence a manifold
modelled on `F`. It is diffeomorphic to `F` itself, by `v ↦ v / √(1 - ‖v‖²)`, with inverse
`v ↦ v / √(1 + ‖v‖²)`. This is Mathlib's `OpenPartialHomeomorph.univUnitBall`, read as a
diffeomorphism of manifolds.

In particular, a subset of a manifold that is the image of a smooth embedding of `ℝᵏ` is also the
image of a smooth embedding of the open unit disc of `ℝᵏ`. Conversely, every interior point of a
finite-dimensional smooth real manifold has arbitrarily small open neighbourhoods diffeomorphic to
the whole model vector space, sending the point to `0`.

## Main definitions

* `TauCeti.unitBallOpens`: the open unit ball, as an open subset.
* `TauCeti.unitBallDiffeomorph`: the diffeomorphism between the open unit ball and the whole space.

## Main results

* `TauCeti.exists_isSmoothEmbedding_unitBall`: the image of a smooth embedding of a real vector
  space of dimension `k` is the image of a smooth embedding of the open unit disc of `ℝᵏ`, with
  the centre going to the image of `0`.
* `TauCeti.exists_diffeomorph_opens_of_isInteriorPoint` and `TauCeti.exists_diffeomorph_opens`:
  every interior point (hence every point of a boundaryless manifold) has an open neighbourhood
  inside any given neighbourhood that is smoothly diffeomorphic to the whole model vector space,
  sending the point to `0`.
-/

public section

noncomputable section

open Filter Manifold Metric OpenPartialHomeomorph Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace TauCeti

section Normed

variable (F : Type*) [NormedAddCommGroup F]

/-- The open unit ball of a normed space, as an open subset. -/
def unitBallOpens : Opens F :=
  ⟨ball 0 1, isOpen_ball⟩

/-- The open unit ball, as a set. -/
@[simp]
theorem coe_unitBallOpens : (unitBallOpens F : Set F) = ball 0 1 := by
  rw [unitBallOpens, Opens.coe_mk]

variable {F} in
/-- A point lies in the open unit ball exactly when its norm is less than `1`. -/
@[simp]
theorem mem_unitBallOpens {v : F} : v ∈ unitBallOpens F ↔ ‖v‖ < 1 := by
  rw [← SetLike.mem_coe, coe_unitBallOpens, mem_ball_zero_iff]

/-- The centre of the open unit ball. -/
theorem zero_mem_unitBallOpens : (0 : F) ∈ unitBallOpens F :=
  mem_unitBallOpens.2 (by simp)

end Normed

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The open unit ball is diffeomorphic to the whole space**, by `v ↦ v / √(1 - ‖v‖²)`, with
inverse `v ↦ v / √(1 + ‖v‖²)`. -/
def unitBallDiffeomorph : unitBallOpens F ≃ₘ^∞⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ F where
  toFun v := univUnitBall.symm v
  invFun v := ⟨univUnitBall v, by
    rw [← SetLike.mem_coe, coe_unitBallOpens, ← univUnitBall_target]
    exact univUnitBall.map_source (mem_univ v)⟩
  left_inv v := Subtype.ext (univUnitBall.right_inv (by
    rw [univUnitBall_target, ← coe_unitBallOpens]; exact v.2))
  right_inv v := univUnitBall.left_inv (mem_univ v)
  contMDiff_toFun :=
    contDiffOn_univUnitBall_symm.contMDiffOn.comp_contMDiff contMDiff_subtype_val fun v ↦ by
      rw [← coe_unitBallOpens]; exact v.2
  contMDiff_invFun :=
    (ContMDiff.subtypeVal_comp_iff (unitBallOpens F) _).1 contDiff_univUnitBall.contMDiff

variable {F}

/-- The diffeomorphism from the open unit ball to the whole space is `univUnitBall.symm`. -/
theorem unitBallDiffeomorph_apply (v : unitBallOpens F) :
    unitBallDiffeomorph F v = univUnitBall.symm (v : F) := by
  rw [unitBallDiffeomorph]
  rfl

/-- The inverse diffeomorphism is `univUnitBall`. -/
theorem coe_unitBallDiffeomorph_symm_apply (v : F) :
    ((unitBallDiffeomorph F).symm v : F) = univUnitBall v := by
  rw [unitBallDiffeomorph]
  rfl

/-- The centre of the ball goes to `0`. -/
@[simp]
theorem unitBallDiffeomorph_zero :
    unitBallDiffeomorph F ⟨0, zero_mem_unitBallOpens _⟩ = 0 := by
  rw [unitBallDiffeomorph_apply, univUnitBall_symm_apply_zero]

/-- **Discs instead of vector spaces.** The image of a smooth embedding `ι` of a real vector space
`V` of dimension `k` is also the image of a smooth embedding of the open unit disc of `ℝᵏ`, which
sends the centre to `ι 0`. -/
theorem exists_isSmoothEmbedding_unitBall {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {k : ℕ} (hk : Module.finrank ℝ V = k)
    {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] {ι : V → N}
    (hι : IsSmoothEmbedding 𝓘(ℝ, V) J ∞ ι) :
    ∃ ι' : unitBallOpens (EuclideanSpace ℝ (Fin k)) → N,
      IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) J ∞ ι' ∧ range ι' = range ι ∧
        ι' ⟨0, zero_mem_unitBallOpens _⟩ = ι 0 := by
  -- Identify `ℝᵏ` with `V` linearly, then the disc with `ℝᵏ`.
  let e : EuclideanSpace ℝ (Fin k) ≃L[ℝ] V :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [finrank_euclideanSpace_fin, hk])
  refine ⟨(ι ∘ e) ∘ unitBallDiffeomorph _, isSmoothEmbedding_comp_diffeomorph _
    (isSmoothEmbedding_comp_continuousLinearEquiv e hι), ?_, ?_⟩
  · exact (e.surjective.comp (unitBallDiffeomorph _).toHomeomorph.surjective).range_comp ι
  · simp

/-- Given an open subset `V` of a finite-dimensional real normed space `E` and `y₀ ∈ V`, there is a
smooth affine diffeomorphism `T : E ≃ₘ^∞ F` onto `F = EuclideanSpace ℝ (Fin (finrank ℝ E))` sending
`y₀` to `0` and pulling back the open unit ball inside `V`. -/
private theorem exists_diffeomorph_unitBallOpens_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {V : Set E} (hV : IsOpen V) {y₀ : E} (hy₀ : y₀ ∈ V) :
    ∃ T : E ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))⟯
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
      T y₀ = 0 ∧ ∀ ⦃y : E⦄, T y ∈ unitBallOpens _ → y ∈ V := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let eF : E ≃L[ℝ] F :=
    (ContinuousLinearEquiv.ofFinrankEq
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := Module.finrank ℝ E))).symm
  let T₁ : E ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ F :=
    (Diffeomorph.smulAdd ∞ (1 : ℝ) (-y₀) one_ne_zero).trans (eF.toContDiffDiffeomorph ∞)
  have h0_tgt : (0 : F) ∈ T₁.symm ⁻¹' V := by
    rw [mem_preimage, T₁.injective (by simp [T₁] : T₁ (T₁.symm 0) = T₁ y₀)]
    exact hy₀
  obtain ⟨r, hr, hr_sub⟩ := Metric.isOpen_iff.1 (hV.preimage T₁.symm.continuous) 0 h0_tgt
  refine ⟨T₁.trans (Diffeomorph.smulAdd ∞ r⁻¹ 0 (inv_ne_zero hr.ne')), by simp [T₁], fun y hy ↦ ?_⟩
  have hnorm : ‖T₁ y‖ < r := by
    have hTy : ‖r⁻¹ • T₁ y‖ < 1 := by simpa using mem_unitBallOpens.1 hy
    have hrT : r * ‖r⁻¹ • T₁ y‖ < r * 1 := mul_lt_mul_of_pos_left hTy hr
    simpa [norm_smul, abs_of_pos hr, mul_inv_cancel_left₀ hr.ne'] using hrT
  simpa only [mem_preimage, T₁.symm_apply_apply] using hr_sub (mem_ball_zero_iff.2 hnorm)

/-- **Every interior point has a coordinate neighbourhood diffeomorphic to the whole model space.**
Inside any neighbourhood `U` of an interior point `x₀` of a finite-dimensional `C^∞` real manifold,
there exist an open subset `W ⊆ U` containing `x₀` and a smooth diffeomorphism `Ψ : W ≃ₘ^∞ E` onto
the entire model vector space `E` sending `x₀` to `0`. -/
theorem exists_diffeomorph_opens_of_isInteriorPoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) {U : Set M} (hU : U ∈ 𝓝 x₀) :
    ∃ (W : Opens M) (hx₀W : x₀ ∈ W) (Ψ : W ≃ₘ^∞⟮I, 𝓘(ℝ, E)⟯ E),
      (W : Set M) ⊆ U ∧ Ψ ⟨x₀, hx₀W⟩ = 0 := by
  let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
  let eF : F ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq
      (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := Module.finrank ℝ E))
  let φ₀ : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ :=
    (extChartPartialDiffeomorph I ∞ x₀).restrOpen (interior U) isOpen_interior
  have hx₀_φ₀ : x₀ ∈ φ₀.source := by
    rw [PartialDiffeomorph.restrOpen_source]
    exact ⟨(mem_extChartPartialDiffeomorph_source I ∞ x₀).2 hx₀, mem_interior_iff_mem_nhds.2 hU⟩
  obtain ⟨T, hT_x₀, hball_tgt⟩ :=
    exists_diffeomorph_unitBallOpens_subset φ₀.open_target (φ₀.map_source hx₀_φ₀)
  let S : Set M := φ₀.source ∩ φ₀ ⁻¹' (T ⁻¹' ball (0 : F) 1)
  have hS_open : IsOpen S :=
    φ₀.contMDiffOn.continuousOn.isOpen_inter_preimage φ₀.open_source
      (isOpen_ball.preimage T.continuous)
  let φ₁ := φ₀.restrOpen S hS_open
  have hx₀W : x₀ ∈ (⟨φ₁.source, φ₁.open_source⟩ : Opens M) := by
    rw [Opens.mem_mk, PartialDiffeomorph.restrOpen_source]
    exact ⟨hx₀_φ₀, hx₀_φ₀, by simp [hT_x₀]⟩
  have htgt (y : E) : y ∈ (⟨φ₁.target, φ₁.open_target⟩ : Opens E) ↔ T y ∈ unitBallOpens F := by
    rw [Opens.mem_mk, PartialDiffeomorph.restrOpen_target, mem_unitBallOpens]
    refine ⟨fun hy ↦ ?_, fun hy ↦ ?_⟩
    · have hmem : T (φ₀ (φ₀.toPartialEquiv.symm y)) ∈ ball (0 : F) 1 := hy.2.2
      rwa [φ₀.right_inv hy.1, mem_ball_zero_iff] at hmem
    · have hy₀ : y ∈ φ₀.target := hball_tgt (mem_unitBallOpens.2 hy)
      exact ⟨hy₀, φ₀.map_target hy₀, by simp [φ₀.right_inv hy₀, hy]⟩
  refine ⟨⟨φ₁.source, φ₁.open_source⟩, hx₀W,
    ((φ₁.toDiffeomorphSourceTarget.trans (T.subtype htgt)).trans
      (unitBallDiffeomorph F)).trans (eF.toContDiffDiffeomorph ∞),
    fun y hy ↦ ?_, ?_⟩
  · rw [Opens.coe_mk, PartialDiffeomorph.restrOpen_source] at hy
    have hy₀ : y ∈ φ₀.source := hy.1
    rw [PartialDiffeomorph.restrOpen_source] at hy₀
    exact interior_subset hy₀.2
  · have h0 : T.subtype htgt (φ₁.toDiffeomorphSourceTarget ⟨x₀, hx₀W⟩) =
        ⟨0, zero_mem_unitBallOpens F⟩ :=
      Subtype.ext (by simp [φ₁, hT_x₀])
    simp [h0]

/-- **Every point of a boundaryless manifold has a coordinate neighbourhood diffeomorphic to the
whole model space.** -/
theorem exists_diffeomorph_opens
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] (x₀ : M) {U : Set M} (hU : U ∈ 𝓝 x₀) :
    ∃ (W : Opens M) (hx₀W : x₀ ∈ W) (Ψ : W ≃ₘ^∞⟮I, 𝓘(ℝ, E)⟯ E),
      (W : Set M) ⊆ U ∧ Ψ ⟨x₀, hx₀W⟩ = 0 :=
  exists_diffeomorph_opens_of_isInteriorPoint BoundarylessManifold.isInteriorPoint hU

end TauCeti
