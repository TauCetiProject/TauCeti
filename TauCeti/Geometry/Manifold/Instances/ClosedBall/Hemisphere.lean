/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Basic
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Closed balls as hemispheres of great spheres

Let `ι : F →ₗᵢ[ℝ] E` be a linear isometry of real inner product spaces and `v` a unit vector of
`E` orthogonal to the range of `ι`. Inverse stereographic projection from `v` (Mathlib's
`stereoInvFun`) carries the orthogonal complement `vᗮ` onto the unit sphere minus `v`, and the
sphere of radius `2` in `vᗮ` onto the great sphere `vᗮ ∩ Sⁿ`, by `w ↦ w / 2`. So

`LinearIsometry.closedBallHemisphereMap ι v x = stereoInvFun (2 ι x)`,

which is `(2 ι x + (‖x‖² - 1) v) / (1 + ‖x‖²)`,

maps the closed unit ball of `F` onto the closed hemisphere centred at `-v` of the great sphere cut
out by `ι F ⊕ ℝ v`, and agrees with `ι` on the unit sphere of `F`
(`LinearIsometry.closedBallHemisphereMap_apply_of_norm_eq_one`). For `F = ℂ` this is a smooth disc
in the unit sphere bounded by the great circle `ι S¹`, such as a Seifert surface of the unknot.

The hemispheres of `TauCeti.prodHemisphereGraph` and `TauCeti.hemisphereHomeomorph` are graphs of
`u ↦ √(1 - ‖u‖²)`, which is not differentiable on the boundary sphere; inverse stereographic
projection is analytic up to the boundary.

The map is a smooth embedding of the closed ball, a manifold with boundary, into the sphere
(`LinearIsometry.isSmoothEmbedding_closedBallHemisphereMap`). Read in a chart
`TauCeti.closedBallChart φ` of the ball, an inversion `y ↦ inversion (-e₀) √2 y` of the model
half-space followed by `φ.symm`, and in the stereographic chart from `v`, it is
`y ↦ 2 N (inversion (-e₀) √2 y)` for the linear isometry `N` of model spaces through which the
stereographic chart reads `ι φ.symm`. Composing that chart of the sphere with the inverse
rescaled inversion `z ↦ inversion (-e₀) √2 (z / 2)` on the first factor of the decomposition
`N.prodOrthogonalRangeEquiv` gives a chart of the sphere in which the map reads as the inclusion
`y ↦ (y, 0)`, so it is an immersion at every point, including on the boundary sphere.

## Main definitions

* `LinearIsometry.closedBallHemisphereMap ι v`: the map `x ↦ stereoInvFun (2 ι x)` from the
  closed unit ball of `F` to the unit sphere of `E`.

## Main results

* `LinearIsometry.coe_closedBallHemisphereMap_apply`: the formula of the hemisphere map.
* `LinearIsometry.closedBallHemisphereMap_apply_of_norm_eq_one`: on the unit sphere of `F` it is
  `ι`.
* `LinearIsometry.isSmoothEmbedding_closedBallHemisphereMap`: it is a smooth embedding of
  manifolds with boundary, at every order of differentiability.
-/

public section

noncomputable section

open Set Metric Function Manifold Module EuclideanGeometry
open scoped Manifold ContDiff InnerProductSpace

namespace LinearIsometry

section RescaledInversion

variable {m : ℕ} [NeZero m]

/-! ### Rescaled inversions -/

local notation "e₀" => (EuclideanSpace.single (0 : Fin _) (1 : ℝ))

private theorem sqrt_two_ne_zero : (√2 : ℝ) ≠ 0 := by positivity

/-- The rescaled inversion `z ↦ inversion (-e₀) √2 (z / 2)` of `EuclideanSpace ℝ (Fin m)`, as an
open partial homeomorphism; its inverse is `y ↦ 2 • inversion (-e₀) √2 y`. It undoes the factor
`2` and the inversion of a closed-ball chart. -/
private def rescaledInversion :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m)) where
  toFun z := inversion (-e₀) √2 ((2 : ℝ)⁻¹ • z)
  invFun y := (2 : ℝ) • inversion (-e₀) √2 y
  source := {z | (2 : ℝ)⁻¹ • z ≠ -e₀}
  target := {y | y ≠ -e₀}
  map_source' _ hz := (inversion_eq_center sqrt_two_ne_zero).not.2 hz
  map_target' _ hy := by
    simpa [smul_smul] using (inversion_eq_center sqrt_two_ne_zero).not.2 hy
  left_inv' _ _ := by simp [inversion_inversion _ sqrt_two_ne_zero, smul_smul]
  right_inv' _ _ := by simp [inversion_inversion _ sqrt_two_ne_zero, smul_smul]
  open_source := isOpen_ne_fun (continuous_const_smul _) continuous_const
  open_target := isOpen_ne_fun continuous_id continuous_const
  continuousOn_toFun := ContinuousOn.inversion continuousOn_const continuousOn_const
    (continuous_const_smul _).continuousOn fun _ hz ↦ hz
  continuousOn_invFun := (continuous_const_smul (2 : ℝ)).comp_continuousOn <|
    ContinuousOn.inversion continuousOn_const continuousOn_const continuousOn_id fun _ hy ↦ hy

private theorem rescaledInversion_source :
    (rescaledInversion (m := m)).source = {z | (2 : ℝ)⁻¹ • z ≠ -e₀} :=
  (rfl)

private theorem rescaledInversion_target :
    (rescaledInversion (m := m)).target = {y | y ≠ -e₀} :=
  (rfl)

private theorem rescaledInversion_apply (z : EuclideanSpace ℝ (Fin m)) :
    rescaledInversion z = inversion (-e₀) √2 ((2 : ℝ)⁻¹ • z) :=
  (rfl)

private theorem rescaledInversion_symm_apply (y : EuclideanSpace ℝ (Fin m)) :
    (rescaledInversion (m := m)).symm y = (2 : ℝ) • inversion (-e₀) √2 y :=
  (rfl)

private theorem contDiffOn_rescaledInversion {k : ℕ∞ω} :
    ContDiffOn ℝ k (rescaledInversion (m := m)) (rescaledInversion (m := m)).source := by
  rw [rescaledInversion_source]
  intro z hz
  exact (((contDiffAt_inversion hz).comp z (contDiff_const_smul _).contDiffAt).congr_of_eventuallyEq
    (Filter.Eventually.of_forall rescaledInversion_apply)).contDiffWithinAt

private theorem contDiffOn_rescaledInversion_symm {k : ℕ∞ω} :
    ContDiffOn ℝ k (rescaledInversion (m := m)).symm (rescaledInversion (m := m)).target := by
  rw [rescaledInversion_target]
  intro y hy
  exact (((contDiffAt_inversion hy).const_smul (2 : ℝ)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall rescaledInversion_symm_apply)).contDiffWithinAt

variable {G V : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup V]
  [NormedSpace ℝ V] (Q : (EuclideanSpace ℝ (Fin m) × G) ≃L[ℝ] V)

/-- Conjugating the product of `rescaledInversion` with the identity of `G` by a continuous linear
equivalence `Q : ℝᵐ × G ≃L[ℝ] V` gives an open partial homeomorphism of `V`. -/
private def conjRescaledInversion : OpenPartialHomeomorph V V :=
  Q.symm.toHomeomorph.toOpenPartialHomeomorph ≫ₕ
    ((rescaledInversion (m := m)).prod (OpenPartialHomeomorph.refl G)) ≫ₕ
      Q.toHomeomorph.toOpenPartialHomeomorph

private theorem conjRescaledInversion_apply (z : V) :
    conjRescaledInversion Q z = Q (rescaledInversion (Q.symm z).1, (Q.symm z).2) :=
  (rfl)

private theorem conjRescaledInversion_symm_apply (z : V) :
    (conjRescaledInversion Q).symm z =
      Q ((rescaledInversion (m := m)).symm (Q.symm z).1, (Q.symm z).2) :=
  (rfl)

private theorem conjRescaledInversion_source :
    (conjRescaledInversion Q).source =
      Q.symm ⁻¹' ((rescaledInversion (m := m)).source ×ˢ univ) := by
  ext z
  simp [conjRescaledInversion]

private theorem conjRescaledInversion_target :
    (conjRescaledInversion Q).target =
      Q.symm ⁻¹' ((rescaledInversion (m := m)).target ×ˢ univ) := by
  ext z
  simp [conjRescaledInversion]

private theorem contDiffOn_conjRescaledInversion {k : ℕ∞ω} :
    ContDiffOn ℝ k (conjRescaledInversion Q) (conjRescaledInversion Q).source := by
  rw [conjRescaledInversion_source]
  have h : ContDiffOn ℝ k (fun z ↦ rescaledInversion (Q.symm z).1)
      (Q.symm ⁻¹' ((rescaledInversion (m := m)).source ×ˢ univ)) :=
    contDiffOn_rescaledInversion.comp (contDiff_fst.comp Q.symm.contDiff).contDiffOn
      fun _ hz ↦ hz.1
  exact (Q.contDiff.comp_contDiffOn
    (h.prodMk (contDiff_snd.comp Q.symm.contDiff).contDiffOn)).congr
    fun z _ ↦ conjRescaledInversion_apply Q z

private theorem contDiffOn_conjRescaledInversion_symm {k : ℕ∞ω} :
    ContDiffOn ℝ k (conjRescaledInversion Q).symm (conjRescaledInversion Q).target := by
  rw [conjRescaledInversion_target]
  have h : ContDiffOn ℝ k (fun z ↦ (rescaledInversion (m := m)).symm (Q.symm z).1)
      (Q.symm ⁻¹' ((rescaledInversion (m := m)).target ×ˢ univ)) :=
    contDiffOn_rescaledInversion_symm.comp (contDiff_fst.comp Q.symm.contDiff).contDiffOn
      fun _ hz ↦ hz.1
  exact (Q.contDiff.comp_contDiffOn
    (h.prodMk (contDiff_snd.comp Q.symm.contDiff).contDiffOn)).congr
    fun z _ ↦ conjRescaledInversion_symm_apply Q z


end RescaledInversion

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] [NormedAddCommGroup F] [InnerProductSpace ℝ F] {m : ℕ} [NeZero m]
  [Fact (finrank ℝ F = m)] (ι : F →ₗᵢ[ℝ] E) {v : sphere (0 : E) 1}

/-- The vector `2 ι x` lies in the orthogonal complement of a unit vector orthogonal to the range
of `ι`. -/
private theorem two_smul_mem_orthogonal (hv : ∀ x, ⟪(v : E), ι x⟫_ℝ = 0) (x : F) :
    (2 : ℝ) • ι x ∈ (ℝ ∙ (v : E))ᗮ :=
  Submodule.smul_mem _ _ (Submodule.mem_orthogonal_singleton_iff_inner_right.2 (hv x))

variable (v) in
/-- The **hemisphere map** of a linear isometry `ι : F →ₗᵢ[ℝ] E` and a unit vector `v` orthogonal
to its range: inverse stereographic projection from `v` of `2 ι x`, for `x` in the closed unit ball
of `F`. It maps the closed ball onto the closed hemisphere centred at `-v` of the great sphere cut
out by `ι F ⊕ ℝ v`, and is `ι` on the unit sphere of `F`. -/
def closedBallHemisphereMap (hv : ∀ x, ⟪(v : E), ι x⟫_ℝ = 0) :
    closedBall (0 : F) 1 → sphere (0 : E) 1 :=
  fun x ↦ stereoInvFun (norm_eq_of_mem_sphere v) ⟨(2 : ℝ) • ι x, two_smul_mem_orthogonal ι hv x⟩

variable (hv : ∀ x, ⟪(v : E), ι x⟫_ℝ = 0)

/-- The hemisphere map sends `x` to `(2 ι x + (‖x‖² - 1) v) / (1 + ‖x‖²)`. -/
@[simp]
theorem coe_closedBallHemisphereMap_apply (x : closedBall (0 : F) 1) :
    (ι.closedBallHemisphereMap v hv x : E) =
      (1 + ‖(x : F)‖ ^ 2)⁻¹ • ((2 : ℝ) • ι x + (‖(x : F)‖ ^ 2 - 1) • (v : E)) := by
  have hw : ‖(⟨(2 : ℝ) • ι x, two_smul_mem_orthogonal ι hv x⟩ : (ℝ ∙ (v : E))ᗮ)‖ =
      2 * ‖(x : F)‖ := by
    rw [← Submodule.norm_coe]
    simp [norm_smul, ι.norm_map]
  rw [closedBallHemisphereMap, stereoInvFun_apply, hw]
  simp only [smul_smul, smul_add]
  congr 1 <;> congr 1 <;> field_simp <;> ring

/-- **On the boundary sphere the hemisphere map is `ι`.** -/
theorem closedBallHemisphereMap_apply_of_norm_eq_one {x : closedBall (0 : F) 1}
    (hx : ‖(x : F)‖ = 1) : (ι.closedBallHemisphereMap v hv x : E) = ι x := by
  rw [coe_closedBallHemisphereMap_apply, hx]
  norm_num [smul_smul]

theorem continuous_closedBallHemisphereMap : Continuous (ι.closedBallHemisphereMap v hv) :=
  (continuous_stereoInvFun _).comp <| Continuous.subtype_mk
    (continuous_const.smul (ι.continuous.comp continuous_subtype_val)) _

theorem closedBallHemisphereMap_injective : Injective (ι.closedBallHemisphereMap v hv) := by
  intro x y h
  have h' := congrArg Subtype.val
    (((stereo_right_inv (norm_eq_of_mem_sphere v) _).symm.trans
      (congrArg (stereoToFun (v : E)) (congrArg Subtype.val h))).trans
      (stereo_right_inv (norm_eq_of_mem_sphere v) _))
  exact Subtype.ext (ι.injective (smul_right_injective E two_ne_zero h'))

/-- The hemisphere map is a topological embedding: it is a continuous injection of the compact
closed ball into the Hausdorff sphere. -/
theorem isEmbedding_closedBallHemisphereMap [FiniteDimensional ℝ F] :
    Topology.IsEmbedding (ι.closedBallHemisphereMap v hv) :=
  have : CompactSpace (closedBall (0 : F) 1) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  ((ι.continuous_closedBallHemisphereMap hv).isClosedEmbedding
    (ι.closedBallHemisphereMap_injective hv)).isEmbedding


/-! ### The hemisphere map is an immersion -/

section Immersion

local notation "e₀" => (EuclideanSpace.single (0 : Fin _) (1 : ℝ))

/-- The linear isometry `ι` with codomain the orthogonal complement of `v`. -/
private def codRestrictOrthogonal : F →ₗᵢ[ℝ] (ℝ ∙ (v : E))ᗮ where
  toLinearMap := ι.toLinearMap.codRestrict _ fun x ↦
    Submodule.mem_orthogonal_singleton_iff_inner_right.2 (hv x)
  norm_map' := ι.norm_map

/-- The linear isometry of model spaces through which the chart `closedBallChart φ` of the ball and
the stereographic chart from `v` of the sphere read `ι`. -/
private def hemisphereModelMap (φ : F ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton n
      (ne_zero_of_mem_unit_sphere v)).repr.toLinearIsometry.comp
    ((ι.codRestrictOrthogonal hv).comp φ.symm.toLinearIsometry)

omit [NeZero m] [Fact (finrank ℝ F = m)] in
/-- In the stereographic chart from `v`, the hemisphere map is `x ↦ 2 N (φ x)`, for the model map
`N` of `ι` attached to `φ`. -/
private theorem stereographic'_closedBallHemisphereMap (φ : F ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m))
    (x : closedBall (0 : F) 1) :
    stereographic' n v (ι.closedBallHemisphereMap v hv x) =
      (ι.hemisphereModelMap hv φ).prodOrthogonalRangeEquiv ((2 : ℝ) • φ x, 0) := by
  rw [prodOrthogonalRangeEquiv_apply_zero, map_smul]
  simp only [stereographic', OpenPartialHomeomorph.trans_apply,
    Homeomorph.toOpenPartialHomeomorph_apply, LinearIsometryEquiv.coe_toHomeomorph]
  have key : stereographic (norm_eq_of_mem_sphere v) (ι.closedBallHemisphereMap v hv x) =
      ⟨(2 : ℝ) • ι x, two_smul_mem_orthogonal ι hv x⟩ :=
    -- The inverse of `stereographic` is `stereoInvFun` by definition, and the hemisphere map is
    -- `stereoInvFun` of `2 ι x` by definition; Mathlib states no `symm_apply` lemma for it.
    (stereographic _).right_inv (mem_univ _)
  rw [key]
  simp only [hemisphereModelMap, coe_comp, comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.symm_apply_apply, ← LinearIsometryEquiv.map_smul]
  congr 1

/-- **The hemisphere map is an immersion at every point**, including on the boundary sphere of the
ball. In a chart `closedBallChart φ` of the ball and the stereographic chart from `v` followed by
the inverse of the rescaled inversion on the first factor of `N.prodOrthogonalRangeEquiv`, it
reads as the inclusion `y ↦ (y, 0)`. -/
theorem isImmersionAt_closedBallHemisphereMap {k : ℕ∞ω} (x : closedBall (0 : F) 1) :
    IsImmersionAt (𝓡∂ m) (𝓡 n) k (ι.closedBallHemisphereMap v hv) x := by
  obtain ⟨φ, hφx, -⟩ := TauCeti.exists_chartAt_closedBall_eq (n := m) x
  set Q := (ι.hemisphereModelMap (n := n) hv φ).prodOrthogonalRangeEquiv
  set ψ := stereographic' n v ≫ₕ conjRescaledInversion Q
  have hst : ∀ y, stereographic' n v (ι.closedBallHemisphereMap v hv y) = Q ((2 : ℝ) • φ y, 0) :=
    ι.stereographic'_closedBallHemisphereMap hv φ
  -- The hemisphere map sends the source of the ball chart into the source of `ψ`.
  have hsource : (TauCeti.closedBallChart φ).source ⊆
      ι.closedBallHemisphereMap v hv ⁻¹' ψ.source := by
    intro y hy
    rw [TauCeti.closedBallChart_source, mem_ofPred_eq] at hy
    rw [mem_preimage, OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · rw [stereographic'_source, mem_compl_singleton_iff]
      exact stereoInvFun_ne_north_pole _ _
    · rw [mem_preimage, hst, conjRescaledInversion_source, mem_preimage,
        ContinuousLinearEquiv.symm_apply_apply, mem_prod, rescaledInversion_source]
      exact ⟨by simpa [smul_smul] using hy, mem_univ _⟩
  -- `ψ` is a chart of the maximal analytic atlas of the sphere.
  have hψ : ψ ∈ IsManifold.maximalAtlas (𝓡 n) ω (sphere (0 : E) 1) :=
    TauCeti.trans_mem_maximalAtlas_of_contDiffAt (IsManifold.subset_maximalAtlas ⟨v, rfl⟩)
      (fun z hz ↦ (contDiffOn_conjRescaledInversion Q).contDiffAt
        ((conjRescaledInversion Q).open_source.mem_nhds hz))
      (fun z hz ↦ (contDiffOn_conjRescaledInversion_symm Q).contDiffAt
        ((conjRescaledInversion Q).open_target.mem_nhds hz))
  have hx : x ∈ (TauCeti.closedBallChart φ).source := by
    rwa [TauCeti.closedBallChart_source, mem_ofPred_eq]
  refine (IsImmersionAtOfComplement.mk_of_charts Q (TauCeti.closedBallChart φ) ψ hx
    (hsource hx)
    (IsManifold.maximalAtlas_subset_of_le le_top
      (IsManifold.subset_maximalAtlas (TauCeti.atlas_closedBall (E := F) (n := m) ▸
        mem_range_self φ)))
    (IsManifold.maximalAtlas_subset_of_le le_top hψ) hsource fun u hu ↦ ?_).isImmersionAt
  rw [OpenPartialHomeomorph.extend_target', TauCeti.closedBallChart_target, image_univ,
    range_modelWithCornersEuclideanHalfSpace] at hu
  have hu : 0 ≤ u 0 := hu
  have hφ : φ ((TauCeti.closedBallChart φ).symm ((𝓡∂ m).symm u)) = inversion (-e₀) √2 u := by
    rw [TauCeti.closedBallChart_symm_apply_coe, LinearIsometryEquiv.apply_symm_apply,
      modelWithCornersEuclideanHalfSpace_symm_apply_of_le hu]
  simp only [comp_apply, OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, id_eq, ψ, OpenPartialHomeomorph.coe_trans, hst, hφ,
    conjRescaledInversion_apply, ContinuousLinearEquiv.symm_apply_apply, rescaledInversion_apply,
    smul_smul, inv_mul_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), one_smul,
    inversion_inversion _ sqrt_two_ne_zero]

/-- The hemisphere map is a `C^k` immersion. -/
theorem isImmersion_closedBallHemisphereMap {k : ℕ∞ω} :
    IsImmersion (𝓡∂ m) (𝓡 n) k (ι.closedBallHemisphereMap v hv) :=
  TauCeti.isImmersion_iff_forall_isImmersionAt.2 (ι.isImmersionAt_closedBallHemisphereMap hv)

/-- **The hemisphere map is a smooth embedding** of the closed unit ball of `F`, a manifold with
boundary, into the unit sphere of `E`, at every order of differentiability. -/
theorem isSmoothEmbedding_closedBallHemisphereMap {k : ℕ∞ω} :
    IsSmoothEmbedding (𝓡∂ m) (𝓡 n) k (ι.closedBallHemisphereMap v hv) :=
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_pos <| by
    rw [Fact.out (p := finrank ℝ F = m)]
    exact Nat.pos_of_neZero m
  ⟨ι.isImmersion_closedBallHemisphereMap hv, ι.isEmbedding_closedBallHemisphereMap hv⟩

end Immersion

end LinearIsometry
