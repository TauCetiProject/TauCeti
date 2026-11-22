/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.ChangeOfVariables
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Calculus.ProjectionGraph
import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The wave front set of a measure on a smooth graph

Let `V` be a subspace of a finite-dimensional real inner product space `E` and `f : V → Vᗮ` a
smooth map. Its graph `S = {v + f v | v ∈ V}` is a smooth submanifold of `E`, and every immersed
submanifold is locally of this form over its tangent space
(`ContDiffOn.exists_openPartialHomeomorph_starProjection`).
Pushing Lebesgue measure of `V` forward along the parametrization `g v = v + f v` gives a measure
carried by `S` with a smooth positive density with respect to its surface measure; as a
distribution on an open set `Ω` it is

`φ ↦ ∫_V φ (v + f v) dv`.

This file proves that its wave front set is the conormal bundle of `S`
(`Distribution.waveFrontSet_ofFun_one_map_graph`):

`WF = {(v + f v, ξ) | v + f v ∈ Ω, ξ ≠ 0, ⟪ξ, u + Df(v) u⟫ = 0 for all u ∈ V}`,

the nonzero covectors annihilating the tangent space `{u + Df(v) u | u ∈ V}` of `S` at `v + f v`.
For `f = 0` this is the conormal set of the subspace `V`
(`Distribution.waveFrontSet_ofFun_one_map_subtype`). A smooth multiple of the measure by a
function which vanishes nowhere on `S ∩ Ω`, such as the density of the surface measure, has the
same wave front set (`Distribution.waveFrontSet_smulLeftCLM_ofFun_one_map_graph`).

## The argument

The shear `Φ x = x + f (P x)`, where `P` is the orthogonal projection onto `V`, is a smooth
diffeomorphism of `E` with inverse `Ψ x = x - f (P x)`, since `P` vanishes on the values of `f`:
`Ψ` is the graph chart `ContinuousLinearMap.projectionGraphChart` of `P`.
It maps `V` onto `S`, and its Jacobian determinant is `1`: its derivative is `1 + X ∘ P` with
`X` taking values in `Vᗮ`, so `det (1 + X ∘ P) = det (1 + P ∘ X) = 1` by the Weinstein–Aronszajn
identity (`ContinuousLinearMap.det_fderiv_projectionGraphChart_symm`). Hence the measure on `S`
is the pullback `Ψ^*` of the surface measure of `V` (`Distribution.compCLMOfOpenPartialHomeomorph`),
and the invariance of the wave front set under changes of variables
(`Distribution.waveFrontSet_compCLMOfOpenPartialHomeomorph`) carries the conormal set of `V` to
that of `S`: the covectors `ξ` over `v + f v` are those with `DΦ(v)ᵀ ξ ∈ Vᗮ`.

## Main results

* `Distribution.waveFrontSet_ofFun_one_map_graph`: the wave front set of the measure on the graph
  of `f` is its conormal bundle.
* `Distribution.waveFrontSet_smulLeftCLM_ofFun_one_map_graph`: the same for a smooth multiple of
  that measure by a function vanishing nowhere on the graph.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.4 and Example 8.2.5 (the wave front set of a smooth density on a
  submanifold is its conormal bundle).
-/

public section

noncomputable section

open Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions RealInnerProductSpace ContDiff InnerProduct

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {V : Submodule ℝ E} {f : V → Vᗮ}

/-! ### The shear straightening the graph -/

/-- The displacement `x ↦ f (P x)` of the shear along the graph of `f`, where `P` is the orthogonal
projection onto `V`. -/
private def shearDisp (f : V → Vᗮ) (x : E) : E :=
  (f (V.orthogonalProjectionOnto x) : E)

/-- The displacement takes values in `Vᗮ`, which the projection onto `V` kills. -/
private theorem starProjection_shearDisp (x : E) : V.starProjection (shearDisp f x) = 0 :=
  V.starProjection_apply_eq_zero_iff.2 (f _).property

/-- The displacement only depends on the projection onto `V`. -/
private theorem shearDisp_starProjection (x : E) :
    shearDisp f (V.starProjection x) = shearDisp f x := by
  rw [shearDisp, shearDisp, Submodule.starProjection_apply,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

/-- On `V`, the displacement at `v` is `f v`. -/
private theorem shearDisp_coe (v : V) : shearDisp f v = f v := by
  rw [shearDisp, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

private theorem contDiff_shearDisp (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (shearDisp f) :=
  Vᗮ.subtypeL.contDiff.comp (hf.comp V.orthogonalProjectionOnto.contDiff)

/-- The derivative of the displacement is `Df(P x) ∘ P`. -/
private theorem hasFDerivAt_shearDisp (hf : ContDiff ℝ ∞ f) (x : E) :
    HasFDerivAt (shearDisp f)
      ((Vᗮ.subtypeL ∘L fderiv ℝ f (V.orthogonalProjectionOnto x)) ∘L V.orthogonalProjectionOnto)
      x :=
  (Vᗮ.subtypeL.hasFDerivAt.comp _ ((hf.differentiable (by simp)) _).hasFDerivAt).comp x
    V.orthogonalProjectionOnto.hasFDerivAt

/-- The graph chart `x ↦ x - f (P x)` of `E`, with inverse the shear `x ↦ x + f (P x)`. It maps
the graph of `f` onto `V`. -/
private def straighten (hf : ContDiff ℝ ∞ f) : OpenPartialHomeomorph E E :=
  V.starProjection.projectionGraphChart (shearDisp f) isOpen_univ
    (contDiff_shearDisp hf).continuous.continuousOn fun x _ ↦ starProjection_shearDisp x

private theorem straighten_source (hf : ContDiff ℝ ∞ f) : (straighten hf).source = univ := by
  simp [straighten]

private theorem straighten_target (hf : ContDiff ℝ ∞ f) : (straighten hf).target = univ := by
  simp [straighten]

private theorem straighten_symm_apply (hf : ContDiff ℝ ∞ f) (x : E) :
    (straighten hf).symm x = x + shearDisp f x := by
  simp [straighten, shearDisp_starProjection]

/-- The straightening sends the point `v + f v` of the graph to `v`. -/
private theorem straighten_add (hf : ContDiff ℝ ∞ f) (v : V) :
    straighten hf ((v : E) + f v) = v := by
  simp [straighten, V.starProjection_apply_eq_zero_iff.2 (f v).property, shearDisp_coe]

private theorem contDiffOn_straighten (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ (⊤ : ℕ∞) (straighten hf) (straighten hf).source := fun _ _ ↦
  (V.starProjection.contDiffAt_projectionGraphChart _ _ _ _
    (contDiff_shearDisp hf).contDiffAt).contDiffWithinAt

private theorem contDiffOn_straighten_symm (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ (⊤ : ℕ∞) (straighten hf).symm (straighten hf).target := fun _ _ ↦
  (V.starProjection.contDiffAt_projectionGraphChart_symm _ _ _ _
    (contDiff_shearDisp hf).contDiffAt).contDiffWithinAt

/-- The derivative of the shear `x ↦ x + f (P x)` is `1 + Df(P x) ∘ P`. -/
private theorem hasFDerivAt_straighten_symm (hf : ContDiff ℝ ∞ f) (x : E) :
    HasFDerivAt (straighten hf).symm (ContinuousLinearMap.id ℝ E +
      ((Vᗮ.subtypeL ∘L fderiv ℝ f (V.orthogonalProjectionOnto (V.starProjection x))) ∘L
        V.orthogonalProjectionOnto) ∘L V.starProjection) x :=
  V.starProjection.hasFDerivAt_projectionGraphChart_symm _ _ _ _ (hasFDerivAt_shearDisp hf _)

/-- **The shear preserves volume.** Its derivative `1 + X ∘ P`, with `X` valued in `Vᗮ`, has
determinant `1`. -/
private theorem det_fderiv_straighten_symm (hf : ContDiff ℝ ∞ f) (x : E) :
    (fderiv ℝ (straighten hf).symm x).det = 1 :=
  V.starProjection.det_fderiv_projectionGraphChart_symm _ _ _ _ (hasFDerivAt_shearDisp hf _)
    (ContinuousLinearMap.ext fun _ ↦ V.starProjection_apply_eq_zero_iff.2 (Subtype.prop _))

/-! ### The measure on the graph as a pullback -/

/-- The measure on the graph of `f`, `φ ↦ ∫_V φ (v + f v) dv`, is the pullback along the
straightening `x ↦ x - f (P x)` of the surface measure of `V`. -/
private theorem ofFun_one_map_graph_eq_compCLMOfOpenPartialHomeomorph [MeasurableSpace E]
    [BorelSpace E] (hf : ContDiff ℝ ∞ f) (Ω : Opens E) :
    ofFun Ω (1 : E → ℂ) (volume.map fun v : V ↦ (v : E) + f v) ⊤ =
      compCLMOfOpenPartialHomeomorph (straighten hf) (contDiffOn_straighten hf)
        (contDiffOn_straighten_symm hf) (by simp [straighten_source])
        (mapsTo_univ _ _) (ofFun ⊤ 1 (volume.map ((↑) : V → E)) ⊤) := by
  have hV : Topology.IsClosedEmbedding ((↑) : V → E) :=
    V.isClosedEmbedding_subtype V.isClosed_of_finiteDimensional
  -- The graph parametrization is the shear composed with the inclusion of `V`.
  have hg : (fun v : V ↦ (v : E) + f v) = (straighten hf).symm ∘ ((↑) : V → E) := by
    ext v
    rw [Function.comp_apply, straighten_symm_apply, shearDisp_coe]
  have hS : Topology.IsClosedEmbedding fun v : V ↦ (v : E) + f v := by
    rw [hg, ← OpenPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv_symm_apply _
      (straighten_source hf) (straighten_target hf)]
    exact (Homeomorph.isClosedEmbedding _).comp hV
  -- Both pushed-forward measures are finite on compact sets.
  have := Measure.isFiniteMeasureOnCompacts_map_of_isProperMap volume hV.isProperMap
  have := Measure.isFiniteMeasureOnCompacts_map_of_isProperMap volume hS.isProperMap
  ext φ
  rw [compCLMOfOpenPartialHomeomorph_apply,
    ofFun_apply (f := 1) ((locallyIntegrable_const 1).locallyIntegrableOn _),
    ofFun_apply (f := 1) ((locallyIntegrable_const 1).locallyIntegrableOn _),
    hS.measurableEmbedding.integral_map, hV.measurableEmbedding.integral_map]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
  simp only [Pi.one_apply]
  rw [pushforwardCLM_apply_of_mem _ (by simp [straighten_target]), det_fderiv_straighten_symm hf,
    abs_one, one_smul, straighten_symm_apply, shearDisp_coe]

/-! ### The wave front set -/

/-- A point lies on the graph of `f` exactly when its straightening lies in `V`. -/
private theorem straighten_mem_iff (hf : ContDiff ℝ ∞ f) (x : E) :
    straighten hf x ∈ V ↔ ∃ v : V, (v : E) + f v = x := by
  have h := V.starProjection.projectionGraphChart_mem_range_iff (shearDisp f) isOpen_univ
    (contDiff_shearDisp hf).continuous.continuousOn (fun x _ ↦ starProjection_shearDisp x)
    V.isIdempotentElem_starProjection (subset_univ _) (fun x _ ↦ starProjection_shearDisp x)
    (mem_univ (V.starProjection x))
  simp only [Submodule.range_starProjection, inter_univ, mem_image, SetLike.mem_coe] at h
  refine h.trans ⟨fun ⟨y, hy, hyx⟩ ↦ ⟨⟨y, hy⟩, ?_⟩, fun ⟨v, hvx⟩ ↦ ⟨v, v.property, ?_⟩⟩
  · rwa [← shearDisp_coe]
  · rwa [shearDisp_coe]

/-- At a point `v` of `V`, the transposed derivative of the shear maps `ξ` into `Vᗮ` exactly
when `ξ` annihilates the tangent vectors `u + Df(v) u`, `u ∈ V`, of the graph. -/
private theorem adjoint_fderiv_straighten_symm_mem_orthogonal_iff (hf : ContDiff ℝ ∞ f) (v : V)
    (ξ : E) : ((fderiv ℝ (straighten hf).symm (v : E))†) ξ ∈ Vᗮ ↔
      ∀ u : V, ⟪ξ, (u : E) + fderiv ℝ f v u⟫ = 0 := by
  have key (u : V) : ⟪((fderiv ℝ (straighten hf).symm (v : E))†) ξ, (u : E)⟫ =
      ⟪ξ, (u : E) + fderiv ℝ f v u⟫ := by
    rw [ContinuousLinearMap.adjoint_inner_left, (hasFDerivAt_straighten_symm hf v).fderiv]
    simp [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  rw [Submodule.mem_orthogonal']
  exact ⟨fun h u ↦ (key u).symm.trans (h u u.property),
    fun h u hu ↦ (key ⟨u, hu⟩).trans (h ⟨u, hu⟩)⟩


variable [MeasurableSpace E] [BorelSpace E]

/-- **The wave front set of a measure on a smooth graph is its conormal bundle.** For a smooth
map `f : V → Vᗮ`, the pushforward of Lebesgue measure of `V` along `v ↦ v + f v`, a measure on
the graph of `f` with a smooth positive density, is singular exactly at the points `v + f v` of
the graph in `Ω`, and there exactly in the nonzero directions `ξ` orthogonal to the tangent space
`{u + Df(v) u | u ∈ V}`. For `f = 0` this is `Distribution.waveFrontSet_ofFun_one_map_subtype`. -/
theorem waveFrontSet_ofFun_one_map_graph (hf : ContDiff ℝ ∞ f) (Ω : Opens E) :
    (ofFun Ω (1 : E → ℂ) (volume.map fun v : V ↦ (v : E) + f v) ⊤).waveFrontSet =
      {p : E × E | p.1 ∈ Ω ∧ ∃ v : V, (v : E) + f v = p.1 ∧ p.2 ≠ 0 ∧
        ∀ u : V, ⟪p.2, (u : E) + fderiv ℝ f v u⟫ = 0} := by
  rw [ofFun_one_map_graph_eq_compCLMOfOpenPartialHomeomorph hf Ω,
    waveFrontSet_compCLMOfOpenPartialHomeomorph, waveFrontSet_ofFun_one_map_subtype]
  ext ⟨x, ξ⟩
  simp only [mem_ofPred_eq, mem_prod, mem_inter_iff, Opens.coe_top, mem_univ, true_and,
    mem_sdiff, SetLike.mem_coe, mem_singleton_iff]
  refine and_congr_right fun hx ↦ ⟨fun ⟨hV, hξV, hξ0⟩ ↦ ?_, fun ⟨v, hv, hξ0, hξ⟩ ↦ ?_⟩
  · obtain ⟨v, rfl⟩ := (straighten_mem_iff hf x).1 hV
    rw [straighten_add] at hξV hξ0
    refine ⟨v, rfl, fun h ↦ hξ0 (by rw [h, map_zero]),
      (adjoint_fderiv_straighten_symm_mem_orthogonal_iff hf v ξ).1 hξV⟩
  · subst hv
    have hinv := (straighten hf).adjoint_fderiv_apply_adjoint_fderiv_symm_apply_of_contDiffOn
      (contDiffOn_straighten hf) (contDiffOn_straighten_symm hf) (by simp)
      (x := (v : E) + f v) (by simp [straighten_source]) ξ
    rw [straighten_add] at hinv ⊢
    refine ⟨v.property,
      (adjoint_fderiv_straighten_symm_mem_orthogonal_iff hf v ξ).2 hξ, fun h ↦ hξ0 ?_⟩
    rw [← hinv, h, map_zero]

/-- **Smooth densities on a graph.** Multiplying the measure on the graph of `f` by a smooth
function `ρ` which vanishes nowhere on the part of the graph in `Ω`, for instance the density of
the surface measure of the graph with respect to it, does not change its wave front set: it is
still the conormal bundle of the graph. -/
theorem waveFrontSet_smulLeftCLM_ofFun_one_map_graph (hf : ContDiff ℝ ∞ f) (Ω : Opens E)
    {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρ0 : ∀ v : V, (v : E) + f v ∈ Ω → ρ ((v : E) + f v) ≠ 0) :
    (smulLeftCLM hρ (ofFun Ω (1 : E → ℂ) (volume.map fun v : V ↦ (v : E) + f v) ⊤)).waveFrontSet =
      {p : E × E | p.1 ∈ Ω ∧ ∃ v : V, (v : E) + f v = p.1 ∧ p.2 ≠ 0 ∧
        ∀ u : V, ⟪p.2, (u : E) + fderiv ℝ f v u⟫ = 0} := by
  rw [waveFrontSet_smulLeftCLM_of_forall_mem_ne_zero _ hρ fun p hp ↦ ?_,
    waveFrontSet_ofFun_one_map_graph hf Ω]
  obtain ⟨hx, v, hv, -⟩ := (waveFrontSet_ofFun_one_map_graph hf Ω).subset hp
  exact hv ▸ hρ0 v (hv ▸ hx)

end Distribution
