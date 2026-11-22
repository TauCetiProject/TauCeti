/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.ChangeOfVariables
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.LinearAlgebra.Determinant.Basic
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
diffeomorphism of `E` with inverse `Ψ x = x - f (P x)`, since `P` vanishes on the values of `f`.
It maps `V` onto `S`, and its Jacobian determinant is `1`: its derivative is `1 + X ∘ P` with
`X = Df(P x)` taking values in `Vᗮ`, so `det (1 + X ∘ P) = det (1 + P ∘ X) = 1` by the
Weinstein–Aronszajn identity (`LinearMap.det_one_add_comp_comm`). Hence the measure on `S` is the
pullback `Ψ^*` of the surface measure of `V` (`Distribution.compCLMOfOpenPartialHomeomorph`), and
the invariance of the wave front set under changes of variables
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
private theorem orthogonalProjectionOnto_shearDisp (x : E) :
    V.orthogonalProjectionOnto (shearDisp f x) = 0 :=
  Submodule.orthogonalProjectionOnto_eq_zero_iff.2 (f _).property

/-- Moving along a vector which the projection onto `V` kills does not change the displacement. -/
private theorem shearDisp_add_of_orthogonalProjectionOnto_eq_zero {x y : E}
    (hy : V.orthogonalProjectionOnto y = 0) : shearDisp f (x + y) = shearDisp f x := by
  simp only [shearDisp, map_add, hy, add_zero]

/-- On the graph, the displacement at `v + f v` is `f v`. -/
private theorem shearDisp_add (v : V) : shearDisp f ((v : E) + f v) = f v := by
  rw [shearDisp_add_of_orthogonalProjectionOnto_eq_zero
    (Submodule.orthogonalProjectionOnto_eq_zero_iff.2 (f v).property), shearDisp,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

/-- On `V`, the displacement at `v` is `f v`. -/
private theorem shearDisp_coe (v : V) : shearDisp f v = f v := by
  rw [shearDisp, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

private theorem contDiff_shearDisp (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (shearDisp f) :=
  Vᗮ.subtypeL.contDiff.comp (hf.comp V.orthogonalProjectionOnto.contDiff)

/-- The homeomorphism `x ↦ x - f (P x)` of `E`, with inverse the shear `x ↦ x + f (P x)`. It maps
the graph of `f` onto `V`. -/
private def straighten (hf : ContDiff ℝ ∞ f) : E ≃ₜ E where
  toFun x := x - shearDisp f x
  invFun x := x + shearDisp f x
  left_inv x := by
    beta_reduce
    rw [sub_eq_add_neg, shearDisp_add_of_orthogonalProjectionOnto_eq_zero (by
      rw [map_neg, orthogonalProjectionOnto_shearDisp, neg_zero]), neg_add_cancel_right]
  right_inv x := by
    beta_reduce
    rw [shearDisp_add_of_orthogonalProjectionOnto_eq_zero (orthogonalProjectionOnto_shearDisp x),
      add_sub_cancel_right]
  continuous_toFun := continuous_id.sub (contDiff_shearDisp hf).continuous
  continuous_invFun := continuous_id.add (contDiff_shearDisp hf).continuous

private theorem straighten_symm_apply (hf : ContDiff ℝ ∞ f) (x : E) :
    (straighten hf).symm x = x + shearDisp f x :=
  (rfl)

/-- The straightening as an open partial homeomorphism with source and target `E`. -/
private def straightenOPH (hf : ContDiff ℝ ∞ f) : OpenPartialHomeomorph E E :=
  (straighten hf).toOpenPartialHomeomorph

private theorem straightenOPH_apply (hf : ContDiff ℝ ∞ f) (x : E) :
    straightenOPH hf x = x - shearDisp f x :=
  (rfl)

private theorem coe_straightenOPH_symm (hf : ContDiff ℝ ∞ f) :
    ⇑(straightenOPH hf).symm = fun x ↦ x + shearDisp f x :=
  (rfl)

private theorem straightenOPH_source (hf : ContDiff ℝ ∞ f) : (straightenOPH hf).source = univ :=
  (rfl)

private theorem straightenOPH_target (hf : ContDiff ℝ ∞ f) : (straightenOPH hf).target = univ :=
  (rfl)

/-- The straightening sends the point `v + f v` of the graph to `v`. -/
private theorem straightenOPH_add (hf : ContDiff ℝ ∞ f) (v : V) :
    straightenOPH hf ((v : E) + f v) = v := by
  rw [straightenOPH_apply, shearDisp_add, add_sub_cancel_right]

private theorem contDiffOn_straightenOPH (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ (⊤ : ℕ∞) (straightenOPH hf) (straightenOPH hf).source :=
  (contDiff_id.sub (contDiff_shearDisp hf)).contDiffOn

private theorem contDiffOn_straightenOPH_symm (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ (⊤ : ℕ∞) (straightenOPH hf).symm (straightenOPH hf).target :=
  (contDiff_id.add (contDiff_shearDisp hf)).contDiffOn

/-- The derivative of the shear `x ↦ x + f (P x)` is `1 + Df(P x) ∘ P`. -/
private theorem hasFDerivAt_shear (hf : ContDiff ℝ ∞ f) (x : E) :
    HasFDerivAt (fun y ↦ y + shearDisp f y)
      (ContinuousLinearMap.id ℝ E + (Vᗮ.subtypeL ∘L fderiv ℝ f (V.orthogonalProjectionOnto x)) ∘L
        V.orthogonalProjectionOnto) x :=
  (hasFDerivAt_id x).add ((Vᗮ.subtypeL.hasFDerivAt.comp _
    ((hf.differentiable (by simp)) _).hasFDerivAt).comp x V.orthogonalProjectionOnto.hasFDerivAt)

/-- **The shear preserves volume.** Its derivative `1 + X ∘ P`, with `X = Df(P x)` valued in
`Vᗮ`, has determinant `det (1 + P ∘ X) = 1`. -/
private theorem det_fderiv_shear (hf : ContDiff ℝ ∞ f) (x : E) :
    (fderiv ℝ (fun y ↦ y + shearDisp f y) x).det = 1 := by
  have hPX : (V.orthogonalProjectionOnto : E →ₗ[ℝ] V) ∘ₗ
      ((Vᗮ.subtypeL ∘L fderiv ℝ f (V.orthogonalProjectionOnto x) : V →L[ℝ] E) : V →ₗ[ℝ] E) = 0 :=
    LinearMap.ext fun u ↦ by
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, LinearMap.zero_apply]
      exact Submodule.orthogonalProjectionOnto_eq_zero_iff.2
        (fderiv ℝ f (V.orthogonalProjectionOnto x) u).property
  have h := LinearMap.det_one_add_comp_comm
    ((Vᗮ.subtypeL ∘L fderiv ℝ f (V.orthogonalProjectionOnto x) : V →L[ℝ] E) : V →ₗ[ℝ] E)
    (V.orthogonalProjectionOnto : E →ₗ[ℝ] V)
  rw [hPX, add_zero, map_one] at h
  rw [(hasFDerivAt_shear hf x).fderiv, ContinuousLinearMap.det,
    ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.coe_id, ← Module.End.one_eq_id,
    ContinuousLinearMap.toLinearMap_comp, h]

/-! ### The measure on the graph as a pullback -/

/-- The measure on the graph of `f`, `φ ↦ ∫_V φ (v + f v) dv`, is the pullback along the
straightening `x ↦ x - f (P x)` of the surface measure of `V`. -/
private theorem ofFun_one_map_graph_eq_compCLMOfOpenPartialHomeomorph [MeasurableSpace E]
    [BorelSpace E] (hf : ContDiff ℝ ∞ f) (Ω : Opens E) :
    ofFun Ω (1 : E → ℂ) (volume.map fun v : V ↦ (v : E) + f v) ⊤ =
      compCLMOfOpenPartialHomeomorph (straightenOPH hf) (contDiffOn_straightenOPH hf)
        (contDiffOn_straightenOPH_symm hf) (by simp [straightenOPH_source])
        (mapsTo_univ _ _) (ofFun ⊤ 1 (volume.map ((↑) : V → E)) ⊤) := by
  have hV : Topology.IsClosedEmbedding ((↑) : V → E) :=
    V.isClosedEmbedding_subtype V.isClosed_of_finiteDimensional
  -- The graph parametrization is the shear composed with the inclusion of `V`.
  have hg : (fun v : V ↦ (v : E) + f v) = (straighten hf).symm ∘ ((↑) : V → E) := by
    ext v
    rw [Function.comp_apply, straighten_symm_apply, shearDisp_coe]
  have hS : Topology.IsClosedEmbedding fun v : V ↦ (v : E) + f v := by
    rw [hg]
    exact (straighten hf).symm.isClosedEmbedding.comp hV
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
  rw [pushforwardCLM_apply_of_mem _ (by simp [straightenOPH_target]), coe_straightenOPH_symm,
    det_fderiv_shear hf, abs_one, one_smul]
  beta_reduce
  rw [shearDisp_coe]

/-! ### The wave front set -/

/-- A point lies on the graph of `f` exactly when its straightening lies in `V`. -/
private theorem straightenOPH_mem_iff (hf : ContDiff ℝ ∞ f) (x : E) :
    straightenOPH hf x ∈ V ↔ ∃ v : V, (v : E) + f v = x := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · -- The point `⟨x - f (P x), hx⟩` of `V` is `P x`, so `f` takes the value `f (P x)` there.
    have hP : (⟨_, hx⟩ : V) = V.orthogonalProjectionOnto x := by
      rw [← Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨_, hx⟩ : V)]
      simp only [straightenOPH_apply, map_sub, orthogonalProjectionOnto_shearDisp, sub_zero]
    have hfx : (f ⟨_, hx⟩ : E) = shearDisp f x := by rw [hP, shearDisp]
    exact ⟨⟨_, hx⟩, by rw [hfx]; simp only [straightenOPH_apply, sub_add_cancel]⟩
  · rintro ⟨v, rfl⟩
    rw [straightenOPH_add]
    exact v.property

/-- At a point `v` of `V`, the transposed derivative of the shear maps `ξ` into `Vᗮ` exactly
when `ξ` annihilates the tangent vectors `u + Df(v) u`, `u ∈ V`, of the graph. -/
private theorem adjoint_fderiv_shear_mem_orthogonal_iff (hf : ContDiff ℝ ∞ f) (v : V) (ξ : E) :
    ((fderiv ℝ (fun y ↦ y + shearDisp f y) (v : E))†) ξ ∈ Vᗮ ↔
      ∀ u : V, ⟪ξ, (u : E) + fderiv ℝ f v u⟫ = 0 := by
  have key (u : V) : ⟪((fderiv ℝ (fun y ↦ y + shearDisp f y) (v : E))†) ξ, (u : E)⟫ =
      ⟪ξ, (u : E) + fderiv ℝ f v u⟫ := by
    rw [ContinuousLinearMap.adjoint_inner_left, (hasFDerivAt_shear hf v).fderiv]
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
  · obtain ⟨v, rfl⟩ := (straightenOPH_mem_iff hf x).1 hV
    rw [straightenOPH_add, coe_straightenOPH_symm] at hξV hξ0
    refine ⟨v, rfl, fun h ↦ hξ0 (by rw [h, map_zero]),
      (adjoint_fderiv_shear_mem_orthogonal_iff hf v ξ).1 hξV⟩
  · subst hv
    have hinv := (straightenOPH hf).adjoint_fderiv_apply_adjoint_fderiv_symm_apply_of_contDiffOn
      (contDiffOn_straightenOPH hf) (contDiffOn_straightenOPH_symm hf) (by simp)
      (x := (v : E) + f v) (by simp [straightenOPH_source]) ξ
    rw [straightenOPH_add, coe_straightenOPH_symm] at hinv ⊢
    refine ⟨v.property,
      (adjoint_fderiv_shear_mem_orthogonal_iff hf v ξ).2 hξ, fun h ↦ hξ0 ?_⟩
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
  rw [← waveFrontSet_ofFun_one_map_graph hf Ω]
  refine Subset.antisymm (fun p hp ↦ (waveFrontSet_smulLeftCLM_subset _ hρ hp).1) fun p hp ↦ ?_
  obtain ⟨hx, v, hv, -⟩ := (waveFrontSet_ofFun_one_map_graph hf Ω).subset hp
  exact (mem_waveFrontSet_smulLeftCLM_iff hρ (hv ▸ hρ0 v (hv ▸ hx))).2 hp

end Distribution
