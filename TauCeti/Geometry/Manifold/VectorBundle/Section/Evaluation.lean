/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.FiniteAtlas
import TauCeti.Analysis.Calculus.ContDiff.OperatorFamily

/-!
# Evaluation on the Banach space of `C^k` sections is `C^k`

Let `V` be a smooth vector bundle with model fibre `F` over a boundaryless manifold `M` modelled
on a locally compact space over `ℝ` or `ℂ`, and give the `C^k` sections of `V` the norm of a finite
chart-frame atlas whose compact pieces have relative interiors covering `M`
(`ContMDiffSection.finiteAtlasNormedAddCommGroup`). This file proves that the evaluation map
`(s, x) ↦ s x`, with values in the total space of `V`, is `C^k` on the product of this normed space
with `M` (`ContMDiffSection.contMDiff_totalSpace_eval_finiteAtlas`). It is the bundle version of
`ContMDiffMap.contMDiff_eval_finiteAtlas` for vector-valued maps.

Near a point `x₀`, the evaluation map is read in the trivialization `e` of `V` at `x₀` and the
chart of `M` at `x₀`: its fibre component is `(s, w) ↦ e (s (φ⁻¹ w))`, where `φ` is the extended
chart. For each `w` in the chart target this is a continuous linear function of `s`, and its
derivatives in `w` of order at most `k` are bounded near each point of the chart target, uniformly
for `s` in the unit ball, because every compact chart-frame `C^k` seminorm is dominated by the
finite-atlas norm (`ContMDiffSection.exists_norm_iteratedFDeriv_frameCoordinates_le`). The joint
regularity theorem for pointwise smooth families of operators,
`TauCeti.contDiffOn_apply_of_forall_norm_iteratedFDeriv_le`, then gives joint `C^k` regularity in
the chart (`ContMDiffSection.contDiffOn_frameCoordinates_extChartAt_symm_finiteAtlas`).

Joint regularity of evaluation is what makes universal constructions over spaces of `C^k` sections
smooth. For the tangent bundle, it says that the family of all `C^k` vector fields, parametrized by
the Banach space of `C^k` vector fields, is jointly `C^k`, which is the hypothesis of the parametric
results on flows of families of vector fields.

## Main results

* `ContMDiffSection.contDiffOn_frameCoordinates_extChartAt_symm_finiteAtlas`: in a chart and a
  smooth trivialization, the frame coefficients `(s, w) ↦ e (s (φ⁻¹ w))` are jointly `C^k`.
* `ContMDiffSection.contMDiff_totalSpace_eval_finiteAtlas`: evaluation is `C^k` for the
  finite-atlas `C^k` norm.

## References

* R. Abraham and J. Robbin, *Transversal mappings and flows*, W. A. Benjamin, 1967, Chapter II
  (the evaluation map of a space of `C^k` sections is `C^k`).
-/

public section

noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff

namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  [IsRCLikeNormedField 𝕜] [I.Boundaryless] [LocallyCompactSpace E]
  (k : ℕ) [ContMDiffVectorBundle k F V I] [IsManifold I k M]
  {ι : Type*} [Fintype ι]
  (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
  {c : ∀ i, U i} {K : ∀ i, Compacts (extChartAt I (c i)).target}
  (hK : ∀ y : M, ∃ i, ∃ hyU : y ∈ U i,
    ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt I (c i)).source,
      (⟨extChartAt I (c i) ⟨y, hyU⟩, (extChartAt I (c i)).map_source hy⟩ :
        (extChartAt I (c i)).target) ∈ interior (K i : Set (extChartAt I (c i)).target))

include hK in
/-- **Frame coefficients are jointly `C^k` in charts.** Give the `C^k` sections of `V` the norm of
a finite chart-frame atlas whose compact pieces have relative interiors covering `M`. For any smooth
trivialization `e'` on an open set `U'` and any point `x` of `U'`, the frame coefficients
`(s, w) ↦ e' (s (φ⁻¹ w))` of sections, read in the extended chart `φ` of `U'` at `x`, are `C^k` on
the product of this normed space with the chart target. -/
theorem contDiffOn_frameCoordinates_extChartAt_symm_finiteAtlas
    (e' : Trivialization F (π F V)) [MemTrivializationAtlas e'] {U' : Opens M}
    (hU' : (U' : Set M) ⊆ e'.baseSet) (x : U') :
    letI := finiteAtlasNormedAddCommGroup (𝕜 := 𝕜) k e U hU hK
    letI := finiteAtlasNormedSpace (𝕜 := 𝕜) k e U hU hK
    ContDiffOn 𝕜 k
      (fun p : Cₛ^k⟮I; F, V⟯ × E ↦ e'.frameCoordinates hU' p.1 ((extChartAt I x).symm p.2))
      (univ ×ˢ (extChartAt I x).target) := by
  let := finiteAtlasNormedAddCommGroup (𝕜 := 𝕜) k e U hU hK
  let := finiteAtlasNormedSpace (𝕜 := 𝕜) k e U hU hK
  classical
  set φ := extChartAt I x
  have hφt : IsOpen φ.target := isOpen_extChartAt_target x
  -- Evaluation of the frame coefficients at the points of the chart, as linear maps.
  let L (w : E) : Cₛ^k⟮I; F, V⟯ →ₗ[𝕜] F :=
    { toFun := fun s ↦ e'.frameCoordinates hU' s (φ.symm w)
      map_add' := fun s t ↦ by simp only [map_add, ContMDiffMap.coe_add, Pi.add_apply]
      map_smul' := fun a s ↦ by
        simp only [map_smul, ContMDiffMap.coe_smul, Pi.smul_apply, RingHom.id_apply] }
  -- Their derivatives in the chart are bounded near each point, uniformly on the unit ball.
  have hbd (m : ℕ) (hm : m ≤ k) (w₀ : E) (hw₀ : w₀ ∈ φ.target) : ∃ C, ∀ᶠ z in 𝓝 w₀,
      ∀ s : Cₛ^k⟮I; F, V⟯, ‖iteratedFDeriv 𝕜 m (fun w ↦ L w s) z‖ ≤ C * ‖s‖ := by
    obtain ⟨C, hC⟩ :=
      exists_norm_iteratedFDeriv_frameCoordinates_le e U hU hK e' hU' x hw₀ k le_rfl hm
    exact ⟨C, hC.mono fun z hz s ↦ (norm_finiteAtlas k e U hU hK s).symm ▸ hz s⟩
  -- On the chart target they are continuous; outside it, replace them by `0`.
  let Φ (w : E) : Cₛ^k⟮I; F, V⟯ →L[𝕜] F :=
    if hw : w ∈ φ.target then
      (L w).mkContinuousOfExistsBound <| (hbd 0 (Nat.zero_le k) w hw).imp fun C hC s ↦ by
        simpa only [norm_iteratedFDeriv_zero] using hC.self_of_nhds s
    else 0
  have hΦ (w : E) (hw : w ∈ φ.target) (s : Cₛ^k⟮I; F, V⟯) : Φ w s = L w s := by
    simp only [Φ, hw, dite_true, LinearMap.mkContinuousOfExistsBound_apply]
  have hbdΦ : ∀ m ≤ k, ∀ w₀ ∈ φ.target, ∃ C, ∀ᶠ z in 𝓝 w₀, ∀ s : Cₛ^k⟮I; F, V⟯,
      ‖iteratedFDeriv 𝕜 m (fun w ↦ Φ w s) z‖ ≤ C * ‖s‖ := fun m hm w₀ hw₀ ↦ by
    obtain ⟨C, hC⟩ := hbd m hm w₀ hw₀
    refine ⟨C, ?_⟩
    filter_upwards [hC, hφt.mem_nhds hw₀] with z hz hzt s
    have hΦL : (fun w ↦ Φ w s) =ᶠ[𝓝 z] fun w ↦ L w s := by
      filter_upwards [hφt.mem_nhds hzt] with w hw using hΦ w hw s
    rw [(hΦL.iteratedFDeriv 𝕜 m).self_of_nhds]
    exact hz s
  have hsmooth (s : Cₛ^k⟮I; F, V⟯) : ContDiffOn 𝕜 k (fun w ↦ Φ w s) φ.target :=
    (((e'.frameCoordinates hU' s).contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt_symm x)).contDiffOn).congr fun w hw ↦ hΦ w hw s
  exact (TauCeti.contDiffOn_apply_of_forall_norm_iteratedFDeriv_le hφt hsmooth hbdΦ).congr
    fun p hp ↦ (hΦ p.2 hp.2 p.1).symm

include hK in
/-- **Evaluation is `C^k`.** Let `V` be a smooth vector bundle over a boundaryless manifold `M`
modelled on a locally compact space, and give the `C^k` sections of `V` the norm of a finite
chart-frame atlas whose compact pieces have relative interiors covering `M`. Then the evaluation
map `(s, x) ↦ s x`, with values in the total space of `V`, is `C^k` on the product of this normed
space with `M`. -/
theorem contMDiff_totalSpace_eval_finiteAtlas :
    letI := finiteAtlasNormedAddCommGroup (𝕜 := 𝕜) k e U hU hK
    letI := finiteAtlasNormedSpace (𝕜 := 𝕜) k e U hU hK
    ContMDiff (𝓘(𝕜, Cₛ^k⟮I; F, V⟯).prod I) (I.prod 𝓘(𝕜, F)) k
      (fun p : Cₛ^k⟮I; F, V⟯ × M ↦ TotalSpace.mk' F p.2 (p.1 p.2)) := by
  let := finiteAtlasNormedAddCommGroup (𝕜 := 𝕜) k e U hU hK
  let := finiteAtlasNormedSpace (𝕜 := 𝕜) k e U hU hK
  rintro ⟨s₀, x₀⟩
  rw [contMDiffAt_totalSpace_iff]
  refine ⟨contMDiffAt_snd, ?_⟩
  -- Read the fibre component in the trivialization at `x₀`, on its base set `U'`.
  set e₀ := trivializationAt F V x₀
  let U' : Opens M := ⟨e₀.baseSet, e₀.open_baseSet⟩
  let x' : U' := ⟨x₀, mem_baseSet_trivializationAt F V x₀⟩
  set φ := extChartAt I x'
  have hx₀t : extChartAt I x₀ x₀ ∈ φ.target := by
    have h := mem_extChartAt_target (I := I) x'
    rwa [TopologicalSpace.Opens.extChartAt_apply] at h
  have hG : ContMDiffAt 𝓘(𝕜, Cₛ^k⟮I; F, V⟯ × E) 𝓘(𝕜, F) k
      (fun p : Cₛ^k⟮I; F, V⟯ × E ↦ e₀.frameCoordinates subset_rfl p.1 (φ.symm p.2))
      (s₀, extChartAt I x₀ x₀) :=
    ((contDiffOn_frameCoordinates_extChartAt_symm_finiteAtlas k e U hU hK e₀
      (U' := U') subset_rfl x').contDiffAt ((isOpen_univ.prod
        (isOpen_extChartAt_target x')).mem_nhds ⟨mem_univ s₀, hx₀t⟩)).contMDiffAt
  -- Near `(s₀, x₀)`, the fibre component is the composite of `(s, x) ↦ (s, φ x)` and `hG`.
  have hsnd : ContMDiffAt (𝓘(𝕜, Cₛ^k⟮I; F, V⟯).prod I) 𝓘(𝕜, E) k
      (fun p : Cₛ^k⟮I; F, V⟯ × M ↦ extChartAt I x₀ p.2) (s₀, x₀) :=
    contMDiffAt_extChartAt.comp (s₀, x₀) contMDiffAt_snd
  refine (hG.comp (s₀, x₀) (contMDiffAt_fst.prodMk_space hsnd)).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_univ.prod ((isOpen_extChartAt_source (I := I) x₀).inter
    e₀.open_baseSet)).mem_nhds
      ⟨mem_univ s₀, mem_extChartAt_source (I := I) x₀, mem_baseSet_trivializationAt F V x₀⟩]
    with p hp
  have hpt : extChartAt I x₀ p.2 ∈ φ.target := by
    rw [TopologicalSpace.Opens.extChartAt_target_eq]
    refine ⟨(extChartAt I x₀).map_source hp.2.1, ?_⟩
    rw [mem_preimage, (extChartAt I x₀).left_inv hp.2.1]
    exact hp.2.2
  have hsymm : (φ.symm (extChartAt I x₀ p.2) : M) = p.2 := by
    rw [TopologicalSpace.Opens.coe_extChartAt_symm_apply U' x' hpt]
    exact (extChartAt I x₀).left_inv hp.2.1
  simp only [Function.comp_apply, Trivialization.frameCoordinates_apply]
  exact congrArg (fun y ↦ (e₀ ⟨y, p.1 y⟩).2) hsymm.symm

end ContMDiffSection
