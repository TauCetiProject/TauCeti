/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.FixedPoints
import TauCeti.Geometry.Manifold.GroupAction.FixedTangentSubspace
import TauCeti.Geometry.Manifold.Riemannian.Invariant
import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Connected components of the fixed set of a group of isometries

Let a group `K` act on a Riemannian manifold `M` by smooth isometries. The results for such `K`
need no topology or Lie group structure on `K`. Around each point `p` of the common fixed set
`M^K`, the Riemannian logarithm at `p` flattens `M^K` onto the linear subspace `V_p ⊆ T_p M` of
vectors fixed by the differentials at `p` (`TauCeti.exists_isSliceChart_fixedPoints`). So every
neighbourhood of `p` contains an open neighbourhood `W` with

`W ∩ M^K = exp_p (B ∩ V_p)`

for a small ball `B` around the origin of `T_p M`, and `B ∩ V_p` is convex. This file draws the
topological consequences for `M^K`:

* `M^K` is locally connected (`TauCeti.locallyConnectedSpace_fixedPoints`), since the sets
  `exp_p (B ∩ V_p)` are connected;
* when `M` is compact, `M^K` has finitely many connected components
  (`TauCeti.finite_connectedComponents_fixedPoints`), since it is closed, hence compact, and
  locally connected;
* a function whose differential vanishes at every point of `M^K` is locally constant on `M^K`
  (`TauCeti.isLocallyConstant_domRestrict_fixedPoints`), hence constant on each connected component
  of `M^K`. Along `exp_p (B ∩ V_p)` it is constant by the mean value inequality on the convex set
  `B ∩ V_p`, since the differential of its composite with `exp_p` vanishes there.

The last statement applies to the components of a moment map, whose differentials vanish at the
fixed points of the group. Different components of `M^K` may have different dimensions, and
neither completeness of the metric nor compactness of `K` is used for these results.

A compact Hausdorff topological group `G` that is a smooth manifold and acts smoothly on a
σ-compact `M` preserves a smooth Riemannian metric, the Haar average of any smooth metric
(`TauCeti.of_forall_riemannianBundle_inner_mfderiv`). So the same conclusions hold for its fixed
set `M^G`, without a metric given in advance: a function with zero differential along `M^G` is
locally constant on `M^G`
(`TauCeti.isLocallyConstant_domRestrict_fixedPoints_of_compactSpace`), and for compact `M` the set
`M^G` has finitely many connected components
(`TauCeti.finite_connectedComponents_fixedPoints_of_compactSpace`).

## Main results

* `TauCeti.isLocallyConstant_domRestrict_fixedPoints`: a function with zero differential at every
  point of `M^K` is locally constant on `M^K`.
* `TauCeti.locallyConnectedSpace_fixedPoints`: `M^K` is locally connected.
* `TauCeti.finite_connectedComponents_fixedPoints`: for compact `M`, `M^K` has finitely many
  connected components.
* `TauCeti.isLocallyConstant_domRestrict_fixedPoints_of_compactSpace`,
  `TauCeti.finite_connectedComponents_fixedPoints_of_compactSpace`: the same for the fixed set of a
  compact group acting smoothly on a σ-compact manifold, with no metric given in advance.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Homework 21, exercise 2, and Theorem 27.1 (the fixed components of a torus
  action, finitely many on a compact manifold).
* S. Kobayashi, *Fixed points of isometries*, Nagoya Mathematical Journal 13 (1958), 63–68.
-/

public section

open Bundle Manifold Set MulAction Filter Topology
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ### Groups acting by isometries -/

section Isometry

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {K : Type*} [Group K] [MulAction K M] [ContMDiffConstSMul I ∞ K M]
  (hK : ∀ (k : K) (x : M) (u w : TangentSpace I x),
    inner ℝ (mfderiv I I (k • ·) x u) (mfderiv I I (k • ·) x w) = inner ℝ u w)

include hK

/-- Inside every neighbourhood `N` of a point `p` of the fixed set there is an open neighbourhood
`W` of `p` whose intersection with the fixed set is the image, under the inverse of a chart centred
at `p`, of a convex set of the chart's target containing the origin, on which that inverse is
differentiable. -/
private theorem exists_inter_fixedPoints_eq_image {p : M} (hp : p ∈ fixedPoints K M)
    {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ (e : OpenPartialHomeomorph M (TangentSpace I p)) (W : Set M)
      (s : Set (TangentSpace I p)), IsOpen W ∧ p ∈ W ∧ W ⊆ N ∧ Convex ℝ s ∧ s ⊆ e.target ∧
        (∀ w ∈ s, MDifferentiableAt 𝓘(ℝ, TangentSpace I p) I e.symm w) ∧ e.symm 0 = p ∧
        (0 : TangentSpace I p) ∈ s ∧ W ∩ fixedPoints K M = e.symm '' s := by
  obtain ⟨φ, hpφ, hφp, -, hφ⟩ := exists_isSliceChart_fixedPoints hK hp
  set e := φ.toOpenPartialHomeomorph
  have he : ∀ y ∈ e.source, (y ∈ fixedPoints K M ↔ e y ∈ fixedTangentSubspace I K p) :=
    fun y hy ↦ (isSliceChart_iff.1 hφ y hy).trans
      (mem_fixedTangentSubspace_iff_of_mem_fixedPoints hp).symm
  have hp' : p ∈ e.source := hpφ
  have hep : e p = 0 := hφp
  have hsymm : e.symm 0 = p := by rw [← hep, e.left_inv hp']
  -- A ball around the origin inside the target which `e.symm` maps into `N`.
  have hN' : e.target ∩ e.symm ⁻¹' N ∈ 𝓝 (0 : TangentSpace I p) := by
    have h0 : (0 : TangentSpace I p) ∈ e.target := hep ▸ e.map_source hp'
    exact inter_mem (e.open_target.mem_nhds h0)
      (e.continuousAt_symm h0 (by rwa [hsymm]))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hN'
  refine ⟨e, e.source ∩ e ⁻¹' Metric.ball 0 ε,
    Metric.ball 0 ε ∩ fixedTangentSubspace I K p,
    e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball,
    ⟨hp', by simpa [hep] using hε⟩, fun y hy ↦ ?_,
    (convex_ball 0 ε).inter (fixedTangentSubspace I K p).convex,
    fun w hw ↦ (hball hw.1).1, fun w hw ↦ φ.symm.mdifferentiableAt (by simp) (hball hw.1).1,
    hsymm, ⟨Metric.mem_ball_self hε, zero_mem _⟩, ?_⟩
  · simpa [e.left_inv hy.1] using (hball hy.2).2
  · ext y
    constructor
    · rintro ⟨⟨hy, hyε⟩, hyK⟩
      exact ⟨e y, ⟨hyε, (he y hy).1 hyK⟩, e.left_inv hy⟩
    · rintro ⟨w, ⟨hwε, hwV⟩, rfl⟩
      have hw : w ∈ e.target := (hball hwε).1
      have hy : e.symm w ∈ e.source := e.map_target hw
      refine ⟨⟨hy, by simpa [e.right_inv hw] using hwε⟩, (he _ hy).2 ?_⟩
      rwa [e.right_inv hw]

/-- **Functions with zero differential on the fixed set are locally constant there.** For a group
acting by isometries, a function whose differential vanishes at every point of the fixed set `M^K`
is locally constant on `M^K`, so it is constant on each connected component of `M^K`. -/
theorem isLocallyConstant_domRestrict_fixedPoints {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : M → F} (hf : ∀ x ∈ fixedPoints K M, HasMFDerivAt I 𝓘(ℝ, F) f x 0) :
    IsLocallyConstant ((fixedPoints K M).domRestrict f) := by
  refine IsLocallyConstant.iff_eventually_eq _ |>.2 fun ⟨p, hp⟩ ↦ ?_
  obtain ⟨e, W, s, hWo, hpW, -, hs, -, hes, he0, h0s, hWs⟩ :=
    exists_inter_fixedPoints_eq_image hK hp univ_mem
  -- The composite `f ∘ exp_p` has zero derivative on the convex set `s`, so it is constant there.
  have hderiv : ∀ w ∈ s, HasFDerivWithinAt (f ∘ e.symm) (0 : TangentSpace I p →L[ℝ] F) s w := by
    intro w hw
    have hfix : e.symm w ∈ fixedPoints K M := (hWs.symm ▸ mem_image_of_mem _ hw).2
    have := (hf _ hfix).comp w (hes w hw).hasMFDerivAt
    rw [ContinuousLinearMap.zero_comp] at this
    exact (hasMFDerivAt_iff_hasFDerivAt.1 this).hasFDerivWithinAt
  have hconst : ∀ w ∈ s, f (e.symm w) = f p := fun w hw ↦ by
    have := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le (C := 0) hderiv
      (fun _ _ ↦ by simp) h0s hw
    rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at this
    simpa [he0] using this
  filter_upwards [continuous_subtypeVal.continuousAt.preimage_mem_nhds (hWo.mem_nhds hpW)]
    with ⟨y, hy⟩ hyW
  obtain ⟨w, hw, rfl⟩ : y ∈ e.symm '' s := hWs ▸ ⟨hyW, hy⟩
  simpa using hconst w hw

/-- **The fixed set of a group of isometries is locally connected.** Every point `p` of the fixed
set has arbitrarily small open neighbourhoods in it which are images of convex sets of tangent
vectors under the exponential map at `p`. -/
theorem locallyConnectedSpace_fixedPoints : LocallyConnectedSpace (fixedPoints K M) := by
  refine locallyConnectedSpace_iff_subsets_isOpen_isConnected (α := fixedPoints K M) |>.2
    fun ⟨p, hp⟩ U hU ↦ ?_
  obtain ⟨N, hN, hNU⟩ := (mem_nhds_subtype _ _ _).1 hU
  obtain ⟨e, W, s, hWo, hpW, hWN, hs, hse, -, -, -, hWs⟩ :=
    exists_inter_fixedPoints_eq_image hK hp hN
  refine ⟨Subtype.val ⁻¹' W, fun y hy ↦ hNU (hWN hy), hWo.preimage continuous_subtypeVal,
    hpW, ⟨⟨p, hp⟩, hpW⟩, ?_⟩
  -- The image of this neighbourhood in `M` is the image of the convex set `s` under `exp_p`.
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, image_preimage_eq_inter_range,
    Subtype.range_coe, hWs]
  exact hs.isPreconnected.image _ (e.continuousOn_symm.mono hse)

/-- **The fixed set of a group of isometries of a compact manifold has finitely many connected
components.** It is closed, hence compact, and locally connected. -/
theorem finite_connectedComponents_fixedPoints [CompactSpace M] :
    Finite (ConnectedComponents (fixedPoints K M)) := by
  have := ContMDiffConstSMul.continuousConstSMul (I := I) (Γ := K) (M := M) ∞
  have := locallyConnectedSpace_fixedPoints hK
  have : CompactSpace (fixedPoints K M) :=
    isCompact_iff_compactSpace.1 (isClosed_fixedPoints_of_continuousConstSMul (M := K)).isCompact
  infer_instance

end Isometry

/-! ### Compact groups acting smoothly -/

section Compact

variable [SigmaCompactSpace M] {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  {HG : Type*} [TopologicalSpace HG] (IG : ModelWithCorners ℝ EG HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [ChartedSpace HG G] [IsManifold IG ∞ G] [MulAction G M] [ContMDiffSMul IG I ∞ G M]

include IG

/-- **Functions with zero differential on the fixed set of a compact group are locally constant
there.** For a smooth action of a compact group on a σ-compact manifold, a function whose
differential vanishes at every point of the fixed set `M^G` is locally constant on `M^G`. -/
theorem isLocallyConstant_domRestrict_fixedPoints_of_compactSpace {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : M → F}
    (hf : ∀ x ∈ fixedPoints G M, HasMFDerivAt I 𝓘(ℝ, F) f x 0) :
    IsLocallyConstant ((fixedPoints G M).domRestrict f) :=
  have : ContMDiffConstSMul I ∞ G M := ContMDiffSMul.contMDiffConstSMul IG
  of_forall_riemannianBundle_inner_mfderiv IG G fun hG ↦
    isLocallyConstant_domRestrict_fixedPoints hG hf

variable (I G) in
include I in
/-- **The fixed set of a compact group acting on a compact manifold has finitely many connected
components.** -/
theorem finite_connectedComponents_fixedPoints_of_compactSpace [CompactSpace M] :
    Finite (ConnectedComponents (fixedPoints G M)) :=
  have : ContMDiffConstSMul I ∞ G M := ContMDiffSMul.contMDiffConstSMul IG
  of_forall_riemannianBundle_inner_mfderiv (I := I) IG G fun hG ↦
    finite_connectedComponents_fixedPoints hG

end Compact

end TauCeti
