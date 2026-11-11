/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.SectionTopology

/-!
# Finite-order section topologies on smooth metrics

The space of smooth metrics can carry a finite-order topology without changing its carrier.
`Bundle.ContMDiffRiemannianMetric.frameCkTopology` is the topology induced by forgetting
regularity to `C^k` and using the compact derivative topology on symmetric tensor sections.
Thus only derivatives through order `k` are controlled, although every metric remains smooth.

This construction allows models with corners, in particular half-space models for compact
manifolds with boundary. It does not apply a completeness theorem for boundaryless section
spaces to a manifold with boundary. The continuity and convergence criteria use the existing
frame-coordinate jets and their compact derivative seminorms, including at boundary points.
Covering smooth frames give the same topology. Convex interpolation is continuous, and the
smooth section topology is finer than each finite-order topology.

These topologies provide the finite-order neighbourhoods needed to measure perturbations of
metrics on collared cylinders and bordisms. They concern the metric tensor, not its scalar
curvature.

## References

* M. Hirsch, *Differential Topology*, GTM 33, Chapter 2, §1, for compact derivative topologies.
* R. Hamilton, *The inverse function theorem of Nash and Moser*, Part I, Example 1.1.5,
  for the section-space description of spaces of metrics.
-/

public noncomputable section

open Bundle Set Filter Topology TopologicalSpace TauCeti
open scoped ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]
  {ι : Type*}
  (e : ι → Trivialization (symmetricBilinearMaps ℝ F ℝ)
    (π (symmetricBilinearMaps ℝ F ℝ) (fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ)))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens B) (hU : ∀ i, (U i : Set B) ⊆ (e i).baseSet)

variable (IB) in
/-- The compact `C^k` topology on the fixed smooth-metric carrier, induced by the
section-space topology on `C^k` metrics. Models with corners are allowed. -/
@[instance_reducible]
def frameCkTopology (k : ℕ) : TopologicalSpace (ContMDiffRiemannianMetric IB ∞ F V) :=
  .induced (fun g : ContMDiffRiemannianMetric IB ∞ F V ↦ g.ofLE (n := ∞) (m := k) (by simp))
    (frameTopology IB k e U hU)

/-- Forgetting regularity embeds smooth metrics with their `C^k` topology into `C^k` metrics
with the section-space topology. -/
theorem isEmbedding_ofLE_frameCkTopology (k : ℕ) :
    let _ := frameTopology IB k e U hU
    let _ := frameCkTopology IB e U hU k
    IsEmbedding (fun g : ContMDiffRiemannianMetric IB ∞ F V ↦ g.ofLE (m := k) (by simp)) := by
  let _ := frameTopology IB k e U hU
  let _ := frameCkTopology IB e U hU k
  refine ⟨.induced _, fun g g' h ↦ ?_⟩
  ext x v w
  simpa only [ofLE_inner] using
    congrArg (fun G : ContMDiffRiemannianMetric IB k F V ↦ G.inner x v w) h

-- Forgetting regularity changes neither the tensor nor its coordinate derivatives. This
-- comparison is used to put every finite-order criterion on the same smooth-section carrier.
private theorem frameCoordinateJet_ofLE (k : ℕ)
    (g : ContMDiffRiemannianMetric IB ∞ F V) (i : ι) (x : U i)
    (m : ℕ) (hm : m ≤ (k : ℕ∞ω)) :
    ContMDiffMap.chartIteratedFDeriv
      ((e i).frameCoordinates (hU i) (g.ofLE (m := k) (by simp)).toSymmetricSection) x m hm =
    ContMDiffMap.chartIteratedFDeriv
      ((e i).frameCoordinates (hU i) g.toSymmetricSection) x m (by simp) := by
  have hc : ⇑((e i).frameCoordinates (hU i)
      (g.ofLE (m := k) (by simp)).toSymmetricSection) =
      ⇑((e i).frameCoordinates (hU i) g.toSymmetricSection) := by
    funext y
    have hs : (g.ofLE (m := k) (by simp)).toSymmetricSection y =
        g.toSymmetricSection y := by
      apply Subtype.ext
      simp
    simp only [Trivialization.frameCoordinates_apply, hs]
  ext z
  simp only [ContMDiffMap.chartIteratedFDeriv_self_target_apply, hc]

/-- A smooth metric family is `C^k`-continuous exactly when the frame-coordinate derivatives
of its symmetric tensor through order `k` are continuous in the compact-open topology. -/
theorem continuous_frameCkTopology_iff (k : ℕ) {P : Type*} [TopologicalSpace P]
    {g : P → ContMDiffRiemannianMetric IB ∞ F V} :
    let _ := frameCkTopology IB e U hU k
    Continuous g ↔ ∀ (i : ι) (x : U i) (m : ℕ) (_hm : m ≤ (k : ℕ∞ω)),
      Continuous (fun p ↦ ContMDiffMap.chartIteratedFDeriv
        ((e i).frameCoordinates (hU i) (g p).toSymmetricSection)
        x m (by simp)) := by
  dsimp only
  let _ := ContMDiffSection.frameTopology (I := IB) (n := k) e U hU
  let _ := frameTopology IB k e U hU
  let _ := frameCkTopology IB e U hU k
  have hc := ((isEmbedding_ofLE_frameCkTopology e U hU k).isInducing.continuous_iff
    (f := g)).trans ((continuous_frameTopology_iff e U hU).trans
      (ContMDiffSection.continuous_frameTopology_iff e U hU))
  simpa only [Function.comp_apply, frameCoordinateJet_ofLE] using hc

/-- Convergence in the `C^k` topology means that every compact frame derivative seminorm,
of order at most `k`, of the difference of the symmetric tensors tends to zero. -/
theorem tendsto_frameCkTopology_iff (k : ℕ) {P : Type*} {l : Filter P}
    {g : P → ContMDiffRiemannianMetric IB ∞ F V}
    {g₀ : ContMDiffRiemannianMetric IB ∞ F V} :
    let _ := frameCkTopology IB e U hU k
    Tendsto g l (𝓝 g₀) ↔ ∀ (i : ι) (x : U i)
      (K : Compacts (extChartAt IB x).target) (m : ℕ) (hm : m ≤ (k : ℕ∞ω)),
      Tendsto (fun p ↦ (e i).chartDerivativeSeminorm (hU i) x K m hm
        (((g p).ofLE (m := k) (by simp)).toSymmetricSection -
          (g₀.ofLE (m := k) (by simp)).toSymmetricSection)) l (𝓝 0) := by
  dsimp only
  let _ := ContMDiffSection.frameTopology (I := IB) (n := k) e U hU
  let _ := frameTopology IB k e U hU
  let _ := frameCkTopology IB e U hU k
  exact (isEmbedding_ofLE_frameCkTopology e U hU k).isInducing.tendsto_nhds_iff.trans
    ((tendsto_frameTopology_iff e U hU).trans
      (ContMDiffSection.tendsto_frameTopology_iff e U hU))

/-- The finite-order topology on smooth metrics is independent of the covering smooth frames,
also for manifolds with boundary. -/
theorem frameCkTopology_eq_of_covers [LocallyCompactSpace EB] (k : ℕ)
    (hcover : ∀ x, ∃ i, x ∈ U i)
    {κ : Type*}
    (e' : κ → Trivialization (symmetricBilinearMaps ℝ F ℝ)
      (π (symmetricBilinearMaps ℝ F ℝ) (fun x ↦ symmetricBilinearMaps ℝ (V x) ℝ)))
    [∀ j, MemTrivializationAtlas (e' j)]
    (U' : κ → Opens B) (hU' : ∀ j, (U' j : Set B) ⊆ (e' j).baseSet)
    (hcover' : ∀ x, ∃ j, x ∈ U' j) :
    frameCkTopology IB e U hU k = frameCkTopology IB e' U' hU' k := by
  unfold frameCkTopology
  rw [frameTopology_eq_of_covers e U hU hcover e' U' hU' hcover']

/-- Covering frames make the finite-order topology on smooth metrics Hausdorff. -/
theorem t2Space_frameCkTopology (k : ℕ) (hcover : ∀ x, ∃ i, x ∈ U i) :
    let _ := frameCkTopology IB e U hU k
    T2Space (ContMDiffRiemannianMetric IB ∞ F V) := by
  let _ := frameTopology IB k e U hU
  let _ := t2Space_frameTopology (IB := IB) (n := k) e U hU hcover
  let _ := frameCkTopology IB e U hU k
  exact (isEmbedding_ofLE_frameCkTopology e U hU k).t2Space

/-- Increasing the number of controlled derivatives makes the topology finer. -/
theorem antitone_frameCkTopology : Antitone (frameCkTopology IB e U hU) := by
  intro k l hkl
  let _ := frameCkTopology IB e U hU l
  have hc := (continuous_frameCkTopology_iff (IB := IB) e U hU l (g := id)).mp continuous_id
  exact (continuous_id_iff_le (t := frameCkTopology IB e U hU l)
    (t' := frameCkTopology IB e U hU k)).mp <|
    (continuous_frameCkTopology_iff (IB := IB) e U hU k).mpr fun i x m hm ↦
      hc i x m (hm.trans (by exact_mod_cast hkl))

/-- The smooth section topology controls every finite-order topology on smooth metrics. -/
theorem frameTopology_le_frameCkTopology (k : ℕ) :
    frameTopology IB ∞ e U hU ≤ frameCkTopology IB e U hU k := by
  let _ := ContMDiffSection.frameTopology (I := IB) (n := ∞) e U hU
  let _ := frameTopology IB ∞ e U hU
  have hs := (isEmbedding_toSymmetricSection_frameTopology (IB := IB) (n := ∞)
    e U hU).continuous
  exact (continuous_id_iff_le (t := frameTopology IB ∞ e U hU)
    (t' := frameCkTopology IB e U hU k)).mp <|
    (continuous_frameCkTopology_iff (IB := IB) e U hU k).mpr fun i x m _ ↦
      (ContMDiffSection.continuous_frameJet_apply e U hU i x m (by simp)).comp hs

/-- Convex interpolation of smooth metrics is jointly continuous in every finite-order
topology, including at the endpoints of the interpolation interval. -/
theorem continuous_convexCombination_frameCkTopology [FiniteDimensional ℝ F] (k : ℕ) :
    let _ := frameCkTopology IB e U hU k
    Continuous (fun p : (ContMDiffRiemannianMetric IB ∞ F V ×
      ContMDiffRiemannianMetric IB ∞ F V) × unitInterval ↦
        p.1.1.convexCombination p.1.2 p.2) := by
  dsimp only
  let _ := frameTopology IB k e U hU
  let _ := frameCkTopology IB e U hU k
  have hi := isEmbedding_ofLE_frameCkTopology (IB := IB) e U hU k
  have hc := (continuous_convexCombination_frameTopology (IB := IB) (n := k) e U hU).comp
    (((hi.continuous.comp (continuous_fst.comp continuous_fst)).prodMk
      (hi.continuous.comp (continuous_snd.comp continuous_fst))).prodMk continuous_snd)
  apply hi.isInducing.continuous_iff.mpr
  refine hc.congr fun p ↦ ?_
  ext x v w
  simp only [Function.comp_apply, ofLE_inner, convexCombination_inner]

end Bundle.ContMDiffRiemannianMetric
