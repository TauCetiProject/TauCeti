/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon (claude+codex), Axel Delaval, Chunlei Liu,
Jinxuan Chen, Wanxu Yang, Zekun Sheng, Yuxuan Liao, Jie Xu
-/
module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import TauCeti.Geometry.Manifold.Riemannian.Distance

/-!
# Metric variation is bounded by Riemannian path length

For a `C¹` curve, each ambient metric chord is bounded by the Riemannian
length of the corresponding curve segment. Summing over a finite monotone
partition and using `Manifold.pathELength_add` shows that the metric total
variation is bounded by `Manifold.pathELength`.

This comparison is one half of the bridge between Mathlib's general metric
variation API and its canonical Riemannian path-length API.

## Provenance

Adapted from
`DoCarmoLib/Riemannian/Geodesic/HopfRinow/EVariationLePathELength.lean`
in the Poincare-Conjecture development at revision
`e6bc8cb66a83e50afa2b4507db664c9370bd4ac4`. The source states the total
variation result on `[0, 1]`; this version works on any ordered compact
interval.
-/

public section

namespace Manifold

open Bundle Set
open scoped ContDiff Manifold

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

/-- The ambient distance between two points of a `C¹` curve is bounded by
the curve's Riemannian length on that parameter interval. -/
theorem edist_le_pathELength_of_contMDiffOn {gamma : ℝ → M} {a b : ℝ}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc a b)) (hab : a ≤ b) :
    edist (gamma a) (gamma b) ≤ pathELength I gamma a b := by
  rw [IsRiemannianManifold.out (I := I) (gamma a) (gamma b)]
  exact riemannianEDist_le_pathELength hgamma rfl rfl hab

/-- The metric total variation of a `C¹` curve on a compact interval is
bounded by its Riemannian path length. -/
theorem eVariationOn_le_pathELength {gamma : ℝ → M} {a b : ℝ}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc a b)) :
    eVariationOn gamma (Icc a b) ≤ pathELength I gamma a b := by
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  have hsegment : ∀ i, edist (gamma (u (i + 1))) (gamma (u i)) ≤
      pathELength I gamma (u i) (u (i + 1)) := by
    intro i
    rw [edist_comm]
    exact edist_le_pathELength_of_contMDiffOn
      (hgamma.mono (Icc_subset_Icc (hus i).1 (hus (i + 1)).2))
      (hu (Nat.le_succ i))
  have htelescoping : ∀ m, ∑ i ∈ Finset.range m,
      pathELength I gamma (u i) (u (i + 1)) =
        pathELength I gamma (u 0) (u m) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih,
        pathELength_add (hu (Nat.zero_le k)) (hu (Nat.le_succ k))]
  calc
    ∑ i ∈ Finset.range n, edist (gamma (u (i + 1))) (gamma (u i))
        ≤ ∑ i ∈ Finset.range n, pathELength I gamma (u i) (u (i + 1)) :=
      Finset.sum_le_sum fun i _ ↦ hsegment i
    _ = pathELength I gamma (u 0) (u n) := htelescoping n
    _ ≤ pathELength I gamma a b := pathELength_mono (hus 0).1 (hus n).2

end

end Manifold
