/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Topology.MetricSpace.GromovHausdorff.Basic
public import TauCeti.Topology.MetricSpace.Length.Proper
import TauCeti.Topology.MetricSpace.Length.CompactLimit

/-!
# Length structure of Gromov–Hausdorff limits

Compact Gromov–Hausdorff limits of length spaces are geodesic spaces. The optimal
Gromov–Hausdorff realizations transfer minimizing curves to approximate curves in the target;
compactness gives a distance-preserving limit and hence a native geodesic segment.

## References

* D. Burago, Y. Burago and S. Ivanov, *A Course in Metric Geometry*, §7.5.
* Public formalization references:
  [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
  [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set Filter Metric
open scoped Topology

namespace Filter.Tendsto

open TauCeti

/-- A compact Gromov–Hausdorff limit of compact length spaces is geodesic. -/
theorem isGeodesicSpace_of_ghDist
    {X : ℕ → Type*} [∀ n, MetricSpace (X n)] [∀ n, CompactSpace (X n)]
    [∀ n, Nonempty (X n)] [∀ n, IsLengthSpace (X n)]
    {Y : Type*} [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (h : Tendsto (fun n ↦ GromovHausdorff.ghDist (X n) Y) atTop (𝓝 0)) :
    IsGeodesicSpace Y := by
  classical
  let (n : ℕ) : IsGeodesicSpace (X n) := isGeodesicSpace_of_properSpace
  let δ : ℕ → ℝ := fun n ↦ GromovHausdorff.ghDist (X n) Y + 1 / ((n : ℝ) + 1)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [add_zero] using h.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h2 : Tendsto (fun n ↦ 2 * δ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using hδ.const_mul 2
  have happ (n : ℕ) : ∃ f : X n → Y,
      (∀ x y, |dist (f x) (f y) - dist x y| < 2 * δ n) ∧
        ∀ y, ∃ x, dist (f x) y < 2 * δ n :=
    TauCeti.exists_approximation_of_ghDist_lt
    (X := X n) (Y := Y) (lt_add_of_pos_right _ (by positivity : 0 < 1 / ((n : ℝ) + 1)))
  choose f hfdist hfcover using happ
  constructor
  intro x y
  choose a ha using fun n ↦ hfcover n x
  choose b hb using fun n ↦ hfcover n y
  have ha' : Tendsto (fun n ↦ f n (a n)) atTop (𝓝 x) :=
    tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero (fun _ ↦ dist_nonneg)
      (fun n ↦ (ha n).le) h2
  have hb' : Tendsto (fun n ↦ f n (b n)) atTop (𝓝 y) :=
    tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero (fun _ ↦ dist_nonneg)
      (fun n ↦ (hb n).le) h2
  have hd : Tendsto (fun n ↦ dist (a n) (b n)) atTop (𝓝 (dist x y)) := by
    have he : Tendsto (fun n ↦ dist (a n) (b n) - dist (f n (a n)) (f n (b n)))
        atTop (𝓝 0) := by
      have hbnd : ∀ n, ‖dist (a n) (b n) - dist (f n (a n)) (f n (b n))‖ ≤ 2 * δ n := by
        intro n
        simpa only [Real.norm_eq_abs, abs_sub_comm] using (hfdist n (a n) (b n)).le
      exact squeeze_zero_norm hbnd h2
    simpa only [zero_add, sub_add_cancel] using he.add (ha'.dist hb')
  choose γ hγ using fun n ↦ IsGeodesicSpace.exists_isGeodesicSegment (a n) (b n)
  apply exists_isGeodesicSegment_of_tendsto_dist (fun n t ↦ f n (γ n t))
    (by simpa only [(hγ _).source] using ha') (by simpa only [(hγ _).target] using hb')
  intro s hs t ht
  have he : Tendsto (fun n ↦ dist (f n (γ n s)) (f n (γ n t)) -
      dist (γ n s) (γ n t)) atTop (𝓝 0) := by
    have hbnd : ∀ n, ‖dist (f n (γ n s)) (f n (γ n t)) - dist (γ n s) (γ n t)‖ ≤
        2 * δ n := by
      intro n
      simpa only [Real.norm_eq_abs] using (hfdist n (γ n s) (γ n t)).le
    exact squeeze_zero_norm hbnd h2
  simpa only [zero_add, sub_add_cancel, (hγ _).dist_eq s hs t ht] using
    he.add (hd.const_mul |s - t|)

end Filter.Tendsto

namespace TauCeti

open GromovHausdorff

/-- The compact length spaces form a closed subset of the Gromov–Hausdorff space. -/
theorem isClosed_setOf_isLengthSpace_ghSpace :
    IsClosed {p : GHSpace | TauCeti.IsLengthSpace p.Rep} := by
  apply IsSeqClosed.isClosed
  intro u p hu hp
  let (n : ℕ) : TauCeti.IsLengthSpace (u n).Rep := hu n
  let : TauCeti.IsGeodesicSpace p.Rep := Filter.Tendsto.isGeodesicSpace_of_ghDist
    (X := fun n ↦ (u n).Rep) (Y := p.Rep) (by
      simpa only [← dist_ghDist] using tendsto_iff_dist_tendsto_zero.mp hp)
  infer_instance

end TauCeti
