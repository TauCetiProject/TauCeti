/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.Topology.Homotopy.Path
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Relative smooth approximation with prescribed germs

A continuous map into a real normed space need not be smooth near the closed set where it is to
be fixed. If a separate smooth map agrees with it on that set, the approximation can be chosen
to agree with the smooth map on an entire neighbourhood. In particular, this lets one prescribe
collar data when smoothing a filling. The straight-line homotopy fixes the closed set and can
be kept in an open target region.

The convex selection argument uses Mathlib's `exists_contMDiffMap_forall_mem_convex_of_local`,
as in `Continuous.exists_contMDiff_approx_and_eqOn`.
-/

public section

open Filter Function Metric Set
open scoped ContDiff Manifold Topology

namespace Continuous

variable {E V H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] {f e : M → V} {ε : M → ℝ} {A O : Set M} {n : ℕ∞}

/-- A continuous map `f` can be approximated within a positive continuous tolerance by a `Cⁿ`
map that agrees near a closed set `A` with a prescribed `Cⁿ` germ `e`. It suffices that `e`
already fits the tolerance on `A`; in particular, it may agree with `f` there. -/
theorem exists_contMDiff_approx_eventuallyEq (hf : Continuous f) (hε : Continuous ε)
    (hεpos : ∀ x, 0 < ε x) (hA : IsClosed A) (hO : O ∈ 𝓝ˢ A)
    (he : ContMDiffOn I 𝓘(ℝ, V) n e O) (hef : ∀ x ∈ A, dist (e x) (f x) < ε x) :
    ∃ g : C^n⟮I, M; 𝓘(ℝ, V), V⟯, (∀ x, dist (g x) (f x) < ε x) ∧
      (∀ᶠ x in 𝓝ˢ A, g x = e x) := by
  let : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  -- Shrink the region where the prescribed germ is used to where it fits the tolerance.
  let U := interior O ∩ {x | dist (e x) (f x) < ε x}
  have hdist : ContinuousOn (fun x ↦ dist (e x) (f x)) (interior O) :=
    continuous_dist.comp_continuousOn
      ((he.continuousOn.mono interior_subset).prodMk hf.continuousOn)
  have hU : IsOpen U :=
    (hdist.prodMk hε.continuousOn).isOpen_inter_preimage isOpen_interior isOpen_lt_prod
  have hAU : A ⊆ U := fun x hx ↦
    ⟨mem_interior_iff_mem_nhds.mpr (mem_nhdsSet_iff_forall.mp hO x hx), hef x hx⟩
  obtain ⟨W, hWopen, hAW, hWU⟩ := normal_exists_closure_subset hA hU hAU
  let S (x : M) := ball (f x) (ε x) ∩ {v : V | x ∈ closure W → v = e x}
  have hS (x : M) : Convex ℝ (S x) :=
    (convex_ball _ _).inter (convex_singleton (e x)).setOfPred_const_imp
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local I hS (n := n) (fun x ↦ by
    by_cases hx : x ∈ closure W
    · exact ⟨U, hU.mem_nhds (hWU hx), e, he.mono (inter_subset_left.trans interior_subset),
        fun y hy ↦ ⟨hy.2, fun _ ↦ rfl⟩⟩
    · have hnear := (continuous_const.dist hf).continuousAt.eventually_lt hε.continuousAt
          (by simpa using hεpos x : dist (f x) (f x) < ε x)
      have hgood : ∀ᶠ y in 𝓝 x, f x ∈ S y := by
        filter_upwards [hnear, isClosed_closure.isOpen_compl.eventually_mem hx] with y hy hyW
        exact ⟨hy, fun hy' ↦ (hyW hy').elim⟩
      exact ⟨_, hgood, fun _ ↦ f x, contMDiffOn_const, fun _ hy ↦ hy⟩)
  refine ⟨g, fun x ↦ (hg x).1, ?_⟩
  filter_upwards [hWopen.mem_nhdsSet.mpr hAW] with x hx using (hg x).2 (subset_closure hx)

end Continuous

namespace ContinuousMap

variable {E V H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] {e : M → V} {ε : M → ℝ} {A O : Set M} {n : ℕ∞}

/-- Relative approximation with prescribed germs admits a homotopy fixing `A`, staying within the
same tolerance as the approximation, and staying in any open set `B` containing the original
image. The homotopy is the straight-line interpolation. -/
theorem exists_contMDiff_approx_homotopyRel_eventuallyEq (f : C(M, V)) (hε : Continuous ε)
    (hεpos : ∀ x, 0 < ε x) (hA : IsClosed A) (hO : O ∈ 𝓝ˢ A)
    (he : ContMDiffOn I 𝓘(ℝ, V) n e O) (hef : EqOn e f A) {B : Set V} (hB : IsOpen B)
    (hfB : ∀ x, f x ∈ B) :
    ∃ g : C^n⟮I, M; 𝓘(ℝ, V), V⟯, (∀ᶠ x in 𝓝ˢ A, g x = e x) ∧
      ∃ F : f.HomotopyRel ⟨g, g.contMDiff.continuous⟩ A,
        ∀ t x, dist (F (t, x)) (f x) < ε x ∧ F (t, x) ∈ B := by
  have hradius : ∃ r : M → ℝ, Continuous r ∧ (∀ x, 0 < r x) ∧
      (∀ x, r x ≤ ε x) ∧ (∀ x, ball (f x) (r x) ⊆ B) := by
    rcases eq_or_ne B univ with rfl | hB'
    · exact ⟨ε, hε, hεpos, fun _ ↦ le_rfl, fun _ ↦ subset_univ _⟩
    let r (x : M) := min (ε x) (infDist (f x) Bᶜ)
    refine ⟨r, hε.min ((continuous_infDist_pt _).comp f.continuous), ?_,
      fun _ ↦ min_le_left _ _, fun x ↦ ?_⟩
    · exact fun x ↦ lt_min (hεpos x)
        ((hB.isClosed_compl.notMem_iff_infDist_pos (nonempty_compl.mpr hB')).mp
          (by simpa using hfB x))
    · exact (ball_subset_ball (min_le_right _ _)).trans ball_infDist_compl_subset
  obtain ⟨r, hr, hrpos, hrε, hrB⟩ := hradius
  obtain ⟨g, hg, hge⟩ := f.continuous.exists_contMDiff_approx_eventuallyEq hr hrpos hA hO he
    (fun x hx ↦ by simpa [hef hx] using hrpos x)
  let L (p : unitInterval × M) := AffineMap.lineMap (f p.2) (g p.2) (p.1 : ℝ)
  have hL : Continuous L := by
    simp only [L, AffineMap.lineMap_apply_module']
    exact ((continuous_subtypeVal.comp continuous_fst).smul
      ((g.contMDiff.continuous.comp continuous_snd).sub (f.continuous.comp continuous_snd))).add
        (f.continuous.comp continuous_snd)
  let F : f.HomotopyRel ⟨g, g.contMDiff.continuous⟩ A :=
    { toFun := L
      continuous_toFun := hL
      map_zero_left := fun x ↦ by simp [L]
      map_one_left := fun x ↦ by simp [L]
      prop' := fun t x hx ↦ by
        have heq := (hge.self_of_nhdsSet x hx).trans (hef hx)
        simp [L, heq] }
  refine ⟨g, hge, F, ?_⟩
  intro t x
  have hlt : dist (L (t, x)) (f x) < r x := by
    dsimp only [L]
    rw [dist_lineMap_left, Real.norm_of_nonneg t.property.1, dist_comm (f x) (g x)]
    exact (mul_le_of_le_one_left dist_nonneg t.property.2).trans_lt (hg x)
  exact ⟨hlt.trans_le (hrε x), hrB x hlt⟩

/-- On a retract `D` of a finite-dimensional normed space, continuous data can be approximated by
an ambient `Cⁿ` map agreeing near a closed `A ⊆ D` with a prescribed ambient germ. For example,
`D` can be an interval or a box (use coordinatewise clamping) or a closed ball (use radial
retraction), with `A` its boundary. -/
theorem exists_contDiff_approx_eventuallyEq_of_retraction {D A O : Set E} (f : C(D, V))
    (r : C(E, D)) (hr : ∀ x : D, r x = x) {e : E → V} {ε : ℝ} (hε : 0 < ε)
    (hA : IsClosed A) (hAD : A ⊆ D) (hO : O ∈ 𝓝ˢ A) (he : ContDiffOn ℝ n e O)
    (hef : ∀ x (hx : x ∈ A), dist (e x) (f ⟨x, hAD hx⟩) < ε) :
    ∃ g : E → V, ContDiff ℝ n g ∧ (∀ x : D, dist (g x) (f x) < ε) ∧
      (∀ᶠ x in 𝓝ˢ A, g x = e x) := by
  have htrace : ∀ x ∈ A, dist (e x) (f.comp r x) < ε := by
    intro x hx
    have hrx := hr ⟨x, hAD hx⟩
    simpa only [ContinuousMap.comp_apply, hrx] using hef x hx
  obtain ⟨g, hg, hge⟩ := (f.comp r).continuous.exists_contMDiff_approx_eventuallyEq
    continuous_const (fun _ ↦ hε) hA hO he.contMDiffOn htrace
  exact ⟨g, g.contMDiff.contDiff, fun x ↦ by simpa only [ContinuousMap.comp_apply, hr x] using hg x,
    hge⟩

end ContinuousMap
