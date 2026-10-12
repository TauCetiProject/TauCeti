/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Sets.Opens
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth cutoffs for compact subsets

This module provides smooth, compactly supported cutoffs for compact subsets of a
finite-dimensional real normed space. The cutoff is equal to one on a neighborhood of the compact
set and has topological support in a prescribed open set, which is the localization step used for
compact exhaustions in domain arguments. Taking differences of consecutive cutoffs along a compact
exhaustion gives a decomposition of unity (not necessarily nonnegative) of an open set by
compactly supported smooth functions, together with cutoffs equal to one on their supports which
are locally finite in the open set (`IsOpen.exists_contDiff_decomposition_cutoff`); this is the
gluing device for global approximation on a domain. Locally finite sums of smooth functions are
smooth (`contDiffAt_tsum_of_eventually_eq_zero`).

It also provides radial cutoffs between two concentric closed balls of radii `r < R` whose
gradient is at most `c / (R - r)` for a universal constant `c`, the quantitative form needed by
iteration arguments over families of balls with shrinking gaps.

## References

* L. C. Evans, *Partial Differential Equations*, §5.2.
-/

public section

open Function Set TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E]

/-- A compact set contained in an open set admits a smooth cutoff equal to one on a neighborhood
of the compact set.

The cutoff takes values in `[0, 1]`, has compact support, and its topological support is contained
in the prescribed open set. -/
theorem _root_.IsCompact.exists_contDiff_cutoff [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ ψ : E → ℝ,
      ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Icc 0 1 ∧
        K ⊆ interior (ψ ⁻¹' {1}) ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ U := by
  obtain ⟨L, hL, hL_closed, hKL, hLU⟩ := exists_compact_closed_between hK hU hKU
  obtain ⟨f, hfK, hfL, hf_range⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (modelWithCornersSelf ℝ E)
      hK.isClosed hKL (n := (⊤ : ℕ∞))
  let ψ : E → ℝ := f
  have hψ_smooth : ContDiff ℝ ∞ ψ := by
    dsimp [ψ]
    exact f.contMDiff.contDiff
  have hψ_eq_one_nhds : K ⊆ interior (ψ ⁻¹' {1}) := by
    intro x hx
    apply mem_interior_iff_mem_nhds.mpr
    exact mem_nhdsSet_iff_forall.mp hfK x hx
  have hψ_support : support ψ ⊆ L := by
    intro x hx
    by_contra hnot
    exact hx (hfL x hnot)
  have hψ_compact : HasCompactSupport ψ :=
    HasCompactSupport.of_support_subset_isCompact hL hψ_support
  have hψ_tsupp : tsupport ψ ⊆ U := by
    rw [tsupport]
    exact (closure_minimal hψ_support hL_closed).trans hLU
  have hψ_range : range ψ ⊆ Icc 0 1 := by
    rintro y ⟨x, rfl⟩
    exact hf_range x
  exact ⟨ψ, hψ_smooth, hψ_range, hψ_eq_one_nhds, hψ_compact, hψ_tsupp⟩

/-- A compact set contained in an open set admits a smooth cutoff whose value and gradient are
bounded by a common nonnegative constant. -/
theorem _root_.IsCompact.exists_contDiff_cutoff_with_bounds [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ψ : E → ℝ, ∃ M : ℝ,
      ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Icc 0 1 ∧
        K ⊆ interior (ψ ⁻¹' {1}) ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ U ∧
          0 ≤ M ∧ (∀ x, |ψ x| ≤ M) ∧ ∀ x, ‖∇ ψ x‖ ≤ M := by
  obtain ⟨ψ, hψ, hψ_range, hψ_one_nhds, hψ_cpt, hψ_ts⟩ :=
    hK.exists_contDiff_cutoff hU hKU
  have hψ_mem : ∀ x, ψ x ∈ Icc (0 : ℝ) 1 := fun x => hψ_range (mem_range_self x)
  obtain ⟨C, hC⟩ := (hψ.continuous_fderiv (by simp)).norm.bddAbove_range_of_hasCompactSupport
    ((hψ_cpt.fderiv ℝ).norm)
  let M : ℝ := max 1 C
  have hM0 : (0 : ℝ) ≤ M := zero_le_one.trans (le_max_left _ _)
  have hψM : ∀ x, |ψ x| ≤ M := fun x => by
    rw [abs_of_nonneg (hψ_mem x).1]
    exact (hψ_mem x).2.trans (le_max_left _ _)
  have hgradψM : ∀ x, ‖∇ ψ x‖ ≤ M := fun x => by
    rw [_root_.gradient, LinearIsometryEquiv.norm_map]
    exact (hC ⟨x, rfl⟩).trans (le_max_right _ _)
  exact ⟨ψ, M, hψ, hψ_range, hψ_one_nhds, hψ_cpt, hψ_ts, hM0, hψM, hgradψM⟩

/-- A compactly supported `C¹` function and its gradient are bounded by a common nonnegative
constant. -/
theorem _root_.ContDiff.exists_abs_le_and_norm_gradient_le [InnerProductSpace ℝ E]
    [CompleteSpace E] {ψ : E → ℝ} (hψ : ContDiff ℝ 1 ψ) (hcpt : HasCompactSupport ψ) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ x, |ψ x| ≤ M) ∧ ∀ x, ‖∇ ψ x‖ ≤ M := by
  obtain ⟨C, hC⟩ := hψ.continuous.norm.bddAbove_range_of_hasCompactSupport hcpt.norm
  obtain ⟨D, hD⟩ := (hψ.continuous_fderiv one_ne_zero).norm.bddAbove_range_of_hasCompactSupport
    (hcpt.fderiv ℝ).norm
  refine ⟨max 0 (max C D), le_max_left _ _, fun x => ?_, fun x => ?_⟩
  · rw [← Real.norm_eq_abs]
    exact (hC ⟨x, rfl⟩).trans ((le_max_left _ _).trans (le_max_right _ _))
  · rw [_root_.gradient, LinearIsometryEquiv.norm_map]
    exact (hD ⟨x, rfl⟩).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- A compact-exhaustion term in an open set admits a smooth cutoff supported in the interior of
the next term. -/
theorem _root_.CompactExhaustion.exists_contDiff_cutoff [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Omega : Opens E} (K : CompactExhaustion Omega) (n : ℕ) :
    ∃ ψ : E → ℝ,
      ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Icc 0 1 ∧
        (Subtype.val : Omega → E) '' K n ⊆ interior (ψ ⁻¹' {1}) ∧
        HasCompactSupport ψ ∧
          tsupport ψ ⊆ (Subtype.val : Omega → E) '' interior (K (n + 1)) := by
  have hK : IsCompact ((Subtype.val : Omega → E) '' K n) :=
    (K.isCompact n).image continuous_subtype_val
  have hU : IsOpen ((Subtype.val : Omega → E) '' interior (K (n + 1))) :=
    Omega.isOpen.isOpenMap_subtype_val _ isOpen_interior
  have hKU :
      (Subtype.val : Omega → E) '' K n ⊆ (Subtype.val : Omega → E) '' interior (K (n + 1)) :=
    image_mono (K.subset_interior_succ n)
  obtain ⟨ψ, hψ_smooth, hψ_range, hψ_eq_one_nhds, hψ_compact, hψ_tsupp⟩ :=
    hK.exists_contDiff_cutoff hU hKU
  exact ⟨ψ, hψ_smooth, hψ_range, hψ_eq_one_nhds, hψ_compact, hψ_tsupp⟩

/-- **A smooth decomposition of unity of an open set, with cutoffs.** Every open set `U` of a
finite-dimensional real normed space carries smooth compactly supported functions `ζ j` and
`χ j`, `j : ℕ`, with topological supports in `U`, such that `χ j = 1` on the topological support
of `ζ j`, and every point of `U` has a neighbourhood on which `χ j` vanishes and
`∑ j ∈ Finset.range N, ζ j = 1` for all large `j` and `N`.

So `(ζ j)` is a decomposition of unity of `U` by test functions on `U`, and the cutoffs `χ j` form
a family which is locally finite in `U`. Neither family is locally finite at the frontier of `U`.
The functions `ζ j` are differences of consecutive cutoffs along a compact exhaustion of `U`, and
need not be nonnegative. -/
theorem _root_.IsOpen.exists_contDiff_decomposition_cutoff [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set E} (hU : IsOpen U) :
    ∃ ζ χ : ℕ → E → ℝ,
      (∀ j, ContDiff ℝ ∞ (ζ j) ∧ HasCompactSupport (ζ j) ∧ tsupport (ζ j) ⊆ U) ∧
      (∀ j, ContDiff ℝ ∞ (χ j) ∧ HasCompactSupport (χ j) ∧ tsupport (χ j) ⊆ U) ∧
      (∀ j, EqOn (χ j) 1 (tsupport (ζ j))) ∧
      ∀ x ∈ U, ∃ m, ∀ᶠ y in 𝓝 x, (∀ j, m ≤ j → χ j y = 0) ∧
        ∀ N, m ≤ N → ∑ j ∈ Finset.range N, ζ j y = 1 := by
  let Omega : Opens E := ⟨U, hU⟩
  have : LocallyCompactSpace Omega := hU.locallyCompactSpace
  let K : CompactExhaustion Omega := (CompactExhaustion.choice Omega).shiftr
  -- `L n` is the `n`-th compact set of the exhaustion, `V n` the image of its interior
  let L : ℕ → Set E := fun n => (Subtype.val : Omega → E) '' K n
  let V : ℕ → Set E := fun n => (Subtype.val : Omega → E) '' interior (K n)
  have hK0 : K 0 = ∅ := rfl
  have hL0 : L 0 = ∅ := by simp only [L, hK0, image_empty]
  have hLcpt : ∀ n, IsCompact (L n) := fun n => (K.isCompact n).image continuous_subtype_val
  have hVopen : ∀ n, IsOpen (V n) := fun n => hU.isOpenMap_subtype_val _ isOpen_interior
  have hVL : ∀ n, V n ⊆ L n := fun n => image_mono interior_subset
  have hLmono : Monotone L := fun m n hmn => image_mono (K.subset hmn)
  have hVmono : Monotone V := fun m n hmn => image_mono (interior_mono (K.subset hmn))
  have hVsub : ∀ n, V n ⊆ U := fun n => by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hcover : ∀ x ∈ U, ∃ n, x ∈ V n := fun x hx => by
    obtain ⟨n, hn⟩ := K.exists_mem ⟨x, hx⟩
    exact ⟨n + 1, ⟨x, hx⟩, K.subset_interior_succ n hn, rfl⟩
  have one_of_mem : ∀ {f : E → ℝ} {y : E}, y ∈ interior (f ⁻¹' {1}) → f y = 1 := fun h => by
    simpa only [mem_preimage, mem_singleton_iff] using interior_subset h
  choose eta heta _ heta_one heta_cpt heta_ts using K.exists_contDiff_cutoff
  -- `eta' (n + 1) = eta n` is a cutoff for `L n`; prepending `eta' 0 = 0` makes the
  -- differences `zeta j = eta' (j + 1) - eta' j` telescope to `eta' N`.
  let eta' : ℕ → E → ℝ := fun n => Nat.casesOn n 0 eta
  have heta'_smooth : ∀ n, ContDiff ℝ ∞ (eta' n) := fun n => by
    cases n
    exacts [contDiff_const, heta _]
  have heta'_cpt : ∀ n, HasCompactSupport (eta' n) := fun n => by
    cases n
    exacts [HasCompactSupport.zero, heta_cpt _]
  have heta'_ts : ∀ n, tsupport (eta' n) ⊆ V n := fun n => by
    cases n
    · simp [eta']
    · exact heta_ts _
  have heta'_one : ∀ m n, m < n → L m ⊆ interior (eta' n ⁻¹' {1}) := fun m n hmn => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hmn
    exact (hLmono (by omega)).trans (heta_one (m + k))
  let zeta : ℕ → E → ℝ := fun j x => eta' (j + 1) x - eta' j x
  have hzeta_smooth : ∀ j, ContDiff ℝ ∞ (zeta j) := fun j =>
    (heta'_smooth (j + 1)).sub (heta'_smooth j)
  have hzeta_cpt : ∀ j, HasCompactSupport (zeta j) := fun j =>
    (heta'_cpt (j + 1)).sub (heta'_cpt j)
  have hzeta_ts : ∀ j, tsupport (zeta j) ⊆ V (j + 1) := fun j =>
    (tsupport_sub _ _).trans
      (union_subset (heta'_ts (j + 1)) ((heta'_ts j).trans (hVmono j.le_succ)))
  -- `zeta j` vanishes near `L (j - 1)`, where both cutoffs equal one
  have hzeta_L : ∀ j, ∀ x ∈ L (j - 1), x ∉ tsupport (zeta j) := fun j x hx => by
    cases j with
    | zero => simp [hL0] at hx
    | succ k =>
      rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [interior_mem_nhds.2 (mem_interior_iff_mem_nhds.1
          (heta'_one k (k + 1) k.lt_succ_self hx)),
        interior_mem_nhds.2 (mem_interior_iff_mem_nhds.1
          (heta'_one k (k + 2) (by omega) hx))] with y hy₁ hy₂
      have h₁ : eta' (k + 1) y = 1 := one_of_mem hy₁
      have h₂ : eta' (k + 1 + 1) y = 1 := one_of_mem hy₂
      simp only [zeta, Pi.zero_apply, h₁, h₂, sub_self]
  have hsum : ∀ N y, ∑ j ∈ Finset.range N, zeta j y = eta' N y := fun N y => by
    simpa [zeta, eta'] using Finset.sum_range_sub (fun n => eta' n y) N
  -- cutoffs equal to one on `tsupport (zeta j)` and supported away from `L (j - 1)`
  have hU : ∀ j, tsupport (zeta j) ⊆ V (j + 1) \ L (j - 1) := fun j x hx =>
    ⟨hzeta_ts j hx, fun hxL => hzeta_L j x hxL hx⟩
  choose chi hchi_smooth _ hchi_one hchi_cpt hchi_ts using fun j =>
    (hzeta_cpt j).exists_contDiff_cutoff ((hVopen (j + 1)).sdiff (hLcpt (j - 1)).isClosed) (hU j)
  refine ⟨zeta, chi, fun j => ⟨hzeta_smooth j, hzeta_cpt j, (hzeta_ts j).trans (hVsub _)⟩,
    fun j => ⟨hchi_smooth j, hchi_cpt j, (hchi_ts j).trans (sdiff_subset.trans (hVsub _))⟩,
    fun j x hx => one_of_mem (hchi_one j hx), fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := hcover x hx
  refine ⟨n + 1, ?_⟩
  filter_upwards [(hVopen n).mem_nhds hn] with y hy
  refine ⟨fun j hj => image_eq_zero_of_notMem_tsupport fun hyj => (hchi_ts j hyj).2 ?_,
    fun N hN => ?_⟩
  · exact hLmono (by omega) (hVL n hy)
  · rw [hsum]
    exact one_of_mem (heta'_one n N (by omega) (hVL n hy))

/-- A sum of functions which are smooth at `x` is smooth at `x` if, on a neighbourhood of `x`,
all but finitely many of them vanish. This makes the locally finite sums built from
`IsOpen.exists_contDiff_decomposition_cutoff` smooth on the open set. -/
theorem contDiffAt_tsum_of_eventually_eq_zero {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : WithTop ℕ∞}
    {g : ι → E → F} {x : E} (s : Finset ι) (hg : ∀ j ∈ s, ContDiffAt 𝕜 n (g j) x)
    (hs : ∀ᶠ y in 𝓝 x, ∀ j ∉ s, g j y = 0) :
    ContDiffAt 𝕜 n (fun y => ∑' j, g j y) x :=
  (ContDiffAt.sum hg).congr_of_eventuallyEq (hs.mono fun _ hy => tsum_eq_sum hy)

/-- **Radial cutoffs with a quantitative gradient bound.** There is a universal constant `c` such
that for every centre `x₀` and radii `0 < r < R`, some smooth `ψ` with values in `[0, 1]` equals
one on `closedBall x₀ r`, has topological support in `closedBall x₀ R`, and satisfies

`‖∇ψ x‖ ≤ c / (R - r)` for every `x`.

The inverse dependence on the gap `R - r` is what iteration arguments over families of balls with
geometrically shrinking gaps need. The cutoff is `Real.smoothTransition ((R - ‖x - x₀‖) / (R - r))`,
and `c` is a Lipschitz constant of `Real.smoothTransition`. -/
theorem exists_forall_contDiff_cutoff_closedBall [InnerProductSpace ℝ E] [CompleteSpace E] :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (x₀ : E) {r R : ℝ}, 0 < r → r < R →
      ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Icc 0 1 ∧ EqOn ψ 1 (Metric.closedBall x₀ r) ∧
        tsupport ψ ⊆ Metric.closedBall x₀ R ∧ ∀ x, ‖∇ ψ x‖ ≤ c / (R - r) := by
  -- `Real.smoothTransition` factors through the projection onto `[0, 1]`, where it is Lipschitz.
  obtain ⟨L, hL⟩ : ∃ L, LipschitzWith L Real.smoothTransition := by
    obtain ⟨L, hL⟩ := (Real.smoothTransition.contDiff (n := 1)).contDiffOn.exists_lipschitzOnWith
      one_ne_zero (convex_Icc (0 : ℝ) 1) isCompact_Icc
    refine ⟨L, ?_⟩
    have := hL.to_restrict.comp (LipschitzWith.projIcc (zero_le_one' ℝ))
    simpa [Function.comp_def] using this
  refine ⟨L, L.2, fun x₀ r R hr hrR => ?_⟩
  have hRr : 0 < R - r := sub_pos.2 hrR
  set ψ : E → ℝ := fun x => Real.smoothTransition ((R - ‖x - x₀‖) / (R - r))
  have hone : ∀ x, ‖x - x₀‖ ≤ r → ψ x = 1 := fun x hx =>
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hRr]; linarith)
  refine ⟨ψ, ?_, ?_, fun x hx => hone x (by rwa [Metric.mem_closedBall, dist_eq_norm] at hx),
    ?_, fun x => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = x₀
    · -- Near the centre, `ψ` is identically one.
      subst hx
      have hev : ψ =ᶠ[𝓝 x] fun _ => 1 := by
        filter_upwards [Metric.ball_mem_nhds x hr] with y hy
        exact hone y (by rw [Metric.mem_ball, dist_eq_norm] at hy; exact hy.le)
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hn : ContDiffAt ℝ ∞ (fun y : E => ‖y - x₀‖) x :=
        (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hx)
      exact Real.smoothTransition.contDiffAt.comp x ((contDiffAt_const.sub hn).div_const _)
  · rintro _ ⟨x, rfl⟩
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
    rw [Metric.mem_closedBall, dist_eq_norm]
    by_contra h
    exact hx (Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hRr.le))
  · have hlip : LipschitzWith (L * Real.toNNReal (R - r)⁻¹) ψ := by
      refine hL.comp (LipschitzWith.of_dist_le_mul fun y z => ?_)
      rw [Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.2 hRr.le), ← sub_div, abs_div,
        abs_of_pos hRr, div_eq_inv_mul]
      gcongr
      have hsub : R - ‖y - x₀‖ - (R - ‖z - x₀‖) = ‖z - x₀‖ - ‖y - x₀‖ := by ring
      rw [dist_eq_norm, hsub, abs_sub_comm]
      simpa using abs_norm_sub_norm_le (y - x₀) (z - x₀)
    rw [_root_.gradient, LinearIsometryEquiv.norm_map]
    refine (norm_fderiv_le_of_lipschitz ℝ hlip).trans_eq ?_
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (inv_nonneg.2 hRr.le), div_eq_mul_inv]

end TauCeti
