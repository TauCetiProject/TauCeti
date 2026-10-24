/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Sets.Opens
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth cutoffs for compact subsets

This module provides smooth, compactly supported cutoffs for compact subsets of a
finite-dimensional real normed space. The cutoff is equal to one on a neighborhood of the compact
set and has topological support in a prescribed open set, which is the localization step used for
compact exhaustions in domain arguments. Taking differences of consecutive cutoffs along a compact
exhaustion gives a decomposition of unity (not necessarily nonnegative) of an open set by
compactly supported smooth functions, together with cutoffs equal to one on their supports which
are locally finite in the open set (`IsOpen.exists_contDiff_decomposition_cutoff`); this is the
gluing device for global approximation on a domain. Multiplying by a cutoff turns a function which
is `C^k` on an open set containing its support into a `C^k` function on the whole space
(`ContDiffOn.contDiff_smul_of_tsupport_subset`). Locally finite sums of smooth functions are
smooth (`contDiffAt_tsum_of_eventually_eq_zero`). A compactly supported `C¹` function is bounded
and Hölder continuous with every exponent at most one
(`ContDiff.exists_holderWith_and_norm_le_of_hasCompactSupport`).

It also provides radial cutoffs between two concentric closed balls of radii `r < R` whose
gradient is at most `c / (R - r)` and whose second derivative is at most `c / (R - r)²` for a
universal constant `c`, the quantitative form needed by iteration arguments over families of balls
with shrinking gaps.

## References

* L. C. Evans, *Partial Differential Equations*, §5.2.
-/

public section

open Function Set TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace NNReal Topology

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

/-- A product `ψ • g` is `C^k` on the whole space when `ψ` and `g` are `C^k` on an open set `s`
containing the topological support of `ψ`: this is how a cutoff `ψ` globalizes a function given
on `s`. -/
theorem _root_.ContDiffOn.contDiff_smul_of_tsupport_subset {𝕜 F : Type*}
    [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {k : WithTop ℕ∞} {ψ : E → 𝕜} {g : E → F} {s : Set E}
    (hg : ContDiffOn 𝕜 k g s) (hs : IsOpen s) (hψ : ContDiffOn 𝕜 k ψ s)
    (hψs : tsupport ψ ⊆ s) : ContDiff 𝕜 k (fun x => ψ x • g x) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ s
  · exact (hψ.contDiffAt (hs.mem_nhds hx)).smul (hg.contDiffAt (hs.mem_nhds hx))
  · have h0 : (fun x => ψ x • g x) =ᶠ[𝓝 x] 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 fun h => hx (hψs h)] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h0

/-- A compactly supported `C¹` function is bounded, and Hölder continuous with every exponent
`α ≤ 1`, with one constant `C` for both: it is Lipschitz and of bounded oscillation. -/
theorem _root_.ContDiff.exists_holderWith_and_norm_le_of_hasCompactSupport [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : E → F} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ C : ℝ≥0, HolderWith C α φ ∧ ∀ x, ‖φ x‖ ≤ C := by
  obtain ⟨K, hK⟩ := hφ.lipschitzWith_of_hasCompactSupport hc one_ne_zero
  obtain ⟨B, hB⟩ := hφ.continuous.bounded_above_of_compact_support hc
  have hB' (x : E) : ‖φ x‖ ≤ (2 * B.toNNReal : ℝ≥0) := by
    push_cast
    linarith [hB x, Real.le_coe_toNNReal B, B.toNNReal.coe_nonneg]
  have h₀ : HolderWith (2 * B.toNNReal) 0 φ := fun x y => by
    rw [NNReal.coe_zero, ENNReal.rpow_zero, mul_one, edist_dist]
    refine ENNReal.ofReal_le_of_le_toReal ?_
    rw [ENNReal.coe_toReal]
    push_cast
    linarith [dist_le_norm_add_norm (φ x) (φ y), hB x, hB y, Real.le_coe_toNNReal B]
  exact ⟨_, h₀.of_le_of_le (holderWith_one.2 hK) zero_le hα,
    fun x => (hB' x).trans (by exact_mod_cast le_max_left _ _)⟩

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

/-- **Radial cutoffs with quantitative derivative bounds.** There is a universal constant `c`
such that for every centre `x₀` and radii `0 ≤ r < R`, some smooth `ψ` with values in `[0, 1]`
equals one on `closedBall x₀ r`, has topological support in `closedBall x₀ R`, and satisfies

`‖∇ψ x‖ ≤ c / (R - r)` and `‖D(∇ψ) x‖ ≤ c / (R - r)²` for every `x`.

The inverse dependence on the gap `R - r` is what iteration arguments over families of balls with
geometrically shrinking gaps need; the second-derivative bound is what localizing a second-order
equation needs. The cutoff is `Real.smoothTransition ((R² - ‖x - x₀‖²) / (R² - r²))`, and `c` is
determined by bounds for the first two derivatives of `Real.smoothTransition`. -/
theorem exists_forall_contDiff_cutoff_closedBall [InnerProductSpace ℝ E] [CompleteSpace E] :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (x₀ : E) {r R : ℝ}, 0 ≤ r → r < R →
      ∃ ψ : E → ℝ, ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Icc 0 1 ∧ EqOn ψ 1 (Metric.closedBall x₀ r) ∧
        tsupport ψ ⊆ Metric.closedBall x₀ R ∧ (∀ x, ‖∇ ψ x‖ ≤ c / (R - r)) ∧
        ∀ x, ‖fderiv ℝ (∇ ψ) x‖ ≤ c / (R - r) ^ 2 := by
  -- The first two derivatives of `Real.smoothTransition` are continuous with compact support.
  set S := Real.smoothTransition
  have hS : ContDiff ℝ ∞ S := Real.smoothTransition.contDiff
  have hS1 : ContDiff ℝ ∞ (deriv S) := hS.iterate_deriv 1
  have hS2 : ContDiff ℝ ∞ (deriv (deriv S)) := hS.iterate_deriv 2
  obtain ⟨L₁, hL₁⟩ := hS1.continuous.bounded_above_of_compact_support
    Real.smoothTransition.hasCompactSupport_deriv
  obtain ⟨L₂, hL₂⟩ := hS2.continuous.bounded_above_of_compact_support
    Real.smoothTransition.hasCompactSupport_deriv.deriv
  have hL₁0 : 0 ≤ L₁ := (norm_nonneg _).trans (hL₁ 0)
  have hL₂0 : 0 ≤ L₂ := (norm_nonneg _).trans (hL₂ 0)
  have hS1neg : ∀ τ < 0, deriv S τ = 0 := fun τ hτ => Real.smoothTransition.deriv_of_neg hτ
  have hS2neg : ∀ τ < 0, deriv (deriv S) τ = 0 := fun τ hτ => by
    have h : deriv S =ᶠ[𝓝 τ] fun _ => 0 :=
      Filter.eventually_of_mem (Iio_mem_nhds hτ) fun _ ht => hS1neg _ ht
    rw [h.deriv_eq, deriv_const]
  refine ⟨2 * L₁ + 4 * L₂, by positivity, fun x₀ r R hr hrR => ?_⟩
  have hRr : 0 < R - r := sub_pos.2 hrR
  have hR : 0 < R := hr.trans_lt hrR
  set D := R ^ 2 - r ^ 2 with hD_def
  have hD : (R - r) * R ≤ D := by nlinarith
  have hD' : (R - r) ^ 2 ≤ D := by nlinarith
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD'
  -- The cutoff is `S ((R² - ‖x - x₀‖²) / D)`.
  set g : E → ℝ := fun x => (R ^ 2 - ‖x - x₀‖ ^ 2) / D with hg
  set ψ : E → ℝ := fun x => S (g x) with hψ
  set c : ℝ → ℝ := fun τ => -(2 / D) * deriv S ((R ^ 2 - τ) / D) with hc
  have hgrad : ∀ x, ∇ ψ x = c (‖x - x₀‖ ^ 2) • (x - x₀) := by
    intro x
    have h1 : HasFDerivAt (fun y => ‖y - x₀‖ ^ 2) (2 • (innerSL ℝ (x - x₀)).comp
        (ContinuousLinearMap.id ℝ E)) x := ((hasFDerivAt_id x).sub_const x₀).norm_sq
    have h2 : HasFDerivAt g ((-(1 / D)) • 2 • innerSL ℝ (x - x₀)) x := by
      have := HasFDerivAt.mul_const (HasFDerivAt.const_sub h1 (R ^ 2)) D⁻¹
      convert this using 1
      · funext y
        simp [g, div_eq_mul_inv]
      · ext v
        simp
    have h3 := ((hS.differentiable (by simp)) (g x)).hasDerivAt.comp_hasFDerivAt x h2
    refine (hasFDerivAt_iff_hasGradientAt.1 h3).gradient.trans ?_
    rw [LinearIsometryEquiv.symm_apply_eq]
    ext v
    simp [c, g]
    ring
  -- The derivative of the radial profile `c`.
  set c' : ℝ → ℝ := fun τ => 2 / D ^ 2 * deriv (deriv S) ((R ^ 2 - τ) / D) with hc'
  have hcd : ∀ τ, HasDerivAt c (c' τ) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ => (R ^ 2 - τ) / D) (-1 / D) τ := by
      simpa using ((hasDerivAt_id τ).const_sub (R ^ 2)).div_const D
    have h2 := (((hS1.differentiable (by simp)) _).hasDerivAt.comp τ h1).const_mul (-(2 / D))
    exact h2.congr_deriv (by simp only [c']; field_simp)
  have hhess : ∀ x, HasFDerivAt (∇ ψ) (c (‖x - x₀‖ ^ 2) • ContinuousLinearMap.id ℝ E +
      (c' (‖x - x₀‖ ^ 2) • 2 • innerSL ℝ (x - x₀)).smulRight (x - x₀)) x := by
    intro x
    rw [show ∇ ψ = fun y => c (‖y - x₀‖ ^ 2) • (y - x₀) from funext hgrad]
    have h1 : HasFDerivAt (fun y => ‖y - x₀‖ ^ 2) (2 • innerSL ℝ (x - x₀)) x := by
      simpa using ((hasFDerivAt_id x).sub_const x₀).norm_sq
    exact ((hcd _).comp_hasFDerivAt x h1).smul ((hasFDerivAt_id x).sub_const x₀)
  -- Outside `closedBall x₀ R` both `c` and `c'` vanish.
  have hout : ∀ x, R < ‖x - x₀‖ → c (‖x - x₀‖ ^ 2) = 0 ∧ c' (‖x - x₀‖ ^ 2) = 0 := by
    intro x hx
    have hneg : (R ^ 2 - ‖x - x₀‖ ^ 2) / D < 0 :=
      div_neg_of_neg_of_pos (by nlinarith) hD0
    exact ⟨by simp [c, hS1neg _ hneg], by simp [c', hS2neg _ hneg]⟩
  have hcb : ∀ τ, |c τ| ≤ 2 / D * L₁ := fun τ => by
    rw [hc, abs_mul, abs_neg, abs_of_pos (by positivity)]
    gcongr
    exact (Real.norm_eq_abs _).symm.le.trans (hL₁ _)
  have hc'b : ∀ τ, |c' τ| ≤ 2 / D ^ 2 * L₂ := fun τ => by
    rw [hc', abs_mul, abs_of_pos (by positivity)]
    gcongr
    exact (Real.norm_eq_abs _).symm.le.trans (hL₂ _)
  have hRD : R / D ≤ 1 / (R - r) := by
    rw [div_le_div_iff₀ hD0 hRr]
    linarith
  have hRD2 : R ^ 2 / D ^ 2 ≤ 1 / (R - r) ^ 2 := by
    rw [← div_pow, one_div, ← inv_pow, ← one_div]
    exact pow_le_pow_left₀ (by positivity) hRD 2
  refine ⟨ψ, hS.comp ((contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)).div_const
    D), ?_, fun x hx => ?_, ?_, fun x => ?_, fun x => ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · rw [Metric.mem_closedBall, dist_eq_norm] at hx
    refine Real.smoothTransition.one_of_one_le ?_
    rw [le_div_iff₀ hD0]
    nlinarith [norm_nonneg (x - x₀)]
  · refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
    rw [Metric.mem_closedBall, dist_eq_norm]
    by_contra h
    exact hx (Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by nlinarith [norm_nonneg (x - x₀)]) hD0.le))
  · rw [hgrad, norm_smul, Real.norm_eq_abs]
    rcases le_or_gt ‖x - x₀‖ R with hx | hx
    · calc |c (‖x - x₀‖ ^ 2)| * ‖x - x₀‖ ≤ 2 / D * L₁ * R :=
            mul_le_mul (hcb _) hx (norm_nonneg _) (by positivity)
        _ = 2 * L₁ * (R / D) := by ring
        _ ≤ 2 * L₁ * (1 / (R - r)) := by gcongr
        _ ≤ (2 * L₁ + 4 * L₂) / (R - r) := by
            rw [mul_one_div]
            gcongr
            linarith
    · rw [(hout x hx).1, abs_zero, zero_mul]
      positivity
  · rw [(hhess x).fderiv, ← Nat.cast_smul_eq_nsmul ℝ]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply, norm_smul, norm_smul,
      innerSL_apply_norm, Real.norm_eq_abs, Real.norm_eq_abs]
    have hid : ‖ContinuousLinearMap.id ℝ E‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    rcases le_or_gt ‖x - x₀‖ R with hx | hx
    · calc |c (‖x - x₀‖ ^ 2)| * ‖ContinuousLinearMap.id ℝ E‖ +
            |c' (‖x - x₀‖ ^ 2)| * (‖((2 : ℕ) : ℝ)‖ * ‖x - x₀‖) * ‖x - x₀‖
          ≤ 2 / D * L₁ * 1 + 2 / D ^ 2 * L₂ * (2 * R) * R := by
            gcongr
            · exact hcb _
            · exact hc'b _
            · norm_num
        _ = 2 * L₁ * (1 / D) + 4 * L₂ * (R ^ 2 / D ^ 2) := by ring
        _ ≤ 2 * L₁ * (1 / (R - r) ^ 2) + 4 * L₂ * (1 / (R - r) ^ 2) := by
            gcongr
        _ = (2 * L₁ + 4 * L₂) / (R - r) ^ 2 := by ring
    · rw [(hout x hx).1, (hout x hx).2, abs_zero, zero_mul, zero_mul, zero_mul, zero_add]
      positivity

end TauCeti
