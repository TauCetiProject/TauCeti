/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Series of smooth functions

This file extends Mathlib's `Mathlib.Analysis.Calculus.SmoothSeries` in three directions: to
series on open sets, to bounds on the derivatives that decay geometrically, and to summable bounds
that only hold near each point.

## Open sets

For a series `∑' i, f i` of `C^N` functions on an open set `s`, summable uniform bounds on `s` for
all iterated derivatives through order `N` across every index `i` imply both that the sum is `C^N`
on `s` (`TauCeti.contDiffOn_tsum`) and that its iterated derivatives are computed termwise
(`TauCeti.iteratedFDeriv_tsum_apply_of_isOpen`). When the summable derivative bounds hold only
eventually (`Filter.cofinite`, i.e. away from finitely many terms), the sum is still `C^N` on `s`
(`TauCeti.contDiffOn_tsum_of_eventually`).

* `TauCeti.iteratedFDeriv_tsum_apply_of_isOpen`: termwise iterated derivatives of a series on an
  open set under full-index summable derivative bounds.
* `TauCeti.contDiffOn_tsum`: `C^N` regularity of a series on an open set under full-index summable
  derivative bounds.
* `TauCeti.contDiffOn_tsum_of_eventually`: `C^N` regularity of a series on an open set under
  eventual (`Filter.cofinite`) summable derivative bounds.

## Geometric bounds

If the derivatives of order `m ≤ k` of a sequence of functions `Gⱼ` are bounded by `B m * q ^ j`
with `0 ≤ q < 1`, then `∑ⱼ Gⱼ` is `C^k`, its derivatives through order `k` are the sums of the
derivatives, and its `m`-th derivative is bounded by `B m / (1 - q)`.

* `TauCeti.contDiff_tsum_of_norm_iteratedFDeriv_le_geometric`: the sum is `C^k`.
* `TauCeti.iteratedFDeriv_tsum_of_norm_iteratedFDeriv_le_geometric`: its derivatives through
  order `k` are the sums of the derivatives.
* `TauCeti.norm_iteratedFDeriv_tsum_le_of_geometric`: the bound `B m / (1 - q)` on them.

## Locally summable bounds

Mathlib's `contDiff_tsum` asks for bounds on the derivatives that hold at every point. A series
whose terms are spread over the space, such as a sum of translates, often only has summable
bounds near each point. On a finite-dimensional real space this suffices: multiplying every term
by a bump function equal to `1` near a point gives a series with global summable bounds, which
agrees with the original one near that point.

* `TauCeti.contDiff_tsum_of_locally_summable`: a series of `C^N` functions whose derivatives of
  every order `k ≤ N` have summable bounds on a neighbourhood of each point is `C^N`.
* `TauCeti.iteratedFDeriv_tsum_of_locally_summable`: its derivatives through order `N` are the
  sums of the derivatives.
-/

public section

open Filter Metric Set Topology
open scoped ContDiff Topology

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F]

section OpenSet

variable {α : Type*} {N : ℕ∞} {f : α → E → F} {v : ℕ → α → ℝ} {s : Set E}

private theorem hasFDerivAt_iteratedFDeriv_tsum_of_isOpen (hs : IsOpen s)
    (hf : ∀ i, ContDiffOn 𝕜 N (f i) s) (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : α), ∀ x ∈ s, (k : ℕ∞) ≤ N → ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i)
    {k : ℕ} (hk : ((k + 1 : ℕ) : ℕ∞) ≤ N) {x : E} (hx : x ∈ s) :
    HasFDerivAt (fun y ↦ ∑' n, iteratedFDeriv 𝕜 k (f n) y)
      (∑' n, fderiv 𝕜 (iteratedFDeriv 𝕜 k (f n)) x) x := by
  let _ : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 _
  have h'k : (k : ℕ∞) < N := lt_of_lt_of_le (WithTop.coe_lt_coe.2 (Nat.lt_succ_self _)) hk
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hs x hx
  have hA : Summable fun n ↦ iteratedFDeriv 𝕜 k (f n) x :=
    .of_norm_bounded (hv k h'k.le) fun n ↦ h'f k n x hx h'k.le
  exact hasFDerivAt_tsum_of_isPreconnected (hv (k + 1) hk) isOpen_ball
    (convex_ball x r).isPreconnected
    (fun n y hy ↦ (((hf n).contDiffAt (hs.mem_nhds (hball hy))).differentiableAt_iteratedFDeriv
      (mod_cast h'k)).hasFDerivAt)
    (fun n y hy ↦ by
      simpa only [fderiv_iteratedFDeriv, Function.comp_apply, LinearIsometryEquiv.norm_map] using
        h'f (k + 1) n y (hball hy) hk)
    (mem_ball_self hr) hA (mem_ball_self hr)

/-- Termwise iterated derivatives of a series of `C^N` functions on an open set, under summable
uniform bounds on the derivatives on that set. -/
theorem iteratedFDeriv_tsum_apply_of_isOpen (hs : IsOpen s) (hf : ∀ i, ContDiffOn 𝕜 N (f i) s)
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : α), ∀ x ∈ s, (k : ℕ∞) ≤ N → ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i)
    {k : ℕ} (hk : (k : ℕ∞) ≤ N) {x : E} (hx : x ∈ s) :
    iteratedFDeriv 𝕜 k (fun y ↦ ∑' n, f n y) x = ∑' n, iteratedFDeriv 𝕜 k (f n) x := by
  induction k generalizing x with
  | zero =>
    simp_rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact (continuousMultilinearCurryFin0 𝕜 E F).symm.toContinuousLinearEquiv.map_tsum
  | succ k ih =>
    have h'k : (k : ℕ∞) ≤ N := (WithTop.coe_le_coe.2 (Nat.le_succ k)).trans hk
    have hderiv := hasFDerivAt_iteratedFDeriv_tsum_of_isOpen hs hf hv h'f hk hx
    have heq : iteratedFDeriv 𝕜 k (fun y ↦ ∑' n, f n y) =ᶠ[𝓝 x]
        fun y ↦ ∑' n, iteratedFDeriv 𝕜 k (f n) y :=
      Filter.eventuallyEq_of_mem (hs.mem_nhds hx) fun y hy ↦ ih h'k hy
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, heq.fderiv_eq, hderiv.fderiv]
    simp_rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    exact (continuousMultilinearCurryLeftEquiv 𝕜
      (fun _ : Fin (k + 1) ↦ E) F).symm.toContinuousLinearEquiv.map_tsum

/-- A series of `C^N` functions on an open set `s` with summable uniform bounds on all iterated
derivatives through order `N` on `s` has a `C^N` sum on `s`. -/
theorem contDiffOn_tsum (hs : IsOpen s) (hf : ∀ i, ContDiffOn 𝕜 N (f i) s)
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ (k : ℕ) (i : α), ∀ x ∈ s, (k : ℕ∞) ≤ N → ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i) :
    ContDiffOn 𝕜 N (fun x ↦ ∑' i, f i x) s := by
  rw [contDiffOn_iff_continuousOn_differentiableOn hs.uniqueDiffOn]
  constructor
  · intro m hm
    refine (continuousOn_tsum
      (fun i x hx ↦ (((hf i).contDiffAt (hs.mem_nhds hx)).continuousAt_iteratedFDeriv
        (mod_cast hm)).continuousWithinAt)
      (hv m (mod_cast hm)) fun n x hx ↦ h'f m n x hx (mod_cast hm)).congr fun x hx ↦ ?_
    rw [iteratedFDerivWithin_of_isOpen m hs hx,
      iteratedFDeriv_tsum_apply_of_isOpen hs hf hv h'f (mod_cast hm) hx]
  · intro m hm x hx
    have hmN : (m : ℕ∞) < N := by exact_mod_cast hm
    have h'm : ((m + 1 : ℕ) : ℕ∞) ≤ N := by
      simpa only [ENat.natCast_add, ENat.natCast_one] using Order.add_one_le_of_lt hmN
    have hderiv := hasFDerivAt_iteratedFDeriv_tsum_of_isOpen hs hf hv h'f h'm hx
    have heq : iteratedFDerivWithin 𝕜 m (fun y ↦ ∑' n, f n y) s =ᶠ[𝓝 x]
        fun y ↦ ∑' n, iteratedFDeriv 𝕜 m (f n) y :=
      Filter.eventuallyEq_of_mem (hs.mem_nhds hx) fun y hy ↦ by
        rw [iteratedFDerivWithin_of_isOpen m hs hy,
          iteratedFDeriv_tsum_apply_of_isOpen hs hf hv h'f hmN.le hy]
    exact (hderiv.congr_of_eventuallyEq heq).differentiableAt.differentiableWithinAt

/-- A series of `C^N` functions on an open set `s` whose iterated derivatives through order `N`
satisfy uniform summable bounds on `s` away from finitely many terms has a `C^N` sum on `s`. -/
theorem contDiffOn_tsum_of_eventually (hs : IsOpen s) (hf : ∀ i, ContDiffOn 𝕜 N (f i) s)
    (hv : ∀ k : ℕ, (k : ℕ∞) ≤ N → Summable (v k))
    (h'f : ∀ k : ℕ, (k : ℕ∞) ≤ N →
      ∀ᶠ i in Filter.cofinite, ∀ x ∈ s, ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i) :
    ContDiffOn 𝕜 N (fun x ↦ ∑' i, f i x) s := by
  classical
  refine contDiffOn_iff_forall_nat_le.2 fun m hm ↦ ?_
  have hfin : Set.Finite { i : α | ¬∀ k ∈ Finset.range (m + 1),
      ∀ x ∈ s, ‖iteratedFDeriv 𝕜 k (f i) x‖ ≤ v k i } := by
    refine eventually_cofinite.1 ((eventually_all_finset _).2 fun k hk ↦ ?_)
    exact h'f k ((Nat.cast_le.2 (Nat.le_of_lt_succ (Finset.mem_range.1 hk))).trans hm)
  let T : Finset α := hfin.toFinset
  have hsplit : EqOn (fun x ↦ ∑' i, f i x)
      (fun x ↦ ∑ i ∈ T, f i x + ∑' i : { i // i ∉ T }, f i x) s := fun x hx ↦ by
    refine (Summable.sum_add_tsum_subtype_compl ?_ T).symm
    refine .of_norm_bounded_eventually (hv 0 zero_le) ?_
    filter_upwards [h'f 0 zero_le] with i hi
    simpa only [norm_iteratedFDeriv_zero] using hi x hx
  refine ((ContDiffOn.sum fun i _ ↦ (hf i).of_le (mod_cast hm)).add ?_).congr hsplit
  refine contDiffOn_tsum hs (fun i ↦ (hf i).of_le (mod_cast hm))
    (fun k hk ↦ (hv k (hk.trans hm)).subtype _) fun k i x hx hk ↦ ?_
  have hi : ∀ j ∈ Finset.range (m + 1), ∀ y ∈ s, ‖iteratedFDeriv 𝕜 j (f i.1) y‖ ≤ v j i.1 := by
    have hnot : i.1 ∉ { j : α | ¬∀ k ∈ Finset.range (m + 1),
        ∀ y ∈ s, ‖iteratedFDeriv 𝕜 k (f j) y‖ ≤ v k j } := by
      simpa [T] using i.2
    simpa only [Set.mem_ofPred_eq, not_not] using hnot
  exact hi k (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.cast_le.1 hk))) x hx

end OpenSet

section Geometric

variable {k : ℕ} {G : ℕ → E → F} {B : ℕ → ℝ} {q : ℝ}

/-- A series of `C^k` functions whose derivatives of order `m ≤ k` are bounded by `B m * q ^ j`,
with `0 ≤ q < 1`, has a `C^k` sum. -/
theorem contDiff_tsum_of_norm_iteratedFDeriv_le_geometric (hG : ∀ j, ContDiff 𝕜 k (G j))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbd : ∀ m ≤ k, ∀ j x, ‖iteratedFDeriv 𝕜 m (G j) x‖ ≤ B m * q ^ j) :
    ContDiff 𝕜 k (fun x ↦ ∑' j, G j x) :=
  contDiff_tsum hG (fun m _ ↦ (summable_geometric_of_lt_one hq0 hq1).mul_left (B m))
    fun m j x hm ↦ hbd m (by exact_mod_cast hm) j x

/-- For a series of `C^k` functions whose derivatives of order `m ≤ k` are bounded by
`B m * q ^ j`, with `0 ≤ q < 1`, the derivatives of the sum through order `k` are the sums of the
derivatives. -/
theorem iteratedFDeriv_tsum_of_norm_iteratedFDeriv_le_geometric (hG : ∀ j, ContDiff 𝕜 k (G j))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbd : ∀ m ≤ k, ∀ j x, ‖iteratedFDeriv 𝕜 m (G j) x‖ ≤ B m * q ^ j) {i : ℕ} (hi : i ≤ k) :
    iteratedFDeriv 𝕜 i (fun x ↦ ∑' j, G j x) = fun x ↦ ∑' j, iteratedFDeriv 𝕜 i (G j) x :=
  iteratedFDeriv_tsum hG (fun m _ ↦ (summable_geometric_of_lt_one hq0 hq1).mul_left (B m))
    (fun m j x hm ↦ hbd m (by exact_mod_cast hm) j x) (by exact_mod_cast hi)

/-- For a series of `C^k` functions whose derivatives of order `m ≤ k` are bounded by
`B m * q ^ j`, with `0 ≤ q < 1`, the `i`-th derivative of the sum, `i ≤ k`, is bounded by
`B i / (1 - q)`. -/
theorem norm_iteratedFDeriv_tsum_le_of_geometric (hG : ∀ j, ContDiff 𝕜 k (G j))
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbd : ∀ m ≤ k, ∀ j x, ‖iteratedFDeriv 𝕜 m (G j) x‖ ≤ B m * q ^ j) {i : ℕ} (hi : i ≤ k)
    (x : E) :
    ‖iteratedFDeriv 𝕜 i (fun x ↦ ∑' j, G j x) x‖ ≤ B i * (1 - q)⁻¹ := by
  rw [iteratedFDeriv_tsum_of_norm_iteratedFDeriv_le_geometric hG hq0 hq1 hbd hi]
  exact tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hq0 hq1).mul_left (B i))
    fun j ↦ hbd i hi j x

end Geometric

section Locally

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : ι → E → F} {N : ℕ∞}

/-- Near each point, a series of smooth functions with locally summable bounds on its derivatives
agrees with a series of smooth functions with globally summable bounds on their derivatives,
term by term near that point. -/
private theorem exists_eventuallyEq_tsum_of_locally_summable (hf : ∀ i, ContDiff ℝ N (f i))
    (h : ∀ x₀, ∃ r > 0, ∀ k : ℕ, (k : ℕ∞) ≤ N → ∃ u : ι → ℝ, Summable u ∧
      ∀ i, ∀ x ∈ Metric.ball x₀ r, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ u i) (x₀ : E) :
    ∃ g : ι → E → F, (∀ i, g i =ᶠ[𝓝 x₀] f i) ∧
      (fun x ↦ ∑' i, g i x) =ᶠ[𝓝 x₀] (fun x ↦ ∑' i, f i x) ∧
      ContDiff ℝ N (fun x ↦ ∑' i, g i x) ∧
      ∀ k : ℕ, (k : ℕ∞) ≤ N →
        iteratedFDeriv ℝ k (fun x ↦ ∑' i, g i x) x₀ = ∑' i, iteratedFDeriv ℝ k (g i) x₀ := by
  obtain ⟨r, hr, hu⟩ := h x₀
  -- Bounds of the orders above `N` are never used; take them to be `0`.
  have hu' (k : ℕ) : ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ x ∈ Metric.ball x₀ r, (k : ℕ∞) ≤ N →
      ‖iteratedFDeriv ℝ k (f i) x‖ ≤ u i := by
    by_cases hk : (k : ℕ∞) ≤ N
    · obtain ⟨u, hus, hu⟩ := hu k hk
      exact ⟨u, hus, fun i x hx _ ↦ hu i x hx⟩
    · exact ⟨0, summable_zero, fun _ _ _ h ↦ absurd h hk⟩
  choose u hus hu using hu'
  -- A bump function equal to `1` on the ball of radius `r / 4` and supported in that of `r / 2`.
  let ρ : ContDiffBump x₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hrout : ρ.rOut = r / 2 := rfl
  choose B hB using fun j : ℕ ↦ ((ρ.contDiff (n := ⊤)).continuous_iteratedFDeriv (m := j)
    (by exact_mod_cast le_top)).bounded_above_of_compact_support
    (ρ.hasCompactSupport.iteratedFDeriv j)
  set g : ι → E → F := fun i x ↦ ρ x • f i x
  have hρ1 : ∀ᶠ x in 𝓝 x₀, ρ x = 1 :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds x₀ (by positivity : 0 < r / 4)) fun x hx ↦
      ρ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
  have hg : ∀ i, ContDiff ℝ N (g i) := fun i ↦ ρ.contDiff.smul (hf i)
  set v : ℕ → ι → ℝ := fun k i ↦
    ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * B j * u (k - j) i
  have hv : ∀ k : ℕ, Summable (v k) := fun k ↦
    summable_sum fun j _ ↦ (hus (k - j)).mul_left _
  have hgv : ∀ (k : ℕ) (i : ι) (x : E), (k : ℕ∞) ≤ N → ‖iteratedFDeriv ℝ k (g i) x‖ ≤ v k i := by
    intro k i x hk
    refine (norm_iteratedFDeriv_smul_le ρ.contDiff (hf i) x (by exact_mod_cast hk)).trans
      (Finset.sum_le_sum fun j _ ↦ ?_)
    by_cases hx : x ∈ Metric.ball x₀ r
    · exact mul_le_mul (mul_le_mul_of_nonneg_left (hB j x) (Nat.cast_nonneg _))
        (hu (k - j) i x hx ((Nat.cast_le.2 (k.sub_le j)).trans hk)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans (hB j x)))
    · have hx' : x ∉ tsupport ρ := by
        rw [ρ.tsupport_eq]
        exact fun h' ↦ hx (Metric.closedBall_subset_ball (by rw [hrout]; linarith) h')
      rw [Function.notMem_support.1 fun h' ↦ hx' (support_iteratedFDeriv_subset j h'), norm_zero,
        mul_zero, zero_mul]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ((norm_nonneg _).trans (hB j x)))
        ((norm_nonneg _).trans (hu (k - j) i x₀ (Metric.mem_ball_self hr)
          ((Nat.cast_le.2 (k.sub_le j)).trans hk)))
  refine ⟨g, fun i ↦ ?_, ?_, contDiff_tsum hg (fun k _ ↦ hv k) fun k i x hk ↦ hgv k i x hk,
    fun k hk ↦ iteratedFDeriv_tsum_apply hg (fun k _ ↦ hv k) (fun k i x hk ↦ hgv k i x hk) hk x₀⟩
  · filter_upwards [hρ1] with x hx
    simp [g, hx]
  · filter_upwards [hρ1] with x hx
    simp [g, hx]

/-- **Smoothness of a series with locally summable bounds.** A series of `C^N` functions on a
finite-dimensional real space whose derivatives of every order `k ≤ N` have summable bounds on a
neighbourhood of each point is `C^N`. -/
theorem contDiff_tsum_of_locally_summable (hf : ∀ i, ContDiff ℝ N (f i))
    (h : ∀ x₀, ∃ r > 0, ∀ k : ℕ, (k : ℕ∞) ≤ N → ∃ u : ι → ℝ, Summable u ∧
      ∀ i, ∀ x ∈ Metric.ball x₀ r, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ u i) :
    ContDiff ℝ N (fun x ↦ ∑' i, f i x) :=
  contDiff_iff_contDiffAt.2 fun x₀ ↦ by
    obtain ⟨g, -, hgf, hgs, -⟩ := exists_eventuallyEq_tsum_of_locally_summable hf h x₀
    exact hgs.contDiffAt.congr_of_eventuallyEq hgf.symm

/-- **Derivatives of a series with locally summable bounds.** For a series of `C^N` functions on a
finite-dimensional real space whose derivatives of every order `k ≤ N` have summable bounds on a
neighbourhood of each point, the derivatives of the sum through order `N` are the sums of the
derivatives. -/
theorem iteratedFDeriv_tsum_of_locally_summable (hf : ∀ i, ContDiff ℝ N (f i))
    (h : ∀ x₀, ∃ r > 0, ∀ k : ℕ, (k : ℕ∞) ≤ N → ∃ u : ι → ℝ, Summable u ∧
      ∀ i, ∀ x ∈ Metric.ball x₀ r, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ u i) {k : ℕ}
    (hk : (k : ℕ∞) ≤ N) (x₀ : E) :
    iteratedFDeriv ℝ k (fun x ↦ ∑' i, f i x) x₀ = ∑' i, iteratedFDeriv ℝ k (f i) x₀ := by
  obtain ⟨g, hg, hgf, -, hgk⟩ := exists_eventuallyEq_tsum_of_locally_summable hf h x₀
  rw [← (hgf.iteratedFDeriv ℝ k).eq_of_nhds, hgk k hk]
  exact tsum_congr fun i ↦ ((hg i).iteratedFDeriv ℝ k).eq_of_nhds

end Locally

end TauCeti
