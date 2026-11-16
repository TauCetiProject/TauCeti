/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Smoothness of series on open sets and geometric bounds

This file extends Mathlib's `Mathlib.Analysis.Calculus.SmoothSeries` in two directions.

First, for a series `∑' i, f i` of `C^N` functions on an open set `s`, summable uniform bounds on
`s` for all iterated derivatives through order `N` (possibly away from finitely many terms) imply
that the sum is `C^N` on `s`, with iterated derivatives computed termwise
(`TauCeti.iteratedFDeriv_tsum_apply_of_isOpen`, `TauCeti.contDiffOn_tsum`,
`TauCeti.contDiffOn_tsum_of_eventually`).

Second, if the derivatives of order `m ≤ k` of a sequence of functions `Gⱼ` are bounded by
`B m * q ^ j` with `0 ≤ q < 1`, then `∑ⱼ Gⱼ` is `C^k`, its derivatives through order `k` are the
sums of the derivatives, and its `m`-th derivative is bounded by `B m / (1 - q)`. These specialise
Mathlib's `contDiff_tsum` and `iteratedFDeriv_tsum` to geometric bounds.

## Main declarations

* `TauCeti.iteratedFDeriv_tsum_apply_of_isOpen`: termwise iterated derivatives of a series on an
  open set.
* `TauCeti.contDiffOn_tsum`, `TauCeti.contDiffOn_tsum_of_eventually`: `C^N` regularity of a series
  on an open set under (eventual) summable derivative bounds.
* `TauCeti.contDiff_tsum_of_norm_iteratedFDeriv_le_geometric`: the sum is `C^k`.
* `TauCeti.iteratedFDeriv_tsum_of_norm_iteratedFDeriv_le_geometric`: its derivatives through
  order `k` are the sums of the derivatives.
* `TauCeti.norm_iteratedFDeriv_tsum_le_of_geometric`: the bound `B m / (1 - q)` on them.
-/

public section

open Filter Metric Set Topology

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

end TauCeti
