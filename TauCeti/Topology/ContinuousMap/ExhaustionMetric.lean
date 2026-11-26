/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import TauCeti.Topology.Compactness.SigmaCompact
public import TauCeti.Topology.UniformSpace.CompactConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.SpecificLimits.HalfPowSucc
import TauCeti.Topology.ContinuousMap.Compact

/-!
# Explicit comparison metric for compact convergence on `C(X, Y)`

Given a compact exhaustion `K : CompactExhaustion X` of a topological space `X` and a
(pseudo)metric target `Y`, the space `C(X, Y)` carries a bounded series distance
`K.continuousMapDist f g` built from the supremum distances `s_n(f, g)` on the compact stages
`K n`:
$$
d_K(f, g) = \sum_{n = 0}^{\infty} 2^{-(n + 1)} \frac{s_n(f, g)}{1 + s_n(f, g)}.
$$
Because `C(X, Y)` already carries the canonical `ContinuousMap.compactConvergenceUniformSpace`
independently of any choice of exhaustion, no `PseudoMetricSpace` or `MetricSpace` typeclass
instance is registered on `C(X, Y)`. Instead, `K.uniformity_eq_iInf_continuousMapDist` proves
equality of uniformities directly, and `K.continuousMapPseudoMetricSpace` and
`K.continuousMapMetricSpace` package the metric data with `toUniformSpace` definitionally equal to
`ContinuousMap.compactConvergenceUniformSpace`.

Termwise comparison bounds `K.continuousMapDist` between `1 / 2` times and `1` times the
`min 1 s_n` series (`half_tsum_min_one_le_continuousMapDist`, `continuousMapDist_le_tsum_min_one`),
with equality at `1 / 2` for constant maps at distance `1` when `(K 0).Nonempty`
(`half_tsum_min_one_eq_continuousMapDist_const`).

From the quantitative single-stage lower bound (`dist_restrict_lt_of_continuousMapDist_lt`) and
head-plus-tail upper bound (`continuousMapDist_le_dist_restrict_add_half_pow_succ`) follow:
* equality of `𝓤 C(X, Y)` with the metric entourages of `K.continuousMapDist`, and hence
  independence of the induced uniformity from the choice of `CompactExhaustion`;
* equivalence of `d_K`-convergence and the `d_K`-Cauchy property with uniform convergence and
  `UniformCauchySeqOn` on every compact subset of `X`;
* the `ε`-`δ` uniform-continuity condition for restriction `C(X, Y) → C(s, Y)` to any compact `s`
  with respect to `K.continuousMapDist`, with the explicit threshold
  `(1 / 2) ^ (n + 1) * (ε / (1 + ε))` when `s ⊆ K n`
  (`dist_restrict_lt_of_subset_of_continuousMapDist_lt`);
* convergence in `K.continuousMapDist` of `d_K`-Cauchy directed nets in any closed subset of
  `C(X, Y)` when `Y` is complete (`exists_tendsto_continuousMapDist_of_isClosed`, combining the
  `d_K` characterizations with `CompactExhaustion.completeSpace_continuousMap`).

## References

* Armin Rainer, *Advanced Complex Analysis*, §11, equation (11.2) and Exercise 19.
* Walter Rudin, *Functional Analysis*, 2nd ed., §1.44.
-/

public section

open Filter Function Metric Set Topology UniformSpace
open scoped Uniformity

namespace CompactExhaustion

section PseudoMetricSpace

variable {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y] (K : CompactExhaustion X)

/-- The supremum distance on stages `K n` is monotone in the stage index `n`. -/
theorem dist_restrict_mono (f g : C(X, Y)) {m n : ℕ} (hmn : m ≤ n) :
    dist (f.restrict (K m)) (g.restrict (K m)) ≤ dist (f.restrict (K n)) (g.restrict (K n)) :=
  f.dist_restrict_le_of_subset g (K.subset hmn)

/-- Explicit Fréchet comparison distance on `C(X, Y)` associated with a compact exhaustion `K` of
`X`, given by `∑' n, (1 / 2) ^ (n + 1) * (s_n / (1 + s_n))` where `s_n` is the supremum distance on
`K n`. Not installed as a `Dist` or `PseudoMetricSpace` instance so that `C(X, Y)` keeps its
canonical exhaustion-independent uniform structure. -/
noncomputable def continuousMapDist (f g : C(X, Y)) : ℝ :=
  ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) *
    (dist (f.restrict (K n)) (g.restrict (K n)) /
      (1 + dist (f.restrict (K n)) (g.restrict (K n))))

/-- Defining series formula for `K.continuousMapDist f g`. -/
theorem continuousMapDist_def (f g : C(X, Y)) :
    K.continuousMapDist f g =
      ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) *
        (dist (f.restrict (K n)) (g.restrict (K n)) /
          (1 + dist (f.restrict (K n)) (g.restrict (K n)))) := (rfl)

private noncomputable def continuousMapDistTerm (f g : C(X, Y)) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (n + 1) *
    (dist (f.restrict (K n)) (g.restrict (K n)) /
      (1 + dist (f.restrict (K n)) (g.restrict (K n))))

private theorem continuousMapDistTerm_nonneg (f g : C(X, Y)) (n : ℕ) :
    0 ≤ K.continuousMapDistTerm f g n := by
  have hd : 0 ≤ dist (f.restrict (K n)) (g.restrict (K n)) := dist_nonneg
  exact mul_nonneg (by positivity) (div_nonneg hd (by linarith))

private theorem continuousMapDistTerm_lt_half_pow_succ (f g : C(X, Y)) (n : ℕ) :
    K.continuousMapDistTerm f g n < (1 / 2 : ℝ) ^ (n + 1) := by
  have hd : 0 ≤ dist (f.restrict (K n)) (g.restrict (K n)) := dist_nonneg
  exact mul_lt_of_lt_one_right (by positivity) ((div_lt_one (by linarith)).mpr (by linarith))

private theorem continuousMapDistTerm_le_half_pow_succ (f g : C(X, Y)) (n : ℕ) :
    K.continuousMapDistTerm f g n ≤ (1 / 2 : ℝ) ^ (n + 1) :=
  (K.continuousMapDistTerm_lt_half_pow_succ f g n).le

/-- The series defining `K.continuousMapDist f g` is summable. -/
theorem summable_continuousMapDist_term (f g : C(X, Y)) :
    Summable fun n : ℕ ↦ (1 / 2 : ℝ) ^ (n + 1) *
      (dist (f.restrict (K n)) (g.restrict (K n)) /
        (1 + dist (f.restrict (K n)) (g.restrict (K n)))) :=
  Summable.of_nonneg_of_le (K.continuousMapDistTerm_nonneg f g)
    (K.continuousMapDistTerm_le_half_pow_succ f g) TauCeti.summable_half_pow_succ

/-- The comparison distance from any continuous map to itself is `0`. -/
@[simp]
theorem continuousMapDist_self (f : C(X, Y)) : K.continuousMapDist f f = 0 := by
  simp [continuousMapDist_def]

/-- `K.continuousMapDist` is symmetric. -/
theorem continuousMapDist_comm (f g : C(X, Y)) :
    K.continuousMapDist f g = K.continuousMapDist g f := by
  simp_rw [continuousMapDist_def, dist_comm (f.restrict _)]

/-- `K.continuousMapDist` is nonnegative. -/
theorem continuousMapDist_nonneg (f g : C(X, Y)) : 0 ≤ K.continuousMapDist f g :=
  tsum_nonneg (K.continuousMapDistTerm_nonneg f g)

/-- Every comparison distance is strictly less than `1`, since each stage ratio `s_n / (1 + s_n)`
is strictly less than `1`. -/
theorem continuousMapDist_lt_one (f g : C(X, Y)) : K.continuousMapDist f g < 1 := by
  rw [← TauCeti.tsum_half_pow_succ, continuousMapDist_def]
  exact TauCeti.summable_half_pow_succ.tsum_lt_tsum_of_nonneg
    (K.continuousMapDistTerm_nonneg f g)
    (K.continuousMapDistTerm_le_half_pow_succ f g)
    (K.continuousMapDistTerm_lt_half_pow_succ f g 0)

/-- Every comparison distance is at most `1`. -/
theorem continuousMapDist_le_one (f g : C(X, Y)) : K.continuousMapDist f g ≤ 1 :=
  (K.continuousMapDist_lt_one f g).le

/-- Triangle inequality for `K.continuousMapDist`. -/
theorem continuousMapDist_triangle (f g h : C(X, Y)) :
    K.continuousMapDist f h ≤ K.continuousMapDist f g + K.continuousMapDist g h := by
  have hfg := K.summable_continuousMapDist_term f g
  have hgh := K.summable_continuousMapDist_term g h
  rw [continuousMapDist_def, continuousMapDist_def, continuousMapDist_def, ← hfg.tsum_add hgh]
  refine (K.summable_continuousMapDist_term f h).tsum_le_tsum (fun n ↦ ?_) (hfg.add hgh)
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  set a := dist (f.restrict (K n)) (g.restrict (K n))
  set b := dist (g.restrict (K n)) (h.restrict (K n))
  set c := dist (f.restrict (K n)) (h.restrict (K n))
  have ha : 0 ≤ a := dist_nonneg
  have hb : 0 ≤ b := dist_nonneg
  have hc : 0 ≤ c := dist_nonneg
  have htri : c ≤ a + b := dist_triangle _ _ _
  have hmono : c / (1 + c) ≤ (a + b) / (1 + (a + b)) :=
    (div_le_div_iff₀ (by linarith) (by linarith)).mpr (by linarith)
  rw [add_div] at hmono
  exact hmono.trans (add_le_add (div_le_div_of_nonneg_left ha (by linarith) (by linarith))
    (div_le_div_of_nonneg_left hb (by linarith) (by linarith)))

/-- On an empty domain `X`, `K.continuousMapDist` vanishes identically. -/
@[simp]
theorem continuousMapDist_of_isEmpty [IsEmpty X] (f g : C(X, Y)) :
    K.continuousMapDist f g = 0 := by
  obtain rfl : f = g := Subsingleton.elim f g
  exact K.continuousMapDist_self f

/-- When every stage `K n` has the same supremum distance `c`, `K.continuousMapDist f g` evaluates
in closed form to `c / (1 + c)`. -/
theorem continuousMapDist_eq_of_forall_dist_restrict_eq {f g : C(X, Y)} {c : ℝ}
    (hc : ∀ n, dist (f.restrict (K n)) (g.restrict (K n)) = c) :
    K.continuousMapDist f g = c / (1 + c) := by
  simp_rw [continuousMapDist_def, hc, tsum_mul_right, TauCeti.tsum_half_pow_succ, one_mul]

/-- If stage `0` of `K` is nonempty, the comparison distance between two constant maps
`ContinuousMap.const X a` and `ContinuousMap.const X b` equals `dist a b / (1 + dist a b)`. -/
theorem continuousMapDist_const_of_nonempty (hK : (K 0).Nonempty) (a b : Y) :
    K.continuousMapDist (ContinuousMap.const X a) (ContinuousMap.const X b) =
      dist a b / (1 + dist a b) :=
  K.continuousMapDist_eq_of_forall_dist_restrict_eq fun n ↦ by
    have : Nonempty (K n) := (hK.mono (K.subset n.zero_le)).to_subtype
    exact ContinuousMap.dist_const a b

/-- Summability of the companion comparison series formed with `min 1 s_n`. -/
theorem summable_half_pow_succ_mul_min_one_dist_restrict (f g : C(X, Y)) :
    Summable fun n : ℕ ↦
      (1 / 2 : ℝ) ^ (n + 1) * min 1 (dist (f.restrict (K n)) (g.restrict (K n))) :=
  Summable.of_nonneg_of_le
    (fun _ ↦ mul_nonneg (by positivity) (le_min zero_le_one dist_nonneg))
    (fun _ ↦ mul_le_of_le_one_right (by positivity) (min_le_left 1 _))
    TauCeti.summable_half_pow_succ

/-- Lower comparison of `K.continuousMapDist` against the `min 1 s_n` series; equality holds for
constant maps at distance `1` when `(K 0).Nonempty`
(`half_tsum_min_one_eq_continuousMapDist_const`). -/
theorem half_tsum_min_one_le_continuousMapDist (f g : C(X, Y)) :
    (1 / 2 : ℝ) *
      (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * min 1 (dist (f.restrict (K n)) (g.restrict (K n)))) ≤
      K.continuousMapDist f g := by
  rw [← tsum_mul_left, continuousMapDist_def]
  refine ((K.summable_half_pow_succ_mul_min_one_dist_restrict f g).mul_left _).tsum_le_tsum
    (fun n ↦ ?_) (K.summable_continuousMapDist_term f g)
  set t := dist (f.restrict (K n)) (g.restrict (K n))
  have ht : 0 ≤ t := dist_nonneg
  have hmin : min 1 t / 2 ≤ t / (1 + t) := by
    rcases le_total t 1 with h1 | h1
    · rw [min_eq_right h1]
      exact div_le_div_of_nonneg_left ht (by linarith) (by linarith)
    · rw [min_eq_left h1]
      exact (div_le_div_iff₀ (by norm_num) (by linarith)).mpr (by linarith)
  calc (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ (n + 1) * min 1 t)
      = (1 / 2 : ℝ) ^ (n + 1) * (min 1 t / 2) := by ring
    _ ≤ (1 / 2 : ℝ) ^ (n + 1) * (t / (1 + t)) := mul_le_mul_of_nonneg_left hmin (by positivity)

/-- Equality holds in `half_tsum_min_one_le_continuousMapDist` for constant maps at distance `1`
whenever stage `0` of `K` is nonempty. -/
theorem half_tsum_min_one_eq_continuousMapDist_const (hK : (K 0).Nonempty) {a b : Y}
    (hab : dist a b = 1) :
    (1 / 2 : ℝ) *
      (∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) *
        min 1 (dist ((ContinuousMap.const X a).restrict (K n))
          ((ContinuousMap.const X b).restrict (K n)))) =
      K.continuousMapDist (ContinuousMap.const X a) (ContinuousMap.const X b) := by
  have hdist (n : ℕ) :
      dist ((ContinuousMap.const X a).restrict (K n))
        ((ContinuousMap.const X b).restrict (K n)) = dist a b := by
    have : Nonempty (K n) := (hK.mono (K.subset n.zero_le)).to_subtype
    exact ContinuousMap.dist_const a b
  rw [K.continuousMapDist_const_of_nonempty hK, hab]
  simp_rw [hdist, hab, min_self, mul_one, TauCeti.tsum_half_pow_succ]
  norm_num

/-- Upper comparison of `K.continuousMapDist` against the `min 1 s_n` series. -/
theorem continuousMapDist_le_tsum_min_one (f g : C(X, Y)) :
    K.continuousMapDist f g ≤
      ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * min 1 (dist (f.restrict (K n)) (g.restrict (K n))) := by
  rw [continuousMapDist_def]
  refine (K.summable_continuousMapDist_term f g).tsum_le_tsum (fun n ↦ ?_)
    (K.summable_half_pow_succ_mul_min_one_dist_restrict f g)
  have ht : 0 ≤ dist (f.restrict (K n)) (g.restrict (K n)) := dist_nonneg
  refine mul_le_mul_of_nonneg_left (le_min ?_ (div_le_self ht (by linarith))) (by positivity)
  exact ((div_lt_one (by linarith)).mpr (by linarith)).le

/-- Each stage term is bounded above by the full comparison distance `K.continuousMapDist f g`. -/
theorem mul_div_one_add_dist_restrict_le_continuousMapDist (f g : C(X, Y)) (n : ℕ) :
    (1 / 2 : ℝ) ^ (n + 1) *
      (dist (f.restrict (K n)) (g.restrict (K n)) /
        (1 + dist (f.restrict (K n)) (g.restrict (K n)))) ≤ K.continuousMapDist f g :=
  (K.summable_continuousMapDist_term f g).le_tsum n fun m _ ↦ K.continuousMapDistTerm_nonneg f g m

/-- Quantitative single-stage bound: `K.continuousMapDist f g < (1 / 2) ^ (n + 1) * (ε / (1 + ε))`
forces the supremum distance on `K n` to be `< ε`. -/
theorem dist_restrict_lt_of_continuousMapDist_lt {f g : C(X, Y)} {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (h : K.continuousMapDist f g < (1 / 2 : ℝ) ^ (n + 1) * (ε / (1 + ε))) :
    dist (f.restrict (K n)) (g.restrict (K n)) < ε := by
  have hterm := (K.mul_div_one_add_dist_restrict_le_continuousMapDist f g n).trans_lt h
  have hdiv := lt_of_mul_lt_mul_left hterm (by positivity : (0 : ℝ) ≤ (1 / 2) ^ (n + 1))
  refine lt_of_not_ge fun hge ↦ ?_
  exact ((div_le_div_iff₀ (by linarith) (by linarith)).mpr (by linarith)).not_gt hdiv

/-- Quantitative compact-subset bound: for any compact `s ⊆ K n`,
`K.continuousMapDist f g < (1 / 2) ^ (n + 1) * (ε / (1 + ε))` implies
`dist (f.restrict s) (g.restrict s) < ε`. -/
theorem dist_restrict_lt_of_subset_of_continuousMapDist_lt {f g : C(X, Y)} {s : Set X}
    [CompactSpace s] {n : ℕ} (hs : s ⊆ K n) {ε : ℝ} (hε : 0 < ε)
    (h : K.continuousMapDist f g < (1 / 2 : ℝ) ^ (n + 1) * (ε / (1 + ε))) :
    dist (f.restrict s) (g.restrict s) < ε :=
  (f.dist_restrict_le_of_subset g hs).trans_lt (K.dist_restrict_lt_of_continuousMapDist_lt hε h)

/-- Pointwise consequence on `K n` when
`K.continuousMapDist f g < (1 / 2) ^ (n + 1) * (ε / (1 + ε))`. -/
theorem dist_apply_lt_of_continuousMapDist_lt {f g : C(X, Y)} {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (h : K.continuousMapDist f g < (1 / 2 : ℝ) ^ (n + 1) * (ε / (1 + ε))) {x : X} (hx : x ∈ K n) :
    dist (f x) (g x) < ε :=
  (ContinuousMap.dist_apply_le_dist ⟨x, hx⟩).trans_lt
    (K.dist_restrict_lt_of_continuousMapDist_lt hε h)

/-- Quantitative head-plus-tail upper bound splitting `K.continuousMapDist f g` at stage `n`. -/
theorem continuousMapDist_le_div_one_add_add_half_pow_succ (f g : C(X, Y)) (n : ℕ) :
    K.continuousMapDist f g ≤
      dist (f.restrict (K n)) (g.restrict (K n)) /
        (1 + dist (f.restrict (K n)) (g.restrict (K n))) + (1 / 2 : ℝ) ^ (n + 1) := by
  have hs := K.summable_continuousMapDist_term f g
  rw [continuousMapDist_def, ← hs.sum_add_tsum_nat_add (n + 1)]
  set s := dist (f.restrict (K n)) (g.restrict (K n))
  have hs0 : 0 ≤ s := dist_nonneg
  set t := s / (1 + s)
  have ht0 : 0 ≤ t := div_nonneg hs0 (by linarith)
  have hhead : ∑ m ∈ Finset.range (n + 1), K.continuousMapDistTerm f g m ≤ t := by
    calc ∑ m ∈ Finset.range (n + 1), K.continuousMapDistTerm f g m
        ≤ ∑ m ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ (m + 1) * t := by
          refine Finset.sum_le_sum fun m hm ↦ mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hm0 : 0 ≤ dist (f.restrict (K m)) (g.restrict (K m)) := dist_nonneg
          have hmn := K.dist_restrict_mono f g (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))
          exact (div_le_div_iff₀ (by linarith) (by linarith)).mpr (by linarith)
      _ = (∑ m ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ (m + 1)) * t := (Finset.sum_mul ..).symm
      _ ≤ 1 * t := mul_le_mul_of_nonneg_right (TauCeti.sum_half_pow_succ_le_one (n + 1)) ht0
      _ = t := one_mul t
  have htail : (∑' k : ℕ, K.continuousMapDistTerm f g (k + (n + 1))) ≤ (1 / 2 : ℝ) ^ (n + 1) := by
    rw [← TauCeti.tsum_half_pow_add_succ (n + 1)]
    exact (hs.comp_injective (add_left_injective (n + 1))).tsum_le_tsum
      (fun k ↦ K.continuousMapDistTerm_le_half_pow_succ f g (k + (n + 1)))
      (TauCeti.summable_half_pow_succ.comp_injective (add_left_injective (n + 1)))
  exact add_le_add hhead htail

/-- Simplified head-plus-tail upper bound
`K.continuousMapDist f g ≤ s_n(f, g) + (1 / 2) ^ (n + 1)`. -/
theorem continuousMapDist_le_dist_restrict_add_half_pow_succ (f g : C(X, Y)) (n : ℕ) :
    K.continuousMapDist f g ≤ dist (f.restrict (K n)) (g.restrict (K n)) + (1 / 2 : ℝ) ^ (n + 1) :=
  have hs0 : 0 ≤ dist (f.restrict (K n)) (g.restrict (K n)) := dist_nonneg
  (K.continuousMapDist_le_div_one_add_add_half_pow_succ f g n).trans
    (add_le_add (div_le_self hs0 (by linarith)) le_rfl)

/-- **Equality of uniformities.** The metric entourages of `K.continuousMapDist` generate the exact
compact-convergence uniformity `𝓤 C(X, Y)`. -/
theorem uniformity_eq_iInf_continuousMapDist :
    𝓤 C(X, Y) = ⨅ ε > 0, 𝓟 {fg : C(X, Y) × C(X, Y) | K.continuousMapDist fg.1 fg.2 < ε} := by
  have hb₁ := K.hasBasis_compactConvergenceUniformity (Metric.uniformity_basis_dist (α := Y))
  have hb₂ : HasBasis (⨅ ε > 0, 𝓟 {fg : C(X, Y) × C(X, Y) | K.continuousMapDist fg.1 fg.2 < ε})
      (0 < ·) (fun ε ↦ {fg | K.continuousMapDist fg.1 fg.2 < ε}) :=
    hasBasis_biInf_principal'
      (fun a ha b hb ↦ ⟨min a b, lt_min ha hb,
        fun _ h ↦ h.trans_le (min_le_left a b), fun _ h ↦ h.trans_le (min_le_right a b)⟩)
      ⟨1, zero_lt_one⟩
  refine le_antisymm (hb₂.ge_iff.mpr ?_) (hb₁.ge_iff.mpr ?_)
  · intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1 / 2 : ℝ) < 1)
    have hn' : (1 / 2 : ℝ) ^ (n + 1) < ε / 2 :=
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) n.le_succ).trans_lt hn
    refine hb₁.mem_iff.mpr ⟨(n, ε / 2), half_pos hε, fun fg hfg ↦ ?_⟩
    have hsup : dist (fg.1.restrict (K n)) (fg.2.restrict (K n)) < ε / 2 :=
      (ContinuousMap.dist_lt_iff (half_pos hε)).mpr fun x ↦ hfg x.val x.property
    exact (K.continuousMapDist_le_dist_restrict_add_half_pow_succ fg.1 fg.2 n).trans_lt
      (by linarith)
  · rintro ⟨n, ε⟩ hε
    refine hb₂.mem_iff.mpr
      ⟨(1 / 2 : ℝ) ^ (n + 1) * (ε / (1 + ε)), by positivity, fun fg hfg x hx ↦
        K.dist_apply_lt_of_continuousMapDist_lt hε hfg hx⟩

/-- Explicit `PseudoMetricSpace` structure on `C(X, Y)` attached to `K`, with `toUniformSpace`
definitionally equal to `ContinuousMap.compactConvergenceUniformSpace`. Not registered as an
instance so that `C(X, Y)` does not acquire an exhaustion-dependent metric typeclass. -/
@[expose, instance_reducible]
noncomputable def continuousMapPseudoMetricSpace : PseudoMetricSpace C(X, Y) where
  dist := K.continuousMapDist
  dist_self := K.continuousMapDist_self
  dist_comm := K.continuousMapDist_comm
  dist_triangle := K.continuousMapDist_triangle
  toUniformSpace := ContinuousMap.compactConvergenceUniformSpace
  uniformity_dist := K.uniformity_eq_iInf_continuousMapDist

/-- The uniform space generated directly by `K.continuousMapDist` agrees with
`ContinuousMap.compactConvergenceUniformSpace`. -/
theorem uniformSpace_ofDist_continuousMapDist :
    UniformSpace.ofDist (K.continuousMapDist (Y := Y)) K.continuousMapDist_self
      K.continuousMapDist_comm K.continuousMapDist_triangle =
      ContinuousMap.compactConvergenceUniformSpace :=
  UniformSpace.ext (K.uniformity_eq_iInf_continuousMapDist (Y := Y)).symm

/-- **Exhaustion independence.** Any two compact exhaustions of `X` induce the same uniform space on
`C(X, Y)` via their comparison distances. -/
theorem uniformSpace_ofDist_continuousMapDist_eq (K' : CompactExhaustion X) :
    UniformSpace.ofDist (K.continuousMapDist (Y := Y)) K.continuousMapDist_self
      K.continuousMapDist_comm K.continuousMapDist_triangle =
      UniformSpace.ofDist (K'.continuousMapDist (Y := Y)) K'.continuousMapDist_self
        K'.continuousMapDist_comm K'.continuousMapDist_triangle := by
  rw [K.uniformSpace_ofDist_continuousMapDist, K'.uniformSpace_ofDist_continuousMapDist]

/-- Convergence in `C(X, Y)` is equivalent to `K.continuousMapDist` tending to `0`. -/
theorem tendsto_iff_tendsto_continuousMapDist {ι : Type*} {p : Filter ι} {F : ι → C(X, Y)}
    {f : C(X, Y)} :
    Tendsto F p (𝓝 f) ↔ Tendsto (fun i ↦ K.continuousMapDist (F i) f) p (𝓝 0) :=
  @tendsto_iff_dist_tendsto_zero _ _ (K.continuousMapPseudoMetricSpace (Y := Y)) F p f

/-- Convergence for `K.continuousMapDist` is uniform convergence on every compact subset of `X`. -/
theorem tendsto_continuousMapDist_iff_forall_isCompact {ι : Type*} {p : Filter ι}
    {F : ι → C(X, Y)} {f : C(X, Y)} :
    Tendsto (fun i ↦ K.continuousMapDist (F i) f) p (𝓝 0) ↔
      ∀ s, IsCompact s → TendstoUniformlyOn (fun i x ↦ F i x) f p s := by
  rw [← K.tendsto_iff_tendsto_continuousMapDist,
    ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]

/-- Filter-level Cauchy equivalence between the compact-convergence uniformity and
`K.continuousMapDist`. -/
theorem cauchy_map_iff_tendsto_continuousMapDist {ι : Type*} {p : Filter ι} {F : ι → C(X, Y)} :
    Cauchy (map F p) ↔
      p.NeBot ∧
        Tendsto (fun ij : ι × ι ↦ K.continuousMapDist (F ij.1) (F ij.2)) (p ×ˢ p) (𝓝 0) := by
  rw [cauchy_map_iff,
    (@Metric.uniformity_basis_dist C(X, Y)
      (K.continuousMapPseudoMetricSpace (Y := Y))).tendsto_right_iff]
  refine and_congr_right fun _ ↦ ?_
  rw [Metric.tendsto_nhds]
  simp only [Real.dist_eq, sub_zero]
  refine ⟨fun h ε hε ↦ (h ε hε).mono fun ij hij ↦ ?_,
    fun h ε hε ↦ (h ε hε).mono fun ij hij ↦ ?_⟩
  · rw [abs_of_nonneg (K.continuousMapDist_nonneg (F ij.1) (F ij.2))]
    exact hij
  · rwa [abs_of_nonneg (K.continuousMapDist_nonneg (F ij.1) (F ij.2))] at hij

/-- Directed-net `CauchySeq` in `C(X, Y)` is equivalent to the metric Cauchy condition for
`K.continuousMapDist`. -/
theorem cauchySeq_iff_continuousMapDist {ι : Type*} [Nonempty ι] [SemilatticeSup ι]
    {u : ι → C(X, Y)} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, K.continuousMapDist (u m) (u n) < ε :=
  @Metric.cauchySeq_iff _ _ (K.continuousMapPseudoMetricSpace (Y := Y)) _ _ u

/-- The `ε`-`δ` uniform-continuity condition for restriction to a compact subset `s` with respect
to `K.continuousMapDist`. -/
theorem exists_pos_forall_dist_restrict_lt (s : Set X) [CompactSpace s] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ f g : C(X, Y), K.continuousMapDist f g < δ →
      dist (f.restrict s) (g.restrict s) < ε := by
  obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact (isCompact_iff_compactSpace.mpr ‹_›)
  exact ⟨(1 / 2 : ℝ) ^ (n + 1) * (ε / (1 + ε)), by positivity,
    fun f g hfg ↦ K.dist_restrict_lt_of_subset_of_continuousMapDist_lt hn hε hfg⟩

/-- Every directed net in a closed subset `S ⊆ C(X, Y)` that is Cauchy for `K.continuousMapDist`
converges in `K.continuousMapDist` to a limit in `S` when `Y` is complete. -/
theorem exists_tendsto_continuousMapDist_of_isClosed [CompleteSpace Y] {S : Set C(X, Y)}
    (hS : IsClosed S) {ι : Type*} [Nonempty ι] [SemilatticeSup ι] {u : ι → C(X, Y)}
    (huS : ∀ n, u n ∈ S)
    (hc : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, K.continuousMapDist (u m) (u n) < ε) :
    ∃ f ∈ S, Tendsto (fun n ↦ K.continuousMapDist (u n) f) atTop (𝓝 0) := by
  have : CompleteSpace C(X, Y) := K.completeSpace_continuousMap
  have hcs : CauchySeq u := K.cauchySeq_iff_continuousMapDist.mpr hc
  obtain ⟨f, hfS, hfu⟩ := cauchySeq_tendsto_of_isComplete hS.isComplete huS hcs
  exact ⟨f, hfS, K.tendsto_iff_tendsto_continuousMapDist.mp hfu⟩

end PseudoMetricSpace

section SeminormedAddCommGroup

variable {X Y : Type*} [TopologicalSpace X] [SeminormedAddCommGroup Y] (K : CompactExhaustion X)

/-- In a seminormed additive group target, shifting `f` by `ContinuousMap.const X c` gives
comparison distance `‖c‖ / (1 + ‖c‖)` whenever stage `0` of `K` is nonempty. -/
theorem continuousMapDist_add_const_of_nonempty (hK : (K 0).Nonempty) (f : C(X, Y)) (c : Y) :
    K.continuousMapDist (f + ContinuousMap.const X c) f = ‖c‖ / (1 + ‖c‖) := by
  refine K.continuousMapDist_eq_of_forall_dist_restrict_eq fun n ↦ le_antisymm ?_ ?_
  · refine (ContinuousMap.dist_le (norm_nonneg c)).mpr fun _ ↦ ?_
    simp [dist_eq_norm]
  · obtain ⟨x, hx⟩ := hK.mono (K.subset n.zero_le)
    simpa [dist_eq_norm] using ContinuousMap.dist_apply_le_dist
      (f := (f + ContinuousMap.const X c).restrict (K n))
      (g := f.restrict (K n)) ⟨x, hx⟩

end SeminormedAddCommGroup

section MetricSpace

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] (K : CompactExhaustion X)

/-- When `Y` is a `MetricSpace`, `K.continuousMapDist` separates distinct continuous maps because
the compact stages `K n` cover `X`. -/
@[simp]
theorem continuousMapDist_eq_zero_iff {f g : C(X, Y)} :
    K.continuousMapDist f g = 0 ↔ f = g := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ K.continuousMapDist_self f⟩
  ext x
  obtain ⟨n, hxn⟩ := K.exists_mem x
  have hterm : K.continuousMapDistTerm f g n = 0 :=
    le_antisymm
      ((K.mul_div_one_add_dist_restrict_le_continuousMapDist f g n).trans_eq h)
      (K.continuousMapDistTerm_nonneg f g n)
  rw [continuousMapDistTerm, mul_eq_zero, div_eq_zero_iff] at hterm
  rcases hterm with hpow | hsn | hden
  · exfalso; exact (by positivity : (0 : ℝ) < (1 / 2) ^ (n + 1)).ne' hpow
  · exact dist_le_zero.mp ((ContinuousMap.dist_apply_le_dist ⟨x, hxn⟩).trans_eq hsn)
  · exfalso; linarith [@dist_nonneg _ _ (f.restrict (K n)) (g.restrict (K n))]

/-- Explicit `MetricSpace` structure on `C(X, Y)` attached to `K`, with `toUniformSpace`
definitionally equal to `ContinuousMap.compactConvergenceUniformSpace`. Not registered as an
instance. -/
@[expose, instance_reducible]
noncomputable def continuousMapMetricSpace : MetricSpace C(X, Y) where
  toPseudoMetricSpace := K.continuousMapPseudoMetricSpace
  eq_of_dist_eq_zero h := K.continuousMapDist_eq_zero_iff.mp h

end MetricSpace

end CompactExhaustion
