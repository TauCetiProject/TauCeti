/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Finite nets on Euclidean spheres

In an `n`-dimensional Euclidean space, the unit sphere has a finite `ε`-cover of cardinality at
most `(1 + 2 / ε)^n`. The proof uses a maximal separated set and the volume comparison for
disjoint balls.

## References

* R. Vershynin, *High-Dimensional Probability*, 2018, §4.2.
-/

public section

open MeasureTheory Metric
open scoped ENNReal NNReal

namespace EuclideanSpace

private theorem ncard_le_of_isSeparated_unitBall {n : ℕ} (hn : 0 < n)
    {ε : ℝ≥0} (hε : 0 < ε) {s : Set (EuclideanSpace ℝ (Fin n))} (hsf : s.Finite)
    (hs : s ⊆ closedBall 0 1) (hsep : IsSeparated (ε : ℝ≥0∞) s) :
    (s.ncard : ℝ) ≤ (1 + 2 / (ε : ℝ)) ^ n := by
  have hne : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let r : ℝ := (ε : ℝ) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hsep' (x y : EuclideanSpace ℝ (Fin n)) (hx : x ∈ s) (hy : y ∈ s)
      (hxy : x ≠ y) : (ε : ℝ) < dist x y := by
    have h := hsep hx hy hxy
    have h' : ENNReal.ofReal (ε : ℝ) < ENNReal.ofReal (dist x y) := by
      simpa [edist_dist] using h
    exact (ENNReal.ofReal_lt_ofReal_iff (dist_pos.mpr hxy)).mp h'
  have hdisj :
      Set.PairwiseDisjoint (hsf.toFinset : Set (EuclideanSpace ℝ (Fin n))) (fun x ↦ ball x r) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    have hdist := hsep' x y (by simpa using hx) (by simpa using hy) hxy
    dsimp [r]
    nlinarith
  have hunion_subset : (⋃ x ∈ hsf.toFinset, ball x r) ⊆ ball 0 (1 + r) := by
    intro z hz
    simp only [Set.mem_iUnion, exists_prop] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    have hxnorm : ‖x‖ ≤ 1 := by
      simpa [mem_closedBall, dist_eq_norm] using hs (by simpa using hx)
    have hdist : dist z x < r := by simpa using hzx
    rw [Metric.mem_ball, dist_zero_right]
    have htriangle : ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by
      calc
        ‖z‖ = ‖(z - x) + x‖ := by congr 1; abel
        _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
    have hdist' : ‖z - x‖ < r := by simpa [dist_eq_norm] using hdist
    linarith
  have hvol :
      (hsf.toFinset.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) r) ≤
        volume (ball (0 : EuclideanSpace ℝ (Fin n)) (1 + r)) := by
    calc
      (hsf.toFinset.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) r)
          = volume (⋃ x ∈ hsf.toFinset, ball x r) := by
              rw [measure_biUnion_finset hdisj (fun _ _ ↦ measurableSet_ball)]
              simp [EuclideanSpace.volume_ball, Finset.sum_const, nsmul_eq_mul]
      _ ≤ volume (ball 0 (1 + r)) := measure_mono hunion_subset
  let c : ℝ := Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)
  have hball (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
      volume (ball x t) = ENNReal.ofReal t ^ n * ENNReal.ofReal c := by
    simpa [c, Fintype.card_fin] using
      (@EuclideanSpace.volume_ball (Fin n) hne inferInstance x t)
  have hc : 0 < (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)) := by
    apply div_pos
    · positivity
    · exact Real.Gamma_pos_of_pos (by positivity)
  have hcard : (hsf.toFinset.card : ℝ≥0∞) =
      ENNReal.ofReal (hsf.toFinset.card : ℝ) := (ENNReal.ofReal_natCast _).symm
  have hreal :
      (hsf.toFinset.card : ℝ) * r ^ n *
          (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)) ≤
        (1 + r) ^ n * (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)) := by
    have hvol' := hvol
    rw [hball 0 r, hball 0 (1 + r)] at hvol'
    rw [hcard, ← ENNReal.ofReal_pow (by positivity : 0 ≤ r) n,
      ← ENNReal.ofReal_pow (by positivity : 0 ≤ 1 + r) n] at hvol'
    rw [← ENNReal.ofReal_mul (p := r ^ n) (q := c) (by positivity),
      ← ENNReal.ofReal_mul (p := (hsf.toFinset.card : ℝ)) (q := r ^ n * c) (by positivity),
      ← ENNReal.ofReal_mul (p := (1 + r) ^ n) (q := c) (by positivity)] at hvol'
    have hvol'' : ENNReal.ofReal
        ((hsf.toFinset.card : ℝ) * r ^ n *
          (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1))) ≤
        ENNReal.ofReal
        ((1 + r) ^ n *
          (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1))) := by
      simpa only [c, mul_assoc] using hvol'
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hvol''
  have hcancel : (hsf.toFinset.card : ℝ) * r ^ n ≤ (1 + r) ^ n := by
    apply (mul_le_mul_iff_right₀ hc).mp
    simpa [mul_assoc, mul_comm, mul_left_comm] using hreal
  have hrpow : 0 < r ^ n := pow_pos hr _
  have hratio : (hsf.toFinset.card : ℝ) ≤ ((1 + r) / r) ^ n := by
    calc
      (hsf.toFinset.card : ℝ) =
          ((hsf.toFinset.card : ℝ) * r ^ n) / r ^ n := by field_simp
      _ ≤ (1 + r) ^ n / r ^ n := div_le_div_of_nonneg_right hcancel hrpow.le
      _ = ((1 + r) / r) ^ n := by rw [← div_pow]
  have heq : (1 + r) / r = 1 + 2 / (ε : ℝ) := by
    dsimp [r]
    field_simp
    ring
  simpa [Set.ncard_eq_toFinset_card s hsf, heq] using hratio

/-- Every Euclidean unit sphere in positive finite dimension has a finite `ε`-cover whose
cardinality is at most `(1 + 2 / ε)^n`. The cover points lie on the sphere. -/
theorem exists_finite_isCover_sphere_card_le (n : ℕ) (hn : 0 < n) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ N : Set (EuclideanSpace ℝ (Fin n)),
      N.Finite ∧ N ⊆ sphere 0 1 ∧ IsCover ε (sphere 0 1) N ∧
        (N.ncard : ℝ) ≤ (1 + 2 / (ε : ℝ)) ^ n := by
  obtain ⟨C, hCsubset, hCfinite, hCcover⟩ :=
    exists_finite_isCover_of_isCompact (ε := ε / 2) (ne_of_gt (by positivity))
      (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  have hpack : packingNumber ε (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ := by
    apply ne_of_lt
    have hεmul : 2 * (ε / 2) = ε := by
      calc
        2 * (ε / 2) = (ε / 2) * 2 := mul_comm _ _
        _ = ε := div_mul_cancel₀ _ (by norm_num : (2 : ℝ≥0) ≠ 0)
    calc
      packingNumber ε (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
          = packingNumber (2 * (ε / 2)) (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by rw [hεmul]
      _ ≤ externalCoveringNumber (ε / 2) (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
        packingNumber_two_mul_le_externalCoveringNumber (ε / 2) _
      _ ≤ C.encard := hCcover.externalCoveringNumber_le_encard
      _ < ⊤ := hCfinite.encard_lt_top
  let N := maximalSeparatedSet ε (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
  have hNfinite : N.Finite := by
    apply Set.encard_lt_top_iff.mp
    rw [encard_maximalSeparatedSet hpack]
    exact hpack.lt_top
  refine ⟨N, hNfinite, maximalSeparatedSet_subset, isCover_maximalSeparatedSet hpack, ?_⟩
  exact ncard_le_of_isSeparated_unitBall hn hε hNfinite
    (fun x hx ↦ by
      have hxSphere : x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
        maximalSeparatedSet_subset hx
      rw [mem_closedBall, dist_zero_right]
      exact (mem_sphere_zero_iff_norm.mp hxSphere).le)
    isSeparated_maximalSeparatedSet

end EuclideanSpace
