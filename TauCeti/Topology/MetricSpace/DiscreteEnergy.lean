/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Discrete energy of finite metric paths

The discrete energy of vertices `x₀, …, xₙ` at times `t₀, …, tₙ` is
`½ ∑ dist(xᵢ,xᵢ₊₁)² / (tᵢ₊₁ - tᵢ)`. It is defined before choosing any
interpolating curves. For increasing times, Cauchy–Schwarz bounds the total
edge length and every vertex's distance from the initial vertex by the energy.
A sufficiently fine time mesh therefore forces every edge to be short.

For fixed endpoints, strict energy sublevels are open subsets of the product
of the interior vertex spaces. In a proper metric space their closed energy
sublevels are compact, including as subsets of any larger strict sublevel.
For finite-dimensional manifolds these are the finite-dimensional carriers used
for broken minimizing paths.

The normalization and finite-path construction follow J. Milnor, *Morse Theory*,
§16. The estimates use Mathlib's finite Cauchy–Schwarz inequality.
-/

public section

open scoped BigOperators

namespace TauCeti

variable {M : Type*} [PseudoMetricSpace M] {n : ℕ}

/-- The distance to any vertex of a finite chain is at most its total edge length. -/
theorem dist_le_sum_adjacent_dist (x : Fin (n + 1) → M) (j : Fin (n + 1)) :
    dist (x 0) (x j) ≤ ∑ i : Fin n, dist (x i.castSucc) (x i.succ) := by
  induction n with
  | zero =>
    have hj : j = 0 := Fin.ext (by omega)
    simp [hj]
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · exact le_trans (by simp) (Finset.sum_nonneg fun _ _ => dist_nonneg)
    · calc
        dist (x 0) (x j.succ) ≤ dist (x 0) (x 1) + dist (x 1) (x j.succ) :=
          dist_triangle _ _ _
        _ ≤ dist (x 0) (x 1) +
            ∑ i : Fin n, dist (x i.castSucc.succ) (x i.succ.succ) :=
          add_le_add_right (ih (fun i => x i.succ) j) _
        _ = ∑ i : Fin (n + 1), dist (x i.castSucc) (x i.succ) := by
          rw [Fin.sum_univ_succ]
          rfl

/-- Half the sum of squared edge lengths divided by the corresponding time steps.
Estimates using this energy require strictly increasing times. -/
noncomputable def discreteEnergy (t : Fin (n + 1) → ℝ) (x : Fin (n + 1) → M) : ℝ :=
  (1 / 2) * ∑ i : Fin n, dist (x i.castSucc) (x i.succ) ^ 2 /
    (t i.succ - t i.castSucc)

/-- The defining finite-sum formula for discrete energy. -/
theorem discreteEnergy_def (t : Fin (n + 1) → ℝ) (x : Fin (n + 1) → M) :
    discreteEnergy t x = (1 / 2) * ∑ i : Fin n,
      dist (x i.castSucc) (x i.succ) ^ 2 / (t i.succ - t i.castSucc) := (rfl)

/-- Discrete energy is continuous in all vertices, with no restriction on the times. -/
@[fun_prop]
theorem continuous_discreteEnergy (t : Fin (n + 1) → ℝ) :
    Continuous (discreteEnergy (M := M) t) := by
  unfold discreteEnergy
  fun_prop

@[simp]
theorem discreteEnergy_const (t : Fin (n + 1) → ℝ) (p : M) :
    discreteEnergy t (fun _ => p) = 0 := by
  simp [discreteEnergy]

/-- Discrete energy is nonnegative for increasing times. -/
theorem discreteEnergy_nonneg {t : Fin (n + 1) → ℝ} (ht : StrictMono t)
    (x : Fin (n + 1) → M) : 0 ≤ discreteEnergy t x := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
    div_nonneg (sq_nonneg _) (sub_pos.mpr (ht i.castSucc_lt_succ)).le)

/-- The discrete Cauchy–Schwarz inequality, in squared form. This includes an
empty chain, whose total time and energy are both zero. -/
theorem sq_sum_dist_le_discreteEnergy {t : Fin (n + 1) → ℝ} (ht : StrictMono t)
    (x : Fin (n + 1) → M) :
    (∑ i : Fin n, dist (x i.castSucc) (x i.succ)) ^ 2 ≤
      2 * (t (Fin.last n) - t 0) * discreteEnergy t x := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (f := fun i : Fin n => dist (x i.castSucc) (x i.succ) ^ 2 /
      (t i.succ - t i.castSucc))
    (g := fun i : Fin n => t i.succ - t i.castSucc)
    (fun i _ => div_nonneg (sq_nonneg _) (sub_pos.mpr (ht i.castSucc_lt_succ)).le)
    (fun i _ => (sub_pos.mpr (ht i.castSucc_lt_succ)).le)
    (fun i _ => le_of_eq (div_mul_cancel₀ _ (ne_of_gt
      (sub_pos.mpr (ht i.castSucc_lt_succ)))).symm)
  have htime : (∑ i : Fin n, (t i.succ - t i.castSucc)) = t (Fin.last n) - t 0 := by
    rw [Finset.sum_sub_distrib]
    have hfirst := Fin.sum_univ_succ t
    have hlast := Fin.sum_univ_castSucc t
    linarith
  rw [htime] at h
  unfold discreteEnergy
  nlinarith

/-- Total edge length is bounded by the square root of twice time times energy. -/
theorem sum_dist_le_sqrt_discreteEnergy {t : Fin (n + 1) → ℝ} (ht : StrictMono t)
    (x : Fin (n + 1) → M) :
    ∑ i : Fin n, dist (x i.castSucc) (x i.succ) ≤
      √(2 * (t (Fin.last n) - t 0) * discreteEnergy t x) := by
  exact Real.le_sqrt_of_sq_le (sq_sum_dist_le_discreteEnergy ht x)

/-- Every vertex stays in the energy-controlled closed ball about the first vertex. -/
theorem dist_le_sqrt_discreteEnergy {t : Fin (n + 1) → ℝ} (ht : StrictMono t)
    (x : Fin (n + 1) → M) (j : Fin (n + 1)) :
    dist (x 0) (x j) ≤ √(2 * (t (Fin.last n) - t 0) * discreteEnergy t x) :=
  (dist_le_sum_adjacent_dist x j).trans (sum_dist_le_sqrt_discreteEnergy ht x)

/-- For increasing times in a metric space, zero energy means that every vertex
is the initial vertex. -/
@[simp]
theorem discreteEnergy_eq_zero_iff {M : Type*} [MetricSpace M]
    {t : Fin (n + 1) → ℝ} (ht : StrictMono t) (x : Fin (n + 1) → M) :
    discreteEnergy t x = 0 ↔ ∀ j, x j = x 0 := by
  constructor
  · intro hx j
    have h := dist_le_sqrt_discreteEnergy ht x j
    simp only [hx, mul_zero, Real.sqrt_zero] at h
    exact (dist_le_zero.mp h).symm
  · intro hx
    have hx' : x = fun _ => x 0 := funext hx
    rw [hx']
    exact discreteEnergy_const t _

/-- Each individual squared edge length is bounded by twice energy times its step. -/
theorem dist_sq_le_discreteEnergy_mul_step {t : Fin (n + 1) → ℝ} (ht : StrictMono t)
    (x : Fin (n + 1) → M) (i : Fin n) :
    dist (x i.castSucc) (x i.succ) ^ 2 ≤
      2 * discreteEnergy t x * (t i.succ - t i.castSucc) := by
  have hi := Finset.single_le_sum
    (s := Finset.univ) (f := fun j : Fin n => dist (x j.castSucc) (x j.succ) ^ 2 /
      (t j.succ - t j.castSucc))
    (fun j _ => div_nonneg (sq_nonneg _) (sub_pos.mpr (ht j.castSucc_lt_succ)).le)
    (Finset.mem_univ i)
  have hstep := sub_pos.mpr (ht i.castSucc_lt_succ)
  have := (div_le_iff₀ hstep).mp hi
  unfold discreteEnergy
  nlinarith

/-- A positive cutoff and a fine mesh force every edge in its strict energy
sublevel to have length less than the chosen positive radius. -/
theorem dist_lt_of_discreteEnergy_lt {t : Fin (n + 1) → ℝ} (ht : StrictMono t)
    (x : Fin (n + 1) → M) {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ)
    (hx : discreteEnergy t x < c)
    (hmesh : ∀ i : Fin n, t i.succ - t i.castSucc < ρ ^ 2 / (2 * c))
    (i : Fin n) : dist (x i.castSucc) (x i.succ) < ρ := by
  have hi := dist_sq_le_discreteEnergy_mul_step ht x i
  have hstep := sub_pos.mpr (ht i.castSucc_lt_succ)
  have hmesh' := (lt_div_iff₀ (by positivity : 0 < 2 * c)).mp (hmesh i)
  have hmul := mul_lt_mul_of_pos_right hx hstep
  have hd : 0 ≤ dist (x i.castSucc) (x i.succ) := dist_nonneg
  nlinarith

/-- The open energy carrier with `n` interior vertices and fixed endpoints `p,q`.
The full vertex tuple is formed using the native `Fin.cons` and `Fin.snoc`. -/
def discreteEnergySublevel (t : Fin (n + 2) → ℝ) (p q : M) (c : ℝ) :
    Set (Fin n → M) :=
  {x | discreteEnergy t (Fin.cons p (Fin.snoc x q)) < c}

@[simp]
theorem mem_discreteEnergySublevel {t : Fin (n + 2) → ℝ} {p q : M} {c : ℝ}
    {x : Fin n → M} :
    x ∈ discreteEnergySublevel t p q c ↔
      discreteEnergy t (Fin.cons p (Fin.snoc x q)) < c := Iff.rfl

/-- Strict energy sublevels are open in the full interior-vertex product. -/
theorem isOpen_discreteEnergySublevel (t : Fin (n + 2) → ℝ) (p q : M) (c : ℝ) :
    IsOpen (discreteEnergySublevel t p q c) := by
  exact isOpen_lt ((continuous_discreteEnergy t).comp
    (Continuous.finCons (A := fun _ : Fin (n + 2) => M) continuous_const
      (Continuous.finSnoc (A := fun _ : Fin (n + 1) => M)
        continuous_id continuous_const))) continuous_const

/-- Decreasing the cutoff gives the canonical inclusion of energy carriers. -/
theorem discreteEnergySublevel_mono (t : Fin (n + 2) → ℝ) (p q : M)
    {a c : ℝ} (hac : a ≤ c) :
    discreteEnergySublevel t p q a ⊆ discreteEnergySublevel t p q c :=
  fun _ hx => hx.trans_le hac

/-- Every interior vertex in a strict energy sublevel lies in the corresponding
open ball. -/
theorem dist_lt_sqrt_of_mem_discreteEnergySublevel {t : Fin (n + 2) → ℝ}
    (ht : StrictMono t) {p q : M} {c : ℝ} {x : Fin n → M}
    (hx : x ∈ discreteEnergySublevel t p q c) (j : Fin n) :
    dist p (x j) < √(2 * (t (Fin.last (n + 1)) - t 0) * c) := by
  have hT : 0 < t (Fin.last (n + 1)) - t 0 := sub_pos.mpr (ht Fin.last_pos')
  have hbound := dist_le_sqrt_discreteEnergy ht (Fin.cons p (Fin.snoc x q)) j.castSucc.succ
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.snoc_castSucc] at hbound
  exact hbound.trans_lt (Real.sqrt_lt_sqrt
    (mul_nonneg (by positivity) (discreteEnergy_nonneg ht _))
    (mul_lt_mul_of_pos_left hx (by positivity)))

/-- Closed fixed-endpoint energy sublevels are compact in a proper metric space.
No geodesic interpolation or small-mesh assumption is needed. -/
theorem isCompact_discreteEnergy_le [ProperSpace M] {t : Fin (n + 2) → ℝ}
    (ht : StrictMono t) (p q : M) (a : ℝ) :
    IsCompact {x : Fin n → M | discreteEnergy t (Fin.cons p (Fin.snoc x q)) ≤ a} := by
  have hcont : Continuous (fun x : Fin n → M =>
      discreteEnergy t (Fin.cons p (Fin.snoc x q))) :=
    (continuous_discreteEnergy t).comp
      (Continuous.finCons (A := fun _ : Fin (n + 2) => M) continuous_const
        (Continuous.finSnoc (A := fun _ : Fin (n + 1) => M)
          continuous_id continuous_const))
  refine (isCompact_univ_pi fun _ : Fin n =>
    isCompact_closedBall p (√(2 * (t (Fin.last (n + 1)) - t 0) * a))).of_isClosed_subset
      (isClosed_le hcont continuous_const) ?_
  intro x hx j _
  have hbound := dist_le_sqrt_discreteEnergy ht (Fin.cons p (Fin.snoc x q)) j.castSucc.succ
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.snoc_castSucc] at hbound
  exact Metric.mem_closedBall.mpr ((dist_comm _ _).trans_le (hbound.trans
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hx
      (mul_nonneg (by norm_num) (sub_nonneg.mpr (ht.monotone (Fin.zero_le _))))))))

/-- A lower closed energy sublevel is compact inside the open energy carrier.
In particular these strict carriers have compact energy bands below their cutoff. -/
theorem isCompact_discreteEnergySublevel_le [ProperSpace M] {t : Fin (n + 2) → ℝ}
    (ht : StrictMono t) (p q : M) {a c : ℝ} (hac : a < c) :
    IsCompact {x : discreteEnergySublevel t p q c |
      discreteEnergy t (Fin.cons p (Fin.snoc (x : Fin n → M) q)) ≤ a} := by
  exact Topology.IsInducing.subtypeVal.isCompact_preimage'
    (isCompact_discreteEnergy_le ht p q a)
    (fun x hx => ⟨⟨x, hx.trans_lt hac⟩, rfl⟩)

end TauCeti
