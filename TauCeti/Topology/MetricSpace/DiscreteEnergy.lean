/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Real.Sqrt
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

The broken-geodesic finite-dimensional approximation is described in J. Milnor,
*Morse Theory*, §16. Here energy is defined on arbitrary vertex tuples before
interpolation, with a factor of `½`: it is half Milnor's energy on broken
minimizing geodesics. The estimates use Mathlib's finite Cauchy–Schwarz inequality.
-/

public section

open scoped BigOperators

namespace TauCeti

variable {M : Type*} [PseudoMetricSpace M] {n : ℕ}

/-- The distance from the first vertex to any vertex of a finite chain is at most
its total edge length. -/
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
        dist (x 0) (x j.succ) ≤
            dist (x 0) (x (Fin.succ 0)) + dist (x (Fin.succ 0)) (x j.succ) :=
          dist_triangle _ _ _
        _ ≤ dist (x 0) (x (Fin.succ 0)) +
            ∑ i : Fin n, dist (x i.castSucc.succ) (x i.succ.succ) :=
          add_le_add_right (ih (fun i => x i.succ) j) _
        _ = ∑ i : Fin (n + 1), dist (x i.castSucc) (x i.succ) := by
          simp only [Fin.sum_univ_succ, Fin.castSucc_zero, Fin.castSucc_succ]

/-- Half the sum of squared edge lengths divided by the corresponding time steps.
Edge-length estimates using this energy require strictly increasing times. -/
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

/-- Every time step in the discrete energy is positive for strictly increasing times. -/
theorem discreteEnergy_step_pos {t : Fin (n + 1) → ℝ} (ht : StrictMono t)
    (i : Fin n) : 0 < t i.succ - t i.castSucc :=
  sub_pos.mpr (ht i.castSucc_lt_succ)

/-- Each discrete-energy summand is nonnegative for nondecreasing times. -/
theorem discreteEnergy_summand_nonneg {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (x : Fin (n + 1) → M) (i : Fin n) :
    0 ≤ dist (x i.castSucc) (x i.succ) ^ 2 / (t i.succ - t i.castSucc) :=
  div_nonneg (sq_nonneg _) (sub_nonneg.mpr (ht i.castSucc_le_succ))

/-- Discrete energy is nonnegative for nondecreasing times. -/
theorem discreteEnergy_nonneg {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (x : Fin (n + 1) → M) : 0 ≤ discreteEnergy t x := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
    discreteEnergy_summand_nonneg ht x i)

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
    (fun i _ => discreteEnergy_summand_nonneg ht.monotone x i)
    (fun i _ => (discreteEnergy_step_pos ht i).le)
    (fun i _ => le_of_eq (div_mul_cancel₀ _ (discreteEnergy_step_pos ht i).ne').symm)
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
    (fun j _ => discreteEnergy_summand_nonneg ht.monotone x j)
    (Finset.mem_univ i)
  have hstep := discreteEnergy_step_pos ht i
  have := (div_le_iff₀ hstep).mp hi
  unfold discreteEnergy
  nlinarith

/-- A fine mesh forces every edge in a strict energy sublevel to have length
less than the chosen positive radius. -/
theorem dist_lt_of_discreteEnergy_lt {t : Fin (n + 1) → ℝ} (ht : StrictMono t)
    (x : Fin (n + 1) → M) {c ρ : ℝ} (hρ : 0 < ρ)
    (hx : discreteEnergy t x < c)
    (hmesh : ∀ i : Fin n, t i.succ - t i.castSucc < ρ ^ 2 / (2 * c))
    (i : Fin n) : dist (x i.castSucc) (x i.succ) < ρ := by
  have hc : 0 < c := (discreteEnergy_nonneg ht.monotone x).trans_lt hx
  have hi := dist_sq_le_discreteEnergy_mul_step ht x i
  have hstep := discreteEnergy_step_pos ht i
  have hmesh' := (lt_div_iff₀ (by positivity : 0 < 2 * c)).mp (hmesh i)
  have hmul := mul_lt_mul_of_pos_right hx hstep
  have hd : 0 ≤ dist (x i.castSucc) (x i.succ) := dist_nonneg
  nlinarith

/-- Fixed-endpoint discrete energy is continuous in the interior vertices. -/
@[fun_prop]
theorem continuous_discreteEnergy_cons_snoc (t : Fin (n + 2) → ℝ) (p q : M) :
    Continuous (fun x : Fin n → M => discreteEnergy t (Fin.cons p (Fin.snoc x q))) := by
  exact (continuous_discreteEnergy t).comp
    (Continuous.finCons (A := fun _ : Fin (n + 2) => M) continuous_const
      (Continuous.finSnoc (A := fun _ : Fin (n + 1) => M)
        continuous_id continuous_const))

/-- Every interior vertex stays in the energy-controlled closed ball about the
fixed initial endpoint. -/
theorem dist_le_sqrt_discreteEnergy_cons_snoc {t : Fin (n + 2) → ℝ}
    (ht : StrictMono t) (p q : M) (x : Fin n → M) (j : Fin n) :
    dist p (x j) ≤ √(2 * (t (Fin.last (n + 1)) - t 0) *
      discreteEnergy t (Fin.cons p (Fin.snoc x q))) := by
  simpa only [Fin.cons_zero, Fin.cons_succ, Fin.snoc_castSucc] using
    dist_le_sqrt_discreteEnergy ht (Fin.cons p (Fin.snoc x q)) j.castSucc.succ

/-- The set of interior vertex tuples `x` with fixed endpoints `p,q` whose energy
`discreteEnergy t (Fin.cons p (Fin.snoc x q))` is strictly less than `c`. -/
def discreteEnergyStrictSublevel (t : Fin (n + 2) → ℝ) (p q : M) (c : ℝ) :
    Set (Fin n → M) :=
  {x | discreteEnergy t (Fin.cons p (Fin.snoc x q)) < c}

@[simp]
theorem mem_discreteEnergyStrictSublevel {t : Fin (n + 2) → ℝ} {p q : M} {c : ℝ}
    {x : Fin n → M} :
    x ∈ discreteEnergyStrictSublevel t p q c ↔
      discreteEnergy t (Fin.cons p (Fin.snoc x q)) < c := Iff.rfl

/-- Strict energy sublevels are open in the full interior-vertex product. -/
theorem isOpen_discreteEnergyStrictSublevel (t : Fin (n + 2) → ℝ) (p q : M) (c : ℝ) :
    IsOpen (discreteEnergyStrictSublevel t p q c) := by
  exact isOpen_lt (continuous_discreteEnergy_cons_snoc t p q) continuous_const

/-- Decreasing the cutoff gives the canonical inclusion of energy carriers. -/
theorem discreteEnergyStrictSublevel_mono (t : Fin (n + 2) → ℝ) (p q : M)
    {a c : ℝ} (hac : a ≤ c) :
    discreteEnergyStrictSublevel t p q a ⊆ discreteEnergyStrictSublevel t p q c :=
  fun _ hx => hx.trans_le hac

/-- Every interior vertex in a strict energy sublevel lies in the corresponding
open ball. -/
theorem dist_lt_sqrt_of_mem_discreteEnergyStrictSublevel {t : Fin (n + 2) → ℝ}
    (ht : StrictMono t) {p q : M} {c : ℝ} {x : Fin n → M}
    (hx : x ∈ discreteEnergyStrictSublevel t p q c) (j : Fin n) :
    dist p (x j) < √(2 * (t (Fin.last (n + 1)) - t 0) * c) := by
  have hT : 0 < t (Fin.last (n + 1)) - t 0 := sub_pos.mpr (ht Fin.last_pos')
  exact (dist_le_sqrt_discreteEnergy_cons_snoc ht p q x j).trans_lt (Real.sqrt_lt_sqrt
    (mul_nonneg (by positivity) (discreteEnergy_nonneg ht.monotone _))
    (mul_lt_mul_of_pos_left hx (by positivity)))

/-- An upper bound on fixed-endpoint energy bounds each interior vertex's distance
from the initial endpoint by the corresponding closed-ball radius. -/
theorem dist_le_sqrt_of_discreteEnergy_le {t : Fin (n + 2) → ℝ}
    (ht : StrictMono t) {p q : M} {a : ℝ} {x : Fin n → M}
    (hx : discreteEnergy t (Fin.cons p (Fin.snoc x q)) ≤ a) (j : Fin n) :
    dist p (x j) ≤ √(2 * (t (Fin.last (n + 1)) - t 0) * a) := by
  have hT : 0 ≤ t (Fin.last (n + 1)) - t 0 :=
    sub_nonneg.mpr (ht.monotone (Fin.zero_le _))
  refine (dist_le_sqrt_discreteEnergy_cons_snoc ht p q x j).trans ?_
  gcongr

/-- Closed fixed-endpoint energy sublevels are compact in a proper metric space.
No geodesic interpolation or small-mesh assumption is needed. -/
theorem isCompact_discreteEnergy_le [ProperSpace M] {t : Fin (n + 2) → ℝ}
    (ht : StrictMono t) (p q : M) (a : ℝ) :
    IsCompact {x : Fin n → M | discreteEnergy t (Fin.cons p (Fin.snoc x q)) ≤ a} := by
  refine (isCompact_univ_pi fun _ : Fin n =>
    isCompact_closedBall p (√(2 * (t (Fin.last (n + 1)) - t 0) * a))).of_isClosed_subset
      (isClosed_le (continuous_discreteEnergy_cons_snoc t p q) continuous_const) ?_
  intro x hx j _
  exact Metric.mem_closedBall.mpr ((dist_comm _ _).trans_le
    (dist_le_sqrt_of_discreteEnergy_le ht hx j))

/-- For `a < c`, the closed energy sublevel `{E ≤ a}` is compact as a subset of
the subtype `discreteEnergyStrictSublevel t p q c`. -/
theorem isCompact_discreteEnergyStrictSublevel_le [ProperSpace M] {t : Fin (n + 2) → ℝ}
    (ht : StrictMono t) (p q : M) {a c : ℝ} (hac : a < c) :
    IsCompact {x : discreteEnergyStrictSublevel t p q c |
      discreteEnergy t (Fin.cons p (Fin.snoc (x : Fin n → M) q)) ≤ a} := by
  exact Topology.IsInducing.subtypeVal.isCompact_preimage'
    (isCompact_discreteEnergy_le ht p q a)
    (fun x hx => ⟨⟨x, hx.trans_lt hac⟩, rfl⟩)

end TauCeti
