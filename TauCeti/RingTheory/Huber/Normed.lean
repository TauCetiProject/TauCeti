/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Uniform
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Bounded and power-bounded elements of normed rings

In a seminormed ring the balls about zero form a neighbourhood basis of zero, so norm-bounded
sets are bounded in the sense of `TauCeti.Huber.IsBounded`. For a normed division ring
this identifies the power-bounded elements with the closed unit ball and shows that the ring is
uniform; for instance `ℚ_[p]` is uniform, and its power-bounded elements are those of `ℤ_[p]`.

For a nontrivially normed field with an ultrametric norm the closed unit ball is moreover open,
and every nonzero element of norm less than one is a pseudouniformiser, so the field is a Tate
ring. This is the Tate structure of the complete rank-one nonarchimedean fields over which rigid
geometry takes place: their closed polydiscs are the adic spectra of the Tate algebras
`K⟨X₁, …, Xₙ⟩`.

## Main results

* `TauCeti.Huber.isBounded_closedBall_zero`: closed balls about zero are bounded.
* `TauCeti.Huber.isPowerBounded_iff_norm_le_one`: in a normed division ring an element is
  power-bounded exactly when its norm is at most one.
* `TauCeti.Huber.IsUniform.of_normedDivisionRing`: normed division rings are uniform.
* `TauCeti.Huber.isPseudoUniformizer_iff_norm_lt_one`: in a normed division ring the
  pseudouniformisers are the nonzero elements of norm less than one.
* `TauCeti.Huber.coe_powerBoundedSubring_eq_closedBall`: in an ultrametric normed field `K°` is the
  closed unit ball.
* `TauCeti.Huber.IsTateRing.of_nontriviallyNormedField`: a nontrivially normed field with an
  ultrametric norm is a Tate ring, with `(𝒪_K, ϖ 𝒪_K)` as a pair of definition; for instance
  `ℚ_[p]`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Definition 5.27.
-/

public section

open Filter Topology

namespace TauCeti.Huber

/-- **Closed balls about zero are bounded** in a seminormed ring. -/
@[simp]
theorem isBounded_closedBall_zero {R : Type*} [SeminormedRing R] (r : ℝ) :
    IsBounded (Metric.closedBall (0 : R) r) := by
  rw [isBounded_iff]
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  have hr : 0 < |r| + 1 := by positivity
  refine ⟨Metric.ball 0 (ε / (|r| + 1)), Metric.ball_mem_nhds 0 (by positivity), ?_⟩
  rintro _ ⟨v, hv, s, hs, rfl⟩
  rw [mem_ball_zero_iff] at hv
  rw [mem_closedBall_zero_iff] at hs
  refine hεU (mem_ball_zero_iff.mpr ?_)
  calc ‖v * s‖ ≤ ‖v‖ * ‖s‖ := norm_mul_le v s
    _ ≤ ‖v‖ * (|r| + 1) := by gcongr; linarith [le_abs_self r]
    _ < ε / (|r| + 1) * (|r| + 1) := by gcongr
    _ = ε := div_mul_cancel₀ ε hr.ne'

/-- An element of norm at most one in a seminormed ring is power-bounded. -/
theorem IsPowerBounded.of_norm_le_one {R : Type*} [SeminormedRing R] {x : R}
    (hx : ‖x‖ ≤ 1) : IsPowerBounded x := by
  refine isPowerBounded_iff.mpr ((isBounded_closedBall_zero (R := R) (max 1 ‖(1 : R)‖)).subset ?_)
  rintro _ ⟨n, rfl⟩
  rw [mem_closedBall_zero_iff]
  cases n with
  | zero => simp
  | succ n =>
    exact (norm_pow_le' x (Nat.succ_pos n)).trans
      ((pow_le_one₀ (norm_nonneg x) hx).trans (le_max_left 1 ‖(1 : R)‖))

section NormedDivisionRing

variable {K : Type*} [NormedDivisionRing K]

/-- **In a normed division ring the power-bounded elements are the closed unit ball.** -/
@[simp]
theorem isPowerBounded_iff_norm_le_one {x : K} : IsPowerBounded x ↔ ‖x‖ ≤ 1 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · by_contra! hlt
    have hx0 : x ≠ 0 := norm_pos_iff.mp (one_pos.trans hlt)
    have hinv : ‖x⁻¹‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ hlt
    obtain ⟨m, hm⟩ := (isPowerBounded_iff.mp hx).exists_pow_mul_subset
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hinv : IsTopologicallyNilpotent x⁻¹)
      (Metric.ball_mem_nhds 0 one_pos)
    have hone : x⁻¹ ^ m * x ^ m = 1 := by
      rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero m hx0)]
    have hmem := hm (Set.mul_mem_mul (Set.mem_singleton _) ⟨m, rfl⟩)
    rw [hone, mem_ball_zero_iff, norm_one] at hmem
    exact lt_irrefl _ hmem
  · exact IsPowerBounded.of_norm_le_one hx

/-- **Normed division rings are uniform.** -/
instance (priority := 100) IsUniform.of_normedDivisionRing : IsUniform K :=
  ⟨(isBounded_closedBall_zero (R := K) 1).subset fun _ hx ↦
    mem_closedBall_zero_iff.mpr (isPowerBounded_iff_norm_le_one.mp hx)⟩

/-- **In a normed division ring the pseudouniformisers are the nonzero elements of norm less than
one.** -/
theorem isPseudoUniformizer_iff_norm_lt_one {ϖ : K} :
    IsPseudoUniformizer ϖ ↔ ϖ ≠ 0 ∧ ‖ϖ‖ < 1 := by
  rw [isPseudoUniformizer_iff, isUnit_iff_ne_zero]
  exact and_congr_right fun _ ↦ tendsto_pow_atTop_nhds_zero_iff_norm_lt_one

end NormedDivisionRing

section Ultrametric

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- **The power-bounded subring of an ultrametric normed field is its closed unit ball**, the ring
of integers `𝒪_K`. -/
theorem coe_powerBoundedSubring_eq_closedBall :
    (powerBoundedSubring K : Set K) = Metric.closedBall 0 1 := by
  ext x
  simp

end Ultrametric

/-- **A nontrivially normed field with an ultrametric norm is a Tate ring.** Its ring of integers
`𝒪_K` is open and bounded, and any element `ϖ` with `0 < ‖ϖ‖ < 1` is a pseudouniformiser, so
`(𝒪_K, ϖ 𝒪_K)` is a pair of definition (`PairOfDefinition.ofIsPseudoUniformizer`). -/
instance IsTateRing.of_nontriviallyNormedField (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] : IsTateRing K := by
  obtain ⟨ϖ, h0, h1⟩ := NormedField.exists_norm_lt_one K
  refine IsTateRing.of_isOpen_isBounded (powerBoundedSubring K) ?_ ?_
    (isPseudoUniformizer_iff_norm_lt_one.mpr ⟨norm_pos_iff.mp h0, h1⟩)
  · rw [coe_powerBoundedSubring_eq_closedBall]
    exact IsUltrametricDist.isOpen_closedBall 0 one_ne_zero
  · rw [coe_powerBoundedSubring_eq_closedBall]
    exact isBounded_closedBall_zero 1

end TauCeti.Huber
