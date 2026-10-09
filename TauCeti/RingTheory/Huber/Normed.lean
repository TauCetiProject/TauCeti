/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Uniform
public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Bounded and power-bounded elements of normed rings

In a seminormed ring the balls about zero form a neighbourhood basis of zero, so norm-bounded
sets are bounded in the sense of `TauCeti.Huber.IsBounded`. For a normed division ring
this identifies the power-bounded elements with the closed unit ball and shows that the ring is
uniform; for instance `ℚ_[p]` is uniform, and its power-bounded elements are those of `ℤ_[p]`.

In a seminormed ring every unit of norm less than one is a pseudouniformiser. If the norm is
moreover ultrametric with `‖1‖ = 1`, the closed unit ball is an open bounded subring, so such
a ring with a unit of norm less than one is a Tate ring. In particular a nontrivially normed
field with an ultrametric norm is a Tate ring. This is the Tate structure of the complete
rank-one nonarchimedean fields over which rigid geometry takes place: their closed polydiscs are
the adic spectra of the Tate algebras `K⟨X₁, …, Xₙ⟩`.

## Main results

* `Subring.unitClosedBall`: the closed unit ball of an ultrametric seminormed ring with
  `‖1‖ = 1`, an open subring.
* `TauCeti.Huber.isBounded_closedBall_zero`: closed balls about zero are bounded.
* `TauCeti.Huber.isPowerBounded_iff_norm_le_one`: in a normed division ring an element is
  power-bounded exactly when its norm is at most one.
* `TauCeti.Huber.IsUniform.of_normedDivisionRing`: normed division rings are uniform.
* `TauCeti.Huber.IsPseudoUniformizer.of_norm_lt_one`: in a seminormed ring a unit of norm less
  than one is a pseudouniformiser.
* `TauCeti.Huber.isPseudoUniformizer_iff_norm_lt_one`: in a normed division ring the
  pseudouniformisers are the nonzero elements of norm less than one.
* `TauCeti.Huber.coe_powerBoundedSubring_eq_closedBall`: in an ultrametric normed field `K°` is the
  closed unit ball.
* `TauCeti.Huber.IsTateRing.of_isUnit_norm_lt_one`: an ultrametric seminormed commutative ring
  with `‖1‖ = 1` and a unit of norm less than one is a Tate ring.
* `TauCeti.Huber.IsTateRing.of_nontriviallyNormedField`: a nontrivially normed field with an
  ultrametric norm is a Tate ring; for instance `ℚ_[p]`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Definition 5.27.
-/

public section

open Filter Topology

section UnitClosedBall

variable (R : Type*) [SeminormedRing R] [IsUltrametricDist R] [NormOneClass R]

/-- **The closed unit ball of an ultrametric seminormed ring with `‖1‖ = 1` is a subring**: it is
the submonoid `Submonoid.unitClosedBall` and the open additive subgroup
`IsUltrametricDist.closedBall_openAddSubgroup`. -/
def Subring.unitClosedBall : Subring R :=
  { Submonoid.unitClosedBall R,
    (IsUltrametricDist.closedBall_openAddSubgroup R one_pos : AddSubgroup R) with }

variable {R} in
/-- An element lies in the closed unit ball exactly when its norm is at most one. -/
@[simp]
theorem Subring.mem_unitClosedBall {x : R} : x ∈ Subring.unitClosedBall R ↔ ‖x‖ ≤ 1 :=
  Submonoid.mem_unitClosedBall R

/-- The carrier of `Subring.unitClosedBall R` is `Metric.closedBall 0 1`. -/
@[simp]
theorem Subring.coe_unitClosedBall :
    (Subring.unitClosedBall R : Set R) = Metric.closedBall 0 1 := by
  ext
  simp

/-- The closed unit ball of an ultrametric seminormed ring is open. -/
theorem Subring.isOpen_unitClosedBall : IsOpen (Subring.unitClosedBall R : Set R) :=
  (IsUltrametricDist.closedBall_openAddSubgroup R one_pos).isOpen'

end UnitClosedBall

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

/-- **In a seminormed ring a unit of norm less than one is a pseudouniformiser**: its powers tend
to zero. -/
theorem IsPseudoUniformizer.of_norm_lt_one {R : Type*} [SeminormedRing R] {ϖ : R}
    (hϖ : IsUnit ϖ) (hϖ1 : ‖ϖ‖ < 1) : IsPseudoUniformizer ϖ :=
  isPseudoUniformizer_iff.mpr ⟨hϖ, tendsto_pow_atTop_nhds_zero_of_norm_lt_one hϖ1⟩

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

/-- **An ultrametric seminormed commutative ring with `‖1‖ = 1` and a unit of norm less than one
is a Tate ring.** The closed unit ball `Subring.unitClosedBall` is open because the norm is
ultrametric and bounded because it is a ball, and the unit is a pseudouniformiser
(`IsPseudoUniformizer.of_norm_lt_one`). -/
theorem IsTateRing.of_isUnit_norm_lt_one {R : Type*} [SeminormedCommRing R] [IsUltrametricDist R]
    [NormOneClass R] {ϖ : R} (hϖ : IsUnit ϖ) (hϖ1 : ‖ϖ‖ < 1) : IsTateRing R :=
  IsTateRing.of_isOpen_isBounded (Subring.unitClosedBall R) (Subring.isOpen_unitClosedBall R)
    (Subring.coe_unitClosedBall R ▸ isBounded_closedBall_zero 1)
    (IsPseudoUniformizer.of_norm_lt_one hϖ hϖ1)

/-- **A nontrivially normed field with an ultrametric norm is a Tate ring**, by
`IsTateRing.of_isUnit_norm_lt_one` applied to any `ϖ` with `0 < ‖ϖ‖ < 1`. Its ring of integers
`𝒪_K` is the closed unit ball. -/
instance IsTateRing.of_nontriviallyNormedField (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] : IsTateRing K := by
  obtain ⟨ϖ, h0, h1⟩ := NormedField.exists_norm_lt_one K
  exact IsTateRing.of_isUnit_norm_lt_one (isUnit_iff_ne_zero.mpr (norm_pos_iff.mp h0)) h1

end TauCeti.Huber
