/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.TateGauge.Basic
public import TauCeti.Analysis.Normed.Ring.PseudoUniformizer

/-!
# The unit-ball Tate gauge and discrete rounding

For a multiplicative pseudo-uniformiser `ϖ` of an ultrametric seminormed commutative ring,
put `c = ‖ϖ‖`. The Tate gauge of the closed unit ball with base `c⁻¹` is exactly
`zpowCeil c ‖x‖`, the norm rounded upwards to `c ^ ℤ ∪ {0}`. Consequently it is bounded-equivalent
to the original norm, but agrees with it only on elements whose norms lie in that discrete set.
Changing the base gives the corresponding power of this rounded norm.

This comparison relates a specified Tate norm to the gauge of its unit ball without assuming
that every element has multiplicative norm. It also explains why replacing a pseudo-uniformiser
by its square can produce a nonmultiplicative gauge even over a valued field. Neither
completeness nor separation of the seminorm is required.

## References

* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4 and Remark 2.4.4.
-/

public section

namespace TauCeti.Huber

variable {R : Type*} [SeminormedCommRing R] [IsUltrametricDist R] [NormOneClass R]

/-- The Tate gauge of the closed unit ball, at the reciprocal pseudo-uniformiser norm,
is the discrete rounding of the given norm. This also holds at elements of seminorm zero. -/
@[simp]
theorem tateGauge_unitClosedBall_eq_zpowCeil (ϖ : NormedRing.PseudoUniformizer R) (x : R) :
    tateGauge (Subring.unitClosedBall R) ϖ.unit ‖(ϖ.unit : R)‖⁻¹ x =
      zpowCeil ‖(ϖ.unit : R)‖ ‖x‖ := by
  set c := ‖(ϖ.unit : R)‖
  have hc₀ : 0 < c := ϖ.norm_pos
  have hc₁ : c < 1 := ϖ.norm_lt_one
  have hbase : 1 < c⁻¹ := (one_lt_inv₀ hc₀).mpr hc₁
  have hmem (n : ℤ) :
      ((ϖ.unit ^ (-n) : Rˣ) : R) * x ∈ Subring.unitClosedBall R ↔ ‖x‖ ≤ c ^ n := by
    rw [Subring.mem_unitClosedBall, ← smul_eq_mul, ϖ.norm_zpow_smul, zpow_neg,
      inv_mul_le_iff₀ (zpow_pos hc₀ n), mul_one]
  by_cases hx : ‖x‖ = 0
  · rw [zpowCeil_of_nonpos hx.le]
    apply (tateGauge_eq_zero_iff_forall
      (Subring.mem_unitClosedBall.mpr hc₁.le) ⟨0, by simp [hx]⟩ hbase).2
    exact fun n ↦ (hmem n).2 (hx ▸ (zpow_pos hc₀ _).le)
  obtain ⟨n, hn⟩ := exists_zpowCeil_eq_zpow (c := c) (lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx))
  have hxn : ‖x‖ ≤ c ^ n := hn ▸ le_zpowCeil hc₀ hc₁ ‖x‖
  rw [tateGauge_def, hn]
  apply IsLeast.csInf_eq
  refine ⟨⟨n, (hmem n).2 hxn, by simp⟩, ?_⟩
  rintro _ ⟨m, hm, rfl⟩
  simpa [← hn] using
    (zpowCeil_le_iff hc₀ hc₁ (zpowCeil_zpow hc₀ hc₁ m)).2 ((hmem m).1 hm)

/-- The unit-ball gauge dominates the given norm. -/
theorem norm_le_tateGauge_unitClosedBall (ϖ : NormedRing.PseudoUniformizer R) (x : R) :
    ‖x‖ ≤ tateGauge (Subring.unitClosedBall R) ϖ.unit ‖(ϖ.unit : R)‖⁻¹ x := by
  rw [tateGauge_unitClosedBall_eq_zpowCeil]
  exact le_zpowCeil ϖ.norm_pos ϖ.norm_lt_one ‖x‖

/-- The loss in replacing a Tate norm by its unit-ball gauge is bounded by the reciprocal
pseudo-uniformiser norm, including at elements of seminorm zero. -/
theorem mul_tateGauge_unitClosedBall_le_norm (ϖ : NormedRing.PseudoUniformizer R) (x : R) :
    ‖(ϖ.unit : R)‖ * tateGauge (Subring.unitClosedBall R) ϖ.unit ‖(ϖ.unit : R)‖⁻¹ x ≤ ‖x‖ := by
  rw [tateGauge_unitClosedBall_eq_zpowCeil]
  exact mul_zpowCeil_le ϖ.norm_pos ϖ.norm_lt_one (norm_nonneg x)

/-- At an element of positive seminorm, the unit-ball gauge loses strictly less than the
reciprocal pseudo-uniformiser norm. -/
theorem mul_tateGauge_unitClosedBall_lt_norm (ϖ : NormedRing.PseudoUniformizer R)
    {x : R} (hx : 0 < ‖x‖) :
    ‖(ϖ.unit : R)‖ * tateGauge (Subring.unitClosedBall R) ϖ.unit ‖(ϖ.unit : R)‖⁻¹ x < ‖x‖ := by
  rw [tateGauge_unitClosedBall_eq_zpowCeil]
  exact mul_zpowCeil_lt ϖ.norm_pos ϖ.norm_lt_one hx

/-- The unit-ball gauge agrees with the norm exactly at the discrete values, or at zero. -/
theorem tateGauge_unitClosedBall_eq_norm_iff (ϖ : NormedRing.PseudoUniformizer R) (x : R) :
    tateGauge (Subring.unitClosedBall R) ϖ.unit ‖(ϖ.unit : R)‖⁻¹ x = ‖x‖ ↔
      ‖x‖ = 0 ∨ ∃ n : ℤ, ‖(ϖ.unit : R)‖ ^ n = ‖x‖ := by
  rw [tateGauge_unitClosedBall_eq_zpowCeil]
  exact zpowCeil_eq_self_iff ϖ.norm_pos ϖ.norm_lt_one (norm_nonneg x)

/-- With any base greater than one, the unit-ball gauge is a power of the discretely
rounded norm. Equal topology need not give linear equivalence for this other base. -/
theorem tateGauge_unitClosedBall_eq_rpow (ϖ : NormedRing.PseudoUniformizer R)
    {a : ℝ} (ha : 1 < a) (x : R) :
    tateGauge (Subring.unitClosedBall R) ϖ.unit a x =
      (zpowCeil ‖(ϖ.unit : R)‖ ‖x‖) ^ (Real.log a / Real.log ‖(ϖ.unit : R)‖⁻¹) := by
  rw [tateGauge_rpow ((one_lt_inv₀ ϖ.norm_pos).mpr ϖ.norm_lt_one) ha,
    tateGauge_unitClosedBall_eq_zpowCeil]

end TauCeti.Huber
