/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import TauCeti.Algebra.Module.ZLattice.Dual

/-!
# Summing Schwartz functions over a lattice

A Schwartz function decays faster than every power of `‖x‖`, while the power `‖x‖ ^ r` is
summable over a discrete subgroup `L` of a finite-dimensional real normed space as soon as
`r < -rank L` (Mathlib's `ZLattice.summable_norm_sub_rpow`). Comparing the two, every translate
`ℓ ↦ f (v + ℓ)` of a Schwartz function is absolutely summable over `L`. By Peetre's inequality
`1 + ‖ℓ‖ ≤ (1 + ‖x‖) (1 + ‖x + ℓ‖)` the domination is uniform for `x` in a ball, so the
periodization `x ↦ ∑' ℓ : L, f (x + ℓ)` is continuous.

The summability of both sides and the continuity of the periodization are the analytic inputs
to Poisson summation over a full lattice `L` in a finite-dimensional real inner product space,
which is not proved here,

`∑' ℓ : L, f (v + ℓ) = (covolume L)⁻¹ * ∑' m : L^∨, exp (2πi ⟪v, m⟫) • 𝓕 f m`,

for a Schwartz function `f`. The lattice side is summable by the comparison above, and the dual
side because the Fourier transform of a Schwartz function is again a Schwartz function and the
phases `exp (2πi ⟪v, m⟫)` have norm one. Both are recorded on their own, in absolute form and in
the plain form for a complete codomain, so that each side can be manipulated on its own.

## Main statements

* `ZLattice.summable_norm_poisson_left`, `ZLattice.summable_poisson_left`: the translates of a
  Schwartz function are (absolutely) summable over a discrete subgroup `L`.
* `ZLattice.exists_summable_forall_norm_poisson_left_le`: these translates are dominated by one
  summable family, uniformly for `x` in a ball.
* `ZLattice.continuous_tsum_poisson_left`: hence the periodization `x ↦ ∑' ℓ : L, f (x + ℓ)` is
  continuous.
* `ZLattice.summable_norm_poisson_right_smul`, `ZLattice.summable_poisson_right_smul`: the
  Fourier transform of a Schwartz function, twisted by the phases `exp (2πi ⟪v, m⟫)`, is
  (absolutely) summable over the dual `L^∨` of a full lattice `L`.
* `ZLattice.summable_norm_poisson_right`, `ZLattice.summable_poisson_right`: the same for a
  complex-valued Schwartz function, with the summand `𝓕 f m * exp (2πi ⟪v, m⟫)`.
-/

public section

open Complex Filter Module Topology
open scoped Real RealInnerProductSpace SchwartzMap FourierTransform

namespace ZLattice

section Left

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Submodule ℤ E) [DiscreteTopology L]

/-- The translates `ℓ ↦ f (v + ℓ)` of a Schwartz function are absolutely summable over a discrete
subgroup `L` of a finite-dimensional real normed space. -/
theorem summable_norm_poisson_left (f : 𝓢(E, F)) (v : E) :
    Summable fun ℓ : L ↦ ‖f (v + ℓ)‖ := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r < -finrank ℤ L := ⟨-finrank ℤ L - 1, by linarith⟩
  -- The points `v + ℓ` leave every compact set of `E`, because `L` is closed and discrete.
  have hL : Tendsto ((↑) : L → E) cofinite (cocompact E) :=
    L.toAddSubgroup.tendsto_coe_cofinite_of_isDiscrete (isDiscrete_iff_discreteTopology.mpr ‹_›)
  have ht : Tendsto (fun ℓ : L ↦ v + (ℓ : E)) cofinite (cocompact E) :=
    (Homeomorph.addLeft v).isClosedEmbedding.tendsto_cocompact.comp hL
  refine summable_of_isBigO ((summable_norm_sub_rpow L r hr (-v)).congr fun ℓ ↦ ?_)
    ((f.isBigO_cocompact_rpow r).comp_tendsto ht).norm_left
  simp [add_comm]

/-- The translates `ℓ ↦ f (v + ℓ)` of a Schwartz function with values in a Banach space are
summable over a discrete subgroup `L` of a finite-dimensional real normed space. -/
theorem summable_poisson_left [CompleteSpace F] (f : 𝓢(E, F)) (v : E) :
    Summable fun ℓ : L ↦ f (v + ℓ) :=
  (summable_norm_poisson_left L f v).of_norm

/-- The translates `ℓ ↦ f (x + ℓ)` of a Schwartz function are dominated, uniformly for `x` in a
closed ball, by a single summable family over a discrete subgroup `L`. -/
theorem exists_summable_forall_norm_poisson_left_le (f : 𝓢(E, F)) (R : ℝ) :
    ∃ u : L → ℝ, Summable u ∧
      ∀ ℓ : L, ∀ x ∈ Metric.closedBall (0 : E) R, ‖f (x + ℓ)‖ ≤ u ℓ := by
  set k := finrank ℤ L + 1
  obtain ⟨C, hC⟩ : ∃ C, ∀ y, (1 + ‖y‖) ^ k * ‖f y‖ ≤ C :=
    ⟨_, fun y ↦ by
      simpa using f.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0)
        le_rfl le_rfl y⟩
  have hsum : Summable fun ℓ : L ↦ ((1 + ‖(ℓ : E)‖) ^ k)⁻¹ := by
    refine Summable.of_norm_bounded_eventually (summable_norm_pow_inv L k (by omega)) ?_
    -- Away from `0`, `(1 + ‖ℓ‖) ^ (-k) ≤ ‖ℓ‖ ^ (-k)`.
    filter_upwards [Set.Finite.compl_mem_cofinite (Set.finite_singleton (0 : L))] with ℓ hℓ
    have hℓ : 0 < ‖(ℓ : E)‖ := by simpa using hℓ
    rw [norm_inv, norm_pow, Real.norm_of_nonneg (by positivity), ← inv_pow]
    gcongr
    simp
  refine ⟨fun ℓ ↦ C * (1 + R) ^ k * ((1 + ‖(ℓ : E)‖) ^ k)⁻¹, hsum.mul_left _, ?_⟩
  · intro ℓ x hx
    rw [mem_closedBall_zero_iff] at hx
    have hy := hC (x + ℓ)
    -- Peetre's inequality: `1 + ‖ℓ‖ ≤ (1 + R) * (1 + ‖x + ℓ‖)` for `‖x‖ ≤ R`.
    have hℓ : 1 + ‖(ℓ : E)‖ ≤ (1 + R) * (1 + ‖x + ℓ‖) := by
      have := norm_sub_le (x + ℓ) x
      rw [add_sub_cancel_left] at this
      nlinarith [norm_nonneg x, norm_nonneg (x + ℓ)]
    have hpos : 0 < (1 + ‖(ℓ : E)‖) ^ k := by positivity
    have hRk : 0 ≤ (1 + R) ^ k := pow_nonneg (by linarith [norm_nonneg x]) k
    dsimp only
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    calc ‖f (x + ℓ)‖ * (1 + ‖(ℓ : E)‖) ^ k
        ≤ ‖f (x + ℓ)‖ * ((1 + R) ^ k * (1 + ‖x + ℓ‖) ^ k) := by
          rw [← mul_pow]
          gcongr
      _ = (1 + R) ^ k * ((1 + ‖x + ℓ‖) ^ k * ‖f (x + ℓ)‖) := by ring
      _ ≤ (1 + R) ^ k * C := by gcongr
      _ = C * (1 + R) ^ k := mul_comm _ _

/-- The periodization `x ↦ ∑' ℓ : L, f (x + ℓ)` of a Schwartz function over a discrete subgroup
`L` is continuous. -/
theorem continuous_tsum_poisson_left [CompleteSpace F] (f : 𝓢(E, F)) :
    Continuous fun x : E ↦ ∑' ℓ : L, f (x + ℓ) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  obtain ⟨u, hu, hle⟩ := exists_summable_forall_norm_poisson_left_le L f (‖x₀‖ + 1)
  have : ContinuousOn (fun x : E ↦ ∑' ℓ : L, f (x + ℓ)) (Metric.ball x₀ 1) :=
    continuousOn_tsum (fun ℓ ↦ (f.continuous.comp (continuous_add_const _)).continuousOn) hu
      fun ℓ x hx ↦ hle ℓ x <| mem_closedBall_zero_iff.2 <| by
        have := norm_le_norm_add_norm_sub' x x₀
        rw [Metric.mem_ball, dist_eq_norm] at hx
        linarith
  exact this.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))

end Left

section Right

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The Fourier transform of a Schwartz function, twisted by the phases `exp (2πi ⟪v, m⟫)`, is
absolutely summable over the dual `L^∨` of a full lattice `L`: the dual side of Poisson
summation. -/
theorem summable_norm_poisson_right_smul (f : 𝓢(E, F)) (v : E) :
    Summable fun m : dual L ↦ ‖cexp (2 * π * I * ⟪v, (m : E)⟫) • 𝓕 (f : E → F) m‖ := by
  have hphase (m : dual L) : ‖cexp (2 * π * I * ⟪v, (m : E)⟫)‖ = 1 := by
    rw [norm_exp]
    simp
  simpa [norm_smul, hphase, SchwartzMap.fourier_coe] using
    summable_norm_poisson_left (dual L) (𝓕 f) 0

/-- The Fourier transform of a Schwartz function with values in a complex Banach space, twisted by
the phases `exp (2πi ⟪v, m⟫)`, is summable over the dual `L^∨` of a full lattice `L`. -/
theorem summable_poisson_right_smul [CompleteSpace F] (f : 𝓢(E, F)) (v : E) :
    Summable fun m : dual L ↦ cexp (2 * π * I * ⟪v, (m : E)⟫) • 𝓕 (f : E → F) m :=
  (summable_norm_poisson_right_smul L f v).of_norm

/-- The Fourier transform of a complex-valued Schwartz function, times the phases
`exp (2πi ⟪v, m⟫)`, is absolutely summable over the dual `L^∨` of a full lattice `L`. -/
theorem summable_norm_poisson_right (f : 𝓢(E, ℂ)) (v : E) :
    Summable fun m : dual L ↦ ‖𝓕 (f : E → ℂ) m * cexp (2 * π * I * ⟪v, (m : E)⟫)‖ :=
  (summable_norm_poisson_right_smul L f v).congr fun m ↦ by rw [smul_eq_mul, mul_comm]

/-- The Fourier transform of a complex-valued Schwartz function, times the phases
`exp (2πi ⟪v, m⟫)`, is summable over the dual `L^∨` of a full lattice `L`: the dual side of
Poisson summation. -/
theorem summable_poisson_right (f : 𝓢(E, ℂ)) (v : E) :
    Summable fun m : dual L ↦ 𝓕 (f : E → ℂ) m * cexp (2 * π * I * ⟪v, (m : E)⟫) :=
  (summable_norm_poisson_right L f v).of_norm

end Right

end ZLattice
