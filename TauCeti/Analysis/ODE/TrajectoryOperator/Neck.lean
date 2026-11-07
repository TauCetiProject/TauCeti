/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.EnergyEstimate.Lyapunov
public import TauCeti.Analysis.ODE.EnergyEstimate.Sobolev
public import TauCeti.Analysis.ODE.TrajectoryOperator.Kernel
public import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import TauCeti.Analysis.ODE.Caratheodory
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.Cosh

/-!
# Kernel and cokernel cancellation on a neck

The operators `D₁ = d/ds + tanh s` and `D₂ = d/ds - tanh s` from `W^{1,2}(ℝ)` to `L²(ℝ)` have
kernel and cokernel of dimensions `(1, 0)` and `(0, 1)`, the nonzero space spanned by `sech s` in
each case. Gluing the
positive end of `D₁` to the negative end of `D₂` along a neck of length `2R` gives the operator

`D_R = d/ds - a_R(s)`, `a_R(s) = 1 - tanh (s + R) + tanh (s - R)`

(`TauCeti.neckCoeff`), which is `D₁` near `s = -R` and `D₂` near `s = R`, and whose coefficient
tends to `1` at both ends. This file shows that `D_R` is invertible, for every `R`: the kernel of
`D₁` cancels against the cokernel of `D₂`, so the index `0 = 1 + (-1)` is additive under gluing
while the kernel and the cokernel separately are not. It also shows that the inverse is not
uniformly bounded as the neck grows: its norm is at least `exp (2 R) / 2`. These are the two
phenomena that the stabilized linear gluing theorem for Cauchy–Riemann operators accounts for:
an obstruction map from `ker D₁ ⊕ ker D₂` to stabilizing cokernel representatives, here a
nonzero map `ℝ → ℝ`, and inverse bounds that are uniform only after stabilization.

The equation `v' = a_R v` has the explicit positive solution

`F_R(s) = exp s * cosh (s - R) / cosh (s + R)`

(`TauCeti.neckSolution`), with `F_R(s) / exp s → exp (∓ 2 R)` as `s → ±∞`, and the adjoint
equation `v' = -a_R v` has the solution `1 / F_R`. Neither is square integrable, so neither
equation has a nonzero square-integrable solution. By the kernel description of
`TauCeti.WeakDerivStep.kerTrajectoryOperatorEquiv`, `D_R` and its formal adjoint are injective;
since `D_R` has closed range
(`TauCeti.WeakDerivStep.isClosed_range_trajectoryOperator_of_hasLyapunovForm`) and the orthogonal
complement of its range is the kernel of the formal adjoint, `D_R` is also surjective.

For the lower bound on the inverse, the translated kernel element `ξ_R(s) = sech (s + R)` of `D₁`
satisfies `D_R ξ_R = -exp (s - R) / (cosh (s - R) cosh (s + R))`, and pointwise
`|D_R ξ_R (s)| ≤ 2 exp (-2 R) sech (s - R) = 2 exp (-2 R) ξ_R (-s)`, so
`‖D_R ξ_R‖ ≤ 2 exp (-2 R) ‖ξ_R‖` in `L²`.

The operator is written in the convention `D_A u = u' + A u` of
`TauCeti.WeakDerivStep.trajectoryOperator`, with the coefficient `A(s) = -a_R(s) • id` acting on
a real Banach (for the kernel and the inverse bound) or finite-dimensional inner product (for the
cokernel) space `E`. The scalar example is `E = ℝ`; `E = ℂ` is its complexification, the zero
Fourier mode of the cylinder operator `∂ₛ + i ∂ₜ - a_R(s)`.

## Main declarations

* `TauCeti.neckCoeff`: the coefficient `a_R(s) = 1 - tanh (s + R) + tanh (s - R)`, with the closed
  form `TauCeti.neckCoeff_eq`, the bounds `-1 < a_R ≤ 1` for `R ≥ 0`, the limits `1` at both
  ends, and the exponential comparisons with `-tanh` and `tanh` after translation by `∓R`.
* `TauCeti.neckSolution`: the positive solution `F_R` of `v' = a_R v`, with its asymptotics.
* `TauCeti.squareIntegrableSolutions_neg_neckCoeff_smul_id` and
  `TauCeti.squareIntegrableSolutions_neckCoeff_smul_id`: neither `v' = a_R v` nor `v' = -a_R v`
  has a nonzero square-integrable solution.
* `TauCeti.WeakDerivStep.ker_trajectoryOperator_neg_neckCoeff_smul_id` and
  `TauCeti.WeakDerivStep.range_trajectoryOperator_neg_neckCoeff_smul_id`: `D_R` has zero kernel
  and is surjective.
* `TauCeti.WeakDerivStep.exists_norm_trajectoryOperator_neg_neckCoeff_smul_id_le`: the test path
  `sech (s + R)` has `‖D_R u‖ ≤ 2 exp (-2 R) ‖u‖`.
* `TauCeti.WeakDerivStep.exp_div_two_le_of_forall_norm_le_mul_norm_trajectoryOperator_neckCoeff`:
  hence every bound `‖u‖ ≤ C ‖D_R u‖` has `C ≥ exp (2 R) / 2`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Chapter 10 (gluing, including the linear gluing of
  Cauchy–Riemann operators).
* M. Schwarz, *Morse Homology*, Birkhäuser, 1993, Chapter 2 (the linearized trajectory operator
  and the additivity of its index under gluing).
-/

public section

noncomputable section

open Filter MeasureTheory TopologicalSpace Set Real
open scoped ENNReal Topology

namespace TauCeti

/-! ### The coefficient `a_R` -/

/-- The coefficient `a_R(s) = 1 - tanh (s + R) + tanh (s - R)` of the operator `d/ds - a_R` on a
neck of length `2 R`, obtained by gluing `d/ds + tanh (s + R)` to `d/ds - tanh (s - R)`. -/
def neckCoeff (R s : ℝ) : ℝ := 1 - tanh (s + R) + tanh (s - R)

theorem neckCoeff_def (R s : ℝ) : neckCoeff R s = 1 - tanh (s + R) + tanh (s - R) := (rfl)

/-- The closed form `a_R(s) = 1 - 2 sinh (2 R) / (cosh (2 s) + cosh (2 R))` of the neck
coefficient. -/
theorem neckCoeff_eq (R s : ℝ) :
    neckCoeff R s = 1 - 2 * sinh (2 * R) / (cosh (2 * s) + cosh (2 * R)) := by
  have h₁ := (cosh_pos (s + R)).ne'
  have h₂ := (cosh_pos (s - R)).ne'
  have hc : cosh (2 * s) + cosh (2 * R) = 2 * cosh (s + R) * cosh (s - R) := by
    rw [show 2 * s = (s + R) + (s - R) by ring, show 2 * R = (s + R) - (s - R) by ring,
      cosh_add (s + R) (s - R), cosh_sub (s + R) (s - R)]
    ring
  have hs : sinh (2 * R) = sinh (s + R) * cosh (s - R) - cosh (s + R) * sinh (s - R) := by
    rw [show 2 * R = (s + R) - (s - R) by ring, sinh_sub (s + R) (s - R)]
  rw [neckCoeff_def, tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh, hc, hs]
  field_simp
  ring

@[fun_prop]
theorem continuous_neckCoeff (R : ℝ) : Continuous (neckCoeff R) := by
  unfold neckCoeff
  fun_prop

@[fun_prop]
theorem contDiff_neckCoeff (R : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (neckCoeff R) := by
  unfold neckCoeff
  fun_prop

/-- The neck coefficient is greater than `-1`. -/
theorem neg_one_lt_neckCoeff (R s : ℝ) : -1 < neckCoeff R s := by
  rw [neckCoeff_def]
  linarith [tanh_lt_one (s + R), neg_one_lt_tanh (s - R)]

/-- For `R ≥ 0` the neck coefficient is at most `1`. -/
theorem neckCoeff_le_one {R : ℝ} (hR : 0 ≤ R) (s : ℝ) : neckCoeff R s ≤ 1 := by
  rw [neckCoeff_def]
  linarith [tanh_strictMono.monotone (by linarith : s - R ≤ s + R)]

/-- For `R ≥ 0` the neck coefficient satisfies `|a_R| ≤ 1`. -/
theorem abs_neckCoeff_le_one {R : ℝ} (hR : 0 ≤ R) (s : ℝ) : |neckCoeff R s| ≤ 1 :=
  abs_le.2 ⟨(neg_one_lt_neckCoeff R s).le, neckCoeff_le_one hR s⟩

/-- Since `a_R = 1 - 2 sinh (2 R) / (cosh (2 s) + cosh (2 R))`, the coefficient tends to `1`
along any filter on which `cosh (2 s)` tends to infinity. -/
private theorem tendsto_neckCoeff_of_tendsto {l : Filter ℝ} (R : ℝ)
    (h : Tendsto (fun s ↦ cosh (2 * s)) l atTop) :
    Tendsto (neckCoeff R) l (𝓝 1) := by
  have := (tendsto_const_nhds (x := 1)).sub ((tendsto_const_nhds (x := 2 * sinh (2 * R))).mul
    (tendsto_atTop_add_const_right _ (cosh (2 * R)) h).inv_tendsto_atTop)
  simpa [funext (neckCoeff_eq R), div_eq_mul_inv] using this

/-- The neck coefficient tends to `1` at `+∞`. -/
theorem tendsto_neckCoeff_atTop (R : ℝ) : Tendsto (neckCoeff R) atTop (𝓝 1) :=
  tendsto_neckCoeff_of_tendsto R (tendsto_cosh_atTop.comp (tendsto_id.const_mul_atTop two_pos))

/-- The neck coefficient tends to `1` at `-∞`. -/
theorem tendsto_neckCoeff_atBot (R : ℝ) : Tendsto (neckCoeff R) atBot (𝓝 1) :=
  tendsto_neckCoeff_of_tendsto R (tendsto_cosh_atBot.comp (tendsto_id.const_mul_atBot two_pos))

/-- The derivative of the neck coefficient,
`a_R'(s) = 4 sinh (2 R) sinh (2 s) / (cosh (2 s) + cosh (2 R)) ^ 2`. -/
theorem hasDerivAt_neckCoeff (R s : ℝ) :
    HasDerivAt (neckCoeff R)
      (4 * sinh (2 * R) * sinh (2 * s) / (cosh (2 * s) + cosh (2 * R)) ^ 2) s := by
  have hD : 0 < cosh (2 * s) + cosh (2 * R) := add_pos (cosh_pos _) (cosh_pos _)
  have h := ((((hasDerivAt_id' s).const_mul 2).cosh.add_const (cosh (2 * R))).inv
    hD.ne').const_mul (2 * sinh (2 * R)) |>.const_sub 1
  convert h using 1
  · funext x
    rw [neckCoeff_eq, div_eq_mul_inv, Pi.inv_apply]
  · field_simp
    ring

/-- The derivative of the neck coefficient is bounded by `4 |sinh (2 R)| / D`. -/
private theorem norm_deriv_neckCoeff_le (R s : ℝ) :
    ‖deriv (neckCoeff R) s‖ ≤ 4 * |sinh (2 * R)| * (cosh (2 * s) + cosh (2 * R))⁻¹ := by
  have hD : 0 < cosh (2 * s) + cosh (2 * R) := add_pos (cosh_pos _) (cosh_pos _)
  have hs : |sinh (2 * s)| ≤ cosh (2 * s) + cosh (2 * R) := by
    rw [abs_le]
    constructor <;> linarith [sinh_lt_cosh (x := 2 * s), sinh_lt_cosh (x := -(2 * s)),
      sinh_neg (2 * s), cosh_neg (2 * s), cosh_pos (2 * R)]
  calc ‖deriv (neckCoeff R) s‖
      = 4 * |sinh (2 * R)| * |sinh (2 * s)| / (cosh (2 * s) + cosh (2 * R)) ^ 2 := by
        simp [(hasDerivAt_neckCoeff R s).deriv, abs_of_pos hD]
    _ ≤ 4 * |sinh (2 * R)| * (cosh (2 * s) + cosh (2 * R)) /
        (cosh (2 * s) + cosh (2 * R)) ^ 2 := by gcongr
    _ = _ := by field_simp

private theorem tendsto_deriv_neckCoeff_of_tendsto {l : Filter ℝ} (R : ℝ)
    (h : Tendsto (fun s ↦ cosh (2 * s)) l atTop) :
    Tendsto (deriv (neckCoeff R)) l (𝓝 0) := by
  refine squeeze_zero_norm (norm_deriv_neckCoeff_le R) ?_
  simpa using (tendsto_const_nhds (x := 4 * |sinh (2 * R)|)).mul
    (tendsto_atTop_add_const_right _ (cosh (2 * R)) h).inv_tendsto_atTop

/-- The derivative of the neck coefficient tends to `0` at `+∞`. -/
theorem tendsto_deriv_neckCoeff_atTop (R : ℝ) : Tendsto (deriv (neckCoeff R)) atTop (𝓝 0) :=
  tendsto_deriv_neckCoeff_of_tendsto R
    (tendsto_cosh_atTop.comp (tendsto_id.const_mul_atTop two_pos))

/-- The derivative of the neck coefficient tends to `0` at `-∞`. -/
theorem tendsto_deriv_neckCoeff_atBot (R : ℝ) : Tendsto (deriv (neckCoeff R)) atBot (𝓝 0) :=
  tendsto_deriv_neckCoeff_of_tendsto R
    (tendsto_cosh_atBot.comp (tendsto_id.const_mul_atBot two_pos))

/-- **The neck near `-R` is `d/ds + tanh s`.** After translation by `-R`, the neck coefficient
differs from `-tanh` by at most `2 exp (2 (s - 2 R))`; so `a_R(s - R) → -tanh s` uniformly on
every half-line `s ≤ c`, exponentially fast as `R → ∞`. -/
theorem abs_neckCoeff_sub_add_tanh_le (R s : ℝ) :
    |neckCoeff R (s - R) + tanh s| ≤ 2 * exp (2 * (s - 2 * R)) := by
  have h : neckCoeff R (s - R) + tanh s = 1 + tanh (s - 2 * R) := by
    rw [neckCoeff_def, sub_add_cancel, show s - R - R = s - 2 * R by ring]
    ring
  rw [h, abs_of_pos (by linarith [neg_one_lt_tanh (s - 2 * R)])]
  exact one_add_tanh_le _

/-- **The neck near `R` is `d/ds - tanh s`.** After translation by `R`, the neck coefficient
differs from `tanh` by at most `2 exp (-2 (s + 2 R))`; so `a_R(s + R) → tanh s` uniformly on
every half-line `s ≥ c`, exponentially fast as `R → ∞`. -/
theorem abs_neckCoeff_add_sub_tanh_le (R s : ℝ) :
    |neckCoeff R (s + R) - tanh s| ≤ 2 * exp (-(2 * (s + 2 * R))) := by
  have h : neckCoeff R (s + R) - tanh s = 1 - tanh (s + 2 * R) := by
    rw [neckCoeff_def, add_sub_cancel_right, show s + R + R = s + 2 * R by ring]
    ring
  rw [h, abs_of_pos (by linarith [tanh_lt_one (s + 2 * R)])]
  exact one_sub_tanh_le _

/-! ### The solution `F_R` of `v' = a_R v` -/

/-- The positive solution `F_R(s) = exp s * cosh (s - R) / cosh (s + R)` of `v' = a_R(s) v`,
normalized by `F_R(0) = 1`. -/
def neckSolution (R s : ℝ) : ℝ := exp s * cosh (s - R) / cosh (s + R)

theorem neckSolution_def (R s : ℝ) :
    neckSolution R s = exp s * cosh (s - R) / cosh (s + R) := (rfl)

theorem neckSolution_pos (R s : ℝ) : 0 < neckSolution R s := by
  rw [neckSolution_def]
  have := cosh_pos (s - R)
  have := cosh_pos (s + R)
  positivity

@[simp]
theorem neckSolution_zero (R : ℝ) : neckSolution R 0 = 1 := by
  rw [neckSolution_def, zero_sub, zero_add, cosh_neg, exp_zero, one_mul,
    div_self (cosh_pos R).ne']

/-- `F_R` solves `F_R' = a_R F_R`. -/
theorem hasDerivAt_neckSolution (R s : ℝ) :
    HasDerivAt (neckSolution R) (neckCoeff R s * neckSolution R s) s := by
  have h₁ := (cosh_pos (s + R)).ne'
  have h₂ := (cosh_pos (s - R)).ne'
  have h := ((hasDerivAt_exp s).mul ((hasDerivAt_id' s).sub_const R).cosh).div
    ((hasDerivAt_id' s).add_const R).cosh h₁
  convert h using 1
  · funext x
    simp [neckSolution_def]
  · simp only [Pi.mul_apply]
    rw [neckCoeff_def, neckSolution_def, tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh]
    field_simp
    ring

/-- `1 / F_R` solves the adjoint equation `v' = -a_R v`. -/
theorem hasDerivAt_inv_neckSolution (R s : ℝ) :
    HasDerivAt (fun s ↦ (neckSolution R s)⁻¹) (-neckCoeff R s * (neckSolution R s)⁻¹) s := by
  have h := (neckSolution_pos R s).ne'
  convert (hasDerivAt_neckSolution R s).inv h using 1
  field_simp

/-- `F_R(s) / exp s → exp (-2 R)` as `s → ∞`. -/
theorem tendsto_neckSolution_div_exp_atTop (R : ℝ) :
    Tendsto (fun s ↦ neckSolution R s / exp s) atTop (𝓝 (exp (-(2 * R)))) := by
  refine (tendsto_cosh_sub_div_cosh_add_atTop R).congr fun s ↦ ?_
  rw [neckSolution_def, mul_div_assoc, mul_div_cancel_left₀ _ (exp_pos s).ne']

/-- `F_R(s) / exp s → exp (2 R)` as `s → -∞`. -/
theorem tendsto_neckSolution_div_exp_atBot (R : ℝ) :
    Tendsto (fun s ↦ neckSolution R s / exp s) atBot (𝓝 (exp (2 * R))) := by
  have h := ((tendsto_cosh_sub_div_cosh_add_atTop R).inv₀ (exp_pos _).ne').comp
    tendsto_neg_atBot_atTop
  rw [exp_neg, inv_inv] at h
  refine h.congr fun s ↦ ?_
  rw [Function.comp_apply, neckSolution_def, mul_div_assoc, mul_div_cancel_left₀ _ (exp_pos s).ne',
    show -s - R = -(s + R) by ring, show -s + R = -(s - R) by ring, cosh_neg, cosh_neg, inv_div]

/-- `F_R` tends to infinity at `+∞`. -/
theorem tendsto_neckSolution_atTop (R : ℝ) : Tendsto (neckSolution R) atTop atTop := by
  refine (tendsto_exp_atTop.atTop_mul_pos (exp_pos _)
    (tendsto_neckSolution_div_exp_atTop R)).congr fun s ↦ ?_
  rw [mul_div_cancel₀ _ (exp_pos s).ne']

/-- `1 / F_R` tends to infinity at `-∞`. -/
theorem tendsto_inv_neckSolution_atBot (R : ℝ) :
    Tendsto (fun s ↦ (neckSolution R s)⁻¹) atBot atTop := by
  have h := (tendsto_neckSolution_div_exp_atBot R).inv₀ (exp_pos _).ne'
  refine ((tendsto_exp_atTop.comp tendsto_neg_atBot_atTop).atTop_mul_pos (inv_pos.2 (exp_pos _))
    h).congr fun s ↦ ?_
  rw [Function.comp_apply, exp_neg, inv_div, ← mul_div_assoc, inv_mul_cancel₀ (exp_pos s).ne',
    one_div]

/-! ### Neither `F_R` nor `1 / F_R` is square integrable -/

section Banach

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **`v' = a_R v` has no nonzero square-integrable solution.** Every solution is `F_R(s) • v 0`,
which grows like `exp s` at `+∞`. In the convention `v' + A v = 0` of
`TauCeti.squareIntegrableSolutions`, the coefficient is `A(s) = -a_R(s) • id`. -/
theorem squareIntegrableSolutions_neg_neckCoeff_smul_id (R : ℝ) :
    squareIntegrableSolutions (fun s ↦ -neckCoeff R s • ContinuousLinearMap.id ℝ F) = ⊥ :=
  squareIntegrableSolutions_neg_smul_id_eq_bot (continuous_neckCoeff R) (hasDerivAt_neckSolution R)
    (neckSolution_zero R) (MeasureTheory.not_memLp_of_tendsto_norm_atTop two_ne_zero
      ENNReal.ofNat_ne_top (tendsto_norm_atTop_atTop.comp (tendsto_neckSolution_atTop R)))

/-- **The adjoint equation `v' = -a_R v` has no nonzero square-integrable solution.** Every
solution is `F_R(s)⁻¹ • v 0`, which grows like `exp (-s)` at `-∞`. -/
theorem squareIntegrableSolutions_neckCoeff_smul_id (R : ℝ) :
    squareIntegrableSolutions (fun s ↦ neckCoeff R s • ContinuousLinearMap.id ℝ F) = ⊥ := by
  simpa using squareIntegrableSolutions_neg_smul_id_eq_bot (F := F) (continuous_neckCoeff R).neg
    (hasDerivAt_inv_neckSolution R) (by simp)
    (MeasureTheory.not_memLp_of_tendsto_norm_atBot two_ne_zero ENNReal.ofNat_ne_top
      (tendsto_norm_atTop_atTop.comp (tendsto_inv_neckSolution_atBot R)))

end Banach

end TauCeti

/-! ### Invertibility of the glued operator -/

namespace TauCeti.WeakDerivStep

section TestPath

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The value `ξ_R(s) = sech (s + R) • e` of the test path, the kernel element of `d/ds + tanh`
translated to the left end of the neck. -/
private def neckTestPath (R : ℝ) (e : F) (s : ℝ) : F := (cosh (s + R))⁻¹ • e

/-- The image `D_R ξ_R = -exp (s - R) / (cosh (s - R) cosh (s + R)) • e` of the test path. -/
private def neckTestImage (R : ℝ) (e : F) (s : ℝ) : F :=
  -(exp (s - R) / (cosh (s - R) * cosh (s + R))) • e

private theorem continuous_neckTestPath (R : ℝ) (e : F) : Continuous (neckTestPath R e) :=
  ((continuous_cosh.comp (continuous_id.add continuous_const : Continuous fun s : ℝ ↦ s + R)).inv₀
    fun _ ↦ (cosh_pos _).ne').smul continuous_const

private theorem continuous_neckTestImage (R : ℝ) (e : F) : Continuous (neckTestImage R e) :=
  have hsub : Continuous fun s : ℝ ↦ s - R := continuous_id.sub continuous_const
  have hadd : Continuous fun s : ℝ ↦ s + R := continuous_id.add continuous_const
  (((continuous_exp.comp hsub).div ((continuous_cosh.comp hsub).mul (continuous_cosh.comp hadd))
    fun _ ↦ (mul_pos (cosh_pos _) (cosh_pos _)).ne').neg).smul continuous_const

private theorem memLp_neckTestPath (R : ℝ) (e : F) : MemLp (neckTestPath R e) 2 :=
  (memLp_inv_cosh.comp_measurePreserving (measurePreserving_add_right volume R)).of_le_mul
    (c := ‖e‖) (continuous_neckTestPath R e).aestronglyMeasurable
    (ae_of_all _ fun s ↦ by simp [neckTestPath, norm_smul, mul_comm])

/-- Pointwise, `‖D_R ξ_R (s)‖ ≤ 2 exp (-2 R) ‖ξ_R (-s)‖`: since `cosh (s - R) + sinh (s - R)` is
`exp (s - R)`, this is `exp (s - R) ≤ 2 exp (-2 R) cosh (s + R)`. -/
private theorem norm_neckTestImage_le (R : ℝ) (e : F) (s : ℝ) :
    ‖neckTestImage R e s‖ ≤ 2 * exp (-(2 * R)) * ‖neckTestPath R e (-s)‖ := by
  have h₁ := cosh_pos (s - R)
  have h₂ := cosh_pos (s + R)
  have key : exp (s - R) ≤ 2 * exp (-(2 * R)) * cosh (s + R) := by
    rw [cosh_eq]
    have h : exp (-(2 * R)) * exp (s + R) = exp (s - R) := by rw [← exp_add]; ring_nf
    nlinarith [mul_pos (exp_pos (-(2 * R))) (exp_pos (-(s + R)))]
  have hscalar : exp (s - R) / (cosh (s - R) * cosh (s + R)) ≤
      2 * exp (-(2 * R)) * (cosh (s - R))⁻¹ := by
    calc exp (s - R) / (cosh (s - R) * cosh (s + R))
        ≤ 2 * exp (-(2 * R)) * cosh (s + R) / (cosh (s - R) * cosh (s + R)) := by gcongr
      _ = 2 * exp (-(2 * R)) * (cosh (s - R))⁻¹ := by field_simp
  simp only [neckTestImage, neckTestPath, norm_smul, norm_neg, Real.norm_eq_abs,
    show -s + R = -(s - R) by ring, cosh_neg]
  rw [abs_of_pos (by positivity), abs_of_pos (inv_pos.2 h₁), ← mul_assoc]
  gcongr

/-- The test path solves `ξ_R' = D_R ξ_R + a_R ξ_R` classically. -/
private theorem hasDerivAt_neckTestPath (R : ℝ) (e : F) (s : ℝ) :
    HasDerivAt (neckTestPath R e) (neckTestImage R e s + neckCoeff R s • neckTestPath R e s) s := by
  have h₁ := (cosh_pos (s + R)).ne'
  have h₂ := (cosh_pos (s - R)).ne'
  have h := (((hasDerivAt_id' s).add_const R).cosh.inv h₁).smul_const e
  unfold neckTestPath neckTestImage
  convert h using 1
  simp only [smul_smul, ← add_smul, neckCoeff_def,
    tanh_eq_sinh_div_cosh, ← cosh_add_sinh]
  congr 1
  field_simp
  ring

end TestPath

section Banach

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The glued operator is injective.** The trajectory operator `D_R u = u' - a_R u` on
`W^{1,2}(ℝ, F)`, with coefficient `A(s) = -a_R(s) • id` in the convention `u' + A u`, has zero
kernel: the kernel of `d/ds + tanh` has cancelled. -/
theorem ker_trajectoryOperator_neg_neckCoeff_smul_id (R : ℝ)
    (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -neckCoeff R s • ContinuousLinearMap.id ℝ F) :
    (trajectoryOperator (p := 2) AL).ker = ⊥ :=
  (ker_trajectoryOperator_eq_bot_iff ((continuous_neckCoeff R).neg.smul continuous_const) AL
    hAL).2 (squareIntegrableSolutions_neg_neckCoeff_smul_id R)

/-- **The inverse of the glued operator is not uniformly bounded.** For every `R` and every
nonzero `e`, there is a path `u ∈ W^{1,2}(ℝ, F)` with `u ≠ 0` and
`‖D_R u‖ ≤ 2 exp (-2 R) ‖u‖_{L²}`; it is `sech (s + R) • e`, the kernel element of `d/ds + tanh`
at the left end of the neck. -/
theorem exists_norm_trajectoryOperator_neg_neckCoeff_smul_id_le (R : ℝ) {e : F} (he : e ≠ 0)
    (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -neckCoeff R s • ContinuousLinearMap.id ℝ F) :
    ∃ u : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      prev _ u ≠ 0 ∧
        ‖trajectoryOperator AL u‖ ≤ 2 * exp (-(2 * R)) * ‖prev _ u‖ := by
  have hres : volume.restrict ((⊤ : Opens ℝ) : Set ℝ) = volume := by simp
  have hξneg : MemLp (fun s ↦ neckTestPath R e (-s)) 2 :=
    (memLp_neckTestPath R e).comp_measurePreserving (Measure.measurePreserving_neg volume)
  have hξneg' : MemLp (fun s ↦ neckTestPath R e (-s)) 2
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) := by
    rw [hres]
    exact hξneg
  -- The classical derivative of `ξ_R` is `D_R ξ_R - A ξ_R`, with `D_R ξ_R` in `L²`.
  obtain ⟨u, hu, hux⟩ := exists_trajectoryOperator_ae_eq_of_hasDerivAt hAL
    (fun s ↦ by simpa using hasDerivAt_neckTestPath R e s) (memLp_neckTestPath R e)
    (hξneg.of_le_mul (continuous_neckTestImage R e).aestronglyMeasurable
      (ae_of_all _ (norm_neckTestImage_le R e)))
  refine ⟨u, ?_, ?_⟩
  · -- `ξ_R` is continuous and nonzero at `0`, so its class is nonzero.
    intro h0
    have h := hux.symm.trans (Lp.eq_zero_iff_ae_eq_zero.1 h0)
    rw [hres] at h
    have := congrFun ((Continuous.ae_eq_iff_eq volume (continuous_neckTestPath R e)
      continuous_zero).1 h) 0
    simp [neckTestPath, he, (cosh_pos R).ne'] at this
  · calc ‖trajectoryOperator AL u‖ ≤ 2 * exp (-(2 * R)) * ‖hξneg'.toLp _‖ :=
          Lp.norm_le_mul_norm_of_ae_le_mul <| by
            filter_upwards [hu, hξneg'.coeFn_toLp] with s hfs hξs
            rw [hfs, hξs]
            exact norm_neckTestImage_le R e s
      _ = 2 * exp (-(2 * R)) * ‖prev _ u‖ := by
          congr 1
          rw [Lp.norm_toLp, Lp.norm_def, eLpNorm_congr_ae hux, hres]
          exact congrArg ENNReal.toReal (eLpNorm_comp_measurePreserving
            (continuous_neckTestPath R e).aestronglyMeasurable
            (Measure.measurePreserving_neg volume))

/-- **The inverse of the glued operator has norm at least `exp (2 R) / 2`.** If
`‖u‖ ≤ C ‖D_R u‖` for every `u ∈ W^{1,2}(ℝ, F)`, with `F ≠ 0`, then `C ≥ exp (2 R) / 2`. So the
bounded inverse of `D_R` (which exists by
`TauCeti.WeakDerivStep.ker_trajectoryOperator_neg_neckCoeff_smul_id` and
`TauCeti.WeakDerivStep.range_trajectoryOperator_neg_neckCoeff_smul_id` when `F` is a
finite-dimensional inner product space) blows up exponentially in the length of the neck. -/
theorem exp_div_two_le_of_forall_norm_le_mul_norm_trajectoryOperator_neckCoeff
    [Nontrivial F] (R : ℝ) (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -neckCoeff R s • ContinuousLinearMap.id ℝ F) {C : ℝ}
    (hC : ∀ u, ‖u‖ ≤ C * ‖trajectoryOperator (p := 2) AL u‖) :
    exp (2 * R) / 2 ≤ C := by
  obtain ⟨e, he⟩ := exists_ne (0 : F)
  obtain ⟨u, hu0, hu⟩ := exists_norm_trajectoryOperator_neg_neckCoeff_smul_id_le R he AL hAL
  have hp : 0 < ‖prev _ u‖ := norm_pos_iff.2 hu0
  have hle : ‖prev _ u‖ ≤ C * ‖trajectoryOperator (p := 2) AL u‖ :=
    (norm_prev_le _ u).trans (hC u)
  have hC0 : 0 < C := by
    by_contra h
    exact absurd (hle.trans (mul_nonpos_of_nonpos_of_nonneg (not_lt.1 h) (norm_nonneg _)))
      (not_le.2 hp)
  have h1 : ‖prev _ u‖ ≤ C * (2 * exp (-(2 * R))) * ‖prev _ u‖ := by
    calc ‖prev _ u‖ ≤ C * ‖trajectoryOperator (p := 2) AL u‖ := hle
      _ ≤ C * (2 * exp (-(2 * R)) * ‖prev _ u‖) := by gcongr
      _ = _ := by ring
  have h2 : 1 ≤ C * (2 * exp (-(2 * R))) := by
    nlinarith
  have h3 : exp (2 * R) * exp (-(2 * R)) = 1 := by rw [← exp_add]; simp
  nlinarith [exp_pos (2 * R), exp_pos (-(2 * R))]

end Banach

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The glued operator is surjective.** On a finite-dimensional real inner product space `E`,
the trajectory operator `D_R u = u' - a_R u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is onto. Together
with `TauCeti.WeakDerivStep.ker_trajectoryOperator_neg_neckCoeff_smul_id`, `D_R` is invertible:
the cokernel of `d/ds - tanh` has cancelled against the kernel of `d/ds + tanh`. -/
theorem range_trajectoryOperator_neg_neckCoeff_smul_id (R : ℝ)
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -neckCoeff R s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) AL).range = ⊤ := by
  set A : ℝ → E →L[ℝ] E := fun s ↦ -neckCoeff R s • ContinuousLinearMap.id ℝ E
  have hsym : ∀ s, (A s).toLinearMap.IsSymmetric := fun s x y ↦ by
    simp [A, inner_smul_left, inner_smul_right]
  have hA : Continuous A := (continuous_neckCoeff R).neg.smul continuous_const
  have hlim {l : Filter ℝ} (h : Tendsto (neckCoeff R) l (𝓝 1)) :
      Tendsto A l (𝓝 (-ContinuousLinearMap.id ℝ E)) := by
    simpa [A] using h.neg.smul_const (ContinuousLinearMap.id ℝ E)
  have hgap : ∀ v, 1 * ‖v‖ ≤ ‖(-ContinuousLinearMap.id ℝ E) v‖ := fun v ↦ by simp
  have hbot := hlim (tendsto_neckCoeff_atBot R)
  have hclosed := isClosed_range_trajectoryOperator_of_hasLyapunovForm hA
    (ContinuousLinearMap.hasLyapunovForm_of_tendsto_of_isSymmetric hsym hbot one_pos hgap)
    (ContinuousLinearMap.hasLyapunovForm_of_tendsto_of_isSymmetric hsym hbot one_pos hgap)
    hbot (hlim (tendsto_neckCoeff_atTop R)) AL hAL
  -- The coefficients are symmetric, so `AL` is also the class of their adjoints.
  have hALadj : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      AL s = ContinuousLinearMap.adjoint (AL s) := by
    filter_upwards [hAL] with s hs
    rw [hs, (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 (hsym s)).adjoint_eq]
  have hnegAL : -AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ neckCoeff R s • ContinuousLinearMap.id ℝ E := by
    filter_upwards [Lp.coeFn_neg AL, hAL] with s hs hAs
    rw [hs, Pi.neg_apply, hAs]
    simp [A]
  have hker : (trajectoryOperator (p := 2) (-AL)).ker = ⊥ :=
    (ker_trajectoryOperator_eq_bot_iff ((continuous_neckCoeff R).smul continuous_const) (-AL)
      hnegAL).2 (squareIntegrableSolutions_neckCoeff_smul_id R)
  have horth : (trajectoryOperator (p := 2) AL).rangeᗮ = ⊥ := by
    rw [orthogonal_range_trajectoryOperator_eq_map_ker hALadj, hker, Submodule.map_bot]
  rw [← hclosed.submodule_topologicalClosure_eq, Submodule.topologicalClosure_eq_top_iff]
  exact horth

end InnerProduct

end TauCeti.WeakDerivStep
