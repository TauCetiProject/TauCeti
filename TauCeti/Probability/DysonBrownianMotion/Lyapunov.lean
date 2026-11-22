/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Vandermonde
public import TauCeti.Probability.DysonBrownianMotion.Drift
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Algebra.BigOperators.Field
import TauCeti.Analysis.Calculus.FDeriv.DiagonalQuadratic
import TauCeti.Topology.Constructions.Pi

/-!
# The Dyson generator and the logarithmic Lyapunov function

The Dyson system `dX_t(i) = √(2 / (β n)) dB_t(i) + dysonDrift n X_t i dt` has the second-order
generator
`dysonGenerator β n f x = (β n)⁻¹ ∑ᵢ ∂ᵢ² f x + ∑ᵢ dysonDrift n x i ∂ᵢ f x`,
the drift term that Itô's formula attaches to `f (X_t)`. This file computes it on the two
functions that control the particles: the squared norm `∑ᵢ xᵢ²` and the logarithmic Vandermonde
potential `logVandermonde n x = ∑_{i < j} log (xᵢ - xⱼ)`, which for distinct coordinates is the
logarithm of the absolute value of the Vandermonde determinant. Off the collision hyperplanes, the
gradient of `logVandermonde n` is `n • dysonDrift n`, and the Calogero–Moser identity
`sum_dysonDrift_sq` gives
* `dysonGenerator β n (fun y ↦ ∑ i, y i ^ 2) x = n - 1 + 2 / β`;
* `dysonGenerator β n (logVandermonde n) x = 2 (1 - β⁻¹) n⁻¹ ∑_{i < j} (xᵢ - xⱼ)⁻²`, which is
  nonnegative in the repulsive regime `β ≥ 1`.

Their difference `dysonLyapunov n x = ∑ᵢ xᵢ² - logVandermonde n x` is smooth on the open Weyl
chamber, its generator is at most `n - 1 + 2 / β` there when `β ≥ 1`, it is bounded below, and its
sublevel sets keep every ordered gap `xᵢ - xⱼ` above a positive constant and `∑ᵢ xᵢ²` bounded. So
it tends to `+∞` both at the chamber walls and at infinity, and its sublevel sets lie in the
regions where `truncatedDysonDrift ε n` agrees with `dysonDrift n`. These are the deterministic
inputs of the Lyapunov argument for noncollision and nonexplosion of Dyson Brownian motion when
`β ≥ 1`.

## Main declarations

* `TauCeti.Probability.dysonGenerator`: the generator of the Dyson system, with
  `TauCeti.Probability.dysonGenerator_eq_of_hasFDerivAt` computing it from an explicit gradient.
* `TauCeti.Probability.logVandermonde`, with
  `TauCeti.Probability.logVandermonde_eq_log_abs_det_vandermonde` and
  `TauCeti.Probability.hasFDerivAt_logVandermonde`.
* `TauCeti.Probability.dysonGenerator_sum_sq` and
  `TauCeti.Probability.dysonGenerator_logVandermonde`: the two generator identities.
* `TauCeti.Probability.dysonLyapunov`, with `TauCeti.Probability.dysonGenerator_dysonLyapunov_le`,
  `TauCeti.Probability.bddBelow_image_dysonLyapunov` and
  `TauCeti.Probability.exists_forall_le_sub_and_sum_sq_le_of_dysonLyapunov_le`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, Lemma 4.3.3.
* L. C. G. Rogers, Z. Shi, *Interacting Brownian particles and the Wigner law*, Probab. Theory
  Related Fields 95 (1993), 555–570.
-/

public section

open Filter Topology
open ContinuousLinearMap (proj)

namespace TauCeti.Probability

variable {β : ℝ} {n : ℕ}

/-! ### The generator of the Dyson system -/

/-- **The generator of the Dyson system** of size `n` and parameter `β`, applied to
`f : (Fin n → ℝ) → ℝ` at `x`: the diffusion term `(β n)⁻¹ ∑ᵢ ∂ᵢ² f x`, from the noise
`√(2 / (β n)) dBᵢ`, plus the transport term `∑ᵢ dysonDrift n x i ∂ᵢ f x`. Partial derivatives are
those of `fderiv` along the coordinate vectors `Pi.single i 1`. -/
noncomputable def dysonGenerator (β : ℝ) (n : ℕ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  (β * n)⁻¹ * ∑ i, fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single i 1) +
    ∑ i, dysonDrift n x i * fderiv ℝ f x (Pi.single i 1)

/-- Unfolding `dysonGenerator`. -/
theorem dysonGenerator_def (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    dysonGenerator β n f x =
      (β * n)⁻¹ * ∑ i, fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single i 1) +
        ∑ i, dysonDrift n x i * fderiv ℝ f x (Pi.single i 1) :=
  (rfl)

/-- **Computing the generator from an explicit gradient.** If near `x` the gradient of `f` has
coordinates `g i`, and each `g i` is differentiable at `x` with derivative `g' i`, then the
generator of `f` at `x` is `(β n)⁻¹ ∑ᵢ g' i (Pi.single i 1) + ∑ᵢ dysonDrift n x i * g i x`. -/
theorem dysonGenerator_eq_of_hasFDerivAt {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    {g : Fin n → (Fin n → ℝ) → ℝ} {g' : Fin n → (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : ∀ᶠ y in 𝓝 x, HasFDerivAt f (∑ i, g i y • (proj i : (Fin n → ℝ) →L[ℝ] ℝ)) y)
    (hg : ∀ i, HasFDerivAt (g i) (g' i) x) :
    dysonGenerator β n f x =
      (β * n)⁻¹ * ∑ i, g' i (Pi.single i 1) + ∑ i, dysonDrift n x i * g i x := by
  have hD : HasFDerivAt (fun y ↦ ∑ i, g i y • (proj i : (Fin n → ℝ) →L[ℝ] ℝ))
      (∑ i, (g' i).smulRight (proj i : (Fin n → ℝ) →L[ℝ] ℝ)) x :=
    HasFDerivAt.fun_sum fun i _ ↦ (hg i).smul_const (proj i : (Fin n → ℝ) →L[ℝ] ℝ)
  have hfd : fderiv ℝ f =ᶠ[𝓝 x] fun y ↦ ∑ i, g i y • (proj i : (Fin n → ℝ) →L[ℝ] ℝ) :=
    hf.mono fun y hy ↦ hy.fderiv
  rw [dysonGenerator_def, hfd.fderiv_eq, hD.fderiv, hf.self_of_nhds.fderiv]
  simp [Pi.single_apply]

/-- Adding a constant does not change the generator. -/
@[simp]
theorem dysonGenerator_add_const (f : (Fin n → ℝ) → ℝ) (c : ℝ) (x : Fin n → ℝ) :
    dysonGenerator β n (fun y ↦ f y + c) x = dysonGenerator β n f x := by
  have h : fderiv ℝ (fun y ↦ f y + c) = fderiv ℝ f := funext fun _ ↦ fderiv_add_const c
  rw [dysonGenerator_def, dysonGenerator_def, h]

/-! ### Derivatives along the open chamber -/

/-- **Derivative of a coordinate of the Dyson drift.** Off the collision hyperplanes,
`dysonDrift n · i` is differentiable with derivative
`n⁻¹ ∑_{j ≠ i} -(xᵢ - xⱼ)⁻² (eᵢ - eⱼ)`, where `eₖ` is the `k`-th coordinate functional. -/
theorem hasFDerivAt_dysonDrift_apply {x : Fin n → ℝ} (hx : Function.Injective x) (i : Fin n) :
    HasFDerivAt (fun y ↦ dysonDrift n y i)
      ((n : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i,
        (-((x i - x j) ^ 2)⁻¹) • ((proj i : (Fin n → ℝ) →L[ℝ] ℝ) - proj j)) x := by
  simp_rw [dysonDrift_apply]
  refine HasFDerivAt.const_mul (HasFDerivAt.fun_sum fun j hj ↦ ?_) _
  exact (hasDerivAt_inv (sub_ne_zero.2 (hx.ne (Finset.ne_of_mem_erase hj).symm))).comp_hasFDerivAt
    (f := fun y : Fin n → ℝ ↦ y i - y j) x
    ((hasFDerivAt_apply (𝕜 := ℝ) i x).sub (hasFDerivAt_apply (𝕜 := ℝ) j x))

/-! ### The logarithmic Vandermonde potential -/

/-- **The logarithmic Vandermonde potential** `∑_{i < j} log (xᵢ - xⱼ)`. With Mathlib's convention
`Real.log t = Real.log |t|`, it is the logarithm of the absolute value of the Vandermonde
determinant when the coordinates are distinct
(`logVandermonde_eq_log_abs_det_vandermonde`). -/
noncomputable def logVandermonde (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.Ioi i, Real.log (x i - x j)

/-- Unfolding `logVandermonde`. -/
theorem logVandermonde_def (x : Fin n → ℝ) :
    logVandermonde n x = ∑ i, ∑ j ∈ Finset.Ioi i, Real.log (x i - x j) :=
  (rfl)

/-- For distinct coordinates, `logVandermonde n x` is the logarithm of the absolute value of the
Vandermonde determinant of `x`. -/
theorem logVandermonde_eq_log_abs_det_vandermonde {x : Fin n → ℝ} (hx : Function.Injective x) :
    logVandermonde n x = Real.log |(Matrix.vandermonde x).det| := by
  rw [Matrix.det_vandermonde, Real.log_abs, Real.log_prod fun i _ ↦ Finset.prod_ne_zero_iff.2
    fun j hj ↦ sub_ne_zero.2 (hx.ne (Finset.mem_Ioi.1 hj).ne')]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Real.log_prod fun j hj ↦ sub_ne_zero.2 (hx.ne (Finset.mem_Ioi.1 hj).ne')]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [← neg_sub, Real.log_neg_eq_log]

/-- `logVandermonde n` is smooth of every order off the collision hyperplanes. -/
theorem contDiffAt_logVandermonde {x : Fin n → ℝ} (hx : Function.Injective x) {k : WithTop ℕ∞} :
    ContDiffAt ℝ k (logVandermonde n) x := by
  have h : logVandermonde n = fun y ↦ ∑ i, ∑ j ∈ Finset.Ioi i, Real.log (y i - y j) :=
    funext logVandermonde_def
  rw [h]
  exact ContDiffAt.sum fun i _ ↦ ContDiffAt.sum fun j hj ↦
    ((contDiffAt_apply ℝ (fun _ ↦ ℝ) i x).sub (contDiffAt_apply ℝ (fun _ ↦ ℝ) j x)).log
      (sub_ne_zero.2 (hx.ne (Finset.mem_Ioi.1 hj).ne))

/-- **The gradient of the logarithmic Vandermonde potential** is `n • dysonDrift n x` off the
collision hyperplanes. -/
theorem hasFDerivAt_logVandermonde {x : Fin n → ℝ} (hx : Function.Injective x) :
    HasFDerivAt (logVandermonde n)
      (∑ i, ((n : ℝ) * dysonDrift n x i) • (proj i : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
  have h : HasFDerivAt (logVandermonde n)
      (∑ i, ∑ j ∈ Finset.Ioi i,
        (x i - x j)⁻¹ • ((proj i : (Fin n → ℝ) →L[ℝ] ℝ) - proj j)) x := by
    have hfun : logVandermonde n = fun y ↦ ∑ i, ∑ j ∈ Finset.Ioi i, Real.log (y i - y j) :=
      funext logVandermonde_def
    rw [hfun]
    exact HasFDerivAt.fun_sum fun i _ ↦ HasFDerivAt.fun_sum fun j hj ↦
      ((hasFDerivAt_apply (𝕜 := ℝ) i x).sub (hasFDerivAt_apply (𝕜 := ℝ) j x)).log
        (sub_ne_zero.2 (hx.ne (Finset.mem_Ioi.1 hj).ne))
  convert h using 1
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [sum_apply, smul_apply,
    sub_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [← mul_inv_cancel_left₀ (Nat.cast_ne_zero.2 hn.ne' : (n : ℝ) ≠ 0)
      (∑ i, ∑ j ∈ Finset.Ioi i, (x i - x j)⁻¹ * (v i - v j))]
  simp_rw [mul_comm (x _ - x _)⁻¹, ← sum_mul_dysonDrift_eq_sum_Ioi, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-! ### Generator identities -/

/-- The generator of a difference of `C²` functions is the difference of their generators. -/
theorem dysonGenerator_sub {f₁ f₂ : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (h₁ : ContDiffAt ℝ 2 f₁ x)
    (h₂ : ContDiffAt ℝ 2 f₂ x) :
    dysonGenerator β n (fun y ↦ f₁ y - f₂ y) x =
      dysonGenerator β n f₁ x - dysonGenerator β n f₂ x := by
  have e₁ := (h₁.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp)
  have e₂ := (h₂.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp)
  have hfd : fderiv ℝ (fun y ↦ f₁ y - f₂ y) =ᶠ[𝓝 x] fderiv ℝ f₁ - fderiv ℝ f₂ :=
    (e₁.and e₂).mono fun y hy ↦ fderiv_fun_sub hy.1 hy.2
  have d₁ := (h₁.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have d₂ := (h₂.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  rw [dysonGenerator_def, dysonGenerator_def, dysonGenerator_def, hfd.fderiv_eq,
    fderiv_sub d₁ d₂, hfd.self_of_nhds]
  simp only [sub_apply, Pi.sub_apply, Finset.sum_sub_distrib, mul_sub]
  ring

/-- **The generator of the squared norm.** At a configuration with distinct coordinates, the
generator of `∑ᵢ xᵢ²` is `n - 1 + 2 / β`: the diffusion contributes `2 / β` and the drift
contributes `2 ∑ᵢ xᵢ dysonDrift n x i = n - 1`. -/
theorem dysonGenerator_sum_sq (hn : 0 < n) {x : Fin n → ℝ} (hx : Function.Injective x) :
    dysonGenerator β n (fun y ↦ ∑ i, y i ^ 2) x = n - 1 + 2 / β := by
  rw [dysonGenerator_eq_of_hasFDerivAt (g := fun i y ↦ 2 * y i)
    (.of_forall fun y ↦ hasFDerivAt_sum_sq y)
    fun i ↦ (hasFDerivAt_apply (𝕜 := ℝ) i x).const_mul 2]
  have hsum : ∑ i, dysonDrift n x i * (2 * x i) = 2 * ∑ i, x i * dysonDrift n x i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
  have hn₀ : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  simp only [smul_apply, ContinuousLinearMap.proj_apply, Pi.single_eq_same,
    smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum, sum_self_mul_dysonDrift hn hx]
  linear_combination (2 * β⁻¹) * inv_mul_cancel₀ hn₀

/-- Evaluating `n` times the derivative of `dysonDrift n · i` on the coordinate vector `eᵢ`: the
diagonal second derivatives of `logVandermonde n` are `-∑_{j ≠ i} (xᵢ - xⱼ)⁻²`. -/
private theorem smul_fderiv_dysonDrift_apply_single (x : Fin n → ℝ) (i : Fin n) :
    (((n : ℝ) • ((n : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i,
        (-((x i - x j) ^ 2)⁻¹) • ((proj i : (Fin n → ℝ) →L[ℝ] ℝ) - proj j))) :
          (Fin n → ℝ) →L[ℝ] ℝ) (Pi.single i 1) =
      -∑ j ∈ Finset.univ.erase i, (x i - x j)⁻¹ ^ 2 := by
  have hn₀ : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fin.pos i).ne'
  rw [smul_smul, mul_inv_cancel₀ hn₀, one_smul, sum_apply,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  simp [Finset.ne_of_mem_erase hj, inv_pow]

/-- **The generator of the logarithmic Vandermonde potential.** At a configuration with distinct
coordinates it is `2 (1 - β⁻¹) n⁻¹ ∑_{i < j} (xᵢ - xⱼ)⁻²`: the diffusion contributes
`-2 (β n)⁻¹ ∑_{i < j} (xᵢ - xⱼ)⁻²` and the drift contributes `n ∑ᵢ (dysonDrift n x i)²`, which the
Calogero–Moser identity `sum_dysonDrift_sq` evaluates. -/
theorem dysonGenerator_logVandermonde {x : Fin n → ℝ} (hx : Function.Injective x) :
    dysonGenerator β n (logVandermonde n) x =
      2 * (1 - β⁻¹) * (n : ℝ)⁻¹ * ∑ i, ∑ j ∈ Finset.Ioi i, (x i - x j)⁻¹ ^ 2 := by
  rw [dysonGenerator_eq_of_hasFDerivAt (g := fun i y ↦ (n : ℝ) * dysonDrift n y i)
    (Filter.mem_of_superset (TauCeti.isOpen_setOf_injective.mem_nhds hx)
      fun _ hy ↦ hasFDerivAt_logVandermonde hy)
    fun i ↦ (hasFDerivAt_dysonDrift_apply hx i).const_mul (n : ℝ)]
  simp_rw [smul_fderiv_dysonDrift_apply_single, Finset.sum_neg_distrib,
    Finset.sum_sum_erase_sub_inv_sq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn₀ : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hsq : ∑ i, dysonDrift n x i * ((n : ℝ) * dysonDrift n x i) =
      (n : ℝ) * ∑ i, dysonDrift n x i ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ ↦ by ring
  rw [hsq, sum_dysonDrift_sq hx, mul_inv]
  field_simp
  ring

/-- In the repulsive regime `β ≥ 1`, the generator of the logarithmic Vandermonde potential is
nonnegative at every configuration with distinct coordinates. -/
theorem dysonGenerator_logVandermonde_nonneg (hβ : 1 ≤ β) {x : Fin n → ℝ}
    (hx : Function.Injective x) : 0 ≤ dysonGenerator β n (logVandermonde n) x := by
  rw [dysonGenerator_logVandermonde hx]
  have : 0 ≤ 1 - β⁻¹ := sub_nonneg.2 (inv_le_one_of_one_le₀ hβ)
  positivity

/-! ### The Lyapunov function -/

/-- **The Lyapunov function of the Dyson system**, `∑ᵢ xᵢ² - ∑_{i < j} log (xᵢ - xⱼ)`. On the open
Weyl chamber it tends to `+∞` at the walls and at infinity. -/
noncomputable def dysonLyapunov (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i ^ 2 - logVandermonde n x

/-- Unfolding `dysonLyapunov`. -/
theorem dysonLyapunov_def (x : Fin n → ℝ) :
    dysonLyapunov n x = ∑ i, x i ^ 2 - logVandermonde n x :=
  (rfl)

/-- `dysonLyapunov n` is smooth of every order off the collision hyperplanes. -/
theorem contDiffAt_dysonLyapunov {x : Fin n → ℝ} (hx : Function.Injective x) {k : WithTop ℕ∞} :
    ContDiffAt ℝ k (dysonLyapunov n) x := by
  have h : dysonLyapunov n = fun y ↦ ∑ i, y i ^ 2 - logVandermonde n y := funext dysonLyapunov_def
  rw [h]
  exact (ContDiffAt.sum fun i _ ↦ (contDiffAt_apply ℝ (fun _ ↦ ℝ) i x).pow 2).sub
    (contDiffAt_logVandermonde hx)

/-- **The generator of the Lyapunov function.** At a configuration with distinct coordinates it is
`n - 1 + 2 / β - 2 (1 - β⁻¹) n⁻¹ ∑_{i < j} (xᵢ - xⱼ)⁻²`. -/
theorem dysonGenerator_dysonLyapunov (hn : 0 < n) {x : Fin n → ℝ} (hx : Function.Injective x) :
    dysonGenerator β n (dysonLyapunov n) x =
      n - 1 + 2 / β - 2 * (1 - β⁻¹) * (n : ℝ)⁻¹ * ∑ i, ∑ j ∈ Finset.Ioi i, (x i - x j)⁻¹ ^ 2 := by
  have h : dysonLyapunov n = fun y ↦ ∑ i, y i ^ 2 - logVandermonde n y := funext dysonLyapunov_def
  rw [h, dysonGenerator_sub (ContDiffAt.sum fun i _ ↦ (contDiffAt_apply ℝ (fun _ ↦ ℝ) i x).pow 2)
    (contDiffAt_logVandermonde hx), dysonGenerator_sum_sq hn hx, dysonGenerator_logVandermonde hx]

/-- **The Lyapunov bound.** For `β ≥ 1`, the generator of `dysonLyapunov n` is at most
`n - 1 + 2 / β` at every configuration with distinct coordinates. -/
theorem dysonGenerator_dysonLyapunov_le (hβ : 1 ≤ β) (hn : 0 < n) {x : Fin n → ℝ}
    (hx : Function.Injective x) : dysonGenerator β n (dysonLyapunov n) x ≤ n - 1 + 2 / β := by
  have h := dysonGenerator_logVandermonde_nonneg hβ hx
  rw [dysonGenerator_logVandermonde hx] at h
  rw [dysonGenerator_dysonLyapunov hn hx]
  linarith

/-! ### Coercivity on the open chamber -/

/-- A single logarithmic gap is dominated by the squared norm: with `a = 2 n²`,
`log (xᵢ - xⱼ) ≤ (∑ₖ xₖ²) / a + log a / 2` whenever `xⱼ < xᵢ`. -/
private theorem log_sub_le {x : Fin n → ℝ} {i j : Fin n} (hij : x j < x i) :
    Real.log (x i - x j) ≤
      (∑ k, x k ^ 2) / (2 * (n : ℝ) ^ 2) + Real.log (2 * (n : ℝ) ^ 2) / 2 := by
  have hne : i ≠ j := fun h ↦ hij.ne (by rw [h])
  have hg : 0 < x i - x j := sub_pos.2 hij
  have ha : 0 < 2 * (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < n := Nat.cast_pos.2 (Fin.pos i)
    positivity
  have hpair : x i ^ 2 + x j ^ 2 ≤ ∑ k, x k ^ 2 := by
    rw [← Finset.sum_pair (f := fun k ↦ x k ^ 2) hne]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ ↦ sq_nonneg _
  have hlog := Real.log_le_sub_one_of_pos (div_pos (pow_pos hg 2) ha)
  rw [Real.log_div (pow_pos hg 2).ne' ha.ne', Real.log_pow] at hlog
  have hsq : (x i - x j) ^ 2 / (2 * (n : ℝ) ^ 2) ≤ 2 * (∑ k, x k ^ 2) / (2 * (n : ℝ) ^ 2) :=
    div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (x i + x j)]) ha.le
  rw [mul_div_assoc] at hsq
  push_cast at hlog
  linarith

/-- **Quantitative coercivity.** Up to a constant depending only on `n`, the Lyapunov function
dominates half the squared norm and minus the logarithm of every ordered gap on the open chamber. -/
private theorem exists_forall_sum_sq_le_and_neg_log_le (n : ℕ) :
    ∃ C : ℝ, ∀ x : Fin n → ℝ, StrictAnti x →
      ∑ i, x i ^ 2 ≤ 2 * (dysonLyapunov n x + C) ∧
        ∀ i j, i < j → -Real.log (x i - x j) ≤ dysonLyapunov n x + C := by
  refine ⟨(n : ℝ) ^ 2 * (Real.log (2 * (n : ℝ) ^ 2) / 2), fun x hx ↦ ?_⟩
  have hQ : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hloga : 0 ≤ Real.log (2 * (n : ℝ) ^ 2) / 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn
    exact div_nonneg (Real.log_nonneg (by nlinarith)) zero_le_two
  set t := (∑ k, x k ^ 2) / (2 * (n : ℝ) ^ 2) + Real.log (2 * (n : ℝ) ^ 2) / 2 with ht_def
  have ht : 0 ≤ t := add_nonneg (div_nonneg hQ (by positivity)) hloga
  have hb (i : Fin n) : ∀ j ∈ Finset.Ioi i, 0 ≤ t - Real.log (x i - x j) :=
    fun j hj ↦ sub_nonneg.2 (log_sub_le (hx (Finset.mem_Ioi.1 hj)))
  -- The pairs number at most `n²`, so the bounds `t` add up to at most `n² t`.
  have hsum_t : ∑ i : Fin n, ∑ _j ∈ Finset.Ioi i, t ≤ (n : ℝ) ^ 2 * t :=
    calc ∑ i : Fin n, ∑ _j ∈ Finset.Ioi i, t ≤ ∑ _i : Fin n, ∑ _j : Fin n, t :=
          Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _) fun _ _ _ ↦ ht
      _ = (n : ℝ) ^ 2 * t := by simp [sq, mul_assoc]
  have hnt : (n : ℝ) ^ 2 * t =
      (∑ k, x k ^ 2) / 2 + (n : ℝ) ^ 2 * (Real.log (2 * (n : ℝ) ^ 2) / 2) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn₀ : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    rw [ht_def]
    field_simp
  have hB : ∑ i, ∑ j ∈ Finset.Ioi i, (t - Real.log (x i - x j)) =
      ∑ i : Fin n, ∑ _j ∈ Finset.Ioi i, t - logVandermonde n x := by
    simp only [Finset.sum_sub_distrib, logVandermonde_def]
  rw [dysonLyapunov_def]
  refine ⟨?_, fun i j hij ↦ ?_⟩
  · have : 0 ≤ ∑ i, ∑ j ∈ Finset.Ioi i, (t - Real.log (x i - x j)) :=
      Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg (hb i)
    linarith
  · have hle : t - Real.log (x i - x j) ≤ ∑ i, ∑ j ∈ Finset.Ioi i, (t - Real.log (x i - x j)) :=
      (Finset.single_le_sum (hb i) (Finset.mem_Ioi.2 hij)).trans
        (Finset.single_le_sum (fun i _ ↦ Finset.sum_nonneg (hb i)) (Finset.mem_univ i))
    linarith

/-- The Lyapunov function is bounded below on the open Weyl chamber. -/
theorem bddBelow_image_dysonLyapunov : BddBelow (dysonLyapunov n '' {x | StrictAnti x}) := by
  obtain ⟨C, hC⟩ := exists_forall_sum_sq_le_and_neg_log_le n
  refine ⟨-C, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have := (hC x hx).1
  have : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  linarith

/-- **Sublevel sets lie in the truncation regions.** For every level `M` there are `ε > 0` and `R`
such that every configuration of the open Weyl chamber with `dysonLyapunov n x ≤ M` has all ordered
gaps `xᵢ - xⱼ` (`i < j`) at least `ε` and `∑ᵢ xᵢ² ≤ R`. -/
theorem exists_forall_le_sub_and_sum_sq_le_of_dysonLyapunov_le (n : ℕ) (M : ℝ) :
    ∃ ε > 0, ∃ R : ℝ, ∀ x : Fin n → ℝ, StrictAnti x → dysonLyapunov n x ≤ M →
      (∀ i j, i < j → ε ≤ x i - x j) ∧ ∑ i, x i ^ 2 ≤ R := by
  obtain ⟨C, hC⟩ := exists_forall_sum_sq_le_and_neg_log_le n
  refine ⟨Real.exp (-(M + C)), Real.exp_pos _, 2 * (M + C), fun x hx hM ↦
    ⟨fun i j hij ↦ ?_, by linarith [(hC x hx).1]⟩⟩
  rw [← Real.le_log_iff_exp_le (sub_pos.2 (hx hij))]
  linarith [(hC x hx).2 i j hij]

end TauCeti.Probability
