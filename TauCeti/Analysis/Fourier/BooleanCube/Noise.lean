/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.BooleanCube.Norm
import TauCeti.Analysis.Fourier.BooleanCube.Plancherel
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The noise operator on the Boolean cube

For a real number `ρ`, the noise operator `noise ρ` averages a real function on the cube
`ι → ZMod 2` against the kernel `noiseKernel ρ x y`, the product over the coordinates of
`(1 + ρ) / 2` where `x` and `y` agree and of `(1 - ρ) / 2` where they differ. For `|ρ| ≤ 1` the
kernel is a probability on `y`: `noise ρ f x` is the mean of `f y` when each coordinate of `y`
equals that of `x` with probability `(1 + ρ) / 2`, independently. For every real `ρ` the operator
multiplies the Walsh coefficient at `S` by `ρ ^ #S`, so the operators compose by the product of
the parameters, commute and are self-adjoint. For `|ρ| ≤ 1` they contract every `L^p` norm with
`1 ≤ p`.

## Main definitions

* `TauCeti.noiseKernel ρ x y`: the kernel `∏ i, (1 + ρ * (-1) ^ (x i + y i).val) / 2`.
* `TauCeti.noise ρ f`: the noise operator `x ↦ ∑ y, noiseKernel ρ x y * f y`.

## Main results

* `TauCeti.noiseKernel_comm`, `TauCeti.sum_noiseKernel`, `TauCeti.noiseKernel_nonneg`: the
  kernel is symmetric, its rows sum to `1`, and it is nonnegative for `|ρ| ≤ 1`.
* `TauCeti.noiseKernel_eq_sum_walsh`: the Walsh expansion of the kernel.
* `TauCeti.noise_eq_sum_walshCoeff`, `TauCeti.walshCoeff_noise`: the Walsh expansion of
  `noise ρ f`, and `walshCoeff (noise ρ f) S = ρ ^ #S * walshCoeff f S`.
* `TauCeti.noise_walsh`, `TauCeti.noise_const`: `noise ρ (walsh S) = ρ ^ #S • walsh S`, and
  `noise ρ` fixes the constant functions.
* `TauCeti.noise_noise`, `TauCeti.noise_comm`: `noise ρ (noise σ f) = noise (ρ * σ) f`, so two
  noise operators commute.
* `TauCeti.noise_one_left`, `TauCeti.noise_zero_left`, `TauCeti.noise_neg_one_left`: `noise 1` is
  the identity, `noise 0 f` is the constant mean of `f`, and `noise (-1) f x = f (x + 1)`.
* `TauCeti.expect_mul_noise_comm`: `noise ρ` is self-adjoint for the uniform measure.
* `TauCeti.cubeNorm_noise_le_of_abs_le_one`: for `|ρ| ≤ 1` and `1 ≤ p`, `noise ρ` does not
  increase the `L^p` norm.

## References

* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014
  (arXiv:2105.10386), Chapter 2: Definitions 2.40 and 2.46, Proposition 2.47,
  Exercises 2.32 and 2.33.
-/

public section

open Finset Real
open scoped BigOperators

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-! ### The kernel -/

/-- The **noise kernel** on the cube: the product over the coordinates of `(1 + ρ) / 2` where
`x` and `y` agree and of `(1 - ρ) / 2` where they differ. -/
noncomputable def noiseKernel (ρ : ℝ) (x y : ι → ZMod 2) : ℝ :=
  ∏ i, (1 + ρ * (-1) ^ (x i + y i).val) / 2

/-- The defining formula of the noise kernel. -/
lemma noiseKernel_def (ρ : ℝ) (x y : ι → ZMod 2) :
    noiseKernel ρ x y = ∏ i, (1 + ρ * (-1) ^ (x i + y i).val) / 2 := (rfl)

/-- The factor of the noise kernel at a coordinate is `(1 + ρ) / 2` where `x` and `y` agree and
`(1 - ρ) / 2` where they differ. -/
lemma noiseKernel_eq_prod_ite (ρ : ℝ) (x y : ι → ZMod 2) :
    noiseKernel ρ x y = ∏ i, if x i = y i then (1 + ρ) / 2 else (1 - ρ) / 2 := by
  -- The sign `(-1) ^ (a + b).val` of two bits is `1` if they agree and `-1` otherwise.
  have h (a b : ZMod 2) : (-1 : ℝ) ^ (a + b).val = if a = b then 1 else -1 := by
    obtain rfl | rfl : a = 0 ∨ a = 1 := by decide +revert
    all_goals obtain rfl | rfl : b = 0 ∨ b = 1 := by decide +revert
    all_goals try simp only [show (1 + 1 : ZMod 2) = 0 from rfl]
    all_goals norm_num [ZMod.val_one]
  refine prod_congr rfl fun i _ ↦ ?_
  rw [h]
  split_ifs <;> ring

/-- The noise kernel is symmetric. -/
lemma noiseKernel_comm (ρ : ℝ) (x y : ι → ZMod 2) : noiseKernel ρ x y = noiseKernel ρ y x := by
  simp_rw [noiseKernel_def, add_comm (x _)]

/-- For `|ρ| ≤ 1` the noise kernel is nonnegative. -/
lemma noiseKernel_nonneg {ρ : ℝ} (hρ : |ρ| ≤ 1) (x y : ι → ZMod 2) : 0 ≤ noiseKernel ρ x y := by
  rw [noiseKernel_eq_prod_ite]
  rw [abs_le] at hρ
  refine prod_nonneg fun i _ ↦ ?_
  split_ifs <;> linarith

/-- The Walsh expansion of the noise kernel:
`noiseKernel ρ x y = (∑ S, ρ ^ #S * walsh S (x + y)) / 2 ^ n`, where `n` is the number of
coordinates. -/
lemma noiseKernel_eq_sum_walsh (ρ : ℝ) (x y : ι → ZMod 2) :
    noiseKernel ρ x y = (∑ S, ρ ^ #S * walsh S (x + y)) / 2 ^ Fintype.card ι := by
  rw [noiseKernel_def, prod_div_distrib, prod_const, card_univ, prod_one_add, powerset_univ]
  congr 1
  refine sum_congr rfl fun S _ ↦ ?_
  rw [prod_mul_distrib, prod_const, walsh_def]
  simp only [Pi.add_apply]

/-- At `ρ = -1` the noise kernel is the indicator of `y = x + 1`. -/
lemma noiseKernel_neg_one_left (x y : ι → ZMod 2) :
    noiseKernel (-1) x y = if y = x + 1 then 1 else 0 := by
  -- Two bits differ exactly when the second is the first plus `1`.
  have h (a b : ZMod 2) : ¬a = b ↔ b = a + 1 := by decide +revert
  have hy : (∀ i, ¬x i = y i) ↔ y = x + 1 := by
    simp only [h, funext_iff, Pi.add_apply, Pi.one_apply]
  rw [noiseKernel_eq_prod_ite]
  calc ∏ i, (if x i = y i then (1 + -1 : ℝ) / 2 else (1 - -1) / 2)
      = ∏ i, if ¬x i = y i then (1 : ℝ) else 0 := prod_congr rfl fun i _ ↦ by split_ifs <;> norm_num
    _ = if y = x + 1 then 1 else 0 := by simp only [Fintype.prod_boole, hy]

/-! ### The operator -/

variable [DecidableEq ι]

/-- The **noise operator** `T_ρ` on real functions on the cube: `noise ρ f x` is the sum of
`f y` against the noise kernel `noiseKernel ρ x y`. For `|ρ| ≤ 1` it is the mean of `f y` when
each coordinate of `y` equals that of `x` with probability `(1 + ρ) / 2`, independently. -/
noncomputable def noise (ρ : ℝ) (f : (ι → ZMod 2) → ℝ) (x : ι → ZMod 2) : ℝ :=
  ∑ y, noiseKernel ρ x y * f y

/-- The defining formula of the noise operator. -/
lemma noise_def (ρ : ℝ) (f : (ι → ZMod 2) → ℝ) (x : ι → ZMod 2) :
    noise ρ f x = ∑ y, noiseKernel ρ x y * f y := (rfl)

/-- The noise operator is additive. -/
@[simp] lemma noise_add (ρ : ℝ) (f g : (ι → ZMod 2) → ℝ) :
    noise ρ (f + g) = noise ρ f + noise ρ g := by
  ext x
  simp [noise_def, mul_add, sum_add_distrib]

/-- The noise operator commutes with scalar multiplication. -/
@[simp] lemma noise_smul (ρ c : ℝ) (f : (ι → ZMod 2) → ℝ) :
    noise ρ (c • f) = c • noise ρ f := by
  ext x
  simp [noise_def, mul_sum, mul_left_comm]

/-- The noise operator sends `0` to `0`. -/
@[simp] lemma noise_zero (ρ : ℝ) : noise ρ (0 : (ι → ZMod 2) → ℝ) = 0 := by
  ext x
  simp [noise_def]

/-- The noise operator commutes with negation. -/
@[simp] lemma noise_neg (ρ : ℝ) (f : (ι → ZMod 2) → ℝ) : noise ρ (-f) = -noise ρ f := by
  simpa using noise_smul ρ (-1) f

/-- The noise operator commutes with subtraction. -/
@[simp] lemma noise_sub (ρ : ℝ) (f g : (ι → ZMod 2) → ℝ) :
    noise ρ (f - g) = noise ρ f - noise ρ g := by
  simp [sub_eq_add_neg]

/-- The noise operator commutes with finite sums. -/
lemma noise_sum {κ : Type*} (ρ : ℝ) (s : Finset κ) (f : κ → (ι → ZMod 2) → ℝ) :
    noise ρ (∑ k ∈ s, f k) = ∑ k ∈ s, noise ρ (f k) := by
  ext x
  simp only [noise_def, Finset.sum_apply, mul_sum]
  exact sum_comm

/-- The Walsh expansion of `noise ρ f`: the coefficient at `S` is `ρ ^ #S * walshCoeff f S`. -/
theorem noise_eq_sum_walshCoeff (ρ : ℝ) (f : (ι → ZMod 2) → ℝ) (x : ι → ZMod 2) :
    noise ρ f x = ∑ S, ρ ^ #S * walshCoeff f S * walsh S x := by
  have hcard : (Fintype.card (ι → ZMod 2) : ℝ) = 2 ^ Fintype.card ι := by
    simp [ZMod.card]
  simp_rw [noise_def, noiseKernel_eq_sum_walsh, walshCoeff_def, Fintype.expect_eq_sum_div_card,
    hcard]
  simp only [sum_div, sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun S _ ↦ sum_congr rfl fun y _ ↦ ?_
  rw [walsh_add]
  ring

/-- **The noise operator on the Walsh expansion.** For every real `ρ`, the noise operator
multiplies the Walsh coefficient at `S` by `ρ ^ #S`. -/
@[simp] theorem walshCoeff_noise (ρ : ℝ) (f : (ι → ZMod 2) → ℝ) (S : Finset ι) :
    walshCoeff (noise ρ f) S = ρ ^ #S * walshCoeff f S :=
  eq_walshCoeff_of_forall_eq_sum (noise_eq_sum_walshCoeff ρ f) S |>.symm

/-- The noise operator multiplies the Walsh character `walsh S` by `ρ ^ #S`. -/
@[simp] lemma noise_walsh (ρ : ℝ) (S : Finset ι) : noise ρ (walsh S) = ρ ^ #S • walsh S := by
  refine walshCoeff_injective (funext fun T ↦ ?_)
  simp only [walshCoeff_noise, walshCoeff_walsh, walshCoeff_smul]
  split_ifs with h
  · rw [h]
  · simp

/-- The noise operator fixes the constant functions. -/
@[simp] lemma noise_const (ρ c : ℝ) : noise ρ (fun _ : ι → ZMod 2 ↦ c) = fun _ ↦ c := by
  refine walshCoeff_injective (funext fun S ↦ ?_)
  simp only [walshCoeff_noise, walshCoeff_const]
  split_ifs with h <;> simp [h]

/-- The rows of the noise kernel sum to `1`, for every real `ρ`. -/
@[simp] lemma sum_noiseKernel (ρ : ℝ) (x : ι → ZMod 2) : ∑ y, noiseKernel ρ x y = 1 := by
  simpa [noise_def] using congrFun (noise_const ρ 1) x

/-- The columns of the noise kernel sum to `1`, for every real `ρ`. -/
@[simp] lemma sum_noiseKernel_left (ρ : ℝ) (y : ι → ZMod 2) : ∑ x, noiseKernel ρ x y = 1 := by
  simp_rw [noiseKernel_comm ρ _ y, sum_noiseKernel]

/-- **The semigroup law.** Applying the noise operators for `σ` and then `ρ` is applying the
noise operator for `ρ * σ`. -/
@[simp] theorem noise_noise (ρ σ : ℝ) (f : (ι → ZMod 2) → ℝ) :
    noise ρ (noise σ f) = noise (ρ * σ) f := by
  refine walshCoeff_injective (funext fun S ↦ ?_)
  simp only [walshCoeff_noise, mul_pow]
  ring

/-- Two noise operators commute. -/
theorem noise_comm (ρ σ : ℝ) (f : (ι → ZMod 2) → ℝ) :
    noise ρ (noise σ f) = noise σ (noise ρ f) := by
  rw [noise_noise, noise_noise, mul_comm]

/-- The noise operator for `ρ = 1` is the identity. -/
@[simp] theorem noise_one_left (f : (ι → ZMod 2) → ℝ) : noise 1 f = f := by
  refine walshCoeff_injective (funext fun S ↦ ?_)
  simp

/-- The noise operator for `ρ = 0` sends a function to the constant function with value its
mean. -/
theorem noise_zero_left (f : (ι → ZMod 2) → ℝ) : noise 0 f = fun _ ↦ 𝔼 x, f x := by
  refine walshCoeff_injective (funext fun S ↦ ?_)
  simp only [walshCoeff_noise, walshCoeff_const]
  split_ifs with h <;> simp [h]

/-- The noise operator for `ρ = -1` is the translation by the all-ones vector. -/
theorem noise_neg_one_left (f : (ι → ZMod 2) → ℝ) (x : ι → ZMod 2) :
    noise (-1) f x = f (x + 1) := by
  simp [noise_def, noiseKernel_neg_one_left]

/-- **Self-adjointness.** The noise operator is self-adjoint for the uniform probability measure
on the cube. -/
theorem expect_mul_noise_comm (ρ : ℝ) (f g : (ι → ZMod 2) → ℝ) :
    𝔼 x, g x * noise ρ f x = 𝔼 x, f x * noise ρ g x := by
  simp_rw [expect_mul_eq_sum_walshCoeff, walshCoeff_noise]
  exact sum_congr rfl fun S _ ↦ by ring

/-- **Contraction.** For `|ρ| ≤ 1` and `1 ≤ p`, the noise operator does not increase the `L^p`
norm. -/
theorem cubeNorm_noise_le_of_abs_le_one {ρ p : ℝ} (hρ : |ρ| ≤ 1) (hp : 1 ≤ p)
    (f : (ι → ZMod 2) → ℝ) :
    cubeNorm p (noise ρ f) ≤ cubeNorm p f := by
  have hp₀ : 0 ≤ p := zero_le_one.trans hp
  -- Jensen's inequality for the probability `noiseKernel ρ x` on `y`.
  have hx (x : ι → ZMod 2) : |noise ρ f x| ^ p ≤ ∑ y, noiseKernel ρ x y * |f y| ^ p := by
    calc |noise ρ f x| ^ p ≤ (∑ y, noiseKernel ρ x y * |f y|) ^ p := by
          refine rpow_le_rpow (abs_nonneg _) ?_ hp₀
          refine (abs_sum_le_sum_abs _ _).trans_eq (sum_congr rfl fun y _ ↦ ?_)
          rw [abs_mul, abs_of_nonneg (noiseKernel_nonneg hρ x y)]
      _ ≤ ∑ y, noiseKernel ρ x y * |f y| ^ p :=
          rpow_arith_mean_le_arith_mean_rpow _ _ _ (fun y _ ↦ noiseKernel_nonneg hρ x y)
            (sum_noiseKernel ρ x) (fun y _ ↦ abs_nonneg _) hp
  -- Averaging over `x` gives the mean of `|f| ^ p`, since the columns sum to `1`.
  have havg : 𝔼 x, ∑ y, noiseKernel ρ x y * |f y| ^ p = 𝔼 y, |f y| ^ p := by
    simp_rw [expect_sum_comm, ← expect_mul, Fintype.expect_eq_sum_div_card, sum_noiseKernel_left,
      sum_div, one_div_mul_eq_div]
  rw [cubeNorm_def, cubeNorm_def]
  refine rpow_le_rpow (expect_nonneg fun _ _ ↦ rpow_nonneg (abs_nonneg _) _) ?_ (inv_nonneg.2 hp₀)
  exact (expect_le_expect fun x _ ↦ hx x).trans_eq havg

end TauCeti
