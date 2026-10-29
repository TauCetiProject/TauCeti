/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Exp
public import TauCeti.Analysis.Calculus.Deriv.RescaledProfile

/-!
# Functions with Gaussian decay

A function `Ψ : E → F` has Gaussian decay at rate `c` if it is smooth and each of its iterated
derivatives, against every polynomial weight `(1 + ‖y‖)^p`, is dominated by `exp(-c ‖y‖²)`.
This class is closed under scalar multiplication, subtraction and `Ψ ↦ (y ↦ DΨ(y) y)`.

Consequently it is stable under the time derivatives of parabolically rescaled profiles: every
iterated derivative in `s` of `s^(-a) Ψ(s^(-1/2) x)` is again of the form
`s^(-(a + j)) Φ(s^(-1/2) x)` with `Φ` of Gaussian decay at the same rate. This is how the time
derivatives of the heat kernel are bounded.

## Main declarations

* `TauCeti.GaussianDecay`: smoothness with Gaussian decay of all weighted derivatives.
* `TauCeti.exists_gaussianDecay_iteratedDeriv_rpow_smul`: iterated time derivatives of
  parabolically rescaled profiles with Gaussian decay.
-/

public section

namespace TauCeti

open Real
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `Ψ` has Gaussian decay at rate `c`: it is smooth, and each of its iterated derivatives,
against every polynomial weight `(1 + ‖y‖)^p`, is dominated by the Gaussian `exp(-c ‖y‖²)`. -/
structure GaussianDecay (c : ℝ) (Ψ : E → F) : Prop where
  /-- A function with Gaussian decay is smooth. -/
  contDiff : ContDiff ℝ ∞ Ψ
  /-- Every weighted iterated derivative is dominated by the Gaussian. -/
  exists_bound : ∀ i p : ℕ, ∃ C, ∀ y,
    (1 + ‖y‖) ^ p * ‖iteratedFDeriv ℝ i Ψ y‖ ≤ C * exp (-c * ‖y‖ ^ 2)

namespace GaussianDecay

variable {c : ℝ}

/-- Gaussian decay is preserved by scalar multiplication. -/
theorem const_smul {Ψ : E → F} (hΨ : GaussianDecay c Ψ) (a : ℝ) :
    GaussianDecay c fun y => a • Ψ y := by
  refine ⟨hΨ.contDiff.const_smul a, fun i p => ?_⟩
  obtain ⟨C, hC⟩ := hΨ.exists_bound i p
  refine ⟨‖a‖ * C, fun y => ?_⟩
  rw [iteratedFDeriv_const_smul_apply' (hΨ.contDiff.contDiffAt.of_le (by exact_mod_cast le_top)),
    norm_smul, mul_left_comm, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg a)

/-- Gaussian decay is preserved by subtraction. -/
theorem sub {Ψ Φ : E → F} (hΨ : GaussianDecay c Ψ) (hΦ : GaussianDecay c Φ) :
    GaussianDecay c fun y => Ψ y - Φ y := by
  refine ⟨hΨ.contDiff.sub hΦ.contDiff, fun i p => ?_⟩
  obtain ⟨C₁, hC₁⟩ := hΨ.exists_bound i p
  obtain ⟨C₂, hC₂⟩ := hΦ.exists_bound i p
  refine ⟨C₁ + C₂, fun y => ?_⟩
  rw [fun_iteratedFDeriv_sub_apply (hΨ.contDiff.contDiffAt.of_le (by exact_mod_cast le_top))
      (hΦ.contDiff.contDiffAt.of_le (by exact_mod_cast le_top))]
  calc (1 + ‖y‖) ^ p * ‖iteratedFDeriv ℝ i Ψ y - iteratedFDeriv ℝ i Φ y‖
      ≤ (1 + ‖y‖) ^ p * ‖iteratedFDeriv ℝ i Ψ y‖ + (1 + ‖y‖) ^ p * ‖iteratedFDeriv ℝ i Φ y‖ := by
        rw [← mul_add]
        gcongr
        exact norm_sub_le _ _
    _ ≤ C₁ * exp (-c * ‖y‖ ^ 2) + C₂ * exp (-c * ‖y‖ ^ 2) := add_le_add (hC₁ y) (hC₂ y)
    _ = (C₁ + C₂) * exp (-c * ‖y‖ ^ 2) := by ring

/-- If `Ψ` has Gaussian decay, so does `y ↦ DΨ(y) y`: the polynomial weights absorb the factor
`y`. -/
theorem fderiv_apply_self {Ψ : E → F} (hΨ : GaussianDecay c Ψ) :
    GaussianDecay c fun y => fderiv ℝ Ψ y y := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ Ψ) := hΨ.contDiff.fderiv_right (by simp)
  choose C hC using hΨ.exists_bound
  refine ⟨hd.clm_apply contDiff_fun_id, fun i p =>
    ⟨∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * C (l + 1) (p + 1), fun y => ?_⟩⟩
  -- The derivatives of the identity are bounded by `1 + ‖y‖`.
  have hid : ∀ r, ‖iteratedFDeriv ℝ r (fun z : E => z) y‖ ≤ 1 + ‖y‖ := by
    have hD : fderiv ℝ (fun z : E => z) = fun _ => ContinuousLinearMap.id ℝ E :=
      funext fun _ => fderiv_fun_id
    rintro (_ | _ | r)
    · simp
    · rw [← norm_iteratedFDeriv_fderiv, hD, norm_iteratedFDeriv_zero]
      linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E), norm_nonneg y]
    · rw [← norm_iteratedFDeriv_fderiv, hD, iteratedFDeriv_const_of_ne (by omega)]
      simp only [Pi.zero_apply, norm_zero]
      positivity
  have hB := (ContinuousLinearMap.id ℝ (E →L[ℝ] F)).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (g := fun z : E => z) hd contDiff_fun_id y (n := i) (by exact_mod_cast le_top)
    ContinuousLinearMap.norm_id_le
  simp only [ContinuousLinearMap.id_apply] at hB
  calc (1 + ‖y‖) ^ p * ‖iteratedFDeriv ℝ i (fun y => fderiv ℝ Ψ y y) y‖
      ≤ (1 + ‖y‖) ^ p * ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) *
          ‖iteratedFDeriv ℝ l (fderiv ℝ Ψ) y‖ * ‖iteratedFDeriv ℝ (i - l) (fun z : E => z) y‖ := by
        gcongr
    _ ≤ ∑ l ∈ Finset.range (i + 1),
          (i.choose l : ℝ) * (C (l + 1) (p + 1) * exp (-c * ‖y‖ ^ 2)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun l _ => ?_
        calc (1 + ‖y‖) ^ p * ((i.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fderiv ℝ Ψ) y‖ *
              ‖iteratedFDeriv ℝ (i - l) (fun z : E => z) y‖)
            ≤ (1 + ‖y‖) ^ p * ((i.choose l : ℝ) * ‖iteratedFDeriv ℝ (l + 1) Ψ y‖ * (1 + ‖y‖)) := by
              rw [norm_iteratedFDeriv_fderiv]
              gcongr
              exact hid _
          _ = (i.choose l : ℝ) * ((1 + ‖y‖) ^ (p + 1) * ‖iteratedFDeriv ℝ (l + 1) Ψ y‖) := by ring
          _ ≤ (i.choose l : ℝ) * (C (l + 1) (p + 1) * exp (-c * ‖y‖ ^ 2)) :=
              mul_le_mul_of_nonneg_left (hC _ _ y) (by positivity)
    _ = (∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * C (l + 1) (p + 1)) *
          exp (-c * ‖y‖ ^ 2) := by
        rw [Finset.sum_mul]
        simp only [mul_assoc]

end GaussianDecay

/-- Iterated time derivatives of a parabolically rescaled profile with Gaussian decay are again
rescaled profiles with Gaussian decay at the same rate. -/
theorem exists_gaussianDecay_iteratedDeriv_rpow_smul {c : ℝ} (j : ℕ) :
    ∀ (a : ℝ) {Ψ : E → F}, GaussianDecay c Ψ → ∃ Φ : E → F, GaussianDecay c Φ ∧
      ∀ x : E, ∀ s : ℝ, 0 < s →
        iteratedDeriv j (fun s : ℝ => s ^ (-a) • Ψ (s ^ (-1 / 2 : ℝ) • x)) s =
          s ^ (-(a + j)) • Φ (s ^ (-1 / 2 : ℝ) • x) := by
  induction j with
  | zero => exact fun a Ψ hΨ => ⟨Ψ, hΨ, fun x s _ => by simp⟩
  | succ j ih =>
    intro a Ψ hΨ
    obtain ⟨Φ, hΦ, h⟩ :=
      ih (a + 1) ((hΨ.const_smul (-a)).sub (hΨ.fderiv_apply_self.const_smul (1 / 2)))
    refine ⟨Φ, hΦ, fun x s hs => ?_⟩
    have hderiv : deriv (fun s : ℝ => s ^ (-a) • Ψ (s ^ (-1 / 2 : ℝ) • x)) =ᶠ[nhds s]
        fun s : ℝ => s ^ (-(a + 1)) • (-a • Ψ (s ^ (-1 / 2 : ℝ) • x) -
          (1 / 2 : ℝ) • fderiv ℝ Ψ (s ^ (-1 / 2 : ℝ) • x) (s ^ (-1 / 2 : ℝ) • x)) :=
      (eventually_gt_nhds hs).mono fun s' hs' =>
        ((hasDerivAt_rpow_smul_comp_rpow_smul a (-1 / 2) x hs'
          ((hΨ.contDiff.differentiable (by simp)).differentiableAt)).congr_deriv
            (by module)).deriv
    have hexp : -(a + 1 + (j : ℝ)) = -(a + ((j + 1 : ℕ) : ℝ)) := by push_cast; ring
    rw [iteratedDeriv_succ', hderiv.iteratedDeriv_eq, h x s hs, hexp]

end TauCeti
