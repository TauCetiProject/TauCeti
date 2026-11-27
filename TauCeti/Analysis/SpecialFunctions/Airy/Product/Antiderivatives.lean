/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.SpecialFunctions.Airy.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.Analysis.SpecialFunctions.Airy.Equation

/-!
# Antiderivatives of products of solutions of Airy's equation

Let `f` and `g` be entire solutions of Airy's equation `w'' = z w`, and let
`𝒲 = f g' - f' g` be their Wronskian, which is constant. Then closed-form antiderivatives exist
for the products `f g`, `f g'`, `f' g'`, `z f g`, `z f g'` and `z f' g'` (DLMF 9.11.5–9.11.10).
For the quotient `g / f` there is a substitution formula (DLMF 9.11.11): if `𝒲 ≠ 0`, `f(z) ≠ 0`
and `F` has derivative `F'` at `g(z) / f(z)`, then `F(g / f) / 𝒲` has derivative `F' / f(z)²` at
`z`. In the statements the Wronskian is written out at the origin as
`f 0 * deriv g 0 - deriv f 0 * g 0`; its constancy is `TauCeti.wronskian_eq_of_airy_ode`.
For `f = Ai`, `g = Bi`, whose Wronskian is `1/π`, it gives antiderivatives of `1/Ai²` and
`1/(Ai Bi)`; a direct computation gives one of `Ai Bi/(Ai² + Bi²)²` (DLMF 9.11.12–9.11.14).

## Main results

* `TauCeti.hasDerivAt_antiderivative_mul_of_airy_ode`: `-f' g' + z f g` is an antiderivative
  of `f g` (DLMF 9.11.5);
* `TauCeti.hasDerivAt_antiderivative_mul_deriv_of_airy_ode`: `(f g + 𝒲 z) / 2` is an
  antiderivative of `f g'` (DLMF 9.11.6);
* `TauCeti.hasDerivAt_antiderivative_deriv_mul_deriv_of_airy_ode`:
  `(f g' + f' g + z f' g' - z² f g) / 3` is an antiderivative of `f' g'` (DLMF 9.11.7);
* `TauCeti.hasDerivAt_antiderivative_id_mul_mul_of_airy_ode`:
  `(f g' + f' g) / 6 - (z f' g' - z² f g) / 3` is an antiderivative of `z f g` (DLMF 9.11.8);
* `TauCeti.hasDerivAt_antiderivative_id_mul_mul_deriv_of_airy_ode`: `f' g' / 2 + 𝒲 z² / 4` is
  an antiderivative of `z f g'` (DLMF 9.11.9);
* `TauCeti.hasDerivAt_antiderivative_id_mul_deriv_mul_deriv_of_airy_ode`:
  `(3/10)(-f g + z f g' + z f' g) + (z² f' g' - z³ f g) / 5` is an antiderivative of `z f' g'`
  (DLMF 9.11.10);
* `TauCeti.hasDerivAt_comp_div_div_wronskian_of_airy_ode`: if `𝒲 ≠ 0`, `f(z) ≠ 0` and `F` has
  derivative `F'` at `g(z) / f(z)`, then `F(g / f) / 𝒲` has derivative `F' / f(z)²` at `z`
  (DLMF 9.11.11);
* `TauCeti.hasDerivAt_antiderivative_inv_airyAi_sq`: where `Ai(z) ≠ 0`, `π Bi/Ai` is an
  antiderivative of `1/Ai²` (DLMF 9.11.12);
* `TauCeti.hasDerivAt_antiderivative_inv_airyAi_mul_airyBi`: where `Bi(z)/Ai(z)` lies in the slit
  plane, `π log(Bi/Ai)` is an antiderivative of `1/(Ai Bi)` (DLMF 9.11.13);
* `TauCeti.hasDerivAt_antiderivative_airyAi_mul_airyBi_div_sq`: where `Ai(z)² + Bi(z)² ≠ 0`,
  `(π/2) Bi²/(Ai² + Bi²)` is an antiderivative of `Ai Bi/(Ai² + Bi²)²` (DLMF 9.11.14).

## References

* NIST Digital Library of Mathematical Functions, §9.11(iv), <https://dlmf.nist.gov/9.11.iv>.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/Airy/Products.lean` (for DLMF 9.11.12–9.11.14: `airyAi_recip_sq_antiderivative`,
`airyAiBi_recip_antiderivative` and `airy_modulus_rational_antiderivative`).
-/

public section

open Complex
open scoped Real

namespace TauCeti

variable {f g : ℂ → ℂ}

/-- For entire solutions `f`, `g` of Airy's equation, `-f' g' + z f g` is an antiderivative of
`f g` (DLMF 9.11.5). -/
theorem hasDerivAt_antiderivative_mul_of_airy_ode (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf' : ∀ z, deriv^[2] f z = z * f z)
    (hg' : ∀ z, deriv^[2] g z = z * g z) (z : ℂ) :
    HasDerivAt (fun t => -deriv f t * deriv g t + t * f t * g t) (f z * g z) z := by
  have h := ((hasDerivAt_deriv_of_airy_ode hf hf' z).neg.mul
    (hasDerivAt_deriv_of_airy_ode hg hg' z)).add
      (((hasDerivAt_id z).mul (hf z).hasDerivAt).mul (hg z).hasDerivAt)
  exact h.congr_deriv (by simp only [id, Pi.mul_apply, Pi.neg_apply]; ring)

/-- For entire solutions `f`, `g` of Airy's equation with Wronskian `𝒲 = f g' - f' g`,
`(f g + 𝒲 z) / 2` is an antiderivative of `f g'` (DLMF 9.11.6). -/
theorem hasDerivAt_antiderivative_mul_deriv_of_airy_ode (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf' : ∀ z, deriv^[2] f z = z * f z)
    (hg' : ∀ z, deriv^[2] g z = z * g z) (z : ℂ) :
    HasDerivAt (fun t => (f t * g t + t * (f 0 * deriv g 0 - deriv f 0 * g 0)) / 2)
      (f z * deriv g z) z := by
  have h := (((hf z).hasDerivAt.mul (hg z).hasDerivAt).add
    ((hasDerivAt_id z).mul_const (f 0 * deriv g 0 - deriv f 0 * g 0))).div_const 2
  have hW := wronskian_eq_of_airy_ode hf hg hf' hg' z 0
  exact h.congr_deriv (by linear_combination -hW / 2)

/-- For entire solutions `f`, `g` of Airy's equation, `(f g' + f' g + z f' g' - z² f g) / 3` is an
antiderivative of `f' g'` (DLMF 9.11.7). -/
theorem hasDerivAt_antiderivative_deriv_mul_deriv_of_airy_ode (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf' : ∀ z, deriv^[2] f z = z * f z)
    (hg' : ∀ z, deriv^[2] g z = z * g z) (z : ℂ) :
    HasDerivAt (fun t => (f t * deriv g t + deriv f t * g t + t * deriv f t * deriv g t -
      t ^ 2 * f t * g t) / 3) (deriv f z * deriv g z) z := by
  have hf₁ := (hf z).hasDerivAt
  have hg₁ := (hg z).hasDerivAt
  have hf₂ := hasDerivAt_deriv_of_airy_ode hf hf' z
  have hg₂ := hasDerivAt_deriv_of_airy_ode hg hg' z
  have h := ((((hf₁.mul hg₂).add (hf₂.mul hg₁)).add (((hasDerivAt_id z).mul hf₂).mul hg₂)).sub
    (((hasDerivAt_pow 2 z).mul hf₁).mul hg₁)).div_const 3
  exact h.congr_deriv (by simp only [id, Pi.mul_apply]; ring)

/-- For entire solutions `f`, `g` of Airy's equation, `(f g' + f' g) / 6 - (z f' g' - z² f g) / 3`
is an antiderivative of `z f g` (DLMF 9.11.8). -/
theorem hasDerivAt_antiderivative_id_mul_mul_of_airy_ode (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf' : ∀ z, deriv^[2] f z = z * f z)
    (hg' : ∀ z, deriv^[2] g z = z * g z) (z : ℂ) :
    HasDerivAt (fun t => (f t * deriv g t + deriv f t * g t) / 6 -
      (t * deriv f t * deriv g t - t ^ 2 * f t * g t) / 3) (z * f z * g z) z := by
  have hf₁ := (hf z).hasDerivAt
  have hg₁ := (hg z).hasDerivAt
  have hf₂ := hasDerivAt_deriv_of_airy_ode hf hf' z
  have hg₂ := hasDerivAt_deriv_of_airy_ode hg hg' z
  have h := (((hf₁.mul hg₂).add (hf₂.mul hg₁)).div_const 6).sub
    (((((hasDerivAt_id z).mul hf₂).mul hg₂).sub
      (((hasDerivAt_pow 2 z).mul hf₁).mul hg₁)).div_const 3)
  exact h.congr_deriv (by simp only [id, Pi.mul_apply]; ring)

/-- For entire solutions `f`, `g` of Airy's equation with Wronskian `𝒲 = f g' - f' g`,
`f' g' / 2 + 𝒲 z² / 4` is an antiderivative of `z f g'` (DLMF 9.11.9). -/
theorem hasDerivAt_antiderivative_id_mul_mul_deriv_of_airy_ode (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf' : ∀ z, deriv^[2] f z = z * f z)
    (hg' : ∀ z, deriv^[2] g z = z * g z) (z : ℂ) :
    HasDerivAt (fun t => deriv f t * deriv g t / 2 +
      t ^ 2 * (f 0 * deriv g 0 - deriv f 0 * g 0) / 4) (z * f z * deriv g z) z := by
  have h := (((hasDerivAt_deriv_of_airy_ode hf hf' z).mul
    (hasDerivAt_deriv_of_airy_ode hg hg' z)).div_const 2).add
      (((hasDerivAt_pow 2 z).mul_const (f 0 * deriv g 0 - deriv f 0 * g 0)).div_const 4)
  have hW := wronskian_eq_of_airy_ode hf hg hf' hg' z 0
  exact h.congr_deriv (by linear_combination -(z / 2) * hW)

/-- For entire solutions `f`, `g` of Airy's equation,
`(3/10)(-f g + z f g' + z f' g) + (z² f' g' - z³ f g) / 5` is an antiderivative of `z f' g'`
(DLMF 9.11.10). -/
theorem hasDerivAt_antiderivative_id_mul_deriv_mul_deriv_of_airy_ode (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf' : ∀ z, deriv^[2] f z = z * f z)
    (hg' : ∀ z, deriv^[2] g z = z * g z) (z : ℂ) :
    HasDerivAt (fun t => 3 / 10 * (-f t * g t + t * f t * deriv g t + t * deriv f t * g t) +
      (t ^ 2 * deriv f t * deriv g t - t ^ 3 * f t * g t) / 5)
      (z * deriv f z * deriv g z) z := by
  have hf₁ := (hf z).hasDerivAt
  have hg₁ := (hg z).hasDerivAt
  have hf₂ := hasDerivAt_deriv_of_airy_ode hf hf' z
  have hg₂ := hasDerivAt_deriv_of_airy_ode hg hg' z
  have h₁ := ((hf₁.neg.mul hg₁).add (((hasDerivAt_id z).mul hf₁).mul hg₂)).add
    (((hasDerivAt_id z).mul hf₂).mul hg₁)
  have h₂ := (((hasDerivAt_pow 2 z).mul hf₂).mul hg₂).sub (((hasDerivAt_pow 3 z).mul hf₁).mul hg₁)
  have h := (h₁.const_mul (3 / 10 : ℂ)).add (h₂.div_const 5)
  exact h.congr_deriv (by simp only [id, Pi.mul_apply, Pi.neg_apply]; ring)

/-- For entire solutions `f`, `g` of Airy's equation with nonzero Wronskian `𝒲 = f g' - f' g`, if
`f(z) ≠ 0` and `F` has derivative `F'` at `g(z) / f(z)`, then `F(g / f) / 𝒲` has derivative
`F' / f(z)²` at `z` (DLMF 9.11.11). -/
theorem hasDerivAt_comp_div_div_wronskian_of_airy_ode (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf' : ∀ z, deriv^[2] f z = z * f z)
    (hg' : ∀ z, deriv^[2] g z = z * g z) {F : ℂ → ℂ} {F' z : ℂ}
    (hF : HasDerivAt F F' (g z / f z)) (hfz : f z ≠ 0)
    (hW : f 0 * deriv g 0 - deriv f 0 * g 0 ≠ 0) :
    HasDerivAt (fun t => F (g t / f t) / (f 0 * deriv g 0 - deriv f 0 * g 0))
      (F' / f z ^ 2) z := by
  have h := (hF.comp z ((hg z).hasDerivAt.div (hf z).hasDerivAt hfz)).div_const
    (f 0 * deriv g 0 - deriv f 0 * g 0)
  have he : deriv g z * f z - g z * deriv f z = f 0 * deriv g 0 - deriv f 0 * g 0 := by
    linear_combination wronskian_eq_of_airy_ode hf hg hf' hg' z 0
  exact h.congr_deriv (by rw [he]; field_simp)

/-- Where `Ai(z) ≠ 0`, `π Bi/Ai` is an antiderivative of `1/Ai²` (DLMF 9.11.12). -/
theorem hasDerivAt_antiderivative_inv_airyAi_sq {z : ℂ} (hz : airyAi z ≠ 0) :
    HasDerivAt (fun t => π * airyBi t / airyAi t) (airyAi z ^ 2)⁻¹ z := by
  -- DLMF 9.11.11 with `F = id`, since `𝒲{Ai, Bi} = 1/π`.
  have h := hasDerivAt_comp_div_div_wronskian_of_airy_ode differentiable_airyAi
    differentiable_airyBi airyAi_ode airyBi_ode (hasDerivAt_id _) hz
    (by rw [wronskian_airyAi_airyBi]; simp)
  simp only [id, wronskian_airyAi_airyBi, one_div] at h
  exact h.congr_of_eventuallyEq (.of_eq (funext fun t => by field_simp))

/-- Where `Bi(z)/Ai(z)` lies in the slit plane, `π log(Bi/Ai)` is an antiderivative of
`1/(Ai Bi)` (DLMF 9.11.13). The slit-plane condition forces `Ai(z) ≠ 0` and `Bi(z) ≠ 0`. -/
theorem hasDerivAt_antiderivative_inv_airyAi_mul_airyBi {z : ℂ}
    (hz : airyBi z / airyAi z ∈ slitPlane) :
    HasDerivAt (fun t => π * log (airyBi t / airyAi t)) (airyAi z * airyBi z)⁻¹ z := by
  obtain ⟨-, ha⟩ := div_ne_zero_iff.mp (slitPlane_ne_zero hz)
  -- DLMF 9.11.11 with `F = log`, since `𝒲{Ai, Bi} = 1/π`.
  have h := hasDerivAt_comp_div_div_wronskian_of_airy_ode differentiable_airyAi
    differentiable_airyBi airyAi_ode airyBi_ode (hasDerivAt_log hz) ha
    (by rw [wronskian_airyAi_airyBi]; simp)
  simp only [wronskian_airyAi_airyBi] at h
  refine (h.congr_of_eventuallyEq (.of_eq (funext fun t => by
    rw [div_inv_eq_mul, mul_comm]))).congr_deriv ?_
  field_simp

/-- Where `Ai(z)² + Bi(z)² ≠ 0`, `(π/2) Bi²/(Ai² + Bi²)` is an antiderivative of
`Ai Bi/(Ai² + Bi²)²` (DLMF 9.11.14). -/
theorem hasDerivAt_antiderivative_airyAi_mul_airyBi_div_sq {z : ℂ}
    (hz : airyAi z ^ 2 + airyBi z ^ 2 ≠ 0) :
    HasDerivAt (fun t => π / 2 * airyBi t ^ 2 / (airyAi t ^ 2 + airyBi t ^ 2))
      (airyAi z * airyBi z / (airyAi z ^ 2 + airyBi z ^ 2) ^ 2) z := by
  have hA := (differentiable_airyAi z).hasDerivAt
  have hB := (differentiable_airyBi z).hasDerivAt
  have h := ((hB.pow 2).const_mul (π / 2 : ℂ)).div ((hA.pow 2).add (hB.pow 2)) hz
  simp only [Pi.pow_apply, Pi.add_apply] at h
  refine h.congr_deriv ?_
  have hW : (π : ℂ) * (airyAi z * deriv airyBi z - deriv airyAi z * airyBi z) = 1 := by
    rw [wronskian_airyAi_airyBi]
    exact mul_inv_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero)
  field_simp
  linear_combination 2 * airyAi z * airyBi z * hW

end TauCeti
