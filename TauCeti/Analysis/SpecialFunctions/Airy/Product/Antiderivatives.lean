/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.ODE.Wronskian

/-!
# Antiderivatives of products of solutions of Airy's equation

Let `f` and `g` be entire solutions of Airy's equation `w'' = z w`, and let
`𝒲 = f g' - f' g` be their Wronskian, which is constant. Then closed-form antiderivatives exist
for the products `f g`, `f g'`, `f' g'`, `z f g`, `z f g'` and `z f' g'` (DLMF 9.11.5–9.11.10).
For the quotient `g / f` there is a substitution formula (DLMF 9.11.11): if `𝒲 ≠ 0`, `f(z) ≠ 0`
and `F` has derivative `F'` at `g(z) / f(z)`, then `F(g / f) / 𝒲` has derivative `F' / f(z)²` at
`z`. In the statements the Wronskian is written out at the origin as
`f 0 * deriv g 0 - deriv f 0 * g 0`; its constancy is `TauCeti.wronskian_eq_of_hasDerivAt`.

## Main results

* `TauCeti.hasDerivAt_deriv_of_airy_ode`: the derivative of an entire solution `w` has
  derivative `z w(z)`;
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
  (DLMF 9.11.11).

## References

* NIST Digital Library of Mathematical Functions, §9.11(iv), <https://dlmf.nist.gov/9.11.iv>.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/Airy/Products.lean`.
-/

public section

namespace TauCeti

variable {f g : ℂ → ℂ}

/-- For an entire solution `w` of Airy's equation, `w'` has derivative `z w(z)` at `z`. -/
theorem hasDerivAt_deriv_of_airy_ode {w : ℂ → ℂ} (hw : Differentiable ℂ w)
    (hw' : ∀ z, deriv^[2] w z = z * w z) (z : ℂ) : HasDerivAt (deriv w) (z * w z) z := by
  rw [← hw' z, Function.iterate_succ_apply, Function.iterate_one]
  exact (hw.deriv z).hasDerivAt

/-- The Wronskian of two entire solutions of Airy's equation equals its value at the origin. -/
private theorem wronskian_eq_wronskian_zero_of_airy_ode (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (hf' : ∀ z, deriv^[2] f z = z * f z)
    (hg' : ∀ z, deriv^[2] g z = z * g z) (z : ℂ) :
    f z * deriv g z - deriv f z * g z = f 0 * deriv g 0 - deriv f 0 * g 0 := by
  have h := wronskian_eq_of_hasDerivAt (q := fun t => t) (fun t => (hg t).hasDerivAt)
    (hasDerivAt_deriv_of_airy_ode hg hg') (fun t => (hf t).hasDerivAt)
    (hasDerivAt_deriv_of_airy_ode hf hf') z 0
  linear_combination h

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
  have hW := wronskian_eq_wronskian_zero_of_airy_ode hf hg hf' hg' z
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
  have hW := wronskian_eq_wronskian_zero_of_airy_ode hf hg hf' hg' z
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
    linear_combination wronskian_eq_wronskian_zero_of_airy_ode hf hg hf' hg' z
  exact h.congr_deriv (by rw [he]; field_simp)

end TauCeti
