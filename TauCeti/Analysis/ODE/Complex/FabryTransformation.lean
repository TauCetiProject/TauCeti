/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Fabry's transformation

For the equation `w'' + f(z) w' + g(z) w = 0` in the complex domain, the substitution
`z = t²` together with the rescaling `W(t) = exp(c t² / 2) w(t²)` gives the equation
`W'' + F(t) W' + G(t) W = 0`, where

* `F(t) = 2t (f(t²) - c) - 1/t`  (`fabryFirstCoeff`), and
* `G(t) = 4t² (g(t²) - (c/2) f(t²) + c²/4)`  (`fabrySecondCoeff`).

This identity holds for every constant `c` and every `t ≠ 0` at which `w` is a holomorphic
solution near `t²` (`deriv_deriv_fabryTransform_add_eq_zero`).

Its use is at an irregular singularity of rank one at infinity. Suppose `f(z) = ∑ f_s z^{-s}` and
`g(z) = ∑ g_s z^{-s}` converge for `|z| > a`, and `c = f₀`. Then `F` and `G` are convergent
series in `t⁻¹` for `|t| > √a`. The series of `F` has only odd powers and starts at `t⁻¹`
(`hasSum_fabryFirstCoeff`), so `F₀ = 0`. In the degenerate case `f₀² = 4g₀`, in which the
characteristic equation `λ² + f₀λ + g₀ = 0` of the original equation has a double root, the
series of `G` has only even powers, with constant term `G₀ = 4g₁ - 2f₀f₁`
(`hasSum_fabrySecondCoeff`), so `G₁ = 0`. Hence either `G₀ ≠ 0`, and the characteristic equation
`λ² + G₀ = 0` of the new equation has two distinct roots; or `G₀ = 0`, and then `t² G(t)` is
again a convergent series in `t⁻¹` (`hasSum_sq_mul_fabrySecondCoeff`), so that, together with
`t F(t)`, infinity is a regular singularity of the new equation.

## References

* NIST Digital Library of Mathematical Functions, §2.7(ii), equation (2.7.19),
  <https://dlmf.nist.gov/2.7.ii>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 7, §1.
-/

public section

open Filter Topology

namespace TauCeti

/-- Fabry's rescaling `W(t) = exp(c t² / 2) w(t²)` of a function `w` of `z = t²`. -/
noncomputable def fabryTransform (c : ℂ) (w : ℂ → ℂ) (t : ℂ) : ℂ :=
  Complex.exp (c * t ^ 2 / 2) * w (t ^ 2)

@[simp]
theorem fabryTransform_apply (c : ℂ) (w : ℂ → ℂ) (t : ℂ) :
    fabryTransform c w t = Complex.exp (c * t ^ 2 / 2) * w (t ^ 2) := (rfl)

/-- The coefficient `F(t) = 2t (f(t²) - c) - 1/t` of `W'` in the equation satisfied by
`fabryTransform c w`. -/
noncomputable def fabryFirstCoeff (c : ℂ) (f : ℂ → ℂ) (t : ℂ) : ℂ :=
  2 * t * (f (t ^ 2) - c) - t⁻¹

@[simp]
theorem fabryFirstCoeff_apply (c : ℂ) (f : ℂ → ℂ) (t : ℂ) :
    fabryFirstCoeff c f t = 2 * t * (f (t ^ 2) - c) - t⁻¹ := (rfl)

/-- The coefficient `G(t) = 4t² (g(t²) - (c/2) f(t²) + c²/4)` of `W` in the equation satisfied
by `fabryTransform c w`. -/
noncomputable def fabrySecondCoeff (c : ℂ) (f g : ℂ → ℂ) (t : ℂ) : ℂ :=
  4 * t ^ 2 * (g (t ^ 2) - c / 2 * f (t ^ 2) + c ^ 2 / 4)

@[simp]
theorem fabrySecondCoeff_apply (c : ℂ) (f g : ℂ → ℂ) (t : ℂ) :
    fabrySecondCoeff c f g t = 4 * t ^ 2 * (g (t ^ 2) - c / 2 * f (t ^ 2) + c ^ 2 / 4) := (rfl)

private theorem hasDerivAt_mul_sq_div_two (c t : ℂ) :
    HasDerivAt (fun s : ℂ => c * s ^ 2 / 2) (c * t) t := by
  convert ((hasDerivAt_pow 2 t).const_mul c).div_const 2 using 1
  ring

private theorem hasDerivAt_sq (t : ℂ) : HasDerivAt (fun s : ℂ => s ^ 2) (2 * t) t := by
  simpa using hasDerivAt_pow 2 t

/-- The first derivative of Fabry's rescaling. -/
theorem hasDerivAt_fabryTransform (c : ℂ) {w : ℂ → ℂ} {t : ℂ}
    (hw : DifferentiableAt ℂ w (t ^ 2)) :
    HasDerivAt (fabryTransform c w)
      (Complex.exp (c * t ^ 2 / 2) * (c * t * w (t ^ 2) + 2 * t * deriv w (t ^ 2))) t := by
  have h := (hasDerivAt_mul_sq_div_two c t).cexp.mul
    (hw.hasDerivAt.comp (h := fun s : ℂ => s ^ 2) t (hasDerivAt_sq t))
  exact h.congr_deriv (by simp only [Function.comp_apply]; ring)

/-- The second derivative of Fabry's rescaling of a function holomorphic near `t²`. -/
theorem deriv_deriv_fabryTransform (c : ℂ) {w : ℂ → ℂ} {t : ℂ}
    (hw : AnalyticAt ℂ w (t ^ 2)) :
    deriv (deriv (fabryTransform c w)) t =
      Complex.exp (c * t ^ 2 / 2) * ((c + c ^ 2 * t ^ 2) * w (t ^ 2) +
        (2 + 4 * c * t ^ 2) * deriv w (t ^ 2) + 4 * t ^ 2 * deriv (deriv w) (t ^ 2)) := by
  have heq : deriv (fabryTransform c w) =ᶠ[𝓝 t] fun s =>
      Complex.exp (c * s ^ 2 / 2) * (c * s * w (s ^ 2) + 2 * s * deriv w (s ^ 2)) := by
    filter_upwards [((continuous_pow 2).tendsto t).eventually hw.eventually_analyticAt]
      with s hs
    exact (hasDerivAt_fabryTransform c hs.differentiableAt).deriv
  have hsq := hasDerivAt_sq t
  have hw₀ := hw.differentiableAt.hasDerivAt.comp (h := fun s : ℂ => s ^ 2) t hsq
  have hw₁ := hw.deriv.differentiableAt.hasDerivAt.comp (h := fun s : ℂ => s ^ 2) t hsq
  have h := (hasDerivAt_mul_sq_div_two c t).cexp.mul
    (((hasDerivAt_id t).const_mul c).mul hw₀ |>.add (((hasDerivAt_id t).const_mul 2).mul hw₁))
  have h' : HasDerivAt (fun s =>
      Complex.exp (c * s ^ 2 / 2) * (c * s * w (s ^ 2) + 2 * s * deriv w (s ^ 2))) _ t := h
  rw [heq.deriv_eq, h'.deriv]
  simp only [Pi.mul_apply, Pi.add_apply, Function.comp_apply, id]
  ring

/-- **Fabry's transformation** (DLMF 2.7.19). If `w` is holomorphic near `t² ≠ 0` and solves
`w'' + f w' + g w = 0` at `t²`, then `W = fabryTransform c w` solves
`W'' + F W' + G W = 0` at `t`, with `F = fabryFirstCoeff c f` and `G = fabrySecondCoeff c f g`.
This holds for every constant `c`; DLMF takes `c = f₀`. -/
theorem deriv_deriv_fabryTransform_add_eq_zero (c : ℂ) {f g w : ℂ → ℂ} {t : ℂ} (ht : t ≠ 0)
    (hw : AnalyticAt ℂ w (t ^ 2))
    (heq : deriv (deriv w) (t ^ 2) + f (t ^ 2) * deriv w (t ^ 2) + g (t ^ 2) * w (t ^ 2) = 0) :
    deriv (deriv (fabryTransform c w)) t +
        fabryFirstCoeff c f t * deriv (fabryTransform c w) t +
        fabrySecondCoeff c f g t * fabryTransform c w t = 0 := by
  rw [deriv_deriv_fabryTransform c hw, (hasDerivAt_fabryTransform c hw.differentiableAt).deriv,
    fabryFirstCoeff_apply, fabrySecondCoeff_apply, fabryTransform_apply]
  have ht' : t⁻¹ * t = 1 := inv_mul_cancel₀ ht
  linear_combination (Complex.exp (c * t ^ 2 / 2) * 4 * t ^ 2) * heq -
    (Complex.exp (c * t ^ 2 / 2) * (c * w (t ^ 2) + 2 * deriv w (t ^ 2))) * ht'

/-- Fabry's transformation on a neighbourhood of infinity: a holomorphic solution of
`w'' + f w' + g w = 0` on `|z| > a` (with `0 ≤ a`) is carried to a solution of
`W'' + F W' + G W = 0` on `|t| > √a`. -/
theorem deriv_deriv_fabryTransform_add_eq_zero_of_differentiableOn (c : ℂ) {f g w : ℂ → ℂ}
    {a : ℝ} (ha : 0 ≤ a) (hw : DifferentiableOn ℂ w {z | a < ‖z‖})
    (heq : ∀ z, a < ‖z‖ → deriv (deriv w) z + f z * deriv w z + g z * w z = 0)
    {t : ℂ} (ht : a < ‖t‖ ^ 2) :
    deriv (deriv (fabryTransform c w)) t +
        fabryFirstCoeff c f t * deriv (fabryTransform c w) t +
        fabrySecondCoeff c f g t * fabryTransform c w t = 0 := by
  have ht₂ : a < ‖t ^ 2‖ := by rwa [norm_pow]
  have ht₀ : t ≠ 0 := by
    rintro rfl
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at ht
    linarith
  refine deriv_deriv_fabryTransform_add_eq_zero c ht₀ ?_ (heq _ ht₂)
  exact hw.analyticAt ((isOpen_lt continuous_const continuous_norm).mem_nhds ht₂)

/-- If `f(t²) = ∑ f_s t^{-2s}`, then `F(t) = 2t (f(t²) - f₀) - 1/t` is the series
`∑ (2 f_{s+1} - δ_{s0}) t^{-(2s+1)}` in odd powers of `t⁻¹`. In particular its constant
term vanishes. -/
theorem hasSum_fabryFirstCoeff {f : ℂ → ℂ} {fc : ℕ → ℂ} {t : ℂ}
    (hf : HasSum (fun s => fc s / (t ^ 2) ^ s) (f (t ^ 2))) :
    HasSum (fun s => (2 * fc (s + 1) - if s = 0 then 1 else 0) / t ^ (2 * s + 1))
      (fabryFirstCoeff (fc 0) f t) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have h₁ := ((hasSum_nat_add_iff' 1).2 hf).mul_left (2 * t)
  have h₂ := hasSum_ite_eq (0 : ℕ) t⁻¹
  convert h₁.sub h₂ using 1
  · funext s
    rcases eq_or_ne s 0 with rfl | hs
    · simp only [ite_true, pow_one, mul_zero, zero_add]
      field_simp
    · simp only [hs, ite_false, sub_zero]
      field_simp
      ring
  · simp [fabryFirstCoeff_apply]

/-- If `f(t²) = ∑ f_s t^{-2s}`, `g(t²) = ∑ g_s t^{-2s}` and `f₀² = 4g₀`, then
`G(t) = 4t² (g(t²) - (f₀/2) f(t²) + f₀²/4)` is the series `∑ (4 g_{s+1} - 2 f₀ f_{s+1}) t^{-2s}`
in even powers of `t⁻¹`. Its constant term is `4g₁ - 2f₀f₁`. -/
theorem hasSum_fabrySecondCoeff {f g : ℂ → ℂ} {fc gc : ℕ → ℂ} {t : ℂ} (ht : t ≠ 0)
    (hf : HasSum (fun s => fc s / (t ^ 2) ^ s) (f (t ^ 2)))
    (hg : HasSum (fun s => gc s / (t ^ 2) ^ s) (g (t ^ 2)))
    (hfg : fc 0 ^ 2 = 4 * gc 0) :
    HasSum (fun s => (4 * gc (s + 1) - 2 * fc 0 * fc (s + 1)) / t ^ (2 * s))
      (fabrySecondCoeff (fc 0) f g t) := by
  have h := (((hasSum_nat_add_iff' 1).2 hg).sub
    (((hasSum_nat_add_iff' 1).2 hf).mul_left (fc 0 / 2))).mul_left (4 * t ^ 2)
  convert h using 1
  · funext s
    field_simp
    ring
  · simp only [fabrySecondCoeff_apply, Finset.range_one, Finset.sum_singleton, pow_zero, div_one]
    linear_combination (-t ^ 2) * hfg

/-- In the case `G₀ = 4g₁ - 2f₀f₁ = 0` of `hasSum_fabrySecondCoeff`, `t² G(t)` is the series
`∑ (4 g_{s+2} - 2 f₀ f_{s+2}) t^{-2s}`. Together with `hasSum_fabryFirstCoeff`, which makes
`t F(t)` a series in `t⁻¹`, this says that infinity is a regular singularity of the transformed
equation. -/
theorem hasSum_sq_mul_fabrySecondCoeff {f g : ℂ → ℂ} {fc gc : ℕ → ℂ} {t : ℂ} (ht : t ≠ 0)
    (hf : HasSum (fun s => fc s / (t ^ 2) ^ s) (f (t ^ 2)))
    (hg : HasSum (fun s => gc s / (t ^ 2) ^ s) (g (t ^ 2)))
    (hfg : fc 0 ^ 2 = 4 * gc 0) (hfg₁ : 4 * gc 1 = 2 * fc 0 * fc 1) :
    HasSum (fun s => (4 * gc (s + 2) - 2 * fc 0 * fc (s + 2)) / t ^ (2 * s))
      (t ^ 2 * fabrySecondCoeff (fc 0) f g t) := by
  have h := ((hasSum_nat_add_iff' 1).2 (hasSum_fabrySecondCoeff ht hf hg hfg)).mul_left (t ^ 2)
  convert h using 1
  · funext s
    field_simp
    ring
  · simp [hfg₁]

end TauCeti
