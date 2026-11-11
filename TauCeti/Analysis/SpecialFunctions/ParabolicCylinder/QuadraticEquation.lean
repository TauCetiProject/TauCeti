/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The general quadratic equation reduces to Weber's equation (DLMF 12.2.1)

The equation `w″ + (αz² + βz + γ) w = 0` with `α ≠ 0` (DLMF 12.2.1) reduces to Weber's equation
`w″ − (z²/4 + a) w = 0` (DLMF 12.2.2) by an affine change of variable: if `s⁴ = −4α` and `f`
solves Weber's equation with parameter `a = (β²/(4α) − γ)/s²`, then `z ↦ f(s (z + β/(2α)))` solves
12.2.1 (DLMF §12.2(i)).

## Main results

* `TauCeti.quadratic_equation_of_weber`: the reduction of DLMF 12.2.1 to DLMF 12.2.2.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §12.2(i),
  <https://dlmf.nist.gov/12.2.i>.

The proof is adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/ParabolicCylinder/ElementaryProperties.lean`.
-/

@[expose] public section

namespace TauCeti

/-- **DLMF 12.2.1 from Weber's equation**: for `α ≠ 0` and `s⁴ = −4α`, if the entire function `f`
solves `f″(z) = (z²/4 + (β²/(4α) − γ)/s²) f(z)` (DLMF 12.2.2), then `z ↦ f(s (z + β/(2α)))`
solves `w″ + (αz² + βz + γ) w = 0`. -/
theorem quadratic_equation_of_weber {α β γ s : ℂ} (hα : α ≠ 0) (hs : s ^ 4 = -4 * α)
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hode : ∀ z, deriv^[2] f z = (z ^ 2 / 4 + (β ^ 2 / (4 * α) - γ) / s ^ 2) * f z) (z : ℂ) :
    deriv^[2] (fun z => f (s * (z + β / (2 * α)))) z +
      (α * z ^ 2 + β * z + γ) * f (s * (z + β / (2 * α))) = 0 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hα (by linear_combination hs / 4)
  set t := β / (2 * α) with ht
  clear_value t
  have hin (w : ℂ) : HasDerivAt (fun z : ℂ => s * (z + t)) s w := by
    simpa using ((hasDerivAt_id w).add_const t).const_mul s
  have d1 : deriv (fun z => f (s * (z + t))) = fun z => deriv f (s * (z + t)) * s := by
    funext w
    exact ((hf _).hasDerivAt.comp w (hin w)).deriv
  have d2 : deriv (fun z => deriv f (s * (z + t)) * s) z =
      deriv (deriv f) (s * (z + t)) * s * s :=
    ((hf.deriv _).hasDerivAt.comp z (hin z)).mul_const s |>.deriv
  have h := hode (s * (z + t))
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq] at h ⊢
  rw [d1, d2, h]
  have hβ : β = 2 * α * t := by rw [ht]; field_simp
  have hq : (β ^ 2 / (4 * α) - γ) / s ^ 2 * s * s = α * t ^ 2 - γ := by
    rw [hβ]
    field_simp
    ring
  linear_combination (z + t) ^ 2 * f (s * (z + t)) / 4 * hs + f (s * (z + t)) * hq +
    z * f (s * (z + t)) * hβ

end TauCeti
