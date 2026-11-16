/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# Functions on the line with derivative bounded below

A differentiable function `f : ℝ → ℝ` whose derivative is at least `λ > 0` everywhere grows at
least at the rate `λ`: `λ (y - x) ≤ f y - f x` for `x ≤ y`, by the mean value theorem
(`mul_sub_le_image_sub_of_le_deriv`). Hence `f` is `λ⁻¹`-antilipschitz
(`Differentiable.antilipschitzWith_of_le_deriv`) and tends to `±∞` at `±∞`, so it is a bijection
of `ℝ` (`Differentiable.surjective_of_le_deriv`) whose inverse is `λ⁻¹`-Lipschitz
(`Differentiable.exists_lipschitzWith_inverse_of_le_deriv`). Such functions arise as primitives of
coefficients bounded below, for instance in Kirchhoff's transformation of a quasilinear equation.
-/

public section

open Filter

namespace Differentiable

variable {f : ℝ → ℝ} {lam : ℝ}

/-- A differentiable function on `ℝ` whose derivative is at least `λ > 0` is antilipschitz with
constant `λ⁻¹`. -/
theorem antilipschitzWith_of_le_deriv (hf : Differentiable ℝ f) (hlam : 0 < lam)
    (hf' : ∀ x, lam ≤ deriv f x) : AntilipschitzWith (Real.toNNReal lam⁻¹) f :=
  AntilipschitzWith.of_le_mul_dist fun x y ↦ by
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.2 hlam.le),
      le_inv_mul_iff₀ hlam]
    rcases le_total x y with h | h
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h), abs_sub_comm]
      exact (mul_sub_le_image_sub_of_le_deriv hf hf' h).trans (le_abs_self _)
    · rw [abs_of_nonneg (sub_nonneg.2 h)]
      exact (mul_sub_le_image_sub_of_le_deriv hf hf' h).trans (le_abs_self _)

/-- A differentiable function on `ℝ` whose derivative is at least `λ > 0` is surjective: it tends
to `+∞` at `+∞` and to `-∞` at `-∞`. -/
theorem surjective_of_le_deriv (hf : Differentiable ℝ f) (hlam : 0 < lam)
    (hf' : ∀ x, lam ≤ deriv f x) : Function.Surjective f := by
  -- `f x - f 0` lies above `λ x` for `x ≥ 0` and below it for `x ≤ 0`.
  have htop : Tendsto (fun x ↦ f x - f 0) atTop atTop :=
    tendsto_atTop_mono' _ (by
      filter_upwards [eventually_ge_atTop 0] with x hx
      simpa using mul_sub_le_image_sub_of_le_deriv hf hf' hx)
      (tendsto_id.const_mul_atTop hlam)
  have hbot : Tendsto (fun x ↦ f x - f 0) atBot atBot :=
    tendsto_atBot_mono' _ (by
      filter_upwards [eventually_le_atBot 0] with x hx
      have := mul_sub_le_image_sub_of_le_deriv hf hf' hx
      simp only [id]
      linarith)
      (tendsto_id.const_mul_atBot hlam)
  exact hf.continuous.surjective (by simpa using htop.atTop_add (tendsto_const_nhds (x := f 0)))
    (by simpa using hbot.atBot_add (tendsto_const_nhds (x := f 0)))

/-- A differentiable function on `ℝ` whose derivative is at least `λ > 0` is a bijection of `ℝ`
with a `λ⁻¹`-Lipschitz two-sided inverse. -/
theorem exists_lipschitzWith_inverse_of_le_deriv (hf : Differentiable ℝ f) (hlam : 0 < lam)
    (hf' : ∀ x, lam ≤ deriv f x) :
    ∃ g : ℝ → ℝ, Function.RightInverse g f ∧ Function.LeftInverse g f ∧
      LipschitzWith (Real.toNNReal lam⁻¹) g := by
  have hanti := hf.antilipschitzWith_of_le_deriv hlam hf'
  have hsurj := hf.surjective_of_le_deriv hlam hf'
  exact ⟨Function.surjInv hsurj, Function.surjInv_eq hsurj,
    fun x ↦ hanti.injective (Function.surjInv_eq hsurj _),
    hanti.to_rightInverse (Function.surjInv_eq hsurj)⟩

end Differentiable
