/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.QPochhammer
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import TauCeti.Algebra.Ring.Periodic
import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair
import TauCeti.NumberTheory.ModularForms.DedekindEta

/-!
# The inversion law of the theta product

For `τ` in the upper half-plane write `q = e^{2π i τ}` and consider the theta product
`θ_τ(z) = θ_q(e^{2π i z}) = (1 - e^{2π i z}) ∏_{n ≥ 1} (1 - qⁿ e^{2π i z}) (1 - qⁿ e^{-2π i z})`
(`TauCeti.qTheta`) as a function of `z ∈ ℂ`. Up to an exponential factor and the Euler product
`∏_{n ≥ 1} (1 - qⁿ)` it is Jacobi's odd theta function `θ₁`. This file proves its transformation
under `τ ↦ -1/τ` (Jacobi's imaginary transformation), with the exact constant:

  `θ_{-1/τ}(z/τ) = -i e^{π i ((z² + z + 1/6)/τ + τ/6 - z)} θ_τ(z)`.

This is the analytic input for the transformation of Siegel functions under `S = [[0, -1], [1, 0]]`.

The proof compares the two sides as entire functions of `z`. Both vanish exactly on the lattice
`ℤ τ + ℤ`, to first order, and both are multiplied by `-e^{2π i (z + 1)/τ}` under `z ↦ z + 1` and
are invariant under `z ↦ z + τ`. Their quotient therefore extends to an entire doubly periodic
function, which is bounded and hence constant by Liouville's theorem. The constant is the ratio of
the derivatives at `z = 0`, which are `-2π i` times squares of Euler products; these are values of
the Dedekind eta function, and the transformation `η(-1/τ)² = -i τ η(τ)²` evaluates it.

## Main results

* `TauCeti.qTheta_exp_neg_one_div`: the inversion law above.

## References

* D. Mumford, *Tata Lectures on Theta I*, Progress in Mathematics 28, Birkhäuser, 1983, Chapter I,
  §§7 and 14 (the product formula for `θ₁` and its transformation under `τ ↦ -1/τ`).
* E. T. Whittaker, G. N. Watson, *A Course of Modern Analysis*, §21.51 (Jacobi's imaginary
  transformation, by comparing zeros and quasi-periods).
-/

public section

open Complex Filter Topology
open scoped Real ModularForm

namespace TauCeti

section Inversion

variable {τ : ℂ}

/-! ### The two sides of the inversion law as functions of `z` -/

/-- The left-hand side `θ_{-1/τ}(z/τ)` of the inversion law. -/
private noncomputable def thetaInv (τ z : ℂ) : ℂ :=
  qTheta (cexp (2 * π * I * (-1 / τ))) (cexp (2 * π * I * (z / τ)))

/-- The right-hand side of the inversion law without its constant:
`e^{π i (z²/τ + z/τ - z)} θ_τ(z)`. -/
private noncomputable def thetaExp (τ z : ℂ) : ℂ :=
  cexp (π * I * (z ^ 2 / τ + z / τ - z)) * qTheta (cexp (2 * π * I * τ)) (cexp (2 * π * I * z))

private theorem norm_exp_two_pi_I_mul_lt_one (hτ : 0 < τ.im) : ‖cexp (2 * π * I * τ)‖ < 1 :=
  UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩

private theorem norm_exp_two_pi_I_neg_one_div_lt_one (hτ : 0 < τ.im) :
    ‖cexp (2 * π * I * (-1 / τ))‖ < 1 :=
  UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨-1 / τ, by
    simpa [neg_div, inv_neg] using UpperHalfPlane.im_inv_neg_coe_pos ⟨τ, hτ⟩⟩

private theorem differentiable_thetaInv (hτ : 0 < τ.im) : Differentiable ℂ (thetaInv τ) :=
  (differentiable_qTheta_exp (norm_exp_two_pi_I_neg_one_div_lt_one hτ)).comp
    (differentiable_id.div_const τ)

private theorem differentiable_thetaExp (hτ : 0 < τ.im) : Differentiable ℂ (thetaExp τ) :=
  (by fun_prop : Differentiable ℂ fun z : ℂ ↦ cexp (π * I * (z ^ 2 / τ + z / τ - z))).mul
    (differentiable_qTheta_exp (norm_exp_two_pi_I_mul_lt_one hτ))

private theorem thetaInv_add_self (hτ : 0 < τ.im) (z : ℂ) : thetaInv τ (z + τ) = thetaInv τ z := by
  have hτ₀ : τ ≠ 0 := fun h ↦ by simp [h] at hτ
  have h : cexp (2 * π * I * ((z + τ) / τ)) = cexp (2 * π * I * (z / τ)) := by
    rw [add_div, div_self hτ₀, mul_add, mul_one, Complex.exp_add, exp_two_pi_mul_I, mul_one]
  rw [thetaInv, thetaInv, h]

/-- Under `z ↦ z + 1` both sides are multiplied by `-e^{2π i (z + 1)/τ}`; this is the
quasi-periodicity of `θ_{-1/τ}` under translation by `-1/τ`. -/
private theorem thetaInv_add_one (hτ : 0 < τ.im) (z : ℂ) :
    thetaInv τ (z + 1) = -cexp (2 * π * I * ((z + 1) / τ)) * thetaInv τ z := by
  have hτ₀ : τ ≠ 0 := fun h ↦ by simp [h] at hτ
  have h := qTheta_mul_left (norm_exp_two_pi_I_neg_one_div_lt_one hτ) (exp_ne_zero _)
    (exp_ne_zero (2 * π * I * ((z + 1) / τ)))
  rw [← Complex.exp_add, show 2 * π * I * (-1 / τ) + 2 * π * I * ((z + 1) / τ) =
    2 * π * I * (z / τ) by field_simp; ring] at h
  rw [thetaInv, thetaInv, h, ← Complex.exp_neg]
  have h₁ : cexp (2 * π * I * ((z + 1) / τ)) * cexp (-(2 * π * I * ((z + 1) / τ))) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  linear_combination
    -qTheta (cexp (2 * π * I * (-1 / τ))) (cexp (2 * π * I * ((z + 1) / τ))) * h₁

private theorem thetaExp_add_self (hτ : 0 < τ.im) (z : ℂ) : thetaExp τ (z + τ) = thetaExp τ z := by
  have hτ₀ : τ ≠ 0 := fun h ↦ by simp [h] at hτ
  have h := qTheta_mul_left (norm_exp_two_pi_I_mul_lt_one hτ) (exp_ne_zero _)
    (exp_ne_zero (2 * π * I * z))
  rw [← Complex.exp_add, ← mul_add, add_comm τ z] at h
  have he : cexp (π * I * ((z + τ) ^ 2 / τ + (z + τ) / τ - (z + τ))) * (cexp (2 * π * I * z))⁻¹ =
      -cexp (π * I * (z ^ 2 / τ + z / τ - z)) := by
    rw [← Complex.exp_neg, ← Complex.exp_add,
      show π * I * ((z + τ) ^ 2 / τ + (z + τ) / τ - (z + τ)) + -(2 * π * I * z) =
        π * I + π * I * (z ^ 2 / τ + z / τ - z) by field_simp; ring,
      Complex.exp_add, exp_pi_mul_I, neg_one_mul]
  rw [thetaExp, thetaExp, h]
  linear_combination -qTheta (cexp (2 * π * I * τ)) (cexp (2 * π * I * z)) * he

private theorem thetaExp_add_one (hτ : 0 < τ.im) (z : ℂ) :
    thetaExp τ (z + 1) = -cexp (2 * π * I * ((z + 1) / τ)) * thetaExp τ z := by
  have hτ₀ : τ ≠ 0 := fun h ↦ by simp [h] at hτ
  have hq : cexp (2 * π * I * (z + 1)) = cexp (2 * π * I * z) := by
    rw [mul_add, mul_one, Complex.exp_add, exp_two_pi_mul_I, mul_one]
  have he : cexp (π * I * ((z + 1) ^ 2 / τ + (z + 1) / τ - (z + 1))) =
      -cexp (2 * π * I * ((z + 1) / τ)) * cexp (π * I * (z ^ 2 / τ + z / τ - z)) := by
    rw [← neg_one_mul, ← Complex.exp_neg_pi_mul_I, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    field_simp
    ring
  rw [thetaExp, thetaExp, hq, he, mul_assoc]

/-- Away from the lattice `ℤ τ + ℤ` the right-hand side does not vanish. -/
private theorem thetaExp_ne_zero (hτ : 0 < τ.im) {z : ℂ}
    (hz : z ∉ (UpperHalfPlane.periodPair ⟨τ, hτ⟩).lattice) : thetaExp τ z ≠ 0 := by
  refine mul_ne_zero (exp_ne_zero _) (qTheta_ne_zero (norm_exp_two_pi_I_mul_lt_one hτ)
    fun k hk ↦ hz ?_)
  rw [← Complex.exp_int_mul, ← mul_assoc, mul_comm (k : ℂ), mul_assoc] at hk
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hk
  refine PeriodPair.mem_lattice.mpr ⟨k, n, ?_⟩
  have h2 : 2 * π * I ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  apply mul_left_cancel₀ h2
  simp only [UpperHalfPlane.periodPair_ω₁, UpperHalfPlane.periodPair_ω₂, mul_one]
  linear_combination -hn

/-! ### The constant -/

/-- The Euler product `∏_{n ≥ 1} (1 - qⁿ)` is `e^{-2π i τ / 24} η(τ)`. -/
private theorem tprod_one_sub_pow_eq_exp_mul_eta (τ : ℂ) :
    ∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1)) = cexp (-(2 * π * I * τ / 24)) * η τ := by
  rw [ModularForm.eta_eq_exp_mul_tprod, ← mul_assoc, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, one_mul]

/-- The derivatives at `z = 0` of the two sides are in the ratio
`-i e^{π i (1/(6τ) + τ/6)}`. -/
private theorem hasDerivAt_thetaInv_zero (hτ : 0 < τ.im) :
    HasDerivAt (thetaInv τ) (-I * cexp (π * I * (1 / 6 / τ + τ / 6)) *
      (-(2 * π * I) * (∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1))) ^ 2)) 0 := by
  have hτ₀ : τ ≠ 0 := fun h ↦ by simp [h] at hτ
  have h := (hasDerivAt_qTheta_exp_zero (norm_exp_two_pi_I_neg_one_div_lt_one hτ)).comp_of_eq
    (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).div_const τ) (by simp)
  convert h using 1
  · funext z
    simp [thetaInv]
  rw [tprod_one_sub_pow_eq_exp_mul_eta, tprod_one_sub_pow_eq_exp_mul_eta, mul_pow, mul_pow,
    ModularForm.eta_neg_one_div_sq hτ, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have he : cexp (π * I * (1 / 6 / τ + τ / 6)) * cexp (((2 : ℕ) : ℂ) * -(2 * π * I * τ / 24)) =
      cexp (((2 : ℕ) : ℂ) * -(2 * π * I * (-1 / τ) / 24)) := by
    rw [← Complex.exp_add]
    congr 1
    field_simp
    push_cast
    ring
  rw [← he]
  field_simp

private theorem hasDerivAt_thetaExp_zero (hτ : 0 < τ.im) :
    HasDerivAt (thetaExp τ)
      (-(2 * π * I) * (∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1))) ^ 2) 0 := by
  have h := ((by fun_prop : Differentiable ℂ fun z : ℂ ↦
    cexp (π * I * (z ^ 2 / τ + z / τ - z))) 0).hasDerivAt.mul
    (hasDerivAt_qTheta_exp_zero (norm_exp_two_pi_I_mul_lt_one hτ))
  convert h using 1
  · funext z
    simp [thetaExp]
  · simp

/-! ### Liouville's theorem -/

/-- **The inversion law of the theta product**, as an equality of entire functions. -/
private theorem thetaInv_eq (hτ : 0 < τ.im) (z : ℂ) :
    thetaInv τ z = -I * cexp (π * I * (1 / 6 / τ + τ / 6)) * thetaExp τ z := by
  classical
  obtain ⟨L, hL⟩ : ∃ L, L = UpperHalfPlane.periodPair ⟨τ, hτ⟩ := ⟨_, rfl⟩
  have hω₁ : L.ω₁ = τ := by rw [hL, UpperHalfPlane.periodPair_ω₁, UpperHalfPlane.coe_mk]
  have hω₂ : L.ω₂ = 1 := by rw [hL, UpperHalfPlane.periodPair_ω₂]
  have hne {y : ℂ} (hy : y ∉ L.lattice) : thetaExp τ y ≠ 0 := thetaExp_ne_zero hτ (hL ▸ hy)
  set c := -I * cexp (π * I * (1 / 6 / τ + τ / 6))
  set b := -(2 * π * I) * (∏' n : ℕ, (1 - cexp (2 * π * I * τ) ^ (n + 1))) ^ 2
  have hb : b ≠ 0 := mul_ne_zero (by simp [Real.pi_ne_zero, I_ne_zero])
    (pow_ne_zero _ (tprod_one_sub_pow_ne_zero (norm_exp_two_pi_I_mul_lt_one hτ)))
  have hA := differentiable_thetaInv hτ
  have hB := differentiable_thetaExp hτ
  have hA₀ : thetaInv τ 0 = 0 := by simp [thetaInv]
  have hB₀ : thetaExp τ 0 = 0 := by simp [thetaExp]
  -- The quotient, extended by `c` on the lattice.
  let H : ℂ → ℂ := fun z ↦ if z ∈ L.lattice then c else thetaInv τ z / thetaExp τ z
  have hper (w : ℂ) (hw : w ∈ L.lattice) (hmul : ∀ z, ∃ m ≠ 0,
      thetaInv τ (z + w) = m * thetaInv τ z ∧ thetaExp τ (z + w) = m * thetaExp τ z) :
      Function.Periodic H w := fun z ↦ by
    obtain ⟨m, hm, hA', hB'⟩ := hmul z
    simp only [H, L.lattice.add_mem_iff_left hw, hA', hB', mul_div_mul_left _ _ hm]
  have hper₁ : Function.Periodic H 1 := hper 1 (hω₂ ▸ L.ω₂_mem_lattice) fun z ↦
    ⟨_, neg_ne_zero.mpr (exp_ne_zero _), thetaInv_add_one hτ z, thetaExp_add_one hτ z⟩
  have hperτ : Function.Periodic H τ := hper τ (hω₁ ▸ L.ω₁_mem_lattice) fun z ↦
    ⟨1, one_ne_zero, by rw [one_mul, thetaInv_add_self hτ], by rw [one_mul, thetaExp_add_self hτ]⟩
  have hperL (w : ℂ) (hw : w ∈ L.lattice) : Function.Periodic H w := by
    obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hw
    rw [hω₁, hω₂]
    exact hperτ.int_mul_add_int_mul hper₁ m n
  -- Near `0`, `H` is the quotient of the difference quotients of the two sides at `0`.
  have hH₀ : DifferentiableAt ℂ H 0 := by
    have hd (f : ℂ → ℂ) (hf : Differentiable ℂ f) : Differentiable ℂ (dslope f 0) := fun x ↦
      (((differentiableOn_dslope univ_mem).mpr hf.differentiableOn) x
        trivial).differentiableAt univ_mem
    have hBd : dslope (thetaExp τ) 0 0 ≠ 0 := by
      rwa [dslope_same, (hasDerivAt_thetaExp_zero hτ).deriv]
    refine (((hd _ hA) 0).div ((hd _ hB) 0) hBd).congr_of_eventuallyEq ?_
    filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with x hx
    by_cases hx₀ : x = 0
    · subst hx₀
      simp only [H, L.lattice.zero_mem, ite_true, Pi.div_apply, dslope_same,
        (hasDerivAt_thetaExp_zero hτ).deriv, (hasDerivAt_thetaInv_zero hτ).deriv]
      exact (mul_div_cancel_right₀ c hb).symm
    · have hxL : x ∉ L.lattice := fun h ↦ hx ⟨h, hx₀⟩
      simp only [H, hxL, ite_false]
      rw [Pi.div_apply, dslope_of_ne _ hx₀, dslope_of_ne _ hx₀, slope_def_field, slope_def_field,
        hA₀, hB₀, sub_zero, sub_zero, sub_zero, div_div_div_cancel_right₀ hx₀]
  have hH : Differentiable ℂ H := by
    intro x
    by_cases hx : x ∈ L.lattice
    · have hcomp : H = fun y ↦ H (y - x) := funext fun y ↦ by
        rw [← hperL x hx (y - x), sub_add_cancel]
      have h₁ : DifferentiableAt ℂ (fun y : ℂ ↦ y - x) x := differentiableAt_id.sub_const x
      have h₂ : DifferentiableAt ℂ H ((fun y : ℂ ↦ y - x) x) := by simpa using hH₀
      have h₃ : DifferentiableAt ℂ (fun y ↦ H (y - x)) x := h₂.comp (f := fun y ↦ y - x) x h₁
      rwa [← hcomp] at h₃
    · refine ((hA x).div (hB x) (hne hx)).congr_of_eventuallyEq ?_
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hx] with y hy
      simp [H, show y ∉ L.lattice from hy]
  -- `H` is doubly periodic, hence bounded and constant.
  have hconst (y : ℂ) : H y = c := by
    have := hH.apply_eq_apply_of_bounded (IsZLattice.isCompact_range_of_periodic L.lattice H
      hH.continuous fun z w hw ↦ hperL w hw z).isBounded y 0
    simpa [H, L.lattice.zero_mem] using this
  -- Off the lattice this is the claim; on it, both sides are limits of their values off it.
  have hoff (y : ℂ) (hy : y ∉ L.lattice) : thetaInv τ y = c * thetaExp τ y := by
    have := hconst y
    simp only [H, hy, ite_false] at this
    rw [← this, div_mul_cancel₀ _ (hne hy)]
  by_cases hz : z ∈ L.lattice
  · have hg : Continuous fun y ↦ thetaInv τ y - c * thetaExp τ y :=
      hA.continuous.sub (continuous_const.mul hB.continuous)
    refine sub_eq_zero.mp (tendsto_nhds_unique (f := fun y ↦ thetaInv τ y - c * thetaExp τ y)
      (l := 𝓝[≠] z) (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' ?_))
    filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds z),
      self_mem_nhdsWithin] with y hy hyz
    rw [hoff y fun h ↦ hy ⟨h, hyz⟩, sub_self]
  · exact hoff z hz

/-- **Jacobi's imaginary transformation of the theta product.** For `τ` in the upper half-plane
and every `z ∈ ℂ`,
`θ_{-1/τ}(z/τ) = -i e^{π i ((z² + z + 1/6)/τ + τ/6 - z)} θ_τ(z)`, where
`θ_τ(z) = θ_q(e^{2π i z})` with `q = e^{2π i τ}`. -/
theorem qTheta_exp_neg_one_div (hτ : 0 < τ.im) (z : ℂ) :
    qTheta (cexp (2 * π * I * (-1 / τ))) (cexp (2 * π * I * (z / τ))) =
      -I * cexp (π * I * ((z ^ 2 + z + 1 / 6) / τ + τ / 6 - z)) *
        qTheta (cexp (2 * π * I * τ)) (cexp (2 * π * I * z)) := by
  have h := thetaInv_eq hτ z
  rw [thetaInv, thetaExp] at h
  have he : π * I * (1 / 6 / τ + τ / 6) + π * I * (z ^ 2 / τ + z / τ - z) =
      π * I * ((z ^ 2 + z + 1 / 6) / τ + τ / 6 - z) := by
    ring
  rw [h, ← he, Complex.exp_add]
  ring

end Inversion

end TauCeti
