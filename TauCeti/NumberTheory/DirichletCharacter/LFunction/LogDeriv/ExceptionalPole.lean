/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.NumberTheory.DirichletCharacter.Basic
import TauCeti.Analysis.Normed.Field.Lipschitz
import TauCeti.Analysis.Normed.Ring.ProdSubProd

/-!
# Cancellation of a principal pole against an exceptional zero

In the Deuring–Heilbronn argument, the simple pole at `1` of a principal Dirichlet L-function
is paired with one copy of a real zero `β` of the quadratic character. At a centre with
`Re z ≥ 2`, the resulting coefficient is bounded by `j (1 - β)` when the zero is
inside the local divisor disc. If it is outside, the pole is far enough away that its coefficient
is bounded by `2⁻ʲ`. Removing one copy from the divisor leaves the other copies of a multiple
zero intact. The scalar estimate for one pole and one zero is
`TauCeti.norm_inv_sub_one_pow_sub_ite_mem_closedBall_le`.

The cancellation follows the four-logarithmic-derivative argument of Levent Alpöge's
[formalization of the Riemann hypothesis for Dirichlet L-functions][alpoege].

[alpoege]: https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005
-/

public section

open Metric MeromorphicOn

namespace TauCeti

open Complex

open Classical in
/-- The difference of the reciprocal powers for a pole at `1` and a real zero `β` is small when
the zero is in the local disc. Outside the disc the coefficient of the pole alone is small. -/
theorem norm_inv_sub_one_pow_sub_ite_mem_closedBall_le {z : ℂ} (hz : 2 ≤ z.re) {β : ℝ}
    (hβ : β ∈ Set.Icc 0 1) (j : ℕ) :
    ‖((z - 1) ^ j)⁻¹ - (if (β : ℂ) ∈ closedBall z 3 then ((z - β) ^ j)⁻¹ else 0)‖ ≤
      if (β : ℂ) ∈ closedBall z 3 then (j : ℝ) * (1 - β) else (2⁻¹ : ℝ) ^ j := by
  have hp : 1 ≤ ‖z - 1‖ := by
    have h := re_le_norm (z - 1)
    simp only [sub_re, one_re] at h
    linarith
  have hgap : ‖(1 : ℂ) - β‖ = 1 - β := by
    rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hβ.2)]
  by_cases hmem : (β : ℂ) ∈ closedBall z 3
  · have hzero : 1 ≤ ‖z - β‖ := by
      have h := re_le_norm (z - (β : ℂ))
      simp only [sub_re, ofReal_re] at h
      linarith [hβ.2]
    have hdiff : ‖(z - 1) - (z - (β : ℂ))‖ = 1 - β := by
      rw [sub_sub_sub_cancel_left, norm_sub_rev, hgap]
    have hinv (w : ℂ) (hw : 1 ≤ ‖w‖) : ‖w⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      simpa only [inv_one] using inv_anti₀ zero_lt_one hw
    have hpow : ‖(z - 1)⁻¹ ^ j - (z - β)⁻¹ ^ j‖ ≤ (j : ℝ) * ‖(z - 1)⁻¹ - (z - β)⁻¹‖ := by
      simpa using norm_prod_sub_prod_le_sum_norm_sub (Finset.range j)
        (a := fun _ ↦ (z - 1)⁻¹) (b := fun _ ↦ (z - β)⁻¹)
        (fun _ _ ↦ hinv _ hp) (fun _ _ ↦ hinv _ hzero)
    have hdist : ‖(z - 1)⁻¹ - (z - β)⁻¹‖ ≤ 1 - β := by
      rw [← hdiff]
      simpa only [one_pow, one_div] using
        norm_sq_div_sub_sq_div_le (c := (1 : ℂ))
          (by simpa using hp) (by simpa using hzero)
    simpa only [ite_eq_left hmem, ← inv_pow] using
      hpow.trans (mul_le_mul_of_nonneg_left hdist (Nat.cast_nonneg j))
  · have hfar : 3 < ‖z - β‖ := by
      simpa only [mem_closedBall_iff_norm', not_le] using hmem
    have htri := norm_sub_le_norm_sub_add_norm_sub z (1 : ℂ) (β : ℂ)
    have hp' : 2 ≤ ‖z - 1‖ := by linarith [hβ.1]
    simp only [ite_eq_right hmem, sub_zero, ← inv_pow, norm_pow, norm_inv]
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ (by norm_num) hp') j

end TauCeti

namespace DirichletCharacter

open Classical in
/-- In the pair `χ, χψ`, with `ψ` nonprincipal and quadratic, a principal pole is paired with
one copy of a real zero `β` of the other character `ψ` in the local disc. Subtract the restricted
singleton from the zero divisor of `ψ` only when the pair contains a principal character.
The change after dropping the pole is at most `j (1 - β)` if `β` is in the disc, and at most
`2⁻ʲ` otherwise. The bound holds for any `ℤ`-valued divisor `D` on the disc; in the application
`D` is the zero divisor of `ψ.entireLFunction`, and then `D - e` is nonnegative when `β` is a
zero, by `AnalyticOnNhd.single_restrict_le_divisor`. -/
theorem norm_ite_inv_pow_add_finsum_sub_single_restrict_le {N : ℕ}
    (χ ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1) (hquad : ψ.IsQuadratic) {z : ℂ} (hz : 2 ≤ z.re)
    {β : ℝ} (hβ : β ∈ Set.Icc 0 1) (j : ℕ) (D : Function.locallyFinsuppWithin (closedBall z 3) ℤ) :
    let U := closedBall z 3
    let e := if χ = 1 ∨ χ = ψ then
      (Function.locallyFinsuppWithin.single (β : ℂ) (1 : ℤ)).restrict (Set.subset_univ U) else 0
    ‖(if χ = 1 then ((z - 1) ^ j)⁻¹ else 0) + (if χ * ψ = 1 then ((z - 1) ^ j)⁻¹ else 0) -
      (∑ᶠ w, (D w : ℂ) / (z - w) ^ j) + (∑ᶠ w, ((D - e) w : ℂ) / (z - w) ^ j)‖ ≤
      if χ = 1 ∨ χ = ψ then
        (if (β : ℂ) ∈ U then (j : ℝ) * (1 - β) else (2⁻¹ : ℝ) ^ j)
      else 0 := by
  intro U e
  have hcompact : IsCompact U := isCompact_closedBall z 3
  have hfin (d : Function.locallyFinsuppWithin U ℤ) :
      (fun w ↦ (d w : ℂ) / (z - w) ^ j).HasFiniteSupport :=
    (d.finiteSupport hcompact).subset (fun w hw ↦ by
      rw [Function.mem_support] at hw ⊢
      exact fun h ↦ hw (by simp [h]))
  have hsplit : (∑ᶠ w, ((D - e) w : ℂ) / (z - w) ^ j) =
      (∑ᶠ w, (D w : ℂ) / (z - w) ^ j) - ∑ᶠ w, (e w : ℂ) / (z - w) ^ j := by
    rw [← finsum_sub_distrib (hfin D) (hfin e)]
    simp only [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply, Int.cast_sub, sub_div]
  have hsingle : (∑ᶠ w, (e w : ℂ) / (z - w) ^ j) =
      if (χ = 1 ∨ χ = ψ) ∧ (β : ℂ) ∈ U then ((z - β) ^ j)⁻¹ else 0 := by
    rw [finsum_eq_single _ (β : ℂ)]
    · by_cases h : χ = 1 ∨ χ = ψ <;> by_cases hβU : (β : ℂ) ∈ U <;>
        simp [e, h, hβU, Function.locallyFinsuppWithin.restrict_apply]
    · intro w hw
      by_cases h : χ = 1 ∨ χ = ψ <;>
        simp [e, h, hw, Function.locallyFinsuppWithin.restrict_apply]
  rw [hsplit, sub_add_sub_cancel, hsingle]
  have hsq : ψ * ψ = 1 := by simpa only [pow_two] using hquad.sq_eq_one
  have hm : χ * ψ = 1 ↔ χ = ψ := by
    refine ⟨fun h ↦ ?_, fun h ↦ h ▸ hsq⟩
    simpa only [mul_assoc, hsq, mul_one, one_mul] using congrArg (· * ψ) h
  by_cases hχ : χ = 1
  · simpa [hχ, hψ, U] using TauCeti.norm_inv_sub_one_pow_sub_ite_mem_closedBall_le hz hβ j
  by_cases hχψ : χ = ψ
  · simpa [hχψ, hψ, hsq, U] using TauCeti.norm_inv_sub_one_pow_sub_ite_mem_closedBall_le hz hβ j
  · simp [hχ, hχψ, hm]

end DirichletCharacter
