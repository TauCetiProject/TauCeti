/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
public import TauCeti.Analysis.Meromorphic.Divisor
import TauCeti.Analysis.Complex.Taylor.PoleCancellation
import TauCeti.NumberTheory.DirichletCharacter.Quadratic

/-!
# Cancellation of a principal pole against an exceptional zero

In the Deuring–Heilbronn argument, the simple pole at `1` of a principal Dirichlet L-function
is paired with one copy of a real zero `β` of the quadratic character. At a centre with
`Re z ≥ 2`, the resulting coefficient is bounded by `j (1 - β)` when the zero is
inside the local divisor disc. If it is outside, the pole is far enough away that its coefficient
is bounded by `2⁻ʲ`. Removing one copy from the divisor leaves the other copies of a multiple
zero intact.

The cancellation follows the four-logarithmic-derivative argument of Levent Alpöge's
[formalization of the Riemann hypothesis for Dirichlet L-functions][alpoege].

[alpoege]: https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005
-/

public section

open Metric MeromorphicOn

namespace DirichletCharacter

open Classical in
/-- The local zero divisor of a pole-cleared Dirichlet L-function dominates one copy of any zero
in the disc. The restricted singleton vanishes if the zero is outside the disc. -/
theorem single_restrict_le_divisor_entireLFunction {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter ℂ N) {β : ℂ} (hβ : ψ.entireLFunction β = 0)
    (z : ℂ) (r : ℝ) :
    (Function.locallyFinsuppWithin.single β (1 : ℤ)).restrict
      (Set.subset_univ (closedBall z r)) ≤ divisor ψ.entireLFunction (closedBall z r) := by
  classical
  have hf : AnalyticOnNhd ℂ ψ.entireLFunction (closedBall z r) :=
    fun w _ ↦ ψ.analyticAt_entireLFunction w
  intro w
  by_cases hw : w ∈ closedBall z r
  · by_cases hwβ : w = β
    · subst w
      rw [Function.locallyFinsuppWithin.restrict_apply, ite_eq_left hw,
        Function.locallyFinsuppWithin.single_apply, ite_eq_left rfl]
      have htop : meromorphicOrderAt ψ.entireLFunction β ≠ ⊤ := by
        rw [(ψ.analyticAt_entireLFunction β).meromorphicOrderAt_eq]
        simp [ψ.analyticOrderAt_entireLFunction_ne_top β]
      exact Int.add_one_le_iff.mpr
        ((hf.meromorphicOn.zero_lt_divisor_iff_of_analyticAt (hf β hw) hw htop).mpr hβ)
    · simpa only [Function.locallyFinsuppWithin.restrict_apply, ite_eq_left hw,
        Function.locallyFinsuppWithin.single_apply, ite_eq_right hwβ,
        Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply] using hf.divisor_nonneg w
  · simpa only [Function.locallyFinsuppWithin.restrict_apply, ite_eq_right hw,
      Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply] using hf.divisor_nonneg w

open Classical in
/-- In the pair `χ, χψ`, with `ψ` nonprincipal and quadratic, a principal pole is paired with
one copy of a real zero `β` of the other character `ψ` in the local disc. Subtract the restricted
singleton from the zero divisor of `ψ` only when the pair contains a principal character.
The change after dropping the pole is at most `j (1 - β)` if `β` is in the disc, and at most
`2⁻ʲ` otherwise. The divisor after removal is nonnegative when `β` is a zero, by
`single_restrict_le_divisor_entireLFunction`. -/
theorem norm_principalPoles_sub_exceptionalDivisor_le {N : ℕ} [NeZero N]
    (χ ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1) (hquad : ψ.IsQuadratic) {z : ℂ} (hz : 2 ≤ z.re)
    {β : ℝ} (hβ : β ∈ Set.Icc 0 1) (j : ℕ) :
    let U := closedBall z 3
    let D := divisor ψ.entireLFunction U
    let e := if χ = 1 ∨ χ = ψ then
      (Function.locallyFinsuppWithin.single (β : ℂ) (1 : ℤ)).restrict (Set.subset_univ U) else 0
    ‖(if χ = 1 then ((z - 1) ^ j)⁻¹ else 0) + (if χ * ψ = 1 then ((z - 1) ^ j)⁻¹ else 0) -
      (∑ᶠ w, (D w : ℂ) / (z - w) ^ j) + (∑ᶠ w, ((D - e) w : ℂ) / (z - w) ^ j)‖ ≤
      if χ = 1 ∨ χ = ψ then
        (if (β : ℂ) ∈ U then (j : ℝ) * (1 - β) else (2⁻¹ : ℝ) ^ j)
      else 0 := by
  intro U D e
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
  · simpa [hχ, hψ, U] using Complex.norm_inv_pow_one_sub_cutoff_inv_pow_le hz hβ j
  by_cases hχψ : χ = ψ
  · simpa [hχψ, hψ, hsq, U] using Complex.norm_inv_pow_one_sub_cutoff_inv_pow_le hz hβ j
  · simp [hχ, hχψ, hm]

end DirichletCharacter
