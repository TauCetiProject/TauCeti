/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Defs
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Analysis.Semigroups.Dissipative.Duality
import TauCeti.MeasureTheory.Function.Lp.Duality

/-!
# Dissipativity on `Lᵖ` in integral form

Let `1 ≤ p < ∞` and let `H` be a real inner product space. The generator `A` of a contraction
semigroup on `Lᵖ(μ; H)` satisfies the classical integral form of dissipativity: every `u` in
the domain of `A` satisfies

`∫ ‖u‖ ^ (p - 2) ⟪u, A u⟫ dμ ≤ 0`

(`ContractionSemigroup.integral_norm_rpow_sub_two_mul_inner_generator_nonpos`), where
`‖u‖ ^ (p - 2) u` vanishes where `u` does. Integration against `‖u‖ ^ (p - 2) u`, scaled by
`‖u‖_p ^ (2 - p)`, is an element of the duality set of `u` in `Lᵖ`
(`MeasureTheory.Lp.exists_mem_dualitySet_apply_eq_integral`), and the generator of a contraction
semigroup is nonpositive against every element of the duality set
(`ContractionSemigroup.apply_generator_nonpos_of_mem_dualitySet`).

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Example II.3.26 and Proposition II.3.23.
-/

public section

namespace TauCeti.Semigroups.ContractionSemigroup

open MeasureTheory

open scoped ENNReal InnerProductSpace

variable {α H : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Dissipativity of a generator on `Lᵖ` in integral form.** For `1 ≤ p < ∞`, every `u` in the
domain of the generator `A` of a contraction semigroup on `Lᵖ(μ; H)`, `H` a real inner product
space, satisfies `∫ ‖u‖ ^ (p - 2) ⟪u, A u⟫ dμ ≤ 0`. Here `‖u‖ ^ (p - 2) u` vanishes where `u`
does. -/
theorem integral_norm_rpow_sub_two_mul_inner_generator_nonpos (hp : p ≠ ∞)
    (S : ContractionSemigroup (Lp H p μ)) (u : S.toStronglyContinuousSemigroup.generator.domain) :
    ∫ x, ‖(u : Lp H p μ) x‖ ^ (p.toReal - 2) *
      ⟪(u : Lp H p μ) x, S.toStronglyContinuousSemigroup.generator u x⟫_ℝ ∂μ ≤ 0 := by
  obtain ⟨f, hf, hfv⟩ := Lp.exists_mem_dualitySet_apply_eq_integral ℝ hp (u : Lp H p μ)
  have hA := S.apply_generator_nonpos_of_mem_dualitySet u hf
  simp only [hfv, RCLike.ofReal_real_eq_id, id_eq, real_inner_smul_left] at hA
  rcases eq_or_ne (u : Lp H p μ) 0 with hu | hu
  · refine (integral_eq_zero_of_ae ?_).le
    filter_upwards [Lp.coeFn_zero H p μ] with x hx
    rw [hu, hx]
    simp
  · exact nonpos_of_mul_nonpos_right hA (by positivity)

end TauCeti.Semigroups.ContractionSemigroup
