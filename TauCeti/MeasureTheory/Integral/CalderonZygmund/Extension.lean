/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.CalderonZygmund.StrongType
public import TauCeti.MeasureTheory.Function.Lp.OperatorExtension

/-!
# Calderón–Zygmund operators on the full `Lᵖ` space

The strong-type estimates for a Calderón–Zygmund operator initially act on `L² ∩ Lᵖ`.
Finite-measure simple functions are dense in `Lᵖ` for `p < ∞`, so these estimates determine a
bounded linear operator on all of `Lᵖ`. The extension agrees almost everywhere with the original
operator on the intersection. For `p > 2`, the cancellation hypothesis is applied to the adjoint.

## References

* A. P. Calderón and A. Zygmund, *On the existence of certain singular integrals*,
  Acta Math. **88** (1952), 85–139.
* E. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter II, §2.
-/

public section

noncomputable section

namespace ContinuousLinearMap

open MeasureTheory Metric Set TauCeti
open scoped ENNReal NNReal

variable {ι : Type*} [Fintype ι] [Nonempty ι] {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The full strong-type Calderón–Zygmund theorem.** An `L²`-bounded operator for which both
it and its adjoint satisfy the cancellation estimate with finite constants extends to a bounded
operator on `Lᵖ(ℝⁿ; H) → Lᵖ(ℝⁿ; K)` for every `1 < p < ∞`. On `L² ∩ Lᵖ`, the extended map agrees
almost everywhere with the given operator. -/
theorem exists_strongTypeExtension_of_setLIntegral_compl_closedBall_le
    (T : Lp H 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp K 2 (volume : Measure (ι → ℝ)))
    {B B' : ℝ≥0∞} (hB : B ≠ ∞) (hB' : B' ≠ ∞)
    (hT : ∀ (b : Lp H 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (r : ℝ),
      (∀ᵐ x, x ∉ closedBall y r → b x = 0) → ∫ x, b x = 0 →
        ∫⁻ x in (closedBall y (2 * r))ᶜ, ‖T b x‖ₑ ≤ B * ∫⁻ x, ‖b x‖ₑ)
    (hT' : ∀ (b : Lp K 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (r : ℝ),
      (∀ᵐ x, x ∉ closedBall y r → b x = 0) → ∫ x, b x = 0 →
        ∫⁻ x in (closedBall y (2 * r))ᶜ, ‖adjoint T b x‖ₑ ≤ B' * ∫⁻ x, ‖b x‖ₑ)
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ (C : ℝ≥0) (S : Lp H p (volume : Measure (ι → ℝ)) →L[ℝ]
      Lp K p (volume : Measure (ι → ℝ))), ‖S‖ ≤ C ∧
      ∀ (f : Lp H 2 (volume : Measure (ι → ℝ))) (hf : MemLp f p volume),
        (S (hf.toLp f) : (ι → ℝ) → K) =ᵐ[volume] T f := by
  obtain ⟨C, hC⟩ := T.exists_eLpNorm_le_of_setLIntegral_compl_closedBall_le
    hB hB' hT hT' hp hp_top
  have hC' : ∀ f : Lp H 2 (volume : Measure (ι → ℝ)), MemLp f p volume →
      eLpNorm (T f) p volume ≤ C * eLpNorm f p volume := fun f _ => hC f
  exact ⟨C, strongTypeExtension T C hC' hp_top,
    norm_strongTypeExtension_le T C hC' hp_top,
    fun f hf => strongTypeExtension_apply_of_memLp T C hC' hp_top f hf⟩

end ContinuousLinearMap
