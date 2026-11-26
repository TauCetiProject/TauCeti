/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Iterated
public import TauCeti.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import TauCeti.Topology.MetricSpace.Holder

/-!
# The derivatives of the sigmoid in the bounded Hölder spaces `C_b^{k,α}(ℝ)`

Every derivative of the sigmoid `σ x = 1 / (1 + exp (-x))` is a polynomial in `σ`, hence bounded,
and Lipschitz since the next derivative is bounded too
(`Real.exists_abs_iteratedDeriv_sigmoid_le`, `Real.memHolder_iteratedDeriv_sigmoid`). So for
`α ≤ 1` every derivative `σ⁽ⁿ⁾` lies in `C_b^{k,α}(ℝ)` for every `k`
(`TauCeti.CkHolderSpace.exists_coe_eq_iteratedDeriv_sigmoid`).

Since `σ` is the derivative of `x ↦ log (1 + exp x)`, this says that the logarithm of the weight
`1 + exp x`, which is unbounded, has derivatives of every positive order in `C_b^{k,α}(ℝ)`. This is
the hypothesis under which, at every order, multiplication by this weight identifies the
unweighted space `C_{par,b}^{k+2+α}` with the weighted class `u / (1 + exp x) ∈ C_{par,b}^{k+2+α}`,
while the conjugated coefficients remain in the unweighted coefficient space `C_{par,b}^{k+α}`.
-/

public section

noncomputable section

open Real
open scoped NNReal

namespace TauCeti.CkHolderSpace

variable {k : ℕ} {α : ℝ≥0}

/-- For `α ≤ 1`, every derivative `σ⁽ⁿ⁾` of the sigmoid is a bounded `C^{k,α}` map on `ℝ` for
every `k`. -/
theorem exists_coe_eq_iteratedDeriv_sigmoid (hα : α ≤ 1) (n : ℕ) :
    ∃ f : CkHolderSpace k α ℝ ℝ, ⇑f = iteratedDeriv n sigmoid := by
  have hd (i : ℕ) : iteratedDeriv i (iteratedDeriv n sigmoid) = iteratedDeriv (i + n) sigmoid := by
    simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]
  obtain ⟨C, hC⟩ := memHolder_iteratedDeriv_sigmoid (k + n) hα
  have hσ : ContDiff ℝ k (iteratedDeriv n sigmoid) := by
    rw [iteratedDeriv_eq_iterate]
    exact ((contDiff_sigmoid.of_le le_top).iterate_deriv n).of_le (by exact_mod_cast le_top)
  refine ⟨ofContDiff _ hσ (fun i _ ↦ ?_) ⟨C, ?_⟩, coe_ofContDiff _ _ _ _⟩
  · obtain ⟨C', hC'⟩ := exists_abs_iteratedDeriv_sigmoid_le (i + n)
    exact ⟨C', fun x ↦ by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hd, Real.norm_eq_abs]
      exact hC' x⟩
  · rw [iteratedFDeriv_eq_equiv_comp, hd, (LinearIsometryEquiv.isometry _).holderWith_comp_iff]
    exact hC

end TauCeti.CkHolderSpace
