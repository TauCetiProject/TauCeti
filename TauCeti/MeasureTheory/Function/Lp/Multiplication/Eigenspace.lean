/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.MeasureTheory.Function.Lp.Multiplication.Basic

/-!
# Eigenspaces of `L²` multiplication operators

When an essentially bounded complex symbol `a : Lp ℂ ∞ μ` avoids a scalar `c : ℂ` almost
everywhere, `MeasureTheory.Lp.multiplicationOperator a` has trivial `c`-eigenspace on `Lp E 2 μ`.

## Main results

* `MeasureTheory.Lp.eq_zero_of_multiplicationOperator_eq_smul`: any `c`-eigenvector vanishes when
  `∀ᵐ x ∂μ, a x ≠ c`.
* `MeasureTheory.Lp.not_hasEigenvalue_multiplicationOperator`: `c` is not an eigenvalue of
  `multiplicationOperator a` when `∀ᵐ x ∂μ, a x ≠ c`.
-/

public section

noncomputable section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}

/-- If a symbol `a ∈ Lp ℂ ∞ μ` avoids `c` almost everywhere, then `multiplicationOperator a` on
`Lp E 2 μ` has trivial `c`-eigenspace. -/
theorem eq_zero_of_multiplicationOperator_eq_smul [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a : Lp ℂ ∞ μ} {c : ℂ} (ha : ∀ᵐ x ∂μ, a x ≠ c) {f : Lp E 2 μ}
    (hf : multiplicationOperator a f = c • f) : f = 0 := by
  refine Lp.eq_zero_iff_ae_eq_zero.mpr ?_
  filter_upwards [(Lp.ext_iff.mp hf.symm).trans (multiplicationOperator_ae a f),
    Lp.coeFn_smul c f, ha] with x hmul hsmul hne
  have heq : (a x - c) • f x = 0 := by
    rw [sub_smul, ← hmul, hsmul, Pi.smul_apply, sub_self]
  exact (smul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr hne)

/-- If a symbol `a ∈ Lp ℂ ∞ μ` avoids `c` almost everywhere, then `c` is not an eigenvalue of
`multiplicationOperator a` on `Lp E 2 μ`. -/
theorem not_hasEigenvalue_multiplicationOperator [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : Lp ℂ ∞ μ) {c : ℂ} (ha : ∀ᵐ x ∂μ, a x ≠ c) :
    ¬ Module.End.HasEigenvalue (multiplicationOperator (E := E) (p := 2) a).toLinearMap c := by
  intro hc
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  exact hv0 <| eq_zero_of_multiplicationOperator_eq_smul ha (Module.End.mem_eigenspace_iff.mp hv)

end MeasureTheory.Lp

end
