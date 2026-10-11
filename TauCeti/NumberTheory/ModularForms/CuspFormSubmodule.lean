/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
public import TauCeti.NumberTheory.ModularForms.Basic

/-!
# Restriction and trace preserve the cusp forms

For subgroups `Γ' ≤ Γ` of `GL₂(ℝ)` of determinant one, the cusp-form submodule of Mathlib's
`ModularForm.cuspFormSubmodule` is preserved by both maps between `M_k(Γ)` and `M_k(Γ')`:
restricting a cusp form to `Γ'` keeps it cuspidal (`ModularForm.ofLe_mem_cuspFormSubmodule`), and
so does tracing a cusp form from `Γ'` up to `Γ` (`ModularForm.traceₗ_mem_cuspFormSubmodule`),
because the trace of a cusp form is Mathlib's `CuspForm.trace`.

## Main results

* `ModularForm.ofLe_mem_cuspFormSubmodule`: restriction preserves cusp forms.
* `ModularForm.traceₗ_mem_cuspFormSubmodule`: the trace preserves cusp forms.
-/

public section

open UpperHalfPlane

namespace ModularForm

variable {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-- Restricting a cusp form for `Γ` to a subgroup `Γ'` gives a cusp form for `Γ'`. -/
theorem ofLe_mem_cuspFormSubmodule [Γ.HasDetOne] [Γ'.HasDetOne] (h : Γ' ≤ Γ)
    {f : ModularForm Γ k} (hf : f ∈ cuspFormSubmodule Γ k) :
    ofLe h f ∈ cuspFormSubmodule Γ' k := by
  obtain ⟨g, rfl⟩ := hf
  refine ⟨CuspForm.ofLe h g, ext fun z ↦ ?_⟩
  rw [CuspForm.toModularFormₗ_apply, CuspForm.coe_ofLe, coe_ofLe, CuspForm.toModularFormₗ_apply]

/-- The trace of a cusp form is a cusp form. -/
theorem traceₗ_mem_cuspFormSubmodule [Γ.HasDetOne] [Γ'.HasDetOne] [Γ'.IsFiniteRelIndex Γ]
    {f : ModularForm Γ' k} (hf : f ∈ cuspFormSubmodule Γ' k) :
    traceₗ Γ f ∈ cuspFormSubmodule Γ k := by
  obtain ⟨g, rfl⟩ := hf
  have hg : ⇑(CuspForm.toModularFormₗ g) = ⇑g := funext (CuspForm.toModularFormₗ_apply g)
  refine ⟨CuspForm.trace Γ g, ext fun z ↦ ?_⟩
  simp only [CuspForm.toModularFormₗ_apply, CuspForm.coe_trace, traceₗ_apply, coe_trace,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  induction q using QuotientGroup.induction_on' with
  | H h => rw [SlashInvariantForm.quotientFunc_mk, SlashInvariantForm.quotientFunc_mk, hg]

end ModularForm
