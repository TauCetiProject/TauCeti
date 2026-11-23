/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.End.Coordinate
public import TauCeti.Topology.Homotopy.AddCircle

/-!
# Null-homotopic loops at the ends of the pair of pants

This file transports null-homotopy of loops `AddCircle 1 → X` under time reparametrization
`t ↦ q.endSign * t` by the sign `±1` of a puncture `q` of the pair of pants `S = ℂ ∖ {0, 1}`,
without importing Floer charts or Hamiltonian orbit theory.

## Main results

* `TauCeti.Floer.exists_nullhomotopic_comp_endSign_mul_iff`: reparametrizing by `t ↦ ±t` with the
  sign of an end preserves descending to a null-homotopic map `AddCircle 1 → X`.
-/

public section

open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

/-- Reparametrizing a curve by `t ↦ ±t`, with the sign of the end `q`, preserves descending to a
null-homotopic map `AddCircle 1 → X`. -/
theorem exists_nullhomotopic_comp_endSign_mul_iff {X : Type*} [TopologicalSpace X]
    {q : Puncture} {γ : ℝ → X} :
    (∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ (q.endSign * t)) ↔
      ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ t := by
  have fwd {δ : ℝ → X}
      (h : ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = δ t) :
      ∃ g : C(AddCircle (1 : ℝ), X), g.Nullhomotopic ∧ ∀ t : ℝ, g t = δ (q.endSign * t) := by
    obtain ⟨g, hg, hgδ⟩ := h
    have hex := hg.exists_addCircle_comp_mul one_ne_zero q.endSign_ne_zero
    rw [abs_endSign, div_one] at hex
    obtain ⟨g', hg', hg'g⟩ := hex
    exact ⟨g', hg', fun t ↦ (hg'g t).trans (by rw [mul_comm, hgδ])⟩
  refine ⟨fun h ↦ ?_, fwd⟩
  simpa only [endSign_mul_endSign_mul] using fwd h

end TauCeti.Floer
