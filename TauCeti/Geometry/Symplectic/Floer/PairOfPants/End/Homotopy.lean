/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
public import TauCeti.Topology.Homotopy.AddCircle

/-!
# Null-homotopic loops at the ends of the pair of pants

This file transports null-homotopy of loops `AddCircle 1 → X` along the end charts `endChart` and
`positiveEndChart` of the pair of pants `S = ℂ ∖ {0, 1}`.

## Main results

* `TauCeti.Floer.exists_nullhomotopic_comp_endSign_mul_iff`: reparametrizing by `t ↦ ±t` with the
  sign of an end preserves descending to a null-homotopic map `AddCircle 1 → X`.
* `TauCeti.Floer.forall_exists_nullhomotopic_positiveEndChart`: if `u` is continuous on `S` and
  one end loop `t ↦ u(φ_q(±s₀, t))` (`s₀ > 0`) is null-homotopic, then every positive-end loop
  `t ↦ (u ∘ φ'_q)(s, t)` (`s > 0`) is null-homotopic.
-/

public section

open Set Function TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

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
  simpa only [← mul_assoc, endSign_mul_self, one_mul] using fwd h

/-- If `u` is continuous on `S = ℂ ∖ {0, 1}` and one end loop `t ↦ u(φ_q(±s₀, t))` (`s₀ > 0`) is
null-homotopic in a locally path-connected, semilocally simply connected space `X`, then every
positive-end loop `t ↦ (u ∘ φ'_q)(s, t)` (`s > 0`) is null-homotopic in `X`. -/
theorem forall_exists_nullhomotopic_positiveEndChart {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] [TauCeti.SemilocallySimplyConnectedSpace X] {u : ℝ × ℝ → X}
    (hu : ContinuousOn u thricePuncturedSphereReal) {q : Puncture}
    (hnull : ∃ s > 0, ∃ g : C(AddCircle (1 : ℝ), X),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (endChart q (q.endSign * s, t))) :
    ∀ s > 0, ∃ g : C(AddCircle (1 : ℝ), X),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = (u ∘ positiveEndChart q) (s, t) := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  obtain ⟨s₀, hs₀, hg₀⟩ := hnull
  have hg₀' : ∃ g : C(AddCircle (1 : ℝ), X),
      g.Nullhomotopic ∧ ∀ t : ℝ, g t = (u ∘ positiveEndChart q) (s₀, t) := by
    simpa only [comp_apply, positiveEndChart_mk] using
      exists_nullhomotopic_comp_endSign_mul_iff.2 hg₀
  exact TauCeti.forall_exists_nullhomotopic_of_isPreconnected isPreconnected_Ioi
    (u := fun s t ↦ (u ∘ positiveEndChart q) (s, t))
    (hu.comp (contDiff_positiveEndChart q 0).continuous.continuousOn
      fun _ hz ↦ positiveEndChart_mem_thricePuncturedSphereReal (mem_Ioi.1 hz.1))
    (fun s _ t ↦ by simp only [comp_apply, positiveEndChart_add_one]) hs₀ hg₀'

end TauCeti.Floer
