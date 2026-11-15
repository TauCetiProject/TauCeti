/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Range-preserving real Lipschitz extension

`LipschitzOnWith.extend_real_mem_Icc` extends real Lipschitz data on an arbitrary subset
while retaining prescribed lower and upper bounds. It applies to empty subsets and singleton
target intervals as well. This is useful before mollification, since truncation of an extension
does not increase its Lipschitz constant.

The construction uses Mathlib's McShane extension `LipschitzOnWith.extend_real`, followed
by projection onto the target interval.
-/

public section

open Set
open scoped NNReal

/-- Real Lipschitz data valued in a nonempty closed interval admit an extension with the
same Lipschitz constant and values in that interval on the whole space. -/
theorem LipschitzOnWith.extend_real_mem_Icc {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {s : Set X} {K : ℝ≥0} (hf : LipschitzOnWith K f s)
    {a b : ℝ} (hab : a ≤ b) (hmem : ∀ x ∈ s, f x ∈ Icc a b) :
    ∃ g : X → ℝ, LipschitzWith K g ∧ EqOn f g s ∧ ∀ x, g x ∈ Icc a b := by
  obtain ⟨g, hg, heq⟩ := hf.extend_real
  refine ⟨fun x => (projIcc a b hab (g x) : ℝ), ?_, ?_, fun x => (projIcc _ _ _ _).property⟩
  · simpa only [one_mul, Function.comp_def] using
      (LipschitzWith.subtype_val (Icc a b)).comp ((LipschitzWith.projIcc hab).comp hg)
  · intro x hx
    simp only [← heq hx, projIcc_of_mem hab (hmem x hx)]
