/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basic

import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Order.Zorn

/-!
# Maximal commutative subspaces of a Lie algebra

A subspace `t` of a Lie algebra `L` is a **maximal commutative subspace** when its elements
commute with each other and every element of `L` commuting with all of `t` lies in `t`. For the
Lie algebra of a compact Lie group these are the Lie algebras of the maximal tori.

## Main results

* `TauCeti.exists_maximal_commuting_submodule`: every Lie algebra has a maximal commutative
  subspace.
-/

public section

namespace TauCeti

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- **Every Lie algebra has a maximal commutative subspace** `t`: the elements of `t` commute with
each other, and every element commuting with all of `t` lies in `t`. -/
theorem exists_maximal_commuting_submodule :
    ∃ t : Submodule R L, (∀ a ∈ t, ∀ b ∈ t, ⁅a, b⁆ = 0) ∧
      ∀ z : L, (∀ H : t, ⁅(H : L), z⁆ = 0) → z ∈ t := by
  -- Zorn's lemma: the union of a chain of commutative subspaces is commutative.
  obtain ⟨t, -, ht, hmax⟩ := zorn_le_nonempty₀
    {t : Submodule R L | ∀ a ∈ t, ∀ b ∈ t, ⁅a, b⁆ = 0} (fun c hcs hc y hy ↦ by
      refine ⟨sSup c, fun a ha b hb ↦ ?_, fun _ ↦ le_sSup⟩
      obtain ⟨p, hp, hap⟩ := (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hc.directedOn).mp ha
      obtain ⟨q, hq, hbq⟩ := (Submodule.mem_sSup_of_directed ⟨y, hy⟩ hc.directedOn).mp hb
      rcases hc.total hp hq with hpq | hqp
      · exact hcs hq a (hpq hap) b hbq
      · exact hcs hp a hap b (hqp hbq)) ⊥ (by simp)
  refine ⟨t, ht, fun z hz ↦ ?_⟩
  -- Adding an element `z` commuting with `t` keeps the subspace commutative.
  have hc : ∀ a ∈ t ⊔ R ∙ z, ∀ b ∈ t ⊔ R ∙ z, ⁅a, b⁆ = 0 := by
    intro a ha b hb
    obtain ⟨a, ha₁, _, hc, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨b, hb₁, _, hd, rfl⟩ := Submodule.mem_sup.mp hb
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hc
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hd
    have hbz : ⁅z, b⁆ = 0 := by rw [← lie_skew, hz ⟨b, hb₁⟩, neg_zero]
    simp [ht a ha₁ b hb₁, hz ⟨a, ha₁⟩, hbz]
  exact hmax hc le_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self z))

end TauCeti
