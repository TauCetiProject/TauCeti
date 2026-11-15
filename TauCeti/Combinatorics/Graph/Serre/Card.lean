/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting the edges of a Serre graph

Every geometric edge of a Serre graph consists of two darts, a dart and its reverse. Hence a Serre
graph has twice as many darts as geometric edges.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.1.
-/

public section

universe u v

namespace TauCeti
namespace SerreGraph

variable (Γ : SerreGraph.{u, v})

/-- A Serre graph has twice as many darts as geometric edges, finitely many or not: each geometric
edge consists of two darts. -/
theorem card_E_eq_two_mul_card_geomEdge : Nat.card Γ.E = 2 * Nat.card Γ.GeomEdge := by
  classical
  obtain ⟨O, hO⟩ := Γ.exists_isOrientation
  -- A dart is its geometric edge together with whether it lies in the orientation `O`.
  have hbij : Function.Bijective fun e => (Γ.toGeomEdge e, decide (e ∈ O)) := by
    refine ⟨fun e e' h => ?_, fun ⟨g, b⟩ => ?_⟩
    · simp only [Prod.mk.injEq, decide_eq_decide] at h
      rcases Γ.toGeomEdge_eq_toGeomEdge_iff.1 h.1 with he | he
      · exact he.symm
      · rw [he, hO.mem_rev_iff] at h
        exact absurd h.2 iff_not_self
    · obtain ⟨e, rfl⟩ := Γ.toGeomEdge_surjective g
      by_cases he : decide (e ∈ O) = b
      · exact ⟨e, by simp [he]⟩
      · refine ⟨Γ.rev e, ?_⟩
        cases b <;> simp_all [hO.mem_rev_iff]
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod,
    Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm]

end SerreGraph
end TauCeti
