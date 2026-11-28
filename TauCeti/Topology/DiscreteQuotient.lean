/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Topology.DiscreteQuotient

/-!
# Continuous projections and finite separation for discrete quotients

`DiscreteQuotient.projContinuousMap` bundles the projection onto a discrete quotient as a
continuous map. For the quotient attached to a locally constant function,
`LocallyConstant.lift_proj` computes its lift on the image of each point.

On a profinite set, two distinct points are separated by some discrete quotient
(`DiscreteQuotient.eq_of_forall_proj_eq`). Taking the meet over all pairs, finitely many points are
separated by a single discrete quotient (`DiscreteQuotient.exists_injOn_proj`). Consequently an
infinite profinite set has finite discrete quotients with arbitrarily many points
(`DiscreteQuotient.exists_lt_natCard`).
-/

public section

namespace DiscreteQuotient

variable {X : Type*} [TopologicalSpace X]

/-- The projection onto a discrete quotient, bundled as a continuous map. -/
def projContinuousMap (Q : DiscreteQuotient X) : C(X, Q) :=
  ⟨Q.proj, Q.proj_continuous⟩

/-- The bundled quotient projection has underlying function `DiscreteQuotient.proj`. -/
@[simp]
theorem coe_projContinuousMap (Q : DiscreteQuotient X) : ⇑Q.projContinuousMap = Q.proj :=
  (rfl)

variable [CompactSpace X] [T2Space X]
  [TotallyDisconnectedSpace X]

/-- Finitely many points of a profinite set are mapped to distinct points of a single discrete
quotient. -/
theorem exists_injOn_proj (s : Finset X) :
    ∃ Q : DiscreteQuotient X, Set.InjOn Q.proj s := by
  classical
  have hsep (p : X × X) : ∃ Q : DiscreteQuotient X, p.1 ≠ p.2 → Q.proj p.1 ≠ Q.proj p.2 := by
    by_cases hp : p.1 = p.2
    · exact ⟨⊤, fun h ↦ (h hp).elim⟩
    · obtain ⟨Q, hQ⟩ := not_forall.mp (mt eq_of_forall_proj_eq hp)
      exact ⟨Q, fun _ ↦ hQ⟩
  choose Q hQ using hsep
  refine ⟨(s ×ˢ s).inf Q, fun x hx y hy hxy ↦ by_contra fun hne ↦ hQ (x, y) hne ?_⟩
  have hle : (s ×ˢ s).inf Q ≤ Q (x, y) := Finset.inf_le (Finset.mk_mem_product hx hy)
  rw [← ofLE_proj hle x, ← ofLE_proj hle y, hxy]

/-- An infinite profinite set has finite discrete quotients with arbitrarily many points. -/
theorem exists_lt_natCard [Infinite X] (n : ℕ) :
    ∃ Q : DiscreteQuotient X, n < Nat.card Q := by
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq X (n + 1)
  obtain ⟨Q, hQ⟩ := exists_injOn_proj s
  have := Nat.card_le_card_of_injective _ hQ.injective
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, hs] at this
  exact ⟨Q, this⟩

end DiscreteQuotient

namespace LocallyConstant

/-- Evaluating the lift at the image of a point recovers the locally constant function. -/
@[simp]
theorem lift_proj {X Y : Type*} [TopologicalSpace X] (f : LocallyConstant X Y) (x : X) :
    f.lift (f.discreteQuotient.proj x) = f x :=
  congrFun f.lift_comp_proj x

end LocallyConstant
