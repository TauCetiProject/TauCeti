/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.PartialIsometry

/-!
# Unitary equivalence of star projections

This file defines projection unitary equivalence (`TauCeti.IsUnitarilyEquivalent`) on any star
monoid `[Monoid S] [StarMul S]`, proving reflexivity on star projections, symmetry, transitivity,
witness and self-equivalence characterizations, and that conjugating a star projection by a unitary
yields a unitarily equivalent star projection.

## Main definitions

* `TauCeti.IsUnitarilyEquivalent p q`: `p` and `q` are star projections conjugated by a unitary
  element `u : unitary S`.

## Main statements

* `TauCeti.IsUnitarilyEquivalent.refl`, `TauCeti.IsUnitarilyEquivalent.symm`,
  `TauCeti.IsUnitarilyEquivalent.trans`: equivalence-relation properties on star projections.
* `TauCeti.isUnitarilyEquivalent_iff`, `TauCeti.isUnitarilyEquivalent_self_iff`,
  `TauCeti.isUnitarilyEquivalent_comm`: witness and basic equivalence criteria.
* `IsStarProjection.isUnitarilyEquivalent_conj`: conjugating a star projection by a unitary gives a
  unitarily equivalent projection.
-/

public section

namespace TauCeti

section IsUnitarilyEquivalent

variable {S : Type*} [Monoid S] [StarMul S] {p q r : S}

/-- Two elements are unitarily equivalent projections when both are star projections and some
unitary `u : unitary S` satisfies `(u : S) * p * star (u : S) = q`. -/
def IsUnitarilyEquivalent (p q : S) : Prop :=
  IsStarProjection p ∧ IsStarProjection q ∧ ∃ u : unitary S, (u : S) * p * star (u : S) = q

namespace IsUnitarilyEquivalent

/-- The left element of a unitary equivalence is a star projection. -/
theorem isStarProjection_left (h : IsUnitarilyEquivalent p q) : IsStarProjection p := h.1

/-- The right element of a unitary equivalence is a star projection. -/
theorem isStarProjection_right (h : IsUnitarilyEquivalent p q) : IsStarProjection q := h.2.1

/-- Extract a unitary conjugating `p` to `q`. -/
theorem exists_unitary (h : IsUnitarilyEquivalent p q) :
    ∃ u : unitary S, (u : S) * p * star (u : S) = q := h.2.2

/-- Every star projection is unitarily equivalent to itself. -/
protected theorem refl (hp : IsStarProjection p) : IsUnitarilyEquivalent p p := ⟨hp, hp, 1, by simp⟩

/-- Unitary equivalence of star projections is symmetric. -/
protected theorem symm (h : IsUnitarilyEquivalent p q) : IsUnitarilyEquivalent q p := by
  obtain ⟨hp, hq, u, hu⟩ := h
  refine ⟨hq, hp, star u, ?_⟩
  have hU : star (u : S) * (u : S) = 1 := Unitary.coe_star_mul_self u
  calc
    ((star u : unitary S) : S) * q * star ((star u : unitary S) : S)
        = (star (u : S) * (u : S)) * p * (star (u : S) * (u : S)) := by
          simp only [← hu, Unitary.coe_star, star_star, mul_assoc]
    _ = p := by rw [hU, one_mul, mul_one]

/-- Unitary equivalence of star projections is transitive. -/
protected theorem trans (h₁ : IsUnitarilyEquivalent p q) (h₂ : IsUnitarilyEquivalent q r) :
    IsUnitarilyEquivalent p r := by
  obtain ⟨hp, _, u, hu⟩ := h₁
  obtain ⟨_, hr, v, hv⟩ := h₂
  refine ⟨hp, hr, v * u, ?_⟩
  calc
    ((v * u : unitary S) : S) * p * star ((v * u : unitary S) : S)
        = (v : S) * ((u : S) * p * star (u : S)) * star (v : S) := by
          simp only [Submonoid.coe_mul, star_mul, mul_assoc]
    _ = r := by rw [hu, hv]

end IsUnitarilyEquivalent

/-- The witness criterion for unitary equivalence of given star projections. -/
theorem isUnitarilyEquivalent_iff (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsUnitarilyEquivalent p q ↔ ∃ u : unitary S, (u : S) * p * star (u : S) = q :=
  ⟨IsUnitarilyEquivalent.exists_unitary, fun h => ⟨hp, hq, h⟩⟩

@[simp]
theorem isUnitarilyEquivalent_self_iff : IsUnitarilyEquivalent p p ↔ IsStarProjection p :=
  ⟨IsUnitarilyEquivalent.isStarProjection_left, IsUnitarilyEquivalent.refl⟩

theorem isUnitarilyEquivalent_comm : IsUnitarilyEquivalent p q ↔ IsUnitarilyEquivalent q p :=
  ⟨IsUnitarilyEquivalent.symm, IsUnitarilyEquivalent.symm⟩

/-- A star projection `p` is unitarily equivalent to `(u : S) * p * star (u : S)` for any unitary
`u`. -/
theorem _root_.IsStarProjection.isUnitarilyEquivalent_conj (hp : IsStarProjection p)
    (u : unitary S) :
    IsUnitarilyEquivalent p ((u : S) * p * star (u : S)) :=
  ⟨hp, hp.conj_unitary u, u, rfl⟩

end IsUnitarilyEquivalent

end TauCeti
