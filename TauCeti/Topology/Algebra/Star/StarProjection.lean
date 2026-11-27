/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.Connected.PathConnected
public import TauCeti.Algebra.Star.PartialIsometry

/-!
# Homotopy equivalence of star projections

This file defines projection homotopy (`TauCeti.IsHomotopicProjection`) on any topological star
magma `[Mul S] [Star S] [TopologicalSpace S]`, together with conjugacy by a unitary in the
path component of the identity of `unitary S` over a topological star monoid.

## Main definitions

* `TauCeti.IsHomotopicProjection p q`: `p` and `q` are star projections joined by a continuous path
  in the subtype `{P : S // IsStarProjection P}`.

## Main statements

* `TauCeti.IsHomotopicProjection.refl`, `TauCeti.IsHomotopicProjection.symm`,
  `TauCeti.IsHomotopicProjection.trans`: equivalence-relation properties on star projections.
* `TauCeti.isHomotopicProjection_iff`, `TauCeti.isHomotopicProjection_self_iff`,
  `TauCeti.isHomotopicProjection_comm`: witness and basic equivalence criteria.
* `IsStarProjection.isHomotopicProjection_conj_of_joined_one`,
  `IsStarProjection.isHomotopicProjection_of_joined_one_unitary_conj`: conjugating a star
  projection by a unitary joined to `1` yields a homotopic projection.
-/

public section

namespace TauCeti

section IsHomotopicProjection

section

variable {S : Type*} [Mul S] [Star S] [TopologicalSpace S] {p q r : S}

/-- Two elements are homotopic star projections when both are star projections and they are
`Joined` in the subtype `{P : S // IsStarProjection P}`. -/
def IsHomotopicProjection (p q : S) : Prop :=
  ∃ (hp : IsStarProjection p) (hq : IsStarProjection q),
    Joined (⟨p, hp⟩ : {P : S // IsStarProjection P}) ⟨q, hq⟩

namespace IsHomotopicProjection

/-- The left element of a projection homotopy is a star projection. -/
theorem isStarProjection_left (h : IsHomotopicProjection p q) : IsStarProjection p := h.1

/-- The right element of a projection homotopy is a star projection. -/
theorem isStarProjection_right (h : IsHomotopicProjection p q) : IsStarProjection q := h.2.1

/-- The projections `p` and `q` are `Joined` in the projection subtype
`{P : S // IsStarProjection P}` (use `Joined.somePath` if an explicit path value is needed). -/
theorem joined (h : IsHomotopicProjection p q) :
    Joined (⟨p, h.isStarProjection_left⟩ : {P : S // IsStarProjection P})
      ⟨q, h.isStarProjection_right⟩ := h.2.2

/-- Every star projection is homotopic to itself. -/
protected theorem refl (hp : IsStarProjection p) : IsHomotopicProjection p p := ⟨hp, hp, .refl _⟩

/-- Projection homotopy is symmetric. -/
protected theorem symm (h : IsHomotopicProjection p q) : IsHomotopicProjection q p :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

/-- Projection homotopy is transitive. -/
protected theorem trans (h₁ : IsHomotopicProjection p q) (h₂ : IsHomotopicProjection q r) :
    IsHomotopicProjection p r := ⟨h₁.1, h₂.2.1, h₁.2.2.trans h₂.2.2⟩

end IsHomotopicProjection

/-- The witness criterion for projection homotopy of given star projections. -/
theorem isHomotopicProjection_iff (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsHomotopicProjection p q ↔ Joined (⟨p, hp⟩ : {P : S // IsStarProjection P}) ⟨q, hq⟩ :=
  ⟨IsHomotopicProjection.joined, fun h => ⟨hp, hq, h⟩⟩

@[simp]
theorem isHomotopicProjection_self_iff : IsHomotopicProjection p p ↔ IsStarProjection p :=
  ⟨IsHomotopicProjection.isStarProjection_left, IsHomotopicProjection.refl⟩

theorem isHomotopicProjection_comm :
    IsHomotopicProjection p q ↔ IsHomotopicProjection q p :=
  ⟨IsHomotopicProjection.symm, IsHomotopicProjection.symm⟩

end

section

variable {S : Type*} [Monoid S] [StarMul S] [TopologicalSpace S] [ContinuousMul S]
  [ContinuousStar S] {p q : S}

/-- Conjugating a star projection `p` by a unitary in the path component of the identity yields a
homotopic projection. -/
theorem _root_.IsStarProjection.isHomotopicProjection_conj_of_joined_one (hp : IsStarProjection p)
    {u : unitary S} (hu : Joined (1 : unitary S) u) :
    IsHomotopicProjection p ((u : S) * p * star (u : S)) := by
  refine ⟨hp, hp.conj_unitary u, ?_⟩
  let φ : unitary S → {P : S // IsStarProjection P} :=
    fun v => ⟨(v : S) * p * star (v : S), hp.conj_unitary v⟩
  have hφ : Continuous φ :=
    ((continuous_subtypeVal.mul continuous_const).mul continuous_subtypeVal.star).subtype_mk _
  simpa [φ] using hu.map hφ

/-- Projections conjugated by a unitary joined to `1` are homotopic. -/
theorem _root_.IsStarProjection.isHomotopicProjection_of_joined_one_unitary_conj
    (hp : IsStarProjection p) {u : unitary S} (hu : Joined (1 : unitary S) u)
    (hu_conj : (u : S) * p * star (u : S) = q) : IsHomotopicProjection p q :=
  hu_conj ▸ hp.isHomotopicProjection_conj_of_joined_one hu

end

end IsHomotopicProjection

end TauCeti
