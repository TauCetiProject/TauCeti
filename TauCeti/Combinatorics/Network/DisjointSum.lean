/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.DisjointUnion

/-!
# Componentwise restriction of assignments on disjoint sums of networks

`TauCeti.DisjointUnionHom` forms the disjoint sum of two arrow families, which may live in
different universes. It retains the arrows inside each summand and has no arrows between the
summands. Exact- and interval-excess assignments on it split into their two components through
`TauCeti.ExcessFlow.restrictEquiv` and `TauCeti.ExcessIntervalFlow.restrictEquiv`.

This file adds the remaining componentwise facts used when assignments on disconnected
components are combined or restricted: extensionality through both restrictions, bounds of an
arbitrary assignment against combined bounds, arrow sums over arbitrary vertex sets of the
disjoint sum, and restriction of circulations.
-/

public section

namespace TauCeti

universe u u' v v' w

variable {V : Type u} {W : Type u'} {Q : V → V → Type v} {R : W → W → Type v'} {K : Type w}

namespace Assignment

/-- Assignments on a disjoint sum agree when their restrictions to both summands agree. -/
theorem ext_restrictLeft_restrictRight {f g : Assignment (DisjointUnionHom Q R) K}
    (hl : f.restrictLeft = g.restrictLeft) (hr : f.restrictRight = g.restrictRight) : f = g :=
  eq_iff_restrictLeft_restrictRight.2 ⟨hl, hr⟩

/-- An assignment on a disjoint sum respects combined bounds exactly when both of its
restrictions respect the corresponding bounds. -/
theorem mem_Icc_disjointUnion_iff [Preorder K] {lo₁ hi₁ : Assignment Q K}
    {lo₂ hi₂ : Assignment R K} {f : Assignment (DisjointUnionHom Q R) K} :
    f ∈ Set.Icc (lo₁.disjointUnion lo₂) (hi₁.disjointUnion hi₂) ↔
      f.restrictLeft ∈ Set.Icc lo₁ hi₁ ∧ f.restrictRight ∈ Set.Icc lo₂ hi₂ := by
  simpa only [restrictLeft_disjointUnion, restrictRight_disjointUnion] using
    mem_Icc_iff_restrictLeft_restrictRight f (lo₁.disjointUnion lo₂) (hi₁.disjointUnion hi₂)

end Assignment

section ArrowSum

variable [∀ x y, Fintype (Q x y)] [∀ x y, Fintype (R x y)] [AddCommMonoid K]

/-- An arrow sum of combined assignments between arbitrary vertex sets of the disjoint sum
splits into the summand arrow sums between their left and right parts. -/
theorem arrowSum_disjointUnion_eq_add_toLeft_toRight (f : Assignment Q K)
    (g : Assignment R K) (S T : Finset (V ⊕ W)) :
    arrowSum (f.disjointUnion g) S T =
      arrowSum f S.toLeft T.toLeft + arrowSum g S.toRight T.toRight := by
  simpa only [Assignment.restrictLeft_disjointUnion, Assignment.restrictRight_disjointUnion]
    using arrowSum_eq_add_restrictLeft_restrictRight (f.disjointUnion g) S T

end ArrowSum

section Circulation

variable [Fintype V] [Fintype W] [∀ x y, Fintype (Q x y)] [∀ x y, Fintype (R x y)]
  [AddCommGroup K] {f : Assignment (DisjointUnionHom Q R) K}

/-- The restriction of a circulation on a disjoint sum to its left summand is a circulation. -/
theorem IsCirculation.restrictLeft (hf : IsCirculation f) : IsCirculation f.restrictLeft :=
  ((isCirculation_iff_restrictLeft_restrictRight f).1 hf).1

/-- The restriction of a circulation on a disjoint sum to its right summand is a circulation. -/
theorem IsCirculation.restrictRight (hf : IsCirculation f) : IsCirculation f.restrictRight :=
  ((isCirculation_iff_restrictLeft_restrictRight f).1 hf).2

end Circulation

end TauCeti
