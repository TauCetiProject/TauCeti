/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Rel
public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Constructions

/-!
# Cylinder sets and agreement of configurations

For a discrete alphabet `A`, Mathlib's cylinder sets `SymbolicDynamics.FullShift.cylinder U x`,
for finite `U`, are clopen (`SymbolicDynamics.FullShift.isOpen_cylinder`,
`SymbolicDynamics.FullShift.isClosed_cylinder`). This file records that they form a basis of the
product topology on `G → A` (`SymbolicDynamics.FullShift.isTopologicalBasis_cylinders`).

It also defines the relation `TauCeti.agreeOn S` "agree on the coordinates of `S`" on
configurations `G → α`; for a discrete alphabet these relations for finite `S` are the basis of the
product uniformity given by `Pi.hasBasis_uniformity_of_discreteUniformity`. A word `w` on a finite
set `S` of coordinates extends to a configuration `TauCeti.extendWord S w`, and two extensions agree
on `S` exactly when the words are equal (`TauCeti.extendWord_mem_agreeOn_iff`).

## Main definitions

* `TauCeti.agreeOn S`: the relation "agree on the coordinates of `S`" on `G → α`.
* `TauCeti.extendWord S w`: a configuration extending the word `w` on `S`.
-/

public section

open TopologicalSpace

namespace SymbolicDynamics.FullShift

/-- For a discrete alphabet, the cylinder sets form a basis of the product topology. -/
theorem isTopologicalBasis_cylinders {G A : Type*} [TopologicalSpace A] [DiscreteTopology A] :
    IsTopologicalBasis (Set.range fun p : Finset G × (G → A) => cylinder p.1 p.2) := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ fun x u hx hu => ?_
  · rintro _ ⟨⟨U, x⟩, rfl⟩
    exact isOpen_cylinder U x
  · obtain ⟨U, v, hv, hsub⟩ := isOpen_pi_iff.1 hu x hx
    refine ⟨cylinder U x, ⟨(U, x), rfl⟩, mem_cylinder.2 fun _ _ => rfl,
      fun y hy => hsub fun i hi => ?_⟩
    rw [mem_cylinder.1 hy i hi]
    exact (hv i hi).2

end SymbolicDynamics.FullShift

namespace TauCeti

variable {α G : Type*}

/-- Configurations agreeing on the coordinates of `S`. -/
@[expose] def agreeOn (S : Set G) : SetRel (G → α) (G → α) := {p | ∀ i ∈ S, p.1 i = p.2 i}

@[simp]
theorem mem_agreeOn {S : Set G} {x y : G → α} : (x, y) ∈ agreeOn S ↔ ∀ i ∈ S, x i = y i :=
  Iff.rfl

/-- Agreeing on a larger set of coordinates implies agreeing on a smaller one. -/
theorem agreeOn_anti {S S' : Set G} (h : S ⊆ S') :
    (agreeOn S' : SetRel (G → α) (G → α)) ⊆ agreeOn S :=
  fun _ hp i hi ↦ hp i (h hi)

/-- Extend a word on `S` to a configuration, by an arbitrary symbol off `S`. -/
noncomputable def extendWord [Nonempty α] (S : Finset G) (w : S → α) : G → α :=
  open Classical in fun i ↦ if h : i ∈ S then w ⟨i, h⟩ else Classical.arbitrary α

/-- On `S`, the extension of a word on `S` is the word. -/
@[simp]
theorem extendWord_of_mem [Nonempty α] {S : Finset G} (w : S → α) {i : G} (hi : i ∈ S) :
    extendWord S w i = w ⟨i, hi⟩ := by
  simp [extendWord, hi]

/-- The extensions of two words on `S` agree on `S` exactly when the words are equal. -/
theorem extendWord_mem_agreeOn_iff [Nonempty α] {S : Finset G} {w w' : S → α} :
    (extendWord S w, extendWord S w') ∈ (agreeOn (S : Set G) : SetRel (G → α) (G → α)) ↔
      w = w' := by
  refine ⟨fun h ↦ funext fun i ↦ ?_, fun h ↦ h ▸ mem_agreeOn.2 fun _ _ ↦ rfl⟩
  rw [← extendWord_of_mem w i.property, ← extendWord_of_mem w' i.property]
  exact mem_agreeOn.1 h i i.property

end TauCeti
