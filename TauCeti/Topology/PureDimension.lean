/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.KrullDimension

/-!
# Pure-dimensional topological spaces

A topological space is pure-dimensional of dimension `d` when every irreducible component has
Krull dimension `d`. Empty spaces are pure-dimensional of every dimension, since they have no
irreducible components. Thus empty fibres automatically satisfy the pure-dimensional component
condition in the definition of a morphism of pure relative dimension.

The property is invariant under homeomorphisms. A discrete space is pure-dimensional of dimension
zero: every irreducible component is nonempty and discrete, hence has Krull dimension zero.

## Main declarations

* `TauCeti.IsPureDimensional`: every irreducible component has the prescribed Krull dimension.
* `TauCeti.IsPureDimensional.homeomorph`: invariance under homeomorphisms.
* `Homeomorph.isPureDimensional_iff`: a homeomorphism preserves pure dimension.
* `TauCeti.isPureDimensional_zero_of_discreteTopology`: discrete spaces have pure dimension zero.

## References

* [Stacks Project, Tag 02NI](https://stacks.math.columbia.edu/tag/02NI)
-/

public section

open Order Topology TopologicalSpace

namespace TauCeti

/-- A topological space is pure-dimensional of dimension `d` if every irreducible component has
topological Krull dimension `d`. -/
def IsPureDimensional (d : ℕ) (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d

/-- Pure dimension is preserved by a homeomorphism. -/
theorem IsPureDimensional.homeomorph {d : ℕ} {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (hX : IsPureDimensional d X) (e : X ≃ₜ Y) :
    IsPureDimensional d Y := by
  intro Z hZ
  have hpre : e ⁻¹' Z ∈ irreducibleComponents X :=
    preimage_mem_irreducibleComponents hZ e.isOpenEmbedding (by simpa using hZ.1.nonempty)
  have hdim := hX (e ⁻¹' Z) hpre
  have he : (e ⁻¹' Z) ≃ₜ Z :=
    e.isEmbedding.homeomorphOfSubsetRange (by simp)
  exact he.isHomeomorph.topologicalKrullDim_eq.symm.trans hdim

end TauCeti

namespace Homeomorph

/-- Pure dimension is invariant under a homeomorphism. -/
theorem isPureDimensional_iff {d : ℕ} {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) :
    TauCeti.IsPureDimensional d X ↔ TauCeti.IsPureDimensional d Y :=
  ⟨fun h ↦ h.homeomorph e, fun h ↦ h.homeomorph e.symm⟩

end Homeomorph

namespace TauCeti

/-- A discrete topological space is pure-dimensional of dimension zero. -/
theorem isPureDimensional_zero_of_discreteTopology (X : Type*) [TopologicalSpace X]
    [DiscreteTopology X] : IsPureDimensional 0 X := by
  intro Z hZ
  let hZirr : IrreducibleSpace Z := Subtype.irreducibleSpace hZ.1
  have hnonempty : Nonempty (IrreducibleCloseds Z) :=
    ⟨⟨Set.univ, @IrreducibleSpace.isIrreducible_univ Z _ hZirr, isClosed_univ⟩⟩
  exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology Z)
    (@krullDim_nonneg (IrreducibleCloseds Z) _ hnonempty)

end TauCeti
