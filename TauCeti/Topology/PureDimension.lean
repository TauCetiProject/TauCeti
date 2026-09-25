/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.KrullDimension

/-!
# Pure-dimensional topological spaces

A topological space is pure-dimensional of dimension `d` when every irreducible component has
Krull dimension `d`. Empty spaces are pure-dimensional of every dimension, since they have no
irreducible components. Thus empty fibres automatically satisfy the pure-dimensional component
condition in the definition of a morphism of pure relative dimension.

The property is invariant under homeomorphisms. A discrete space is pure-dimensional of dimension
zero: every irreducible component is nonempty and discrete, hence has Krull dimension zero.

Pure dimension is local on spaces in which every nonempty open part `Z ∩ U` of an irreducible
component `Z` has the Krull dimension of `Z`, such as schemes locally of finite type over a field:
the irreducible components of an open subspace are the traces of the components of the whole
space that meet it. Without that hypothesis this fails: the spectrum of a discrete valuation ring
is irreducible of dimension one, while its generic point is an open subspace of dimension zero.

## Main declarations

* `TauCeti.IsPureDimensional`: every irreducible component has the prescribed Krull dimension.
* `TauCeti.IsPureDimensional.homeomorph`: invariance under homeomorphisms.
* `Homeomorph.isPureDimensional_iff`: a homeomorphism preserves pure dimension.
* `TauCeti.isPureDimensional_zero_of_discreteTopology`: discrete spaces have pure dimension zero.
* `TauCeti.IsPureDimensional.of_isOpenEmbedding` and
  `TauCeti.isPureDimensional_iff_forall_of_isOpenEmbedding`: locality of pure dimension on spaces
  whose irreducible components have all nonempty open parts of full dimension.

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

/-- An empty space is pure-dimensional of every dimension. -/
@[simp]
theorem isPureDimensional_of_isEmpty (d : ℕ) (X : Type*) [TopologicalSpace X] [IsEmpty X] :
    IsPureDimensional d X := by
  intro Z hZ
  obtain ⟨x, hx⟩ := hZ.1.nonempty
  exact isEmptyElim x

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

namespace TauCeti

variable {d : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Let `X` be a space in which every nonempty open part of an irreducible component has the
Krull dimension of the component. If `X` is pure-dimensional, then so is every open subspace. -/
theorem IsPureDimensional.of_isOpenEmbedding (hX : IsPureDimensional d X)
    (hdim : ∀ Z ∈ irreducibleComponents X, ∀ U : Set X, IsOpen U → (Z ∩ U).Nonempty →
      topologicalKrullDim ↥(Z ∩ U) = topologicalKrullDim Z)
    {e : Y → X} (he : IsOpenEmbedding e) : IsPureDimensional d Y := by
  intro C hC
  -- The component `C` of `Y` is the preimage of the component `Z` of `X` containing its image.
  obtain ⟨Z, hZ, hCZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (hC.1.image e he.continuous.continuousOn)
  have hne : (Z ∩ Set.range e).Nonempty := by
    obtain ⟨y, hy⟩ := hC.1.nonempty
    exact ⟨e y, hCZ ⟨y, hy, rfl⟩, y, rfl⟩
  rw [hC.eq_of_le (preimage_mem_irreducibleComponents hZ he hne).1 (Set.image_subset_iff.mp hCZ),
    he.isEmbedding.topologicalKrullDim_preimage, hdim Z hZ _ he.isOpen_range hne, hX Z hZ]

/-- Let `X` be a space in which every nonempty open part of an irreducible component has the
Krull dimension of the component. Given open embeddings whose ranges cover `X`, the space `X` is
pure-dimensional exactly when each of their domains is. -/
theorem isPureDimensional_iff_forall_of_isOpenEmbedding {ι : Type*} {Y : ι → Type*}
    [∀ i, TopologicalSpace (Y i)]
    (hdim : ∀ Z ∈ irreducibleComponents X, ∀ U : Set X, IsOpen U → (Z ∩ U).Nonempty →
      topologicalKrullDim ↥(Z ∩ U) = topologicalKrullDim Z)
    (e : ∀ i, Y i → X) (he : ∀ i, IsOpenEmbedding (e i))
    (hcover : ∀ x, ∃ i, x ∈ Set.range (e i)) :
    IsPureDimensional d X ↔ ∀ i, IsPureDimensional d (Y i) := by
  refine ⟨fun hX i ↦ hX.of_isOpenEmbedding hdim (he i), fun hY Z hZ ↦ ?_⟩
  obtain ⟨x, hx⟩ := hZ.1.nonempty
  obtain ⟨i, hi⟩ := hcover x
  have hne : (Z ∩ Set.range (e i)).Nonempty := ⟨x, hx, hi⟩
  rw [← hdim Z hZ _ (he i).isOpen_range hne, ← (he i).isEmbedding.topologicalKrullDim_preimage,
    hY i _ (preimage_mem_irreducibleComponents hZ (he i) hne)]

end TauCeti
