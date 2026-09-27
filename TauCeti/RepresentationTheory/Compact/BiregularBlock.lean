/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.IsotypicBlock

/-!
# The Peter--Weyl blocks as two-sided subrepresentations

Two-sided translation `((g, h) · f) x = f (g⁻¹ * x * h)` makes `L²(G)` a representation of `G × G`
(`TauCeti.biregularLp`).  This file shows that the Peter--Weyl block of an irreducible model, the
span of the `L²` matrix coefficients of that model, is a subrepresentation for it.

The computation behind this is one identity: two-sided translation carries a matrix coefficient of a
unitary `π` to a matrix coefficient of the *same* `π`, moving the right translation onto its first
vector and the left translation onto its second,

`(g, h) · π_{v, w} = π_{π h v, π g w}`

(`TauCeti.biregularLp_matrixCoeffLp`).  So the block is spanned by a set that two-sided translation
maps into itself, and the block is therefore stable.  Because the two-sided action is unitary, the
restricted action is unitary too, and the block is an honest unitary `G × G`-representation.

This is the group-theoretic half of the Peter--Weyl decomposition that
`TauCeti.RepresentationTheory.Compact.IsotypicBlock` deliberately leaves out: the statements there
are about Hilbert spaces, their subspaces and their isometries, and the only translation statements
proved there are the one-sided stabilities `TauCeti.rightRegularLp_mem_peterWeylBlock` and
`TauCeti.leftRegularLp_mem_peterWeylBlock`, which is exactly what the two-sided stability is
assembled from here.  Equivariance of the identification of a block with `End(V_π)` needs in
addition the `G × G`-action `(g, h) · A = π g ∘ A ∘ π h⁻¹` on `End(V_π)` and is not proved here.

## Main definitions

* `TauCeti.peterWeylBlockBiregular`: the Peter--Weyl block of a model, as a representation of
  `G × G` by two-sided translation.

## Main statements

* `TauCeti.biregularLp_matrixCoeffLp`: two-sided translation of a matrix coefficient of a unitary
  representation is the matrix coefficient with the two translations absorbed into its two vectors.
* `TauCeti.biregularLp_mem_peterWeylBlock`: a block is stable under two-sided translation, so it is
  a `G × G`-subrepresentation of `L²(G)`, and
  `TauCeti.biregularLp_mem_iSup_peterWeylBlock`: so is the sum of the blocks of a family, the
  subspace whose closure is all of `L²(G)` for a skeleton
  (`TauCeti.topologicalClosure_iSup_peterWeylBlock`).
* `TauCeti.isUnitary_peterWeylBlockBiregular`: the restricted two-sided action is unitary.

## References

* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 2.
* [Compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
  Layer 5, "The isotypic decomposition".

## Tags

Peter-Weyl theorem, regular representation, isotypic component
-/

public section

open MeasureTheory

namespace TauCeti

section CompactGroup

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-! ### Two-sided translation of a matrix coefficient -/

/-- **Two-sided translation absorbs into the defining vectors of a matrix coefficient.**  For a
continuous unitary `π`, the `(g, h)`-translate of `π_{v, w} : g ↦ ⟪π g v, w⟫` is `π_{π h v, π g w}`:
the right translation lands on the first vector and the left translation on the second. -/
theorem biregularLp_matrixCoeffLp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    {π : ContRepresentation 𝕜 G V} (hπ : Continuous π)
    (hunitary : ContRepresentation.IsUnitary π) (a : G × G) (v w : V) :
    biregularLp 𝕜 G a (ContRepresentation.matrixCoeffLp π hπ v w)
      = ContRepresentation.matrixCoeffLp π hπ (π a.2 v) (π a.1 w) := by
  rw [ContRepresentation.matrixCoeffLp_def, biregularLp_toLp, ← ContinuousMap.comp_assoc,
    ContRepresentation.matrixCoeff_comp_mulLeft hπ hunitary, inv_inv,
    ContRepresentation.matrixCoeff_comp_mulRight, ← ContRepresentation.matrixCoeffLp_def]

/-! ### Stability of a block -/

/-- **Each block is stable under two-sided translation**, so it is a `G × G`-subrepresentation of
`L²(G)`: two-sided translation is right translation after left translation, and a block is stable
under each. -/
theorem biregularLp_mem_peterWeylBlock (model : IrrepModel 𝕜 G) (a : G × G)
    {f : Lp 𝕜 2 (haarProb G)} (hf : f ∈ peterWeylBlock model) :
    biregularLp 𝕜 G a f ∈ peterWeylBlock model := by
  rw [biregularLp_apply]
  exact rightRegularLp_mem_peterWeylBlock model a.2
    (leftRegularLp_mem_peterWeylBlock model a.1 hf)

/-- **The sum of the blocks of a family of models is stable under two-sided translation.**  Each
block is (`TauCeti.biregularLp_mem_peterWeylBlock`), and a sum of stable subspaces is stable.  For a
skeleton of the unitary dual this subspace is dense in `L²(G)`
(`TauCeti.topologicalClosure_iSup_peterWeylBlock`), which is what makes the Peter-Weyl decomposition
of `L²(G)` a decomposition of `G × G`-representations. -/
theorem biregularLp_mem_iSup_peterWeylBlock {ι : Type*} (models : ι → IrrepModel 𝕜 G)
    (a : G × G) {f : Lp 𝕜 2 (haarProb G)} (hf : f ∈ ⨆ i, peterWeylBlock (models i)) :
    biregularLp 𝕜 G a f ∈ ⨆ i, peterWeylBlock (models i) := by
  refine Submodule.iSup_induction (motive := fun x => biregularLp 𝕜 G a x ∈
    ⨆ i, peterWeylBlock (models i)) _ hf (fun i x hx => ?_) (by simp) fun x y hx hy => ?_
  · exact Submodule.mem_iSup_of_mem i (biregularLp_mem_peterWeylBlock (models i) a hx)
  · simpa using Submodule.add_mem _ hx hy

/-! ### The block as a representation of `G × G` -/

/-- **The Peter--Weyl block of a model, as a representation of `G × G`** by two-sided translation.
Its carrier is the span of the `L²` matrix coefficients of the model, which
`TauCeti.finrank_peterWeylBlock` computes to have dimension `(dim V_π)²` over an algebraically
closed `𝕜`. -/
noncomputable def peterWeylBlockBiregular (model : IrrepModel 𝕜 G) :
    ContRepresentation 𝕜 (G × G) (peterWeylBlock model) :=
  ContRepresentation.subrepresentation (biregularLp 𝕜 G) (peterWeylBlock model) fun a _ hv =>
    biregularLp_mem_peterWeylBlock model a hv

/-- The block representation is two-sided translation, read on the underlying vectors of `L²(G)`. -/
@[simp]
theorem coe_peterWeylBlockBiregular_apply (model : IrrepModel 𝕜 G) (a : G × G)
    (f : peterWeylBlock model) :
    ((peterWeylBlockBiregular model a f : peterWeylBlock model) : Lp 𝕜 2 (haarProb G))
      = biregularLp 𝕜 G a (f : Lp 𝕜 2 (haarProb G)) :=
  ContRepresentation.coe_subrepresentation_apply a f

/-- **The block representation is unitary**, the ambient two-sided translation being unitary and the
block carrying the restricted norm. -/
theorem isUnitary_peterWeylBlockBiregular (model : IrrepModel 𝕜 G) :
    ContRepresentation.IsUnitary (peterWeylBlockBiregular model) := by
  rw [ContRepresentation.isUnitary_iff_norm_map]
  intro a f
  rw [← Submodule.norm_coe, ← Submodule.norm_coe f, coe_peterWeylBlockBiregular_apply]
  exact (ContRepresentation.isUnitary_iff_norm_map _).mp (isUnitary_biregularLp 𝕜 G) a _

end CompactGroup

end TauCeti
