/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.PeterWeyl

/-!
# The isotypic blocks of `L²(G)`

The Peter-Weyl theorem (`TauCeti.peterWeylBasis`) exhibits a Hilbert basis of `L²(G)` indexed by
the matrix positions `Σ i, Fin dᵢ × Fin dᵢ` of a skeleton of the unitary dual of a compact group
`G`. Grouping those positions by the model they belong to splits `L²(G)` into one **block** for
each irreducible, and this file builds that splitting.

The `i`-th block `TauCeti.peterWeylBlock models i` is the span, inside `L²(G)`, of *all* matrix
coefficients of the `i`-th model -- not only the normalized basis ones. The two spans agree
(`TauCeti.peterWeylBlock_eq_span_range`), because expanding the two defining vectors in the
canonical orthonormal basis of the model writes an arbitrary matrix coefficient as a combination
of the `dᵢ²` basis ones. That identification is what makes the block finite-dimensional, of
dimension exactly `dᵢ²`, the dimension of `End(V_π)`.

Distinct blocks are orthogonal, by the second Schur orthogonality relation
(`TauCeti.ContRepresentation.schur_orthogonality`), and together they span `L²(G)` densely,
because their supremum is the span of the whole Peter-Weyl family. So `L²(G)` is the Hilbert sum
of the blocks: this is the statement `L²(G) ≅ ⨁̂_π End(V_π)`, with the `π`-block of dimension
`(dim V_π)²` spanned by `π`'s matrix coefficients.

What is *not* proved here is that the splitting is one of `G × G`-representations under left and
right translation. Translation carries matrix coefficients of a model to matrix coefficients of the
same model (`TauCeti.ContRepresentation.matrixCoeff_comp_mulLeft` and
`TauCeti.ContRepresentation.matrixCoeff_comp_mulRight`), so each block is translation-stable, but
the identification of the block with `End(V_π)` as a `G × G`-representation needs the tensor
decomposition `V_π ⊗ V_π^*` and is left for later.

## Main definitions

* `TauCeti.peterWeylBlock`: the span in `L²(G)` of the matrix coefficients of one model.

## Main statements

* `TauCeti.peterWeylBlock_eq_span_range`: the block is already spanned by the `dᵢ²` normalized
  matrix coefficients of the Peter-Weyl family that belong to it.
* `TauCeti.finrank_peterWeylBlock`: **the block has dimension `dᵢ²`**, and
  `TauCeti.finrank_peterWeylBlock_eq_finrank_end` reads that dimension as `finrank End(V_π)`.
* `TauCeti.toLp_star_character_mem_peterWeylBlock`: the conjugate character of a model lies in its
  own block, the trace direction of `End(V_π)`.
* `TauCeti.peterWeylBlock_isOrtho`, `TauCeti.orthogonalFamily_peterWeylBlock`: **distinct blocks
  are orthogonal**, so the blocks form an orthogonal family of subspaces, and
  `TauCeti.iSupIndep_peterWeylBlock` that they are independent.
* `TauCeti.iSup_peterWeylBlock_eq_span_peterWeylFamily`: their supremum is the span of the
  Peter-Weyl family.
* `TauCeti.orthogonal_iSup_peterWeylBlock_eq_bot` and
  `TauCeti.topologicalClosure_iSup_peterWeylBlock`: **the blocks are dense in `L²(G)`**, which
  with the orthogonality above is the Hilbert-sum decomposition.

## References

* Daniel Bump, *Lie Groups*, second edition, Chapter 2.
* [Compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
  Layer 5, "The isotypic decomposition".

## Tags

Peter-Weyl theorem, isotypic decomposition, matrix coefficient, compact group
-/

public section

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 G ι : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- **The `π`-block of `L²(G)`**: the span of the `L²` matrix coefficients of the `i`-th model of a
family. The vectors defining the coefficients range over the whole carrier, so nothing is fixed by
the choice of a basis; `TauCeti.peterWeylBlock_eq_span_range` says the `dᵢ²` normalized
coefficients of the Peter-Weyl family already span it. -/
noncomputable def peterWeylBlock (models : ι → IrrepModel 𝕜 G) (i : ι) :
    Submodule 𝕜 (Lp 𝕜 2 (haarProb G)) :=
  Submodule.span 𝕜
    {f | ∃ v w, f = ContRepresentation.matrixCoeffLp (models i).rep (models i).continuous_rep v w}

/-- Every `L²` matrix coefficient of the `i`-th model lies in the `i`-th block. -/
theorem matrixCoeffLp_mem_peterWeylBlock (models : ι → IrrepModel 𝕜 G) (i : ι)
    (v w : EuclideanSpace 𝕜 (Fin (models i).dim)) :
    ContRepresentation.matrixCoeffLp (models i).rep (models i).continuous_rep v w ∈
      peterWeylBlock models i :=
  Submodule.subset_span ⟨v, w, rfl⟩

/-- The Peter-Weyl family element at a matrix position of the `i`-th model lies in the `i`-th
block: it is a scalar multiple of a matrix coefficient of that model. -/
theorem peterWeylFamily_mem_peterWeylBlock (models : ι → IrrepModel 𝕜 G) (i : ι)
    (p : Fin (models i).dim × Fin (models i).dim) :
    peterWeylFamily models ⟨i, p⟩ ∈ peterWeylBlock models i := by
  rw [peterWeylFamily_apply]
  exact Submodule.smul_mem _ _ (matrixCoeffLp_mem_peterWeylBlock models i _ _)

/-- **The block is spanned by the normalized matrix coefficients it contains.** An arbitrary
matrix coefficient of a model is a combination of the `dᵢ²` coefficients at pairs of canonical
basis vectors, by sesquilinearity; that is
`TauCeti.matrixCoeffLp_mem_span_peterWeylFamily`, applied to the one-member family
`fun _ : Unit => models i`, whose Peter-Weyl family is exactly the part of this family's that
belongs to the `i`-th block. -/
theorem peterWeylBlock_eq_span_range (models : ι → IrrepModel 𝕜 G) (i : ι) :
    peterWeylBlock models i =
      Submodule.span 𝕜 (Set.range fun p : Fin (models i).dim × Fin (models i).dim =>
        peterWeylFamily models ⟨i, p⟩) := by
  have hrange : Set.range (peterWeylFamily fun _ : Unit => models i) =
      Set.range fun p : Fin (models i).dim × Fin (models i).dim =>
        peterWeylFamily models ⟨i, p⟩ := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro - ⟨x, rfl⟩
      exact ⟨x.2, by simp⟩
    · rintro - ⟨p, rfl⟩
      exact ⟨⟨(), p⟩, by simp⟩
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro - ⟨v, w, rfl⟩
    rw [SetLike.mem_coe, ← hrange]
    exact matrixCoeffLp_mem_span_peterWeylFamily (fun _ : Unit => models i) () v w
  · rintro - ⟨p, rfl⟩
    exact peterWeylFamily_mem_peterWeylBlock models i p

/-- **A Peter-Weyl block is finite-dimensional**, being spanned by the finitely many normalized
matrix coefficients of its model. -/
instance finiteDimensional_peterWeylBlock (models : ι → IrrepModel 𝕜 G) (i : ι) :
    FiniteDimensional 𝕜 (peterWeylBlock models i) := by
  rw [peterWeylBlock_eq_span_range]
  exact FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)

/-- **The conjugate character of a model lies in its own block.** It is the sum of the `dᵢ`
diagonal matrix coefficients (`TauCeti.ContRepresentation.star_character`), so it spans the trace
direction of the copy of `End(V_π)` that the block is; the conjugation is forced by Mathlib's
inner product being conjugate linear in its first argument. -/
theorem toLp_star_character_mem_peterWeylBlock (models : ι → IrrepModel 𝕜 G) (i : ι) :
    ContinuousMap.toLp 2 (haarProb G) 𝕜
        (star (ContRepresentation.character (models i).rep (models i).continuous_rep)) ∈
      peterWeylBlock models i := by
  rw [ContRepresentation.star_character _ _ (models i).basis, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [← ContRepresentation.matrixCoeffLp_def]
  exact matrixCoeffLp_mem_peterWeylBlock models i _ _

/-- The `i`-th block sits inside the span of the whole Peter-Weyl family. -/
theorem peterWeylBlock_le_span_peterWeylFamily (models : ι → IrrepModel 𝕜 G) (i : ι) :
    peterWeylBlock models i ≤ Submodule.span 𝕜 (Set.range (peterWeylFamily models)) :=
  Submodule.span_le.2 <| by
    rintro - ⟨v, w, rfl⟩
    exact matrixCoeffLp_mem_span_peterWeylFamily models i v w

/-- **The supremum of the blocks is the span of the Peter-Weyl family.** Each block is spanned by
matrix coefficients of a single model, and each family element belongs to the block of its own
model. -/
theorem iSup_peterWeylBlock_eq_span_peterWeylFamily (models : ι → IrrepModel 𝕜 G) :
    ⨆ i, peterWeylBlock models i = Submodule.span 𝕜 (Set.range (peterWeylFamily models)) := by
  refine le_antisymm (iSup_le fun i => peterWeylBlock_le_span_peterWeylFamily models i)
    (Submodule.span_le.2 ?_)
  rintro - ⟨x, rfl⟩
  exact Submodule.mem_iSup_of_mem x.1 (peterWeylFamily_mem_peterWeylBlock models x.1 x.2)

section Skeleton

variable {models : ι → IrrepModel 𝕜 G}

/-- The normalized matrix coefficients belonging to a single block are orthonormal: they are a
subfamily of the Peter-Weyl family, indexed injectively. -/
theorem IsIrrepSkeleton.orthonormal_peterWeylFamily_block [IsAlgClosed 𝕜]
    (h : IsIrrepSkeleton models) (i : ι) :
    Orthonormal 𝕜 fun p : Fin (models i).dim × Fin (models i).dim =>
      peterWeylFamily models ⟨i, p⟩ :=
  h.orthonormal_peterWeylFamily.comp (fun p => ⟨i, p⟩) fun p q hpq => by simpa using hpq

/-- **A Peter-Weyl block has dimension `dᵢ²`.** It is spanned by the `dᵢ²` normalized matrix
coefficients of its model, and those are orthonormal, hence linearly independent. -/
theorem finrank_peterWeylBlock [IsAlgClosed 𝕜] (h : IsIrrepSkeleton models) (i : ι) :
    Module.finrank 𝕜 (peterWeylBlock models i) = (models i).dim ^ 2 := by
  rw [peterWeylBlock_eq_span_range,
    finrank_span_eq_card (h.orthonormal_peterWeylFamily_block i).linearIndependent]
  simp [pow_two]

/-- **The dimension of a Peter-Weyl block is the dimension of the endomorphism algebra of its
model**, `dim End(V_π) = (dim V_π)²`: the block is the copy of `End(V_π)` inside `L²(G)` that the
isotypic decomposition `L²(G) ≅ ⨁̂_π End(V_π)` predicts. -/
theorem finrank_peterWeylBlock_eq_finrank_end [IsAlgClosed 𝕜] (h : IsIrrepSkeleton models)
    (i : ι) :
    Module.finrank 𝕜 (peterWeylBlock models i) =
      Module.finrank 𝕜 (Module.End 𝕜 (EuclideanSpace 𝕜 (Fin (models i).dim))) := by
  rw [finrank_peterWeylBlock h i, Module.finrank_linearMap, finrank_euclideanSpace_fin, sq]

/-- **Distinct Peter-Weyl blocks are orthogonal.** This is the second Schur orthogonality
relation: the models of a skeleton are pairwise inequivalent, so a matrix coefficient of one is
`L²`-orthogonal to every matrix coefficient of another. -/
theorem peterWeylBlock_isOrtho (h : IsIrrepSkeleton models) {i j : ι} (hij : i ≠ j) :
    peterWeylBlock models i ⟂ peterWeylBlock models j := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨v, w, rfl⟩
  have hji : peterWeylBlock models j ⟂
      Submodule.span 𝕜 {ContRepresentation.matrixCoeffLp (models i).rep
        (models i).continuous_rep v w} := by
    refine Submodule.span_le.2 ?_
    rintro - ⟨v', w', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact ContRepresentation.schur_orthogonality _ (models j).continuous_rep _
      (models i).continuous_rep (models i).isUnitary (models j).isIrreducible
      (models i).isIrreducible (h.pairwise_isEmpty_equiv (Ne.symm hij)) v' w' v w
  exact hji.symm.le (Submodule.subset_span (Set.mem_singleton _))

/-- **The Peter-Weyl blocks are an orthogonal family of subspaces of `L²(G)`**, the form in which
the Hilbert-sum decomposition of `L²(G)` consumes their orthogonality. -/
theorem orthogonalFamily_peterWeylBlock (h : IsIrrepSkeleton models) :
    OrthogonalFamily 𝕜 (fun i => (peterWeylBlock models i : Type _))
      fun i => (peterWeylBlock models i).subtypeₗᵢ :=
  OrthogonalFamily.of_pairwise fun _ _ hij => peterWeylBlock_isOrtho h hij

/-- **The Peter-Weyl blocks are independent**: the algebraic direct sum of the blocks injects into
`L²(G)`, so with `TauCeti.topologicalClosure_iSup_peterWeylBlock` the decomposition
`L²(G) ≅ ⨁̂_π End(V_π)` has no collapsing. -/
theorem iSupIndep_peterWeylBlock (h : IsIrrepSkeleton models) :
    iSupIndep (peterWeylBlock models) :=
  (orthogonalFamily_peterWeylBlock h).independent

/-- **The Peter-Weyl blocks have vanishing orthogonal complement**, so they span `L²(G)`
densely. -/
theorem orthogonal_iSup_peterWeylBlock_eq_bot (h : IsIrrepSkeleton models) :
    (⨆ i, peterWeylBlock models i)ᗮ = ⊥ := by
  rw [iSup_peterWeylBlock_eq_span_peterWeylFamily]
  exact h.orthogonal_span_peterWeylFamily_eq_bot

/-- **The Peter-Weyl blocks are dense in `L²(G)`.** With `TauCeti.orthogonalFamily_peterWeylBlock`
and `TauCeti.finrank_peterWeylBlock` this is the isotypic decomposition
`L²(G) ≅ ⨁̂_π End(V_π)`: `L²(G)` is the closure of the algebraic direct sum of pairwise orthogonal
blocks, the `π`-block of dimension `(dim V_π)²`. -/
theorem topologicalClosure_iSup_peterWeylBlock (h : IsIrrepSkeleton models) :
    (⨆ i, peterWeylBlock models i).topologicalClosure = ⊤ :=
  Submodule.topologicalClosure_eq_top_iff.2 (orthogonal_iSup_peterWeylBlock_eq_bot h)

end Skeleton

end TauCeti
