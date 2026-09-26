/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.PeterWeyl
public import TauCeti.RepresentationTheory.Compact.RegularRepresentation

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
of the `dᵢ²` basis ones. Those `dᵢ²` coefficients are in fact a basis of the block
(`TauCeti.peterWeylBlockBasis`), so the block is finite-dimensional of dimension `dᵢ²`, and
matching a matrix position with the matrix unit at that position identifies the block linearly
with `End(V_π)` (`TauCeti.endEquivPeterWeylBlock`).

Distinct blocks are orthogonal, by the second Schur orthogonality relation
(`TauCeti.ContRepresentation.schur_orthogonality`), and together they span `L²(G)` densely,
because their supremum is the span of the whole Peter-Weyl family. So `L²(G)` is the Hilbert sum
of the blocks (`TauCeti.isHilbertSum_peterWeylBlock`), whose `IsHilbertSum.linearIsometryEquiv` is
an isometry of `L²(G)` onto the `ℓ²` sum of the **block subspaces**. That, together with the
separate linear identification of each block with `End(V_π)` and the dimension count
`dim = (dim V_π)²`, is the isotypic decomposition `L²(G) ≅ ⨁̂_π End(V_π)` in the form proved here:
the isometry is not transported to an `ℓ²` sum of the spaces `End(V_π)` themselves, because
`Module.End` carries no inner product instance to express the Hilbert-Schmidt structure that would
make `TauCeti.endEquivPeterWeylBlock` an isometry, even though both bases involved are orthonormal.

The results about a single block -- the orthonormal family, the basis, the dimension, the
comparison with `End(V_π)` -- assume nothing about the rest of the family. Pairwise inequivalence
of the models is what makes distinct blocks orthogonal and independent, and exhaustiveness of the
skeleton enters exactly where density is claimed.

The blocks are stable under left and right translation
(`TauCeti.compMeasurePreserving_mulLeft_mem_peterWeylBlock` and
`TauCeti.rightRegularLp_mem_peterWeylBlock`), because translation carries matrix coefficients of a
model to matrix coefficients of the same model
(`TauCeti.ContRepresentation.matrixCoeff_comp_mulLeft` and
`TauCeti.ContRepresentation.matrixCoeff_comp_mulRight`). That the identification of a block with
`End(V_π)` is one of `G × G`-representations needs the tensor decomposition `V_π ⊗ V_π^*` and is
not proved here.

## Main definitions

* `TauCeti.peterWeylBlock`: the span in `L²(G)` of the matrix coefficients of one model.
* `TauCeti.peterWeylBlockBasis`: the basis of the block given by the `dᵢ²` normalized matrix
  coefficients of its model.
* `TauCeti.endEquivPeterWeylBlock`: **the block is a copy of `End(V_π)`**, matching the matrix
  unit at a position with the normalized matrix coefficient at that position.

## Main statements

* `TauCeti.peterWeylBlock_eq_span_range`: the block is already spanned by the `dᵢ²` normalized
  matrix coefficients of the Peter-Weyl family that belong to it.
* `TauCeti.finrank_peterWeylBlock`: **the block has dimension `dᵢ²`**.
* `TauCeti.toLp_star_character_mem_peterWeylBlock`: the conjugate character of a model lies in its
  own block, the trace direction of `End(V_π)`.
* `TauCeti.rightRegularLp_mem_peterWeylBlock` and
  `TauCeti.compMeasurePreserving_mulLeft_mem_peterWeylBlock`: **each block is stable under right
  and left translation**.
* `TauCeti.isOrtho_peterWeylBlock`, `TauCeti.orthogonalFamily_peterWeylBlock`: **distinct blocks
  are orthogonal**, so the blocks form an orthogonal family of subspaces, and
  `TauCeti.iSupIndep_peterWeylBlock` that they are independent.
* `TauCeti.iSup_peterWeylBlock_eq_span_peterWeylFamily`: their supremum is the span of the
  Peter-Weyl family.
* `TauCeti.orthogonal_iSup_peterWeylBlock_eq_bot` and
  `TauCeti.topologicalClosure_iSup_peterWeylBlock`: **the blocks are dense in `L²(G)`**, whence
  `TauCeti.isHilbertSum_peterWeylBlock`: `L²(G)` is the Hilbert sum of the blocks.

## References

* Daniel Bump, *Lie Groups*, second edition, Chapter 2.

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

/-! ### Stability under translation -/

/-- **Each block is stable under right translation**, that is, under the right regular
representation `TauCeti.rightRegularLp` of `G` on `L²(G)`: right translating a matrix coefficient of
a model absorbs the translation into its first vector
(`TauCeti.ContRepresentation.matrixCoeff_comp_mulRight`), so the translate is again a matrix
coefficient of the same model. -/
theorem rightRegularLp_mem_peterWeylBlock (models : ι → IrrepModel 𝕜 G) (i : ι) (g : G)
    {f : Lp 𝕜 2 (haarProb G)} (hf : f ∈ peterWeylBlock models i) :
    rightRegularLp 𝕜 G g f ∈ peterWeylBlock models i := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, w, rfl⟩ := hx
    rw [ContRepresentation.matrixCoeffLp_def, rightRegularLp_toLp,
      ContRepresentation.matrixCoeff_comp_mulRight, ← ContRepresentation.matrixCoeffLp_def]
    exact matrixCoeffLp_mem_peterWeylBlock models i _ _
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

/-- **Each block is stable under left translation**: left translating a matrix coefficient of a
unitary model moves the inverse translation onto its second vector
(`TauCeti.ContRepresentation.matrixCoeff_comp_mulLeft`), so the translate is again a matrix
coefficient of the same model.

Left translation is spelled as Mathlib's precomposition operator
`MeasureTheory.Lp.compMeasurePreserving`, which is also what `TauCeti.rightRegularLp_apply` unfolds
right translation to; the left regular representation of `G` on `L²(G)` is not in the library. -/
theorem compMeasurePreserving_mulLeft_mem_peterWeylBlock (models : ι → IrrepModel 𝕜 G) (i : ι)
    (g : G) {f : Lp 𝕜 2 (haarProb G)} (hf : f ∈ peterWeylBlock models i) :
    Lp.compMeasurePreserving (g * ·) (measurePreserving_mul_left (haarProb G) g) f ∈
      peterWeylBlock models i := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, w, rfl⟩ := hx
    have htranslate : Lp.compMeasurePreserving (g * ·) (measurePreserving_mul_left (haarProb G) g)
        (ContRepresentation.matrixCoeffLp (models i).rep (models i).continuous_rep v w) =
        ContRepresentation.matrixCoeffLp (models i).rep (models i).continuous_rep v
          ((models i).rep g⁻¹ w) := by
      rw [ContRepresentation.matrixCoeffLp_def, ContRepresentation.matrixCoeffLp_def,
        ← ContRepresentation.matrixCoeff_comp_mulLeft (models i).continuous_rep
          (models i).isUnitary v w g]
      exact Lp.compMeasurePreserving_toLp 𝕜 _ (ContinuousMap.mulLeft g)
        (measurePreserving_mul_left (haarProb G) g)
    rw [htranslate]
    exact matrixCoeffLp_mem_peterWeylBlock models i _ _
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    -- `Lp.compMeasurePreserving` is bundled as an `AddMonoidHom`, so its `𝕜`-linearity comes from
    -- the linear-map form of the same precomposition.
    have hsmul : Lp.compMeasurePreserving (g * ·) (measurePreserving_mul_left (haarProb G) g)
        (c • x) =
        c • Lp.compMeasurePreserving (g * ·) (measurePreserving_mul_left (haarProb G) g) x :=
      (Lp.compMeasurePreservingₗ 𝕜 (g * ·) (measurePreserving_mul_left (haarProb G) g)).map_smul c x
    rw [hsmul]
    exact Submodule.smul_mem _ c hx

/-! ### A block is a copy of the endomorphism algebra of its model -/

/-- The normalized matrix coefficients belonging to a single block are orthonormal. This is Schur
orthogonality for the single model `models i`, so no inequivalence hypothesis is involved: it is
`TauCeti.ContRepresentation.orthonormal_matrixCoeffLp` for the one-member family
`fun _ : Unit => models i`. -/
theorem orthonormal_peterWeylFamily_block [IsAlgClosed 𝕜] (models : ι → IrrepModel 𝕜 G) (i : ι) :
    Orthonormal 𝕜 fun p : Fin (models i).dim × Fin (models i).dim =>
      peterWeylFamily models ⟨i, p⟩ := by
  have h := (ContRepresentation.orthonormal_matrixCoeffLp (fun _ : Unit => (models i).rep)
      (fun _ => (models i).continuous_rep) (fun _ => (models i).isUnitary)
      (fun _ => (models i).isIrreducible) Subsingleton.pairwise
      fun _ => (models i).basis).comp
    (fun p : Fin (models i).dim × Fin (models i).dim => (⟨(), p⟩ : Σ _ : Unit, _))
    fun p q hpq => by simpa using hpq
  simpa [Function.comp_def] using h

/-- **The normalized matrix coefficients of a model are a basis of its block.** They span it by
`TauCeti.peterWeylBlock_eq_span_range` and are linearly independent because they are orthonormal
in `L²(G)`. -/
noncomputable def peterWeylBlockBasis [IsAlgClosed 𝕜] (models : ι → IrrepModel 𝕜 G) (i : ι) :
    Module.Basis (Fin (models i).dim × Fin (models i).dim) 𝕜 (peterWeylBlock models i) :=
  (Module.Basis.span (orthonormal_peterWeylFamily_block models i).linearIndependent).map
    (LinearEquiv.ofEq _ _ (peterWeylBlock_eq_span_range models i).symm)

@[simp]
theorem coe_peterWeylBlockBasis [IsAlgClosed 𝕜] (models : ι → IrrepModel 𝕜 G) (i : ι)
    (p : Fin (models i).dim × Fin (models i).dim) :
    (peterWeylBlockBasis models i p : Lp 𝕜 2 (haarProb G)) = peterWeylFamily models ⟨i, p⟩ := by
  rw [peterWeylBlockBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply]
  exact Module.Basis.coe_span_apply _ p

/-- **A Peter-Weyl block has dimension `dᵢ²`**, the `dᵢ²` normalized matrix coefficients of its
model being a basis. -/
theorem finrank_peterWeylBlock [IsAlgClosed 𝕜] (models : ι → IrrepModel 𝕜 G) (i : ι) :
    Module.finrank 𝕜 (peterWeylBlock models i) = (models i).dim ^ 2 := by
  rw [peterWeylBlock_eq_span_range,
    finrank_span_eq_card (orthonormal_peterWeylFamily_block models i).linearIndependent]
  simp [pow_two]

/-- **A Peter-Weyl block is a copy of the endomorphism algebra of its model.** The equivalence
carries the matrix unit at a matrix position, in the canonical basis of the model, to the
normalized matrix coefficient at that position. Both families are orthonormal -- the matrix units
for the Hilbert-Schmidt inner product, the coefficients in `L²(G)` by
`TauCeti.orthonormal_peterWeylFamily_block` -- but only the linear equivalence is recorded, since
`Module.End` carries no inner product. -/
noncomputable def endEquivPeterWeylBlock [IsAlgClosed 𝕜] (models : ι → IrrepModel 𝕜 G) (i : ι) :
    Module.End 𝕜 (EuclideanSpace 𝕜 (Fin (models i).dim)) ≃ₗ[𝕜] peterWeylBlock models i :=
  (Module.Basis.end (models i).basis.toBasis).equiv (peterWeylBlockBasis models i) (Equiv.refl _)

@[simp]
theorem coe_endEquivPeterWeylBlock_basis_end [IsAlgClosed 𝕜] (models : ι → IrrepModel 𝕜 G) (i : ι)
    (p : Fin (models i).dim × Fin (models i).dim) :
    (endEquivPeterWeylBlock models i (Module.Basis.end (models i).basis.toBasis p) :
        Lp 𝕜 2 (haarProb G)) = peterWeylFamily models ⟨i, p⟩ := by
  rw [endEquivPeterWeylBlock, Module.Basis.equiv_apply]
  simp

/-! ### Orthogonality of distinct blocks, and the Hilbert sum -/

section Orthogonality

variable {models : ι → IrrepModel 𝕜 G}

/-- **The Peter-Weyl blocks of two inequivalent models are orthogonal.** This is the second Schur
orthogonality relation: for inequivalent models, a matrix coefficient of one is `L²`-orthogonal to
every matrix coefficient of the other. Only the two models involved are constrained; the family
version is `TauCeti.orthogonalFamily_peterWeylBlock`. -/
theorem isOrtho_peterWeylBlock {i j : ι}
    (hne : IsEmpty (_root_.ContRepresentation.Equiv (models i).rep (models j).rep)) :
    peterWeylBlock models i ⟂ peterWeylBlock models j := by
  have hne' : IsEmpty (_root_.ContRepresentation.Equiv (models j).rep (models i).rep) :=
    ⟨fun e ↦ hne.elim e.symm⟩
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
      (models i).isIrreducible hne' v' w' v w
  exact hji.symm.le (Submodule.subset_span (Set.mem_singleton _))

/-- **The Peter-Weyl blocks of pairwise inequivalent models are an orthogonal family of subspaces
of `L²(G)`**, the form in which the Hilbert-sum decomposition of `L²(G)` consumes their
orthogonality. -/
theorem orthogonalFamily_peterWeylBlock
    (hne : Pairwise fun i j ↦
      IsEmpty (_root_.ContRepresentation.Equiv (models i).rep (models j).rep)) :
    OrthogonalFamily 𝕜 (fun i => (peterWeylBlock models i : Type _))
      fun i => (peterWeylBlock models i).subtypeₗᵢ :=
  OrthogonalFamily.of_pairwise fun _ _ hij => isOrtho_peterWeylBlock (hne hij)

/-- **The Peter-Weyl blocks of pairwise inequivalent models are independent**: the algebraic
direct sum of the blocks injects into `L²(G)`, so with
`TauCeti.topologicalClosure_iSup_peterWeylBlock` the decomposition of `L²(G)` into its blocks has
no collapsing. -/
theorem iSupIndep_peterWeylBlock
    (hne : Pairwise fun i j ↦
      IsEmpty (_root_.ContRepresentation.Equiv (models i).rep (models j).rep)) :
    iSupIndep (peterWeylBlock models) :=
  (orthogonalFamily_peterWeylBlock hne).independent

/-- **The Peter-Weyl blocks have vanishing orthogonal complement**, so they span `L²(G)`
densely. -/
theorem orthogonal_iSup_peterWeylBlock_eq_bot (h : IsIrrepSkeleton models) :
    (⨆ i, peterWeylBlock models i)ᗮ = ⊥ := by
  rw [iSup_peterWeylBlock_eq_span_peterWeylFamily]
  exact h.orthogonal_span_peterWeylFamily_eq_bot

/-- **The Peter-Weyl blocks are dense in `L²(G)`.** Exhaustiveness of the skeleton is what makes
this the whole of `L²(G)`. -/
theorem topologicalClosure_iSup_peterWeylBlock (h : IsIrrepSkeleton models) :
    (⨆ i, peterWeylBlock models i).topologicalClosure = ⊤ :=
  Submodule.topologicalClosure_eq_top_iff.2 (orthogonal_iSup_peterWeylBlock_eq_bot h)

/-- **`L²(G)` is the Hilbert sum of the Peter-Weyl blocks.** The blocks are pairwise orthogonal and
dense, so `IsHilbertSum.linearIsometryEquiv` is an isometry of `L²(G)` onto the `ℓ²` sum of the
block subspaces. This is the isotypic decomposition `L²(G) ≅ ⨁̂_π End(V_π)` up to the separate
linear identification `TauCeti.endEquivPeterWeylBlock` of the `π`-block with `End(V_π)`, which is
not an isometry statement: `Module.End` carries no inner product instance. -/
theorem isHilbertSum_peterWeylBlock (h : IsIrrepSkeleton models) :
    IsHilbertSum 𝕜 (fun i => (peterWeylBlock models i : Type _))
      fun i => (peterWeylBlock models i).subtypeₗᵢ :=
  IsHilbertSum.mkInternal _ (orthogonalFamily_peterWeylBlock h.pairwise_isEmpty_equiv)
    (topologicalClosure_iSup_peterWeylBlock h).ge

end Orthogonality

end TauCeti
