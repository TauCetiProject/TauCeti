/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Character.Projection
public import TauCeti.RepresentationTheory.Compact.PeterWeyl
public import TauCeti.RepresentationTheory.Compact.RegularRepresentation

/-!
# The isotypic blocks of `L²(G)`

The Peter-Weyl theorem (`TauCeti.peterWeylBasis`) exhibits a Hilbert basis of `L²(G)` indexed by
the matrix positions `Σ i, Fin dᵢ × Fin dᵢ` of a skeleton of the unitary dual of a compact group
`G`. Grouping those positions by the model they belong to splits `L²(G)` into one **block** for
each irreducible, and this file builds that splitting.

The block `TauCeti.peterWeylBlock model` of an irreducible model is the span, inside `L²(G)`, of
*all* matrix coefficients of that model -- not only the normalized basis ones. It depends on
nothing but the model, and in fact only on its equivalence class
(`TauCeti.peterWeylBlock_eq_of_equiv`); a family of models enters only where several blocks are
compared. The two
spans agree (`TauCeti.peterWeylBlock_eq_span_range`), because expanding the two defining vectors in
the canonical orthonormal basis of the model writes an arbitrary matrix coefficient as a
combination of the `dᵢ²` basis ones. Those `dᵢ²` coefficients are in fact an orthonormal basis of
the block (`TauCeti.peterWeylBlockOrthonormalBasis`), so the block is finite-dimensional of
dimension `dᵢ²`, and matching a matrix position with the matrix unit at that position identifies
the block with `End(V_π)` (`TauCeti.endEquivPeterWeylBlock`).

Distinct blocks are orthogonal, by the second Schur orthogonality relation
(`TauCeti.ContRepresentation.schur_orthogonality`), and together they span `L²(G)` densely,
because their supremum is the span of the whole Peter-Weyl family. So `L²(G)` is the Hilbert sum
of the blocks (`TauCeti.isHilbertSum_peterWeylBlock`), whose `IsHilbertSum.linearIsometryEquiv` is
an isometry of `L²(G)` onto the `ℓ²` sum of the **block subspaces**. Reading each block in its
orthonormal basis transports that isometry to the `ℓ²` sum of the endomorphism spaces of the
models (`TauCeti.isHilbertSum_euclideanSpace_peterWeylBlock`), an isometry of Hilbert spaces
`L²(G) ≅ ⨁̂_π End(V_π)`. The summand `End(V_π)` is spelled there as
`EuclideanSpace 𝕜 (Fin dᵢ × Fin dᵢ)`, the matrices in the canonical basis of the model with their
Hilbert-Schmidt inner product `⟪a, b⟫ = ∑ conj aⱼₖ * bⱼₖ`, because `Module.End` carries no inner
product instance in Mathlib. That spelling loses nothing:
`TauCeti.repr_endEquivPeterWeylBlock_basis_end` reads `TauCeti.endEquivPeterWeylBlock` in the
matrix units and finds the standard basis vectors, which are the orthonormal basis of the
Hilbert-Schmidt structure.

Each block also carries its **character projection** `TauCeti.peterWeylBlockProjection`, the
convolution operator of the kernel `dim V_π · conj χ_π`. Convolution moves the group argument of a
matrix coefficient, hence acts on the defining vectors of the coefficient through the integrated
operator of that kernel on the model's carrier; that operator is the identity on the model itself
and zero on an inequivalent one, so the projection is the identity on the `π`-block and kills every
other block. Its kernel being symmetric it is self-adjoint, and for a skeleton of the unitary dual
every element of `L²(G)` is carried into the `π`-block, so the projection *is* the orthogonal
projection of `L²(G)` onto that block (`TauCeti.peterWeylBlockProjection_eq_starProjection`). That
is the sense in which averaging against the character is the isotypic projector here: it is a
statement about the orthogonal projection onto a subspace of `L²(G)`, not about a `G`-isotypic
decomposition.

The results about a single block -- the orthonormal family, the basis, the dimension, the
comparison with `End(V_π)` -- assume nothing about the rest of the family. Pairwise inequivalence
of the models is what makes distinct blocks orthogonal and independent, and exhaustiveness of the
skeleton enters exactly where density is claimed.

## What is not proved here

Every statement in this file is a statement about Hilbert spaces, their subspaces, their isometries
and their bounded operators. The blocks are called *isotypic* because the `π`-block is spanned by
the matrix coefficients of `π` alone; that it is the `π`-isotypic component of a `G`-action, and
that the decomposition of `L²(G)` is one of unitary `G × G`-representations under left and right
translation, are statements about group actions and are **not** proved here. What is proved about
the action is that each block is stable under both translations
(`TauCeti.compMeasurePreserving_mulLeft_mem_peterWeylBlock` and
`TauCeti.rightRegularLp_mem_peterWeylBlock`), because translation carries matrix coefficients of a
model to matrix coefficients of the same model
(`TauCeti.ContRepresentation.matrixCoeff_comp_mulLeft` and
`TauCeti.ContRepresentation.matrixCoeff_comp_mulRight`). Equivariance of the identification of a
block with `End(V_π)` is not proved either, and what it needs is a `G × G`-action on each side:
bi-translation `((g, h) · f) x = f (g⁻¹ * x * h)` on `L²(G)`, of which only the right factor is in
the library (`TauCeti.rightRegularLp`), and `(g, h) · A = π g ∘ A ∘ π h⁻¹` on `End(V_π)`, together
with the proof that the identification intertwines them. No `G × G`-action is defined in the
library, and `TauCeti.endEquivPeterWeylBlock` is built from the canonical basis of the model, so
nothing is claimed here about its equivariance. The character projection
`TauCeti.peterWeylBlockProjection` *is* proved here, but not as an instance of
`TauCeti.ContRepresentation.isotypicProjector`: that projector is built from
`TauCeti.ContRepresentation.integratedOperator` for a *finite-dimensional* carrier and a
norm-continuous representation, while `L²(G)` is infinite-dimensional and its regular
representation is only strongly continuous (`TauCeti.continuous_rightRegularLp_apply`). The
averaging is carried out instead by `TauCeti.convolutionOperator`, which needs no continuity of the
action on `L²(G)`, and the integrated operator is used only on the finite-dimensional carrier of a
model, where it is available.

## Main definitions

* `TauCeti.peterWeylBlock`: the span in `L²(G)` of the matrix coefficients of one model.
* `TauCeti.peterWeylBlockOrthonormalBasis`: the orthonormal basis of the block given by the `dᵢ²`
  normalized matrix coefficients of its model; its `OrthonormalBasis.repr` is the isometry of the
  block onto the Hilbert-Schmidt space `EuclideanSpace 𝕜 (Fin dᵢ × Fin dᵢ)`.
* `TauCeti.endEquivPeterWeylBlock`: **the block is a copy of `End(V_π)`**, matching the matrix
  unit at a position with the normalized matrix coefficient at that position.
* `TauCeti.peterWeylBlockProjection`: **the character projection onto the block**, convolution
  against the kernel `dim V_π · conj χ_π`.

## Main statements

* `TauCeti.peterWeylBlock_eq_span_range`: the block is already spanned by the `dᵢ²` normalized
  matrix coefficients of the Peter-Weyl family that belong to it.
* `TauCeti.finrank_peterWeylBlock`: **the block has dimension `dᵢ²`**.
* `TauCeti.peterWeylBlock_eq_of_equiv` and `TauCeti.peterWeylBlockProjection_eq_of_equiv`: **the
  block and its character projection depend on the model only through its equivalence class**, so
  they identify the same isotypic component of `L²(G)` whichever model of `π` is chosen.
* `TauCeti.toLp_star_character_mem_peterWeylBlock`: the conjugate character of a model lies in its
  own block, the trace direction of `End(V_π)`.
* `TauCeti.rightRegularLp_mem_peterWeylBlock` and
  `TauCeti.compMeasurePreserving_mulLeft_mem_peterWeylBlock`: **each block is stable under right
  and left translation**.
* `TauCeti.isOrtho_peterWeylBlock`, `TauCeti.orthogonalFamily_peterWeylBlock`: **the blocks of
  inequivalent models are orthogonal**, so the blocks of a family of pairwise inequivalent models
  form an orthogonal family of subspaces, and `TauCeti.iSupIndep_peterWeylBlock` that they are
  independent.
* `TauCeti.iSup_peterWeylBlock_eq_span_peterWeylFamily`: their supremum is the span of the
  Peter-Weyl family.
* `TauCeti.orthogonal_iSup_peterWeylBlock_eq_bot` and
  `TauCeti.topologicalClosure_iSup_peterWeylBlock`: **the blocks are dense in `L²(G)`**, whence
  `TauCeti.isHilbertSum_peterWeylBlock`: `L²(G)` is the Hilbert sum of the blocks.
* `TauCeti.isHilbertSum_euclideanSpace_peterWeylBlock`: **`L²(G)` is isometrically the Hilbert sum
  of the endomorphism spaces of the models**, each carrying its Hilbert-Schmidt inner product.
* `TauCeti.peterWeylBlockProjection_apply_of_mem` and
  `TauCeti.peterWeylBlockProjection_apply_eq_zero_of_mem`: **the character projection is the
  identity on its own block and kills the block of an inequivalent model**, the two blockwise
  identities of the averaging kernel.
* `TauCeti.peterWeylBlockProjection_eq_starProjection` and
  `TauCeti.range_peterWeylBlockProjection`: **the character projection is the orthogonal projection
  of `L²(G)` onto the block**, whose range is therefore the block itself; this is the statement
  that the character averages are the isotypic projectors.

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

/-- **The `π`-block of `L²(G)`**: the span of the `L²` matrix coefficients of an irreducible model.
The vectors defining the coefficients range over the whole carrier, so nothing is fixed by the
choice of a basis; `TauCeti.peterWeylBlock_eq_span_range` says the `dᵢ²` normalized coefficients of
the Peter-Weyl family already span it. -/
noncomputable def peterWeylBlock (model : IrrepModel 𝕜 G) :
    Submodule 𝕜 (Lp 𝕜 2 (haarProb G)) :=
  Submodule.span 𝕜
    {f | ∃ v w, f = ContRepresentation.matrixCoeffLp model.rep model.continuous_rep v w}

/-- Every `L²` matrix coefficient of a model lies in its block. -/
@[simp]
theorem matrixCoeffLp_mem_peterWeylBlock (model : IrrepModel 𝕜 G)
    (v w : EuclideanSpace 𝕜 (Fin model.dim)) :
    ContRepresentation.matrixCoeffLp model.rep model.continuous_rep v w ∈
      peterWeylBlock model :=
  Submodule.subset_span ⟨v, w, rfl⟩

-- Not `@[simp]`: `TauCeti.peterWeylFamily_apply` is a `simp` lemma, so the left-hand side below is
-- not in `simp`-normal form and the `simpNF` linter rejects the tag. The normal form is reached by
-- `peterWeylFamily_apply` followed by `Submodule.smul_mem` and the `simp` lemma
-- `TauCeti.matrixCoeffLp_mem_peterWeylBlock`.
/-- The Peter-Weyl family element at a matrix position of the `i`-th model lies in the block of
that model: it is a scalar multiple of a matrix coefficient of it. -/
theorem peterWeylFamily_mem_peterWeylBlock (models : ι → IrrepModel 𝕜 G) (i : ι)
    (p : Fin (models i).dim × Fin (models i).dim) :
    peterWeylFamily models ⟨i, p⟩ ∈ peterWeylBlock (models i) := by
  rw [peterWeylFamily_apply]
  exact Submodule.smul_mem _ _ (matrixCoeffLp_mem_peterWeylBlock (models i) _ _)

/-- **The block is spanned by the normalized matrix coefficients it contains.** An arbitrary
matrix coefficient of a model is a combination of the `dᵢ²` coefficients at pairs of canonical
basis vectors, by sesquilinearity; that is
`TauCeti.matrixCoeffLp_mem_span_peterWeylFamily`, applied to the one-member family
`fun _ : Unit => models i`, whose Peter-Weyl family is exactly the part of this family's that
belongs to the `i`-th block. -/
theorem peterWeylBlock_eq_span_range (models : ι → IrrepModel 𝕜 G) (i : ι) :
    peterWeylBlock (models i) =
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
instance finiteDimensional_peterWeylBlock (model : IrrepModel 𝕜 G) :
    FiniteDimensional 𝕜 (peterWeylBlock model) := by
  rw [peterWeylBlock_eq_span_range (fun _ : Unit => model) ()]
  exact FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)

/-! ### A block depends only on the equivalence class of its model -/

/-- A matrix coefficient of a model is a matrix coefficient of any equivalent model: an equivalence
`φ` carries `⟪π x v, w⟫` to `⟪π' x (φ v), w⟫`, so running it backwards moves the first defining
vector by `φ.symm` and the second by the adjoint of `φ`, since `⟪φ u, w⟫ = ⟪u, φ† w⟫`.

This is the computation behind `TauCeti.peterWeylBlock_eq_of_equiv`. -/
private theorem matrixCoeffLp_eq_of_equiv {model model' : IrrepModel 𝕜 G}
    (φ : _root_.ContRepresentation.Equiv model.rep model'.rep)
    (v w : EuclideanSpace 𝕜 (Fin model'.dim)) :
    ContRepresentation.matrixCoeffLp model'.rep model'.continuous_rep v w =
      ContRepresentation.matrixCoeffLp model.rep model.continuous_rep (φ.symm v)
        (ContinuousLinearMap.adjoint φ.toContinuousLinearEquiv.toContinuousLinearMap w) := by
  rw [ContRepresentation.matrixCoeffLp_def, ContRepresentation.matrixCoeffLp_def]
  congr 1
  ext x
  rw [ContRepresentation.matrixCoeff_apply, ContRepresentation.matrixCoeff_apply,
    ContinuousLinearMap.adjoint_inner_right]
  congr 1
  rw [ContinuousLinearEquiv.coe_coe,
    _root_.ContRepresentation.Equiv.toContinuousLinearEquiv_apply,
    φ.toContIntertwiningMap.isIntertwining x (φ.symm v)]
  simp

/-- **A block depends on its model only through its equivalence class**: equivalent models have the
same matrix coefficients, hence the same block. -/
theorem peterWeylBlock_eq_of_equiv {model model' : IrrepModel 𝕜 G}
    (φ : _root_.ContRepresentation.Equiv model.rep model'.rep) :
    peterWeylBlock model = peterWeylBlock model' := by
  have key : ∀ {m m' : IrrepModel 𝕜 G} (_ : _root_.ContRepresentation.Equiv m.rep m'.rep),
      peterWeylBlock m' ≤ peterWeylBlock m := by
    intro m m' ψ
    refine Submodule.span_le.2 ?_
    rintro - ⟨v, w, rfl⟩
    rw [SetLike.mem_coe, matrixCoeffLp_eq_of_equiv ψ]
    exact matrixCoeffLp_mem_peterWeylBlock m _ _
  exact le_antisymm (key φ.symm) (key φ)

/-- **The conjugate character of a model lies in its own block.** It is the sum of the `dᵢ`
diagonal matrix coefficients (`TauCeti.ContRepresentation.star_character`), so it spans the trace
direction of the copy of `End(V_π)` that the block is; the conjugation is forced by Mathlib's
inner product being conjugate linear in its first argument. -/
theorem toLp_star_character_mem_peterWeylBlock (model : IrrepModel 𝕜 G) :
    ContinuousMap.toLp 2 (haarProb G) 𝕜
        (star (ContRepresentation.character model.rep model.continuous_rep)) ∈
      peterWeylBlock model := by
  rw [ContRepresentation.star_character _ _ model.basis, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [← ContRepresentation.matrixCoeffLp_def]
  exact matrixCoeffLp_mem_peterWeylBlock model _ _

/-- The block of the `i`-th model sits inside the span of the whole Peter-Weyl family. -/
theorem peterWeylBlock_le_span_peterWeylFamily (models : ι → IrrepModel 𝕜 G) (i : ι) :
    peterWeylBlock (models i) ≤ Submodule.span 𝕜 (Set.range (peterWeylFamily models)) :=
  Submodule.span_le.2 <| by
    rintro - ⟨v, w, rfl⟩
    exact matrixCoeffLp_mem_span_peterWeylFamily models i v w

/-- **The supremum of the blocks is the span of the Peter-Weyl family.** Each block is spanned by
matrix coefficients of a single model, and each family element belongs to the block of its own
model. -/
theorem iSup_peterWeylBlock_eq_span_peterWeylFamily (models : ι → IrrepModel 𝕜 G) :
    ⨆ i, peterWeylBlock (models i) = Submodule.span 𝕜 (Set.range (peterWeylFamily models)) := by
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
theorem rightRegularLp_mem_peterWeylBlock (model : IrrepModel 𝕜 G) (g : G)
    {f : Lp 𝕜 2 (haarProb G)} (hf : f ∈ peterWeylBlock model) :
    rightRegularLp 𝕜 G g f ∈ peterWeylBlock model := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, w, rfl⟩ := hx
    rw [ContRepresentation.matrixCoeffLp_def, rightRegularLp_toLp,
      ContRepresentation.matrixCoeff_comp_mulRight, ← ContRepresentation.matrixCoeffLp_def]
    exact matrixCoeffLp_mem_peterWeylBlock model _ _
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
theorem compMeasurePreserving_mulLeft_mem_peterWeylBlock (model : IrrepModel 𝕜 G)
    (g : G) {f : Lp 𝕜 2 (haarProb G)} (hf : f ∈ peterWeylBlock model) :
    Lp.compMeasurePreserving (g * ·) (measurePreserving_mul_left (haarProb G) g) f ∈
      peterWeylBlock model := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, w, rfl⟩ := hx
    have htranslate : Lp.compMeasurePreserving (g * ·) (measurePreserving_mul_left (haarProb G) g)
        (ContRepresentation.matrixCoeffLp model.rep model.continuous_rep v w) =
        ContRepresentation.matrixCoeffLp model.rep model.continuous_rep v
          (model.rep g⁻¹ w) := by
      rw [ContRepresentation.matrixCoeffLp_def, ContRepresentation.matrixCoeffLp_def,
        ← ContRepresentation.matrixCoeff_comp_mulLeft model.continuous_rep
          model.isUnitary v w g]
      exact Lp.compMeasurePreserving_toLp 𝕜 _ (ContinuousMap.mulLeft g)
        (measurePreserving_mul_left (haarProb G) g)
    rw [htranslate]
    exact matrixCoeffLp_mem_peterWeylBlock model _ _
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

/-- **The normalized matrix coefficients of a model are an orthonormal basis of its block.** They
span it by `TauCeti.peterWeylBlock_eq_span_range` and are orthonormal by
`TauCeti.orthonormal_peterWeylFamily_block`. Its `OrthonormalBasis.repr` is the resulting isometry
of the block onto `EuclideanSpace 𝕜 (Fin dᵢ × Fin dᵢ)`, the `dᵢ × dᵢ` matrices carrying the
Hilbert-Schmidt inner product. -/
noncomputable def peterWeylBlockOrthonormalBasis [IsAlgClosed 𝕜] (model : IrrepModel 𝕜 G) :
    OrthonormalBasis (Fin model.dim × Fin model.dim) 𝕜 (peterWeylBlock model) :=
  OrthonormalBasis.mk
    (v := fun p => ⟨peterWeylFamily (fun _ : Unit => model) ⟨(), p⟩,
      peterWeylFamily_mem_peterWeylBlock (fun _ : Unit => model) () p⟩)
    (by
      rw [← (peterWeylBlock model).subtypeₗᵢ.orthonormal_comp_iff]
      simpa [Function.comp_def] using
        orthonormal_peterWeylFamily_block (fun _ : Unit => model) ())
    (by
      have hmap : Submodule.map (peterWeylBlock model).subtype
          (Submodule.span 𝕜 (Set.range fun p : Fin model.dim × Fin model.dim =>
            (⟨peterWeylFamily (fun _ : Unit => model) ⟨(), p⟩,
              peterWeylFamily_mem_peterWeylBlock (fun _ : Unit => model) () p⟩ :
              peterWeylBlock model))) =
          Submodule.map (peterWeylBlock model).subtype ⊤ := by
        rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
        exact (peterWeylBlock_eq_span_range (fun _ : Unit => model) ()).symm
      exact (Submodule.map_injective_of_injective (peterWeylBlock model).injective_subtype
        hmap).ge)

@[simp]
theorem coe_peterWeylBlockOrthonormalBasis [IsAlgClosed 𝕜] (models : ι → IrrepModel 𝕜 G) (i : ι)
    (p : Fin (models i).dim × Fin (models i).dim) :
    (peterWeylBlockOrthonormalBasis (models i) p : Lp 𝕜 2 (haarProb G)) =
      peterWeylFamily models ⟨i, p⟩ := by
  rw [peterWeylBlockOrthonormalBasis, OrthonormalBasis.coe_mk]
  simp

/-- **A Peter-Weyl block has dimension `dᵢ²`**, the `dᵢ²` normalized matrix coefficients of its
model being a basis. -/
theorem finrank_peterWeylBlock [IsAlgClosed 𝕜] (model : IrrepModel 𝕜 G) :
    Module.finrank 𝕜 (peterWeylBlock model) = model.dim ^ 2 := by
  rw [peterWeylBlock_eq_span_range (fun _ : Unit => model) (),
    finrank_span_eq_card
      (orthonormal_peterWeylFamily_block (fun _ : Unit => model) ()).linearIndependent]
  simp [pow_two]

/-- **A Peter-Weyl block is a copy of the endomorphism algebra of its model.** The equivalence
carries the matrix unit at a matrix position, in the canonical basis of the model, to the
normalized matrix coefficient at that position. Both families are orthonormal -- the matrix units
for the Hilbert-Schmidt inner product, the coefficients in `L²(G)` by
`TauCeti.orthonormal_peterWeylFamily_block` -- so this is the Hilbert-Schmidt isometry, read in
the matrix units by `TauCeti.repr_endEquivPeterWeylBlock_basis_end`; it is recorded as a linear
equivalence because `Module.End` carries no inner product instance. -/
noncomputable def endEquivPeterWeylBlock [IsAlgClosed 𝕜] (model : IrrepModel 𝕜 G) :
    Module.End 𝕜 (EuclideanSpace 𝕜 (Fin model.dim)) ≃ₗ[𝕜] peterWeylBlock model :=
  (Module.Basis.end model.basis.toBasis).equiv
    (peterWeylBlockOrthonormalBasis model).toBasis (Equiv.refl _)

@[simp]
theorem coe_endEquivPeterWeylBlock_basis_end [IsAlgClosed 𝕜] (models : ι → IrrepModel 𝕜 G) (i : ι)
    (p : Fin (models i).dim × Fin (models i).dim) :
    (endEquivPeterWeylBlock (models i) (Module.Basis.end (models i).basis.toBasis p) :
        Lp 𝕜 2 (haarProb G)) = peterWeylFamily models ⟨i, p⟩ := by
  rw [endEquivPeterWeylBlock, Module.Basis.equiv_apply]
  simp

/-- **The comparison with `End(V_π)` is the Hilbert-Schmidt identification**: it carries the matrix
unit at a position to the block vector whose coordinate in the orthonormal basis of the block is
the standard basis vector at that position. -/
@[simp]
theorem repr_endEquivPeterWeylBlock_basis_end [IsAlgClosed 𝕜] (model : IrrepModel 𝕜 G)
    (p : Fin model.dim × Fin model.dim) :
    (peterWeylBlockOrthonormalBasis model).repr
        (endEquivPeterWeylBlock model (Module.Basis.end model.basis.toBasis p)) =
      EuclideanSpace.single p 1 := by
  rw [endEquivPeterWeylBlock, Module.Basis.equiv_apply, Equiv.refl_apply,
    OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_self]

/-! ### Orthogonality of distinct blocks, and the Hilbert sum -/

/-- **The Peter-Weyl blocks of two inequivalent models are orthogonal.** This is the second Schur
orthogonality relation: for inequivalent models, a matrix coefficient of one is `L²`-orthogonal to
every matrix coefficient of the other. Only the two models involved are constrained; the family
version is `TauCeti.orthogonalFamily_peterWeylBlock`. -/
theorem isOrtho_peterWeylBlock {model model' : IrrepModel 𝕜 G}
    (hne : IsEmpty (_root_.ContRepresentation.Equiv model.rep model'.rep)) :
    peterWeylBlock model ⟂ peterWeylBlock model' := by
  refine Submodule.isOrtho_span.2 ?_
  rintro - ⟨v, w, rfl⟩ - ⟨v', w', rfl⟩
  exact ContRepresentation.schur_orthogonality _ model.continuous_rep _ model'.continuous_rep
    model'.isUnitary model.isIrreducible model'.isIrreducible hne v w v' w'

section Orthogonality

variable {models : ι → IrrepModel 𝕜 G}

/-- **The Peter-Weyl blocks of pairwise inequivalent models are an orthogonal family of subspaces
of `L²(G)`**, the form in which the Hilbert-sum decomposition of `L²(G)` consumes their
orthogonality. -/
theorem orthogonalFamily_peterWeylBlock
    (hne : Pairwise fun i j ↦
      IsEmpty (_root_.ContRepresentation.Equiv (models i).rep (models j).rep)) :
    OrthogonalFamily 𝕜 (fun i => (peterWeylBlock (models i) : Type _))
      fun i => (peterWeylBlock (models i)).subtypeₗᵢ :=
  OrthogonalFamily.of_pairwise fun _ _ hij => isOrtho_peterWeylBlock (hne hij)

/-- **The Peter-Weyl blocks of pairwise inequivalent models are independent**: the algebraic
direct sum of the blocks injects into `L²(G)`, so with
`TauCeti.topologicalClosure_iSup_peterWeylBlock` the decomposition of `L²(G)` into its blocks has
no collapsing. -/
theorem iSupIndep_peterWeylBlock
    (hne : Pairwise fun i j ↦
      IsEmpty (_root_.ContRepresentation.Equiv (models i).rep (models j).rep)) :
    iSupIndep fun i => peterWeylBlock (models i) :=
  (orthogonalFamily_peterWeylBlock hne).independent

/-- **The Peter-Weyl blocks have vanishing orthogonal complement**, so they span `L²(G)`
densely. -/
theorem orthogonal_iSup_peterWeylBlock_eq_bot (h : IsIrrepSkeleton models) :
    (⨆ i, peterWeylBlock (models i))ᗮ = ⊥ := by
  rw [iSup_peterWeylBlock_eq_span_peterWeylFamily]
  exact h.orthogonal_span_peterWeylFamily_eq_bot

/-- **The Peter-Weyl blocks are dense in `L²(G)`.** Exhaustiveness of the skeleton is what makes
this the whole of `L²(G)`. -/
theorem topologicalClosure_iSup_peterWeylBlock (h : IsIrrepSkeleton models) :
    (⨆ i, peterWeylBlock (models i)).topologicalClosure = ⊤ :=
  Submodule.topologicalClosure_eq_top_iff.2 (orthogonal_iSup_peterWeylBlock_eq_bot h)

/-- **`L²(G)` is the Hilbert sum of the Peter-Weyl blocks.** The blocks are pairwise orthogonal and
dense, so `IsHilbertSum.linearIsometryEquiv` is an isometry of `L²(G)` onto the `ℓ²` sum of the
block subspaces. `TauCeti.endEquivPeterWeylBlock` identifies the `π`-block linearly with
`End(V_π)`; the isometric form of that identification, with the Hilbert-Schmidt structure on the
summands, is `TauCeti.isHilbertSum_euclideanSpace_peterWeylBlock`. -/
theorem isHilbertSum_peterWeylBlock (h : IsIrrepSkeleton models) :
    IsHilbertSum 𝕜 (fun i => (peterWeylBlock (models i) : Type _))
      fun i => (peterWeylBlock (models i)).subtypeₗᵢ :=
  IsHilbertSum.mkInternal _ (orthogonalFamily_peterWeylBlock h.pairwise_isEmpty_equiv)
    (topologicalClosure_iSup_peterWeylBlock h).ge

/-- **`L²(G)` is isometrically the Hilbert sum of the endomorphism spaces of the models**, the
Hilbert-space decomposition `L²(G) ≅ ⨁̂_π End(V_π)`: reading each block in its orthonormal basis
`TauCeti.peterWeylBlockOrthonormalBasis` turns `TauCeti.isHilbertSum_peterWeylBlock` into a Hilbert
sum whose summands are the endomorphism spaces of the models themselves, so that
`IsHilbertSum.linearIsometryEquiv` is an isometry of `L²(G)` onto their `ℓ²` sum. The summand for
the `i`-th model is spelled `EuclideanSpace 𝕜 (Fin dᵢ × Fin dᵢ)`: its matrices in the canonical
basis of the model, carrying the Hilbert-Schmidt inner product that `Module.End` has no instance
for; `TauCeti.repr_endEquivPeterWeylBlock_basis_end` identifies that spelling with
`TauCeti.endEquivPeterWeylBlock`. This is an isometry of Hilbert spaces; that it is one of
`G × G`-representations is not proved here (see the module docstring). -/
theorem isHilbertSum_euclideanSpace_peterWeylBlock [IsAlgClosed 𝕜] (h : IsIrrepSkeleton models) :
    IsHilbertSum 𝕜 (fun i => EuclideanSpace 𝕜 (Fin (models i).dim × Fin (models i).dim))
      fun i => (peterWeylBlock (models i)).subtypeₗᵢ.comp
        (peterWeylBlockOrthonormalBasis (models i)).repr.symm.toLinearIsometry := by
  refine IsHilbertSum.mk (fun i j hij v w => ?_) ?_
  · exact orthogonalFamily_peterWeylBlock h.pairwise_isEmpty_equiv hij
      ((peterWeylBlockOrthonormalBasis (models i)).repr.symm v)
      ((peterWeylBlockOrthonormalBasis (models j)).repr.symm w)
  · have hrange : ∀ i, LinearMap.range (((peterWeylBlock (models i)).subtypeₗᵢ.comp
        (peterWeylBlockOrthonormalBasis (models i)).repr.symm.toLinearIsometry).toLinearMap) =
        peterWeylBlock (models i) := by
      intro i
      refine le_antisymm ?_ ?_
      · rintro - ⟨v, rfl⟩
        exact ((peterWeylBlockOrthonormalBasis (models i)).repr.symm v).2
      · intro x hx
        exact ⟨(peterWeylBlockOrthonormalBasis (models i)).repr ⟨x, hx⟩, by simp⟩
    simp only [hrange]
    exact (topologicalClosure_iSup_peterWeylBlock h).ge

end Orthogonality

/-! ### The character projection onto a block

Averaging the right translations of `L²(G)` against the kernel `dim V_π · conj χ_π` projects
`L²(G)` onto the `π`-block. The averaging is convolution (`TauCeti.convolutionOperator`), which is
bounded on `L²(G)` for a continuous kernel and needs no continuity of the action of `G` on `L²(G)`;
on a matrix coefficient it moves the group argument, so it acts through the integrated operator of
the same kernel on the finite-dimensional carrier of the model, where the character identities of
`TauCeti/RepresentationTheory/Compact/Character/Projection.lean` evaluate it. -/

/-- Convolving a matrix coefficient of a model against a continuous kernel `k` gives the matrix
coefficient at the same first vector and at the second vector moved by the integrated operator of
`k` on the model's carrier.

This is the computation behind `TauCeti.peterWeylBlockProjection`, and it is where the unitarity of
the model is used: convolution translates the group argument of the coefficient, and for a unitary
action the translation may be moved from the first vector to the second. -/
private theorem convolutionOperator_matrixCoeffLp (model : IrrepModel 𝕜 G) (k : C(G, 𝕜))
    (v w : EuclideanSpace 𝕜 (Fin model.dim)) :
    convolutionOperator k (ContRepresentation.matrixCoeffLp model.rep model.continuous_rep v w)
      = ContRepresentation.matrixCoeffLp model.rep model.continuous_rep v
          (ContRepresentation.integratedOperator model.rep model.continuous_rep k w) := by
  have hint : Integrable (fun g : G => k g • model.rep g w) (haarProb G) :=
    integrable_continuousMap G ⟨fun g => k g • model.rep g w,
      k.continuous.smul (model.continuous_rep.clm_apply continuous_const)⟩
  rw [ContRepresentation.matrixCoeffLp_def, convolutionOperator_apply,
    ContRepresentation.matrixCoeffLp_def]
  congr 1
  ext x
  rw [convolutionCLM_toLp_apply, ContRepresentation.matrixCoeff_apply,
    ContRepresentation.integratedOperator_apply, ← integral_inner hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  -- `integral_congr_ae` leaves the two integrands applied but unreduced.
  beta_reduce
  have hmul : model.rep (z⁻¹ * x) v = model.rep z⁻¹ (model.rep x v) := by simp [map_mul]
  rw [ContRepresentation.matrixCoeff_apply, hmul, inner_smul_right,
    model.isUnitary.inner_map_left z⁻¹ (model.rep x v) w, inv_inv]

/-- **The character projection onto the `π`-block**: convolution against the kernel
`dim V_π · conj χ_π`.

It is the identity on the `π`-block (`TauCeti.peterWeylBlockProjection_apply_of_mem`) and kills the
block of an inequivalent model (`TauCeti.peterWeylBlockProjection_apply_eq_zero_of_mem`), because
the integrated operator of that kernel on the carrier of a model is the identity for `π` itself and
zero for an inequivalent one. For a skeleton of the unitary dual those two identities make it the
orthogonal projection of `L²(G)` onto the block
(`TauCeti.peterWeylBlockProjection_eq_starProjection`). -/
noncomputable def peterWeylBlockProjection (model : IrrepModel 𝕜 G) :
    Lp 𝕜 2 (haarProb G) →L[𝕜] Lp 𝕜 2 (haarProb G) :=
  convolutionOperator ((model.dim : 𝕜) •
    star (ContRepresentation.character model.rep model.continuous_rep))

/-- The character projection is convolution against the kernel `dim V_π · conj χ_π`. -/
theorem peterWeylBlockProjection_def (model : IrrepModel 𝕜 G) :
    peterWeylBlockProjection model =
      convolutionOperator ((model.dim : 𝕜) •
        star (ContRepresentation.character model.rep model.continuous_rep)) :=
  (rfl)

/-- **The character projection depends on its model only through its equivalence class**: its
kernel is built from the dimension and the character, and equivalent models share both -- the
dimension because an equivalence is a linear isomorphism of the carriers, the character because it
is a trace, invariant under conjugation (`Representation.char_iso`). -/
theorem peterWeylBlockProjection_eq_of_equiv {model model' : IrrepModel 𝕜 G}
    (φ : _root_.ContRepresentation.Equiv model.rep model'.rep) :
    peterWeylBlockProjection model = peterWeylBlockProjection model' := by
  have hdim : model.dim = model'.dim := by
    simpa using φ.toContinuousLinearEquiv.toLinearEquiv.finrank_eq
  have hrep : Representation.Equiv model.rep.toRepresentation model'.rep.toRepresentation :=
    Representation.Equiv.mk φ.toContinuousLinearEquiv.toLinearEquiv fun g =>
      LinearMap.ext fun v => φ.toContIntertwiningMap.isIntertwining g v
  have hchar : ContRepresentation.character model.rep model.continuous_rep =
      ContRepresentation.character model'.rep model'.continuous_rep := by
    refine ContinuousMap.ext fun g => ?_
    rw [congrFun (ContRepresentation.coe_character model.rep model.continuous_rep) g,
      congrFun (ContRepresentation.coe_character model'.rep model'.continuous_rep) g]
    exact congrFun (Representation.char_iso hrep) g
  rw [peterWeylBlockProjection_def, peterWeylBlockProjection_def, hchar, hdim]

/-- **The character projection fixes the matrix coefficients of its own model.** The kernel
`dim V_π · conj χ_π` acts on the carrier of `π` as the identity, by
`TauCeti.ContRepresentation.finrank_smul_integratedOperator_star_character_self`. -/
@[simp]
theorem peterWeylBlockProjection_matrixCoeffLp_self [IsAlgClosed 𝕜] (model : IrrepModel 𝕜 G)
    (v w : EuclideanSpace 𝕜 (Fin model.dim)) :
    peterWeylBlockProjection model
        (ContRepresentation.matrixCoeffLp model.rep model.continuous_rep v w)
      = ContRepresentation.matrixCoeffLp model.rep model.continuous_rep v w := by
  have hop : ContRepresentation.integratedOperator model.rep model.continuous_rep
      ((model.dim : 𝕜) • star (ContRepresentation.character model.rep model.continuous_rep))
      = ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin model.dim)) := by
    rw [ContRepresentation.integratedOperator_smul]
    simpa using ContRepresentation.finrank_smul_integratedOperator_star_character_self
      model.rep model.continuous_rep model.isUnitary model.isIrreducible
  rw [peterWeylBlockProjection, convolutionOperator_matrixCoeffLp, hop]
  simp

/-- **The character projection kills the matrix coefficients of an inequivalent model.** The kernel
`dim V_π · conj χ_π` acts as zero on the carrier of an irreducible model inequivalent to `π`, by
`TauCeti.ContRepresentation.integratedOperator_star_character_eq_zero`; Schur's lemma is what turns
inequivalence into the vanishing of every intertwiner. -/
@[simp]
theorem peterWeylBlockProjection_matrixCoeffLp_eq_zero [IsAlgClosed 𝕜]
    {model model' : IrrepModel 𝕜 G}
    (hne : IsEmpty (_root_.ContRepresentation.Equiv model.rep model'.rep))
    (v w : EuclideanSpace 𝕜 (Fin model'.dim)) :
    peterWeylBlockProjection model
        (ContRepresentation.matrixCoeffLp model'.rep model'.continuous_rep v w) = 0 := by
  have hne' : IsEmpty (_root_.ContRepresentation.Equiv model'.rep model.rep) :=
    ⟨fun φ => hne.false φ.symm⟩
  have hop : ContRepresentation.integratedOperator model'.rep model'.continuous_rep
      ((model.dim : 𝕜) • star (ContRepresentation.character model.rep model.continuous_rep))
      = 0 := by
    rw [ContRepresentation.integratedOperator_smul,
      ContRepresentation.integratedOperator_star_character_eq_zero model.rep model.continuous_rep
        model'.rep model'.continuous_rep model.isUnitary model'.isIrreducible
        (fun φ => by
          simp [ContRepresentation.eq_zero_of_isEmpty_equiv model'.isIrreducible
            model.isIrreducible hne' φ]),
      smul_zero]
  rw [peterWeylBlockProjection, convolutionOperator_matrixCoeffLp, hop]
  simp

/-- **The character projection is the identity on its own block**, the block being spanned by the
matrix coefficients of its model. -/
theorem peterWeylBlockProjection_apply_of_mem [IsAlgClosed 𝕜] (model : IrrepModel 𝕜 G)
    {f : Lp 𝕜 2 (haarProb G)} (hf : f ∈ peterWeylBlock model) :
    peterWeylBlockProjection model f = f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, w, rfl⟩ := hx
    exact peterWeylBlockProjection_matrixCoeffLp_self model v w
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

/-- **The character projection kills the block of an inequivalent model.** -/
theorem peterWeylBlockProjection_apply_eq_zero_of_mem [IsAlgClosed 𝕜]
    {model model' : IrrepModel 𝕜 G}
    (hne : IsEmpty (_root_.ContRepresentation.Equiv model.rep model'.rep))
    {f : Lp 𝕜 2 (haarProb G)} (hf : f ∈ peterWeylBlock model') :
    peterWeylBlockProjection model f = 0 := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, w, rfl⟩ := hx
    exact peterWeylBlockProjection_matrixCoeffLp_eq_zero hne v w
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]

/-- **The character projection is self-adjoint.** Its kernel is symmetric in the sense of
`TauCeti.isSelfAdjoint_convolutionOperator`, because the character of a unitary representation at an
inverse is the conjugate of its value. -/
theorem isSelfAdjoint_peterWeylBlockProjection (model : IrrepModel 𝕜 G) :
    IsSelfAdjoint (peterWeylBlockProjection model) :=
  isSelfAdjoint_convolutionOperator _ fun g => by
    simp [ContRepresentation.character_apply_inv model.rep model.continuous_rep model.isUnitary g]

section Projection

variable {models : ι → IrrepModel 𝕜 G}

/-- **The character projection maps the whole of `L²(G)` into its block.** The preimage of the
block is a closed subspace, the block being finite-dimensional, and it contains every block of the
skeleton: its own by `TauCeti.peterWeylBlockProjection_apply_of_mem`, the others by
`TauCeti.peterWeylBlockProjection_apply_eq_zero_of_mem`. Since the blocks of a skeleton are dense
(`TauCeti.topologicalClosure_iSup_peterWeylBlock`), that preimage is everything; this is where
exhaustiveness of the skeleton enters. -/
theorem peterWeylBlockProjection_apply_mem_peterWeylBlock [IsAlgClosed 𝕜]
    (h : IsIrrepSkeleton models) (i : ι) (f : Lp 𝕜 2 (haarProb G)) :
    peterWeylBlockProjection (models i) f ∈ peterWeylBlock (models i) := by
  set K := (peterWeylBlock (models i)).comap
    (peterWeylBlockProjection (models i)).toLinearMap with hK
  have hclosed : IsClosed (K : Set (Lp 𝕜 2 (haarProb G))) :=
    ((peterWeylBlock (models i)).closed_of_finiteDimensional).preimage
      (peterWeylBlockProjection (models i)).continuous
  have hle : ⨆ j, peterWeylBlock (models j) ≤ K := by
    refine iSup_le fun j x hx => Submodule.mem_comap.2 ?_
    rw [ContinuousLinearMap.coe_coe]
    rcases eq_or_ne j i with rfl | hji
    · rw [peterWeylBlockProjection_apply_of_mem (models j) hx]
      exact hx
    · rw [peterWeylBlockProjection_apply_eq_zero_of_mem
        (h.pairwise_isEmpty_equiv (Ne.symm hji)) hx]
      exact Submodule.zero_mem _
  have htop : (⊤ : Submodule 𝕜 (Lp 𝕜 2 (haarProb G))) ≤ K :=
    (topologicalClosure_iSup_peterWeylBlock h).ge.trans
      (Submodule.topologicalClosure_minimal _ hle hclosed)
  exact htop (Submodule.mem_top (x := f))

/-- **The character projection is the orthogonal projection onto its block**: averaging against
`dim V_π · conj χ_π` is the isotypic projector of `π`, in the Hilbert-space sense that its value is
the component of `f` in the `π`-block. It lands in the block by
`TauCeti.peterWeylBlockProjection_apply_mem_peterWeylBlock`, and what it removes is orthogonal to
the block because the projection is self-adjoint and fixes the block. -/
theorem peterWeylBlockProjection_eq_starProjection [IsAlgClosed 𝕜] (h : IsIrrepSkeleton models)
    (i : ι) :
    peterWeylBlockProjection (models i) = (peterWeylBlock (models i)).starProjection := by
  refine ContinuousLinearMap.ext fun f => (Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (peterWeylBlockProjection_apply_mem_peterWeylBlock h i f) fun b hb => ?_).symm
  have hsym : ⟪peterWeylBlockProjection (models i) f, b⟫_𝕜
      = ⟪f, peterWeylBlockProjection (models i) b⟫_𝕜 := by
    simpa using (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1
      (isSelfAdjoint_peterWeylBlockProjection (models i))) f b
  rw [inner_sub_left, hsym, peterWeylBlockProjection_apply_of_mem (models i) hb, sub_self]

/-- **The range of the character projection is the block it belongs to.** -/
theorem range_peterWeylBlockProjection [IsAlgClosed 𝕜] (h : IsIrrepSkeleton models) (i : ι) :
    (peterWeylBlockProjection (models i)).range = peterWeylBlock (models i) := by
  rw [peterWeylBlockProjection_eq_starProjection h i]
  exact Submodule.range_starProjection _

end Projection

end TauCeti
