/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.IsotypicBlock
public import TauCeti.RepresentationTheory.Continuous.TraceCoefficient
-- Private: `Module.finrank_linearMap` is used only inside a proof.
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
-- Private: `LinearMap.injective_iff_surjective_of_finrank_eq_finrank` is used only inside a proof.
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The Peter-Weyl block of a compact group is `End(V_π)`, equivariantly

For a compact group `G`, the `π`-block `TauCeti.peterWeylBlock` of `L²(G)` is the span of the matrix
coefficients of an irreducible model `π`, and
`TauCeti/RepresentationTheory/Compact/IsotypicBlock.lean` identifies it with the endomorphisms of
the model's carrier by matching a matrix position with a matrix unit. That identification is built
from a basis, so it says nothing about group actions. This file supplies the equivariant form.

The `L²` trace coefficient `ContRepresentation.traceCoeffLp` sends an operator `T` on the carrier to
the class of `x ↦ trace (T ∘ π x⁻¹)`. It is basis-free, it carries the rank-one operator
`rankOne 𝕜 w v` to the matrix coefficient of `v` and `w`, and its range is exactly the block
(`TauCeti.range_traceCoeffLp`). Its point is the two-sided equivariance
(`ContRepresentation.biRegularLp_traceCoeffLp`): the biregular action
`((g, h) · f) x = f (g⁻¹ * x * h)` on `L²(G)`, built in
`TauCeti/RepresentationTheory/Compact/BiregularRepresentation.lean`, corresponds under it to the
two-sided conjugation `T ↦ π g ∘ T ∘ π h⁻¹` of `ContRepresentation.biLinHom π π`. The trace is
cyclic, which is the whole proof.

Counting dimensions turns that into an **equivalence of `G × G`-representations**. The block of an
irreducible model over an algebraically closed field has dimension `(dim V_π)²`
(`TauCeti.finrank_peterWeylBlock`), which is the dimension of the operator space, so the trace
coefficient is injective as well as onto and `TauCeti.biLinHomEquivPeterWeylBlock` is an
equivalence

`End(V_π) ≃ (π-block of L²(G))`

of representations of `G × G`. Only this block-by-block identification is built here: assembling
the blocks into an equivariant equivalence `L²(G) ≅ ⨁̂_π End(V_π)` over a skeleton of the
irreducibles is not provided, and would have to combine these maps with the Hilbert-sum
decomposition `TauCeti.isHilbertSum_peterWeylBlock` of
`TauCeti/RepresentationTheory/Compact/IsotypicBlock.lean`.

## Main definitions

* `ContRepresentation.traceCoeffLp`: the trace coefficient as a linear map into `L²(G)`.
* `TauCeti.peterWeylBlockRep`: a Peter-Weyl block as a `G × G`-subrepresentation of `L²(G)` under
  the biregular action.
* `TauCeti.traceCoeffBlock`: the trace coefficient of a model, corestricted to its block.
* `TauCeti.biLinHomEquivPeterWeylBlock`: **for an algebraically closed `𝕜` the block is the
  endomorphism algebra of its model as a `G × G`-representation.**

## Main statements

* `ContRepresentation.traceCoeffLp_rankOne`: a rank-one operator pairs to a matrix coefficient.
* `ContRepresentation.traceCoeffLp_eq_sum`: a trace coefficient is a sum of matrix coefficients
  over an orthonormal basis.
* `ContRepresentation.biRegularLp_traceCoeffLp`: **the trace coefficient intertwines two-sided
  conjugation of operators with bi-translation in `L²(G)`**, with
  `ContRepresentation.leftRegularLp_traceCoeffLp` and
  `ContRepresentation.rightRegularLp_traceCoeffLp` as its two one-sided shadows.
* `TauCeti.range_traceCoeffLp`: the trace coefficients of a model are exactly its Peter-Weyl block.
* `TauCeti.surjective_traceCoeffBlock` and `TauCeti.bijective_traceCoeffBlock`: the trace
  coefficient is onto its block, and bijective onto it for an algebraically closed `𝕜`.
* `TauCeti.isUnitary_peterWeylBlockRep` and `TauCeti.continuous_peterWeylBlockRep`: a block is a
  unitary `G × G`-representation, with a continuous operator-valued action.
* `TauCeti.coe_endEquivPeterWeylBlock_basis_end_eq_smul_traceCoeffLp_rankOne`: at a matrix unit of
  the canonical basis, the comparison of
  `TauCeti/RepresentationTheory/Compact/IsotypicBlock.lean` is the trace coefficient of the
  transposed rank-one operator, scaled by `√(dim V_π)`.

## Implementation notes

Two comparisons of a block with the operators of its model now coexist, and they are genuinely
different maps. `TauCeti.endEquivPeterWeylBlock` matches the matrix unit at a position with the
normalized matrix coefficient at that position, in the canonical basis; the trace coefficient
reaches the same matrix coefficient from the matrix unit at the *transposed* position
(`TauCeti.coe_endEquivPeterWeylBlock_basis_end_eq_smul_traceCoeffLp_rankOne`). Transposition is
not equivariant for `ContRepresentation.biLinHom π π` — it conjugates that action into the one
built from the contragredient of `π` — so the basis-built comparison cannot be reused for the
equivariant statement, and rescaling it cannot repair this. The trace pairing is also defined
without choosing a basis, without an inner product on the carrier and without assuming `𝕜`
algebraically closed: only the comparison with the matrix coefficients needs
`[InnerProductSpace 𝕜 V]`, and only the passage from "onto the block" to "bijective onto the
block" needs the dimension count, hence
`[IsAlgClosed 𝕜]`.

## References

* Daniel Bump, *Lie Groups*, second edition, Chapter 2.

## Tags

Peter-Weyl theorem, isotypic decomposition, biregular representation, compact group
-/

public section

open MeasureTheory
open scoped InnerProductSpace

open TauCeti TauCeti.ContRepresentation

namespace ContRepresentation

section TraceCoeffLp

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- **The `L²` trace coefficient**: the trace coefficient
`x ↦ trace (T ∘ π x⁻¹)` of `TauCeti/RepresentationTheory/Continuous/TraceCoefficient.lean`, read in
`L²(G)` for normalized Haar measure.

A trace coefficient is continuous and `G` is compact, so `ContinuousMap.toLp` applies, exactly as
for `TauCeti.ContRepresentation.matrixCoeffLp`. -/
noncomputable def traceCoeffLp (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    (V →L[𝕜] V) →ₗ[𝕜] Lp 𝕜 2 (haarProb G) :=
  (ContinuousMap.toLp 2 (haarProb G) 𝕜 : C(G, 𝕜) →L[𝕜] Lp 𝕜 2 (haarProb G)).toLinearMap ∘ₗ
    traceCoeff π hπ

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

theorem traceCoeffLp_def (T : V →L[𝕜] V) :
    traceCoeffLp π hπ T = ContinuousMap.toLp 2 (haarProb G) 𝕜 (traceCoeff π hπ T) :=
  (rfl)

/-- An `L²` trace coefficient is represented, almost everywhere, by the function it comes from. -/
theorem coeFn_traceCoeffLp (T : V →L[𝕜] V) :
    traceCoeffLp π hπ T =ᵐ[haarProb G] fun x ↦ traceCLM 𝕜 V (T ∘L π x⁻¹) := by
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := 𝕜) (p := 2) (haarProb G)
    (traceCoeff π hπ T)] with x hx
  rw [traceCoeffLp_def, hx, traceCoeff_apply]

end TraceCoeffLp

/-! ### Comparison with the matrix coefficients -/

section MatrixCoeffLp

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- **The `L²` trace coefficient of a rank-one operator is an `L²` matrix coefficient**, for a
unitary representation. -/
theorem traceCoeffLp_rankOne (hunitary : IsUnitary π) (v w : V) :
    traceCoeffLp π hπ (InnerProductSpace.rankOne 𝕜 w v) = matrixCoeffLp π hπ v w := by
  rw [traceCoeffLp_def, traceCoeff_rankOne π hπ hunitary, matrixCoeffLp_def]

/-- **An `L²` trace coefficient expands over an orthonormal basis as a sum of `L²` matrix
coefficients.** -/
theorem traceCoeffLp_eq_sum {ι : Type*} [Fintype ι] (hunitary : IsUnitary π)
    (e : OrthonormalBasis ι 𝕜 V) (T : V →L[𝕜] V) :
    traceCoeffLp π hπ T = ∑ i, matrixCoeffLp π hπ (e i) (T (e i)) := by
  rw [traceCoeffLp_def, traceCoeff_eq_sum π hπ hunitary e T, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ (matrixCoeffLp_def π hπ (e i) (T (e i))).symm

end MatrixCoeffLp

/-! ### Two-sided equivariance -/

section Bitranslation

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- **The trace coefficient intertwines two-sided conjugation of operators with bi-translation in
`L²(G)`**: the biregular action of `(g, h)` on `traceCoeffLp π hπ T` is the trace coefficient of
`π g ∘ T ∘ π h⁻¹`.

This is the equivariance that the basis-built comparison
`TauCeti.endEquivPeterWeylBlock` of
`TauCeti/RepresentationTheory/Compact/IsotypicBlock.lean` does not provide. No unitarity is needed:
it is the cyclicity of the trace. -/
theorem biRegularLp_traceCoeffLp (p : G × G) (T : V →L[𝕜] V) :
    biRegularLp 𝕜 G p (traceCoeffLp π hπ T) = traceCoeffLp π hπ (biLinHom π π p T) := by
  simp only [traceCoeffLp_def, biRegularLp_toLp, traceCoeff_biLinHom]

/-- Left translation of a trace coefficient postcomposes its operator with the action. -/
theorem leftRegularLp_traceCoeffLp (g : G) (T : V →L[𝕜] V) :
    leftRegularLp 𝕜 G g (traceCoeffLp π hπ T) = traceCoeffLp π hπ ((π g).comp T) := by
  rw [← biRegularLp_apply_mk_one, biRegularLp_traceCoeffLp, biLinHom_apply_mk_one]

/-- Right translation of a trace coefficient precomposes its operator with the action of the
inverse. -/
theorem rightRegularLp_traceCoeffLp (h : G) (T : V →L[𝕜] V) :
    rightRegularLp 𝕜 G h (traceCoeffLp π hπ T) = traceCoeffLp π hπ (T.comp (π h⁻¹)) := by
  rw [← biRegularLp_apply_one_mk, biRegularLp_traceCoeffLp, biLinHom_apply_one_mk]

end Bitranslation

end ContRepresentation

namespace TauCeti

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- **A Peter-Weyl block is the range of the trace coefficient of its model.** The inclusion of the
range in the block is the expansion of a trace coefficient over the canonical basis; the reverse
inclusion is that every matrix coefficient is the trace coefficient of a rank-one operator. -/
theorem range_traceCoeffLp (model : IrrepModel 𝕜 G) :
    LinearMap.range (_root_.ContRepresentation.traceCoeffLp model.rep model.continuous_rep) =
      peterWeylBlock model := by
  refine le_antisymm (LinearMap.range_le_iff_comap.2 (eq_top_iff.2 fun T _ ↦ ?_)) ?_
  · rw [Submodule.mem_comap, _root_.ContRepresentation.traceCoeffLp_eq_sum model.rep
      model.continuous_rep model.isUnitary model.basis T]
    exact Submodule.sum_mem _ fun i _ ↦ matrixCoeffLp_mem_peterWeylBlock model _ _
  · rw [peterWeylBlock_eq_span_range (fun _ : Unit ↦ model) ()]
    refine Submodule.span_le.2 ?_
    rintro - ⟨q, rfl⟩
    simp only [SetLike.mem_coe, peterWeylFamily_apply]
    exact Submodule.smul_mem _ _
      ⟨InnerProductSpace.rankOne 𝕜 (model.basis q.2) (model.basis q.1),
        _root_.ContRepresentation.traceCoeffLp_rankOne model.rep model.continuous_rep
          model.isUnitary _ _⟩

/-- **The trace coefficient of a model, corestricted to its Peter-Weyl block.** The corestriction is
legitimate by `TauCeti.range_traceCoeffLp`, and it is the map that
`TauCeti.biLinHomEquivPeterWeylBlock` promotes to an equivalence of representations. -/
noncomputable def traceCoeffBlock (model : IrrepModel 𝕜 G) :
    (EuclideanSpace 𝕜 (Fin model.dim) →L[𝕜] EuclideanSpace 𝕜 (Fin model.dim)) →ₗ[𝕜]
      peterWeylBlock model :=
  (_root_.ContRepresentation.traceCoeffLp model.rep model.continuous_rep).codRestrict
    (peterWeylBlock model) fun T ↦ (range_traceCoeffLp model).le ⟨T, rfl⟩

@[simp]
theorem coe_traceCoeffBlock (model : IrrepModel 𝕜 G)
    (T : EuclideanSpace 𝕜 (Fin model.dim) →L[𝕜] EuclideanSpace 𝕜 (Fin model.dim)) :
    (traceCoeffBlock model T : Lp 𝕜 2 (haarProb G)) =
      _root_.ContRepresentation.traceCoeffLp model.rep model.continuous_rep T :=
  (rfl)

/-- **The corestricted trace coefficient is onto the block**, which is
`TauCeti.range_traceCoeffLp` read as a surjection. -/
theorem surjective_traceCoeffBlock (model : IrrepModel 𝕜 G) :
    Function.Surjective (traceCoeffBlock model) := by
  intro f
  obtain ⟨T, hT⟩ := (range_traceCoeffLp model).ge f.2
  exact ⟨T, Subtype.ext hT⟩

/-- **The trace coefficient of an irreducible model is a bijection onto its block**, for an
algebraically closed `𝕜`. Surjectivity is `TauCeti.surjective_traceCoeffBlock`; injectivity is then
forced, because the operator space and the block both have dimension `(dim V_π)²`. -/
theorem bijective_traceCoeffBlock [IsAlgClosed 𝕜] (model : IrrepModel 𝕜 G) :
    Function.Bijective (traceCoeffBlock model) := by
  refine ⟨?_, surjective_traceCoeffBlock model⟩
  refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).2
    (surjective_traceCoeffBlock model)
  have e : (EuclideanSpace 𝕜 (Fin model.dim) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin model.dim)) ≃ₗ[𝕜]
      (EuclideanSpace 𝕜 (Fin model.dim) →L[𝕜] EuclideanSpace 𝕜 (Fin model.dim)) :=
    LinearMap.toContinuousLinearMap
  rw [finrank_peterWeylBlock model, ← e.finrank_eq, Module.finrank_linearMap,
    finrank_euclideanSpace_fin, pow_two]

/-- **A Peter-Weyl block as a `G × G`-subrepresentation of `L²(G)`**: the block is stable under
bi-translation (`TauCeti.biRegularLp_mem_peterWeylBlock`), so the biregular representation restricts
to it. -/
noncomputable def peterWeylBlockRep (model : IrrepModel 𝕜 G) :
    ContRepresentation 𝕜 (G × G) (peterWeylBlock model) :=
  ContRepresentation.subrepresentation (biRegularLp 𝕜 G) (peterWeylBlock model)
    fun p _ hf ↦ biRegularLp_mem_peterWeylBlock model p hf

/-- **A Peter-Weyl block is a unitary `G × G`-representation**, bi-translation being an isometry of
`L²(G)`. -/
theorem isUnitary_peterWeylBlockRep (model : IrrepModel 𝕜 G) :
    ContRepresentation.IsUnitary (peterWeylBlockRep model) :=
  (isUnitary_biRegularLp 𝕜 G).subrepresentation _

/-- The restricted action is bi-translation, read on the underlying `L²` functions. -/
@[simp]
theorem coe_peterWeylBlockRep_apply (model : IrrepModel 𝕜 G) (p : G × G)
    (f : peterWeylBlock model) :
    ((peterWeylBlockRep model p f : peterWeylBlock model) : Lp 𝕜 2 (haarProb G)) =
      biRegularLp 𝕜 G p (f : Lp 𝕜 2 (haarProb G)) :=
  ContRepresentation.coe_subrepresentation_apply p f

/-- **A Peter-Weyl block has a continuous operator-valued action.** This is not
`TauCeti.ContRepresentation.continuous_subrepresentation`: the ambient biregular representation of
`L²(G)` is only *strongly* continuous (`TauCeti.continuous_biRegularLp_apply`), and for an infinite
compact group it is not continuous in the operator norm. The block, however, is finite-dimensional,
so the surjection `TauCeti.traceCoeffBlock` onto it has a continuous linear section `s`, and the
equivariance `ContRepresentation.biRegularLp_traceCoeffLp` then writes the action as the composite
`traceCoeffBlock ∘ biLinHom π π (g, h) ∘ s`, which is continuous in `(g, h)` because
`ContRepresentation.continuous_biLinHom` is.

Only surjectivity of the trace coefficient onto the block is used, not the injectivity of
`TauCeti.bijective_traceCoeffBlock`, so no algebraic closedness is needed. -/
theorem continuous_peterWeylBlockRep (model : IrrepModel 𝕜 G) :
    Continuous (peterWeylBlockRep model) := by
  obtain ⟨s, hs⟩ :=
    (LinearMap.toContinuousLinearMap (traceCoeffBlock model)).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.2 (surjective_traceCoeffBlock model))
  have key : ⇑(peterWeylBlockRep model) = fun p ↦
      (LinearMap.toContinuousLinearMap (traceCoeffBlock model)).comp
        ((_root_.ContRepresentation.biLinHom model.rep model.rep p).comp s) := by
    funext p
    refine (ContinuousLinearMap.ext fun f ↦ ?_).symm
    have hsf : traceCoeffBlock model (s f) = f := by
      simpa using congr($hs f)
    have hequiv : traceCoeffBlock model
        (_root_.ContRepresentation.biLinHom model.rep model.rep p (s f)) =
          peterWeylBlockRep model p (traceCoeffBlock model (s f)) :=
      Subtype.ext <| by
        rw [coe_traceCoeffBlock, coe_peterWeylBlockRep_apply, coe_traceCoeffBlock,
          _root_.ContRepresentation.biRegularLp_traceCoeffLp]
    simp only [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap']
    rw [hequiv, hsf]
  rw [key]
  exact continuous_const.clm_comp
    ((_root_.ContRepresentation.continuous_biLinHom model.rep model.rep model.continuous_rep
      model.continuous_rep).clm_comp continuous_const)

/-- **At a matrix unit of the canonical basis, the basis-built comparison of
`TauCeti.endEquivPeterWeylBlock` is the trace coefficient of the transposed rank-one operator**,
scaled by `√(dim V_π)`: the matrix unit `Basis.end b (i, j)` sends
`b j ↦ b i`, that is, it is the rank-one operator `rankOne 𝕜 (b i) (b j)`, while the trace
coefficient reaches the same matrix coefficient from `rankOne 𝕜 (b j) (b i)`.

The swap of the two indices is a transposition, and transposition turns the two-sided conjugation
`ContRepresentation.biLinHom π π` into the conjugation by the *contragredient* of `π`. That is
why `TauCeti.endEquivPeterWeylBlock` cannot carry the equivariance of
`TauCeti.biLinHomEquivPeterWeylBlock`, and why the basis-free trace pairing is the comparison the
`G × G`-action sees. -/
theorem coe_endEquivPeterWeylBlock_basis_end_eq_smul_traceCoeffLp_rankOne [IsAlgClosed 𝕜]
    (model : IrrepModel 𝕜 G) (p : Fin model.dim × Fin model.dim) :
    (endEquivPeterWeylBlock model (Module.Basis.end model.basis.toBasis p) :
        Lp 𝕜 2 (haarProb G)) =
      (Real.sqrt model.dim : 𝕜) • _root_.ContRepresentation.traceCoeffLp model.rep
        model.continuous_rep (InnerProductSpace.rankOne 𝕜 (model.basis p.2) (model.basis p.1)) := by
  rw [_root_.ContRepresentation.traceCoeffLp_rankOne model.rep model.continuous_rep
    model.isUnitary,
    TauCeti.coe_endEquivPeterWeylBlock_basis_end (fun _ : Unit ↦ model) () p,
    peterWeylFamily_apply]

/-- **For an algebraically closed `𝕜` the Peter-Weyl block of an irreducible model is the
endomorphism algebra of its carrier, as a representation of `G × G`.** The equivalence is the trace
coefficient `T ↦ (x ↦ trace (T ∘ π x⁻¹))`, which carries the two-sided conjugation
`T ↦ π g ∘ T ∘ π h⁻¹` to bi-translation `f ↦ (x ↦ f (g⁻¹ * x * h))`.

This is the equivariant form of `TauCeti.endEquivPeterWeylBlock`, which compares the same two
spaces as modules only. -/
noncomputable def biLinHomEquivPeterWeylBlock [IsAlgClosed 𝕜] (model : IrrepModel 𝕜 G) :
    _root_.ContRepresentation.Equiv
      (_root_.ContRepresentation.biLinHom model.rep model.rep) (peterWeylBlockRep model) :=
  .mk (LinearEquiv.ofBijective _ (bijective_traceCoeffBlock model)).toContinuousLinearEquiv
    fun p ↦ ContinuousLinearMap.ext fun T ↦ Subtype.ext <| by
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        coe_peterWeylBlockRep_apply]
      exact (_root_.ContRepresentation.biRegularLp_traceCoeffLp model.rep model.continuous_rep p
        T).symm

/-- The equivalence of `TauCeti.biLinHomEquivPeterWeylBlock` is the trace coefficient. -/
@[simp]
theorem coe_biLinHomEquivPeterWeylBlock_apply [IsAlgClosed 𝕜] (model : IrrepModel 𝕜 G)
    (T : EuclideanSpace 𝕜 (Fin model.dim) →L[𝕜] EuclideanSpace 𝕜 (Fin model.dim)) :
    ((biLinHomEquivPeterWeylBlock model T : peterWeylBlock model) : Lp 𝕜 2 (haarProb G)) =
      _root_.ContRepresentation.traceCoeffLp model.rep model.continuous_rep T :=
  (rfl)

end TauCeti
