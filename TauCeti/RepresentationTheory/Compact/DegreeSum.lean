/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import TauCeti.RepresentationTheory.Compact.Finite
public import TauCeti.RepresentationTheory.Compact.PeterWeyl
-- Non-public: the cardinality of a basis index and the positivity of the dimension of an
-- irreducible are used only inside proofs.
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import TauCeti.RepresentationTheory.Irreducible

/-!
# Peter-Weyl for a finite group: the matrix-coefficient basis and the sum of the squared degrees

For a compact group `G` the normalized matrix coefficients of a skeleton of the unitary dual are a
*Hilbert* basis of `L²(G)` (`TauCeti.peterWeylBasis`). When `G` is finite and discrete that
statement collapses to an algebraic one, and this file carries out the collapse.

Normalized Haar measure on a finite discrete group has full support, so `L²(G)` *is* the space
`G → 𝕜` of all functions on `G` (`TauCeti.lpHaarProbEquivFun`); in particular it is
finite-dimensional, of dimension `|G|`. A Hilbert basis of a finite-dimensional inner product space
is an ordinary module basis: its span has trivial orthogonal complement, and a submodule of a
finite-dimensional space with trivial orthogonal complement is everything. Reading the resulting
basis off both spaces gives

* the matrix coefficients as a **basis of the functions on `G`**, and
* the count `∑_π (dim V_π)² = |G|`, because the basis is indexed by
  `Σ π, Fin (dim V_π) × Fin (dim V_π)`.

Finiteness of the index runs the other way: a skeleton of the unitary dual of a finite group has
finitely many members, because every model has positive dimension and so contributes at least one
basis vector.

The same count is proved algebraically, over any algebraically closed field whose characteristic
does not divide `|G|`, by the Wedderburn decomposition of the group algebra in
`TauCeti/RepresentationTheory/CharacterTable/Wedderburn.lean`; what is new here is that the
*analytic* Peter-Weyl basis returns it, which is the acceptance criterion the compact-groups
roadmap states for the finite case.

## Main definitions

* `TauCeti.peterWeylModuleBasis`: the Peter-Weyl family of a skeleton as a module basis of `L²(G)`,
  for finite `G`.
* `TauCeti.peterWeylFunBasis`: the same family read as a basis of `G → 𝕜`, that is, the normalized
  matrix coefficients as a basis of the functions on a finite group.

## Main statements

* `TauCeti.finrank_lp_haarProb`: `L^p` of a finite discrete group has dimension `|G|`.
* `TauCeti.IrrepModel.dim_pos`: a model of an irreducible representation has positive dimension.
* `TauCeti.IsIrrepSkeleton.finite`: a skeleton of the unitary dual of a finite group is finite.
* `TauCeti.IsIrrepSkeleton.sum_sq_dim_eq_natCard`: **the squares of the degrees sum to the order of
  the group**, `∑_π (dim V_π)² = |G|`.
* `TauCeti.peterWeylFunBasis_apply`: the values of the basis of `G → 𝕜`, the normalized matrix
  coefficients `g ↦ √(dim V_π) · ⟪π g eₐ, e_b⟫`.
* `TauCeti.finite_irrepClass` and `TauCeti.sum_sq_dim_irrepClass_eq_natCard`: the unconditional
  forms, for the canonical skeleton `TauCeti.IrrepClass.model` that
  `TauCeti.isIrrepSkeleton_model` supplies. A `Fintype` instance for the index of the second is
  obtained from the first through `Fintype.ofFinite`.

## References

* Daniel Bump, *Lie Groups*, second edition, Chapter 2.
* [Compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
  whose first worked example asks that `peterWeylBasis`, specialized to a finite group, give
  `dim L²(G) = ∑_π (dim V_π)² = |G|` with the matrix coefficients as a basis.

## Tags

Peter-Weyl theorem, finite group, matrix coefficient, degree
-/

public section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TauCeti

section FiniteDimensional

variable (G : Type*) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G] (𝕜 : Type*) [NontriviallyNormedField 𝕜] (p : ℝ≥0∞)

/-- **`L^p` of a finite discrete group is finite-dimensional.** It is the space `G → 𝕜` of all
functions on `G`, by `TauCeti.lpHaarProbEquivFun`. -/
instance finiteDimensional_lp_haarProb : FiniteDimensional 𝕜 (Lp 𝕜 p (haarProb G)) := by
  have : Fintype G := Fintype.ofFinite G
  exact Module.Finite.equiv (lpHaarProbEquivFun G 𝕜 p).symm

/-- **`L^p` of a finite discrete group has dimension the order of the group.** No exponent
condition is needed: the identification with `G → 𝕜` holds for every `p`. -/
theorem finrank_lp_haarProb : Module.finrank 𝕜 (Lp 𝕜 p (haarProb G)) = Nat.card G := by
  have : Fintype G := Fintype.ofFinite G
  rw [(lpHaarProbEquivFun G 𝕜 p).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card]

end FiniteDimensional

section Dimension

variable {𝕜 G : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G]

/-- **A model of an irreducible representation has positive dimension.** Irreducibility asks for a
nonzero carrier, and the carrier of a model is `EuclideanSpace 𝕜 (Fin dim)`. -/
theorem IrrepModel.dim_pos (m : IrrepModel 𝕜 G) : 0 < m.dim := by
  simpa using Representation.IsIrreducible.finrank_pos m.isIrreducible

end Dimension

section Basis

variable {𝕜 G ι : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G] [Finite G] [TopologicalSpace G]
  [DiscreteTopology G] [MeasurableSpace G] [BorelSpace G] {models : ι → IrrepModel 𝕜 G}

omit [IsAlgClosed 𝕜] in
/-- **For a finite group the Peter-Weyl family spans `L²(G)` algebraically.** Completeness of the
family says that the orthogonal complement of its span vanishes; in a finite-dimensional inner
product space that forces the span itself to be everything, with no closure taken. -/
theorem IsIrrepSkeleton.span_peterWeylFamily_eq_top (h : IsIrrepSkeleton models) :
    Submodule.span 𝕜 (Set.range (peterWeylFamily models)) = ⊤ :=
  Submodule.orthogonal_eq_bot_iff.mp h.orthogonal_span_peterWeylFamily_eq_bot

/-- **The Peter-Weyl basis of a finite group as a module basis.** Its elements are the same
normalized matrix coefficients as those of the Hilbert basis `TauCeti.peterWeylBasis`; what the
finiteness of `G` adds is that they span `L²(G)` without a closure, so that they form a basis in
the algebraic sense. -/
noncomputable def peterWeylModuleBasis (h : IsIrrepSkeleton models) :
    Module.Basis (Σ i, Fin (models i).dim × Fin (models i).dim) 𝕜 (Lp 𝕜 2 (haarProb G)) :=
  Module.Basis.mk h.orthonormal_peterWeylFamily.linearIndependent h.span_peterWeylFamily_eq_top.ge

/-- The module basis of `TauCeti.peterWeylModuleBasis` is the Peter-Weyl family, so it agrees
vector by vector with the Hilbert basis `TauCeti.peterWeylBasis`. -/
@[simp]
theorem coe_peterWeylModuleBasis (h : IsIrrepSkeleton models) :
    ⇑(peterWeylModuleBasis h) = peterWeylFamily models :=
  Module.Basis.coe_mk _ _

/-- **A skeleton of the unitary dual of a finite group is finite**: a finite group has only
finitely many irreducible unitary representations up to equivalence. Each model contributes at
least one basis vector of the finite-dimensional space `L²(G)`, because its dimension is
positive. -/
theorem IsIrrepSkeleton.finite (h : IsIrrepSkeleton models) : Finite ι := by
  have : Fintype (Σ i, Fin (models i).dim × Fin (models i).dim) :=
    FiniteDimensional.fintypeBasisIndex (peterWeylModuleBasis h)
  refine Finite.of_surjective (α := Σ i, Fin (models i).dim × Fin (models i).dim) Sigma.fst ?_
  intro i
  have : NeZero (models i).dim := ⟨(models i).dim_pos.ne'⟩
  exact ⟨⟨i, (0, 0)⟩, rfl⟩

/-- **The Peter-Weyl basis of a finite group has `|G|` elements.** Its index is the type of matrix
positions `Σ π, Fin (dim V_π) × Fin (dim V_π)`, and it is a basis of a space of dimension
`|G|`. -/
theorem IsIrrepSkeleton.natCard_sigma_eq_natCard (h : IsIrrepSkeleton models) :
    Nat.card (Σ i, Fin (models i).dim × Fin (models i).dim) = Nat.card G := by
  rw [← Module.finrank_eq_nat_card_basis (peterWeylModuleBasis h), finrank_lp_haarProb]

/-- **The squares of the degrees sum to the order of the group**: for a skeleton of the unitary
dual of a finite group, `∑_π (dim V_π)² = |G|`. This is the matrix-position count of
`TauCeti.IsIrrepSkeleton.natCard_sigma_eq_natCard`, one degree square per member of the skeleton.

A `Fintype` instance for the index is available from `TauCeti.IsIrrepSkeleton.finite`. -/
theorem IsIrrepSkeleton.sum_sq_dim_eq_natCard [Fintype ι] (h : IsIrrepSkeleton models) :
    ∑ i, (models i).dim ^ 2 = Nat.card G := by
  rw [← h.natCard_sigma_eq_natCard, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp [pow_two]

end Basis

section FunBasis

variable {𝕜 G ι : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G] [Finite G] [TopologicalSpace G]
  [DiscreteTopology G] [MeasurableSpace G] [BorelSpace G] {models : ι → IrrepModel 𝕜 G}

/-- **The normalized matrix coefficients are a basis of the functions on a finite group.** This is
`TauCeti.peterWeylModuleBasis` read through the identification `L²(G) = (G → 𝕜)` of
`TauCeti.lpHaarProbEquivFun`; its values are computed by
`TauCeti.peterWeylFunBasis_apply`. -/
noncomputable def peterWeylFunBasis (h : IsIrrepSkeleton models) :
    Module.Basis (Σ i, Fin (models i).dim × Fin (models i).dim) 𝕜 (G → 𝕜) :=
  (peterWeylModuleBasis h).map (lpHaarProbEquivFun G 𝕜 2)

/-- **The basis vectors of `TauCeti.peterWeylFunBasis` are the normalized matrix coefficients**
`g ↦ √(dim V_π) · ⟪π g eₐ, e_b⟫`, on the nose rather than almost everywhere: normalized Haar
measure on a finite discrete group has full support. -/
@[simp]
theorem peterWeylFunBasis_apply (h : IsIrrepSkeleton models)
    (x : Σ i, Fin (models i).dim × Fin (models i).dim) (g : G) :
    peterWeylFunBasis h x g =
      (Real.sqrt (models x.1).dim : 𝕜) *
        ⟪(models x.1).rep g ((models x.1).basis x.2.1), (models x.1).basis x.2.2⟫_𝕜 := by
  have hcoe : ⇑(peterWeylFamily models x) = fun g : G ↦
      (Real.sqrt (models x.1).dim : 𝕜) *
        ⟪(models x.1).rep g ((models x.1).basis x.2.1), (models x.1).basis x.2.2⟫_𝕜 :=
    eq_of_ae_eq_haarProb G (coeFn_peterWeylFamily models x)
  simp only [peterWeylFunBasis, Module.Basis.map_apply, coe_peterWeylModuleBasis,
    lpHaarProbEquivFun_apply]
  exact congrFun hcoe g

end FunBasis

section StandardSkeleton

variable (𝕜 G : Type*) [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G] [Finite G] [TopologicalSpace G]
  [DiscreteTopology G] [MeasurableSpace G] [BorelSpace G]

/-- **A finite group has finitely many irreducible unitary representations up to equivalence.**
This is `TauCeti.IsIrrepSkeleton.finite` for the canonical skeleton of
`TauCeti.isIrrepSkeleton_model`, whose index is the type `TauCeti.IrrepClass` of unitary
equivalence classes itself. -/
theorem finite_irrepClass : Finite (IrrepClass 𝕜 G) :=
  (isIrrepSkeleton_model 𝕜 G).finite

/-- **The squares of the degrees sum to the order of the group**, in the unconditional form: the
sum runs over the unitary equivalence classes of irreducible representations of the finite group
`G`, each contributing the square of the dimension of its chosen model. A `Fintype` instance for
the classes follows from `TauCeti.finite_irrepClass`. -/
theorem sum_sq_dim_irrepClass_eq_natCard [Fintype (IrrepClass 𝕜 G)] :
    ∑ i : IrrepClass 𝕜 G, (IrrepClass.model i).dim ^ 2 = Nat.card G :=
  (isIrrepSkeleton_model 𝕜 G).sum_sq_dim_eq_natCard

end StandardSkeleton

end TauCeti
