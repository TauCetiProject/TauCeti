/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index

import TauCeti.Topology.Algebra.Module.Complement

/-!
# Fredholm operators

This file extends Mathlib's notion of a **Fredholm operator** with finite-dimensional examples,
invariance under scalar multiplication and continuous linear changes of coordinates, and
preservation under restriction of scalars along a finite extension of scalar fields.
All Fredholm hypotheses use `ContinuousLinearMap.IsFredholm` directly. That predicate asks for a
strict map with closed range, finite-dimensional kernel and cokernel, and a topologically
complemented kernel. Between Banach spaces over an `IsRCLikeNormedField`, finite-dimensional
kernel and cokernel imply the strictness, closed-range and complemented-kernel conditions.
Thus the predicate is *equivalent* there to finite dimensionality of the kernel and cokernel alone;
that equivalence is proved in `TauCeti.Analysis.Fredholm.ClosedRange` as
`TauCeti.isFredholm_iff_finite_ker_coker`.
Outside that setting `ContinuousLinearMap.IsFredholm` is genuinely stronger, and it is the notion
intended throughout.

## Main declarations

* `ContinuousLinearMap.instNonemptyIsFredholmSelf`: the Fredholm endomorphism locus `{T : E →L[𝕜]
  E // T.IsFredholm}` is nonempty, witnessed by the identity operator.
* `ContinuousLinearMap.IsFredholm.finiteDimensional_iff`: a Fredholm operator has
  finite-dimensional domain if and only if it has finite-dimensional codomain; consequently, the
  Fredholm locus is empty in mixed dimension
  (`ContinuousLinearMap.isEmpty_isFredholm_of_finiteDimensional_of_not_finiteDimensional`,
  `ContinuousLinearMap.isEmpty_isFredholm_of_not_finiteDimensional_of_finiteDimensional`).
* `FredholmDecomposition.completeSpace_X₁_iff` and
  `ContinuousLinearMap.IsFredholm.completeSpace_iff`: between Hausdorff uniform topological vector
  spaces over a complete nontrivially normed field, a space is complete if and only if the
  essential factor of a Fredholm decomposition is complete, and a Fredholm operator has complete
  domain if and only if it has complete codomain.
* `ContinuousLinearMap.isFredholm_of_finiteDimensional`: every operator between finite-dimensional
  topological vector spaces over a complete scalar field, with Hausdorff target, is Fredholm.
* `ContinuousLinearMap.IsFredholm.neg`, `ContinuousLinearMap.IsFredholm.smul`: Fredholmness is
  preserved by negation and by nonzero scalar multiples.
* `ContinuousLinearMap.IsFredholm.comp_equiv` and
  `ContinuousLinearMap.IsFredholm.equiv_comp`: composing with a continuous linear equivalence on
  either side preserves Fredholmness. These implications hold between topological modules over any
  `NontriviallyNormedField`, without completeness or separation assumptions.
* `ContinuousLinearMap.IsFredholm.isInvertible_of_injective_of_index_eq_zero`: an injective
  Fredholm operator of index zero is invertible.
* `ContinuousLinearMap.index_comp`: the index of a composition of Fredholm operators is the sum
  of their indices.
* `ContinuousLinearMap.isFredholm_iff_of_comp_eq`: operators conjugate under continuous linear
  equivalences are simultaneously Fredholm.
* `ContinuousLinearMap.IsFredholm.restrictScalars`: a Fredholm operator over `𝕜'` stays Fredholm
  over a subfield `𝕜` with `𝕜'` finite-dimensional over `𝕜`; for instance, the realification of
  a complex Fredholm operator is Fredholm. Its index is computed by
  `ContinuousLinearMap.index_restrictScalars`.
* `ContinuousLinearMap.IsFredholm.finiteDimensional_ker_of_restrictScalars_eq`,
  `ContinuousLinearMap.IsFredholm.finiteDimensional_quotient_range_of_restrictScalars_eq`: a
  `𝕜'`-linear map whose underlying `𝕜`-linear map is Fredholm has finite-dimensional kernel and
  cokernel over `𝕜'`.

The Fredholm index and its elementary API live in
`TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index`.
-/

public section

namespace ContinuousLinearMap

open Module

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F G : Type*}
variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
variable [AddCommGroup G] [TopologicalSpace G] [Module 𝕜 G]

/-- The Fredholm endomorphism locus `{T : E →L[𝕜] E // T.IsFredholm}` is nonempty, witnessed by the
identity operator. -/
instance instNonemptyIsFredholmSelf : Nonempty {T : E →L[𝕜] E // T.IsFredholm} :=
  ⟨⟨.id 𝕜 E, .id⟩⟩

/-- A Fredholm operator has finite-dimensional domain if and only if it has finite-dimensional
codomain. -/
theorem IsFredholm.finiteDimensional_iff {T : E →L[𝕜] F} (hT : T.IsFredholm) :
    FiniteDimensional 𝕜 E ↔ FiniteDimensional 𝕜 F := by
  have := hT.finite_ker
  have := hT.finite_coker
  refine ⟨fun _ ↦ Module.Finite.of_submodule_quotient T.range, fun _ ↦ ?_⟩
  have : FiniteDimensional 𝕜 (E ⧸ T.ker) := T.quotKerEquivRange.symm.finiteDimensional
  exact Module.Finite.of_submodule_quotient T.ker

/-- The Fredholm locus is empty when the domain is finite-dimensional and the codomain is
infinite-dimensional. -/
theorem isEmpty_isFredholm_of_finiteDimensional_of_not_finiteDimensional [FiniteDimensional 𝕜 E]
    (hF : ¬ FiniteDimensional 𝕜 F) : IsEmpty {T : E →L[𝕜] F // T.IsFredholm} :=
  ⟨fun T ↦ hF (T.property.finiteDimensional_iff.1 inferInstance)⟩

/-- The Fredholm locus is empty when the domain is infinite-dimensional and the codomain is
finite-dimensional. -/
theorem isEmpty_isFredholm_of_not_finiteDimensional_of_finiteDimensional
    (hE : ¬ FiniteDimensional 𝕜 E) [FiniteDimensional 𝕜 F] :
    IsEmpty {T : E →L[𝕜] F // T.IsFredholm} :=
  ⟨fun T ↦ hE (T.property.finiteDimensional_iff.2 inferInstance)⟩

section FiniteDimensional

variable [CompleteSpace 𝕜]
variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
variable [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [T2Space F] [FiniteDimensional 𝕜 F]

/-- Every continuous linear map between finite-dimensional topological vector spaces over a
complete scalar field is Fredholm, provided the target is Hausdorff. -/
lemma isFredholm_of_finiteDimensional (T : E →L[𝕜] F) : IsFredholm T where
  isStrictMap := T.isStrictMap_of_finiteDimensional
  isClosed_range := (LinearMap.range (T : E →ₗ[𝕜] F)).isClosed_of_finiteDimensional
  finite_ker := inferInstance
  finite_coker := inferInstance
  closedComplemented_ker :=
    Submodule.ClosedComplemented.of_finiteDimensional_quotient T.isClosed_ker

end FiniteDimensional

section CompEquiv

variable {T : E →L[𝕜] F}

/-- Postcomposing a Fredholm operator with a continuous linear equivalence yields a Fredholm
operator.

Unlike `ContinuousLinearMap.isFredholm_equiv_comp`, this implication does not require a complete
scalar field, continuous module operations, or Hausdorff spaces. -/
lemma IsFredholm.equiv_comp (hT : IsFredholm T) (e : F ≃L[𝕜] G) :
    IsFredholm ((e : F →L[𝕜] G).comp T) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Expose function composition so the homeomorphism strictness lemma applies.
    change Topology.IsStrictMap (fun x ↦ e (T x))
    exact e.toHomeomorph.comp_isStrictMap_iff.mpr hT.isStrictMap
  · rw [toLinearMap_comp, LinearMap.range_comp]
    simpa [Submodule.map_coe] using e.isClosed_image.2 hT.isClosed_range
  · rw [toLinearMap_comp,
      ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap, LinearEquiv.ker_comp]
    exact hT.finite_ker
  · rw [toLinearMap_comp,
      ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap, LinearMap.range_comp]
    have := hT.finite_coker
    exact (Submodule.Quotient.equiv _ _ e.toLinearEquiv rfl).finiteDimensional
  · rw [toLinearMap_comp,
      ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap, LinearEquiv.ker_comp]
    exact hT.closedComplemented_ker

/-- Precomposing a Fredholm operator with a continuous linear equivalence yields a Fredholm
operator.

Unlike `ContinuousLinearMap.isFredholm_comp_equiv`, this implication does not require a complete
scalar field, continuous module operations, or Hausdorff spaces. -/
lemma IsFredholm.comp_equiv (hT : IsFredholm T) (e : G ≃L[𝕜] E) :
    IsFredholm (T.comp (e : G →L[𝕜] E)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Expose function composition so the homeomorphism strictness lemma applies.
    change Topology.IsStrictMap (fun x ↦ T (e x))
    exact e.toHomeomorph.isStrictMap_comp_iff.mpr hT.isStrictMap
  · simpa using hT.isClosed_range
  · rw [toLinearMap_comp, LinearMap.ker_comp,
      ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap,
      Submodule.comap_equiv_eq_map_symm]
    have := hT.finite_ker
    exact (e.symm.submoduleMap _).finiteDimensional
  · simpa using hT.finite_coker
  · rw [toLinearMap_comp, LinearMap.ker_comp,
      ContinuousLinearEquiv.toLinearMap_toContinuousLinearMap,
      Submodule.comap_equiv_eq_map_symm]
    exact hT.closedComplemented_ker.map e.symm

/-- Operators conjugate under continuous linear equivalences, `e' ∘ T = S ∘ e`, are
simultaneously Fredholm. -/
lemma isFredholm_iff_of_comp_eq {H : Type*} [AddCommGroup H] [TopologicalSpace H] [Module 𝕜 H]
    {S : G →L[𝕜] H} (e : E ≃L[𝕜] G) (e' : F ≃L[𝕜] H)
    (h : (e' : F →L[𝕜] H).comp T = S.comp (e : E →L[𝕜] G)) : IsFredholm T ↔ IsFredholm S := by
  have hS : S = ((e' : F →L[𝕜] H).comp T).comp (e.symm : G →L[𝕜] E) := by
    rw [h]
    ext x
    simp
  have hT : T = ((e'.symm : H →L[𝕜] F).comp S).comp (e : E →L[𝕜] G) := by
    rw [hS]
    ext x
    simp
  refine ⟨fun hT' ↦ ?_, fun hS' ↦ ?_⟩
  · rw [hS]
    exact (hT'.equiv_comp e').comp_equiv e.symm
  · rw [hT]
    exact (hS'.equiv_comp e'.symm).comp_equiv e

end CompEquiv

variable [ContinuousConstSMul 𝕜 F] in
/-- A nonzero scalar multiple of a Fredholm operator is Fredholm. -/
lemma IsFredholm.smul {T : E →L[𝕜] F} (hT : IsFredholm T) {c : 𝕜} (hc : c ≠ 0) :
    IsFredholm (c • T) := by
  convert hT.equiv_comp (ContinuousLinearEquiv.smulLeft (R₁ := 𝕜) (M₁ := F)
    (Units.mk0 c hc)) using 1
  ext x
  simp

variable [IsTopologicalAddGroup F] in
/-- The negation of a Fredholm operator is Fredholm. -/
lemma IsFredholm.neg {T : E →L[𝕜] F} (hT : IsFredholm T) : IsFredholm (-T) := by
  convert hT.equiv_comp (ContinuousLinearEquiv.neg 𝕜) using 1
  ext x
  simp

/-- An injective Fredholm operator of index zero is invertible: index zero forces its cokernel to
vanish. -/
lemma IsFredholm.isInvertible_of_injective_of_index_eq_zero {T : E →L[𝕜] F} (hT : IsFredholm T)
    (hinj : Function.Injective T) (h0 : T.index = 0) : T.IsInvertible := by
  have := hT.finite_coker
  exact isInvertible_iff_isFredholm_and_bijective.2
    ⟨hT, T.bijective_of_injective_of_index_eq_zero hinj h0⟩

/-- The index of a composition of Fredholm operators is the sum of their indices. This is
Mathlib's `ContinuousLinearMap.IsFredholm.index_comp`, stated for `ContinuousLinearMap.index`
rather than for the index of the underlying linear maps. -/
lemma index_comp {S : F →L[𝕜] G} {T : E →L[𝕜] F} (hS : IsFredholm S) (hT : IsFredholm T) :
    (S ∘L T).index = S.index + T.index := by
  simpa only [index_def] using hS.index_comp hT

section RestrictScalars

variable (𝕜) {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [Module 𝕜 𝕜'] [Module.Finite 𝕜 𝕜']
  [Module 𝕜' E] [IsScalarTower 𝕜 𝕜' E] [Module 𝕜' F] [IsScalarTower 𝕜 𝕜' F]

/-- Restricting scalars along a finite extension `𝕜 → 𝕜'` of nontrivially normed fields preserves
Fredholmness. In particular the realification of a complex Fredholm operator is Fredholm. -/
lemma IsFredholm.restrictScalars {T : E →L[𝕜'] F} (hT : IsFredholm T) :
    IsFredholm (T.restrictScalars 𝕜) where
  isStrictMap := by simpa only [coe_restrictScalars'] using hT.isStrictMap
  isClosed_range := by
    simpa only [coe_restrictScalars, LinearMap.range_restrictScalars,
      Submodule.coe_restrictScalars] using hT.isClosed_range
  finite_ker := by
    have := hT.finite_ker
    -- The kernel of the restricted map is `T.ker` with the `𝕜`-structure inherited from `E`.
    have : FiniteDimensional 𝕜 T.ker := Module.Finite.trans 𝕜' T.ker
    exact this
  finite_coker := by
    have := hT.finite_coker
    have : FiniteDimensional 𝕜 (F ⧸ T.range) := Module.Finite.trans 𝕜' _
    exact (Submodule.Quotient.restrictScalarsEquiv 𝕜 T.range).symm.finiteDimensional
  closedComplemented_ker := hT.closedComplemented_ker.restrictScalars 𝕜

variable {𝕜} in
omit [Module.Finite 𝕜 𝕜'] in
/-- The kernel of a `𝕜'`-linear map `f` whose underlying `𝕜`-linear map is a Fredholm operator
`A` is finite-dimensional over `𝕜'`. For instance, the complex kernel of a complex-linear map
whose realification is Fredholm is finite-dimensional. -/
theorem IsFredholm.finiteDimensional_ker_of_restrictScalars_eq {A : E →L[𝕜] F}
    (hA : A.IsFredholm) {f : E →ₗ[𝕜'] F} (hf : f.restrictScalars 𝕜 = A) :
    FiniteDimensional 𝕜' (LinearMap.ker f) := by
  -- The kernel of `f`, with its `𝕜`-structure, is the kernel of `A`.
  have : FiniteDimensional 𝕜 ((LinearMap.ker f).restrictScalars 𝕜) := by
    rw [← LinearMap.ker_restrictScalars, hf]
    exact hA.finite_ker
  have : FiniteDimensional 𝕜 (LinearMap.ker f) :=
    Module.Finite.equiv (((LinearMap.ker f).restrictScalarsEquiv 𝕜).restrictScalars 𝕜)
  exact Module.Finite.of_restrictScalars_finite 𝕜 𝕜' (LinearMap.ker f)

variable {𝕜} in
omit [Module.Finite 𝕜 𝕜'] in
/-- The cokernel of a `𝕜'`-linear map `f` whose underlying `𝕜`-linear map is a Fredholm operator
`A` is finite-dimensional over `𝕜'`. For instance, the complex cokernel of a complex-linear map
whose realification is Fredholm is finite-dimensional. -/
theorem IsFredholm.finiteDimensional_quotient_range_of_restrictScalars_eq {A : E →L[𝕜] F}
    (hA : A.IsFredholm) {f : E →ₗ[𝕜'] F} (hf : f.restrictScalars 𝕜 = A) :
    FiniteDimensional 𝕜' (F ⧸ LinearMap.range f) := by
  have : FiniteDimensional 𝕜 (F ⧸ (LinearMap.range f).restrictScalars 𝕜) := by
    rw [← LinearMap.range_restrictScalars, hf]
    exact hA.finite_coker
  have : FiniteDimensional 𝕜 (F ⧸ LinearMap.range f) :=
    Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv 𝕜 _)
  exact Module.Finite.of_restrictScalars_finite 𝕜 𝕜' _

end RestrictScalars

end ContinuousLinearMap

section CompleteSpace

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E] [Module 𝕜 E]
  [ContinuousSMul 𝕜 E] [T2Space E]
variable [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [Module 𝕜 F]
  [ContinuousSMul 𝕜 F] [T2Space F]

/-- The essential (finite-codimension) factor of a Fredholm decomposition of a Hausdorff uniform
topological vector space over a complete nontrivially normed field is complete if and only if the
ambient space is complete. -/
theorem FredholmDecomposition.completeSpace_X₁_iff (dec : FredholmDecomposition 𝕜 E) :
    CompleteSpace dec.X₁ ↔ CompleteSpace E := by
  have : IsUniformAddGroup dec.X₀ := dec.X₀.toAddSubgroup.isUniformAddGroup
  have : IsUniformAddGroup dec.X₁ := dec.X₁.toAddSubgroup.isUniformAddGroup
  let e := dec.X₁.prodEquivOfIsTopCompl dec.X₀ dec.isTopCompl
  have := dec.finite_X₀
  have hX₀ : CompleteSpace dec.X₀ := FiniteDimensional.completeSpace 𝕜 dec.X₀
  rw [← e.isUniformEmbedding.completeSpace_congr e.surjective,
    completeSpace_prod_of_nonempty, and_iff_left hX₀]

/-- A Fredholm operator between Hausdorff uniform topological vector spaces over a complete
nontrivially normed field has complete domain if and only if it has complete codomain. -/
theorem ContinuousLinearMap.IsFredholm.completeSpace_iff {T : E →L[𝕜] F} (hT : T.IsFredholm) :
    CompleteSpace E ↔ CompleteSpace F := by
  obtain ⟨pkg⟩ := hT.nonempty_fredholmPackage
  have : IsUniformAddGroup pkg.decDom.X₁ := pkg.decDom.X₁.toAddSubgroup.isUniformAddGroup
  have : IsUniformAddGroup pkg.decCodom.X₁ := pkg.decCodom.X₁.toAddSubgroup.isUniformAddGroup
  exact pkg.decDom.completeSpace_X₁_iff.symm.trans
    ((pkg.equiv.isUniformEmbedding.completeSpace_congr pkg.equiv.surjective).trans
      pkg.decCodom.completeSpace_X₁_iff)

end CompleteSpace
