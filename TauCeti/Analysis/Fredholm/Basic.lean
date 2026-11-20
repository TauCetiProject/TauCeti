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
* `ContinuousLinearMap.isFredholm_iff_of_comp_eq`: operators conjugate under continuous linear
  equivalences are simultaneously Fredholm.
* `ContinuousLinearMap.IsFredholm.restrictScalars`: a Fredholm operator over `𝕜'` stays Fredholm
  over a subfield `𝕜` with `𝕜'` finite-dimensional over `𝕜`; for instance, the realification of
  a complex Fredholm operator is Fredholm. Its index is computed by
  `ContinuousLinearMap.index_restrictScalars`.
* `FredholmDecomposition.proj₀`: the continuous projection onto the finite-dimensional summand
  `dec.X₀` along `dec.X₁`.
* `ContinuousLinearMap.FredholmPackage.symm`,
  `ContinuousLinearMap.FredholmPackage.id_sub_quasiInverse_comp_self`,
  `ContinuousLinearMap.FredholmPackage.id_sub_self_comp_quasiInverse`,
  `ContinuousLinearMap.FredholmPackage.projectionL_decDom_eq_of_X₁_eq`,
  `ContinuousLinearMap.FredholmPackage.projectionL_decCodom_eq_of_X₀_eq`: package duality for
  `pkg.quasiInverse`, finite-rank corner error projections, and ambient projection agreement for
  packages sharing a complement.

The Fredholm index and its elementary API live in
`TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index`.
-/

public section

/-- Given a `FredholmDecomposition` `dec` of `E`, `dec.proj₀` is the continuous linear projection
onto the finite-dimensional part `dec.X₀` along the essential part `dec.X₁`. -/
noncomputable abbrev FredholmDecomposition.proj₀ {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousSub E]
    (dec : FredholmDecomposition 𝕜 E) : E →L[𝕜] dec.X₀ :=
  dec.X₀.projectionOntoL dec.X₁ dec.isTopCompl.symm

namespace ContinuousLinearMap

open Module

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F G : Type*}
variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
variable [AddCommGroup G] [TopologicalSpace G] [Module 𝕜 G]

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

end RestrictScalars

namespace FredholmPackage

noncomputable section

variable {T : E →L[𝕜] F} (pkg : T.FredholmPackage)

-- The body is exposed so that `pkg.symm.decDom` and `pkg.symm.decCodom` reduce in downstream types.
/-- Swapping the domain and codomain decompositions of a `FredholmPackage` for `T` gives a
`FredholmPackage` for `pkg.quasiInverse`. -/
@[expose]
def symm : pkg.quasiInverse.FredholmPackage where
  decDom := pkg.decCodom
  decCodom := pkg.decDom
  equiv := pkg.equiv.symm
  eq_equiv := rfl

@[simp]
theorem symm_decDom : pkg.symm.decDom = pkg.decCodom :=
  rfl

@[simp]
theorem symm_decCodom : pkg.symm.decCodom = pkg.decDom :=
  rfl

@[simp]
theorem symm_equiv : pkg.symm.equiv = pkg.equiv.symm :=
  rfl

/-- Taking the quasi-inverse of the dual package recovers the original operator. -/
@[simp]
theorem symm_quasiInverse : pkg.symm.quasiInverse = T :=
  pkg.eq_equiv.symm

/-- The kernel of `pkg.quasiInverse` is the finite-dimensional codomain complement `decCodom.X₀`. -/
@[simp]
theorem ker_quasiInverse : pkg.quasiInverse.ker = pkg.decCodom.X₀ :=
  pkg.symm.ker_eq

/-- The range of `pkg.quasiInverse` is the essential domain summand `decDom.X₁`. -/
@[simp]
theorem range_quasiInverse : pkg.quasiInverse.range = pkg.decDom.X₁ :=
  pkg.symm.range_eq

/-- Left composition of `T` with `pkg.quasiInverse` is the projection onto `decDom.X₁` along
`decDom.X₀`. -/
theorem quasiInverse_comp_self :
    pkg.quasiInverse ∘L T = pkg.decDom.X₁.projectionL pkg.decDom.X₀ pkg.decDom.isTopCompl := by
  ext x
  simp [pkg.eq_equiv, FredholmPackage.quasiInverse]

/-- Right composition of `T` with `pkg.quasiInverse` is the projection onto `decCodom.X₁` along
`decCodom.X₀`. -/
theorem self_comp_quasiInverse :
    T ∘L pkg.quasiInverse = pkg.decCodom.X₁.projectionL pkg.decCodom.X₀ pkg.decCodom.isTopCompl :=
  (congrArg (· ∘L pkg.quasiInverse) pkg.symm_quasiInverse.symm).trans
    pkg.symm.quasiInverse_comp_self

/-- The left quasi-inverse defect `id - pkg.quasiInverse ∘L T` is the finite-rank projection onto
the kernel `decDom.X₀` along `decDom.X₁`. -/
theorem id_sub_quasiInverse_comp_self [IsTopologicalAddGroup E] :
    ContinuousLinearMap.id 𝕜 E - pkg.quasiInverse ∘L T =
      pkg.decDom.X₀.projectionL pkg.decDom.X₁ pkg.decDom.isTopCompl.symm := by
  rw [pkg.quasiInverse_comp_self,
    ← Submodule.projectionL_eq_id_sub_projectionL pkg.decDom.isTopCompl]

/-- The right quasi-inverse defect `id - T ∘L pkg.quasiInverse` is the finite-rank projection onto
the codomain complement `decCodom.X₀` along `decCodom.X₁`. -/
theorem id_sub_self_comp_quasiInverse [IsTopologicalAddGroup F] :
    ContinuousLinearMap.id 𝕜 F - T ∘L pkg.quasiInverse =
      pkg.decCodom.X₀.projectionL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm := by
  rw [pkg.self_comp_quasiInverse,
    ← Submodule.projectionL_eq_id_sub_projectionL pkg.decCodom.isTopCompl]

/-- Two `FredholmPackage`s for `T` with the same essential domain summand `decDom.X₁` induce the
same ambient domain projection `E →L[𝕜] E` (and hence the same `quasiInverse ∘L T`). -/
theorem projectionL_decDom_eq_of_X₁_eq {pkg' : T.FredholmPackage}
    (hdom : pkg.decDom.X₁ = pkg'.decDom.X₁) :
    pkg.decDom.X₁.projectionL pkg.decDom.X₀ pkg.decDom.isTopCompl =
      pkg'.decDom.X₁.projectionL pkg'.decDom.X₀ pkg'.decDom.isTopCompl :=
  Submodule.projectionL_congr hdom (pkg.ker_eq.symm.trans pkg'.ker_eq)

/-- Two `FredholmPackage`s for `T` with the same codomain complement `decCodom.X₀` induce the same
ambient codomain projection `F →L[𝕜] F` (and hence the same `T ∘L quasiInverse`). -/
theorem projectionL_decCodom_eq_of_X₀_eq {pkg' : T.FredholmPackage}
    (hcod : pkg.decCodom.X₀ = pkg'.decCodom.X₀) :
    pkg.decCodom.X₁.projectionL pkg.decCodom.X₀ pkg.decCodom.isTopCompl =
      pkg'.decCodom.X₁.projectionL pkg'.decCodom.X₀ pkg'.decCodom.isTopCompl :=
  Submodule.projectionL_congr (pkg.range_eq.symm.trans pkg'.range_eq) hcod

/-- The quasi-inverse of a Fredholm package has finite range if and only if the entire domain `E`
is finite-dimensional; on an infinite-dimensional domain it is never a finite-rank map. -/
theorem hasFiniteRange_quasiInverse_iff :
    LinearMap.HasFiniteRange (pkg.quasiInverse : F →ₗ[𝕜] E) ↔ FiniteDimensional 𝕜 E := by
  have := pkg.decDom.finite_X₀
  rw [LinearMap.hasFiniteRange_iff_range, pkg.range_quasiInverse,
    Submodule.fg_iff_finiteDimensional]
  refine ⟨fun _ => ?_, fun _ => inferInstance⟩
  exact (Submodule.prodEquivOfIsCompl pkg.decDom.X₁ pkg.decDom.X₀
    pkg.decDom.isTopCompl.isCompl).finiteDimensional

/-- The index of an operator admitting a `FredholmPackage` is `dim decDom.X₀ - dim decCodom.X₀`. -/
theorem index_eq :
    T.index = (finrank 𝕜 pkg.decDom.X₀ : ℤ) - finrank 𝕜 pkg.decCodom.X₀ := by
  rw [index_eq_finrank_sub, pkg.ker_eq, pkg.range_eq,
    (pkg.decCodom.X₁.quotientEquivOfIsCompl pkg.decCodom.X₀
      pkg.decCodom.isTopCompl.isCompl).finrank_eq]

/-- The quasi-inverse of a `FredholmPackage` has index opposite to that of `T`. -/
@[simp]
theorem index_quasiInverse : pkg.quasiInverse.index = -T.index := by
  rw [pkg.symm.index_eq, pkg.index_eq, symm_decDom, symm_decCodom]
  omega

/-- Over a complete scalar field, the quasi-inverse attached to a `FredholmPackage` is itself a
Fredholm operator. -/
theorem isFredholm_quasiInverse [CompleteSpace 𝕜]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
    [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F] [T2Space F] :
    IsFredholm pkg.quasiInverse :=
  pkg.symm.isFredholm

end

end FredholmPackage

end ContinuousLinearMap
