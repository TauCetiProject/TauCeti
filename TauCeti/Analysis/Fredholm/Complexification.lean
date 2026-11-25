/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Prod
public import TauCeti.Analysis.InnerProductSpace.Complexification
public import TauCeti.Topology.Algebra.Module.Complexification
import TauCeti.Analysis.Normed.Operator.ComplexLinearPart

/-!
# Complexification of real Fredholm operators

A real Fredholm operator and its complexification are Fredholm together and have the same index.
This is how real elliptic operators enter complex index theory: the complex index of the
complexified operator is the real index of the original one.

The index statement is algebraic. For a real-linear map `T`, the kernel of its complexification
is the complexification `ℂ ⊗[ℝ] ker T` of the kernel (`LinearMap.tensorKerEquiv`, since `ℂ` is flat
over `ℝ`), and its cokernel is the complexification of the cokernel
(`LinearMap.cokernelBaseChangeEquiv`). So the complex dimensions of the kernel and cokernel are
the real dimensions of the real ones, and `LinearMap.index_baseChange` gives equality of indices,
with no Fredholm hypothesis.

Fredholmness is topological. Over the real numbers the complexification of `T` is conjugate, by
the real coordinates `x + i y ↦ (x, y)`, to the product `T × T`, which is Fredholm exactly when
`T` is (`ContinuousLinearMap.isFredholm_prodMap_iff`). A complex operator is Fredholm exactly when
its realification is (`ContinuousLinearMap.isFredholm_restrictScalars_real_iff`): the only
condition that does not transfer directly is the complementation of the kernel, and a real
continuous projection onto a complex subspace is turned into a complex one by taking its
complex-linear part (`Submodule.ClosedComplemented.of_restrictScalars`).

Three carriers of the complexification are covered: the algebraic tensor product `ℂ ⊗[ℝ] W` of a
real topological vector space with its product topology (`ContinuousLinearMap.baseChangeComplex`),
the normed complexification `TauCeti.Complexification X` with its Taylor norm
(`ContinuousLinearMap.complexify`), and the Hilbert complexification
`WithLp 2 (TauCeti.Complexification X)` with its `L²` norm (`ContinuousLinearMap.complexifyL2`).

## Main results

* `ContinuousLinearMap.isFredholm_restrictScalars_real_iff`: a complex-linear operator is Fredholm
  exactly when its realification is.
* `ContinuousLinearMap.isFredholm_baseChangeComplex_iff`,
  `ContinuousLinearMap.isFredholm_complexify_iff`,
  `ContinuousLinearMap.isFredholm_complexifyL2_iff`: the complexification of a real operator is
  Fredholm exactly when the operator is.
* `ContinuousLinearMap.index_baseChangeComplex`, `ContinuousLinearMap.index_complexify`,
  `ContinuousLinearMap.index_complexifyL2`: the complexification of a real operator has the same
  index.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. **87** (1968),
  484–530, where real operators are treated through their complexifications.
-/

public section

open TauCeti
open scoped TensorProduct

namespace ContinuousLinearMap

section RestrictScalars

variable {E F : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [Module ℝ E]
  [Module ℂ E] [IsScalarTower ℝ ℂ E] [ContinuousConstSMul ℂ E]
  [AddCommGroup F] [TopologicalSpace F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F]

/-- A complex-linear operator is Fredholm exactly when its realification is. -/
@[simp]
theorem isFredholm_restrictScalars_real_iff {T : E →L[ℂ] F} :
    (T.restrictScalars ℝ).IsFredholm ↔ T.IsFredholm := by
  refine ⟨fun hT ↦ ⟨?_, ?_, ?_, ?_, ?_⟩, fun hT ↦ hT.restrictScalars ℝ⟩
  · simpa only [coe_restrictScalars'] using hT.isStrictMap
  · simpa only [coe_restrictScalars, LinearMap.range_restrictScalars,
      Submodule.coe_restrictScalars] using hT.isClosed_range
  · -- The kernel of the realification is `T.ker` with its inherited real structure.
    have : Module.Finite ℝ T.ker := hT.finite_ker
    exact Module.Finite.of_restrictScalars_finite ℝ ℂ T.ker
  · have : Module.Finite ℝ (F ⧸ T.range.restrictScalars ℝ) := by
      simpa only [coe_restrictScalars, LinearMap.range_restrictScalars] using hT.finite_coker
    have : Module.Finite ℝ (F ⧸ T.range) :=
      (Submodule.Quotient.restrictScalarsEquiv ℝ T.range).finiteDimensional
    exact Module.Finite.of_restrictScalars_finite ℝ ℂ (F ⧸ T.range)
  · exact .of_restrictScalars hT.closedComplemented_ker

end RestrictScalars

section BaseChangeComplex

variable {W W' : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [TopologicalSpace (ℂ ⊗[ℝ] W)]
  [IsComplexificationTopology W] [AddCommGroup W'] [Module ℝ W'] [TopologicalSpace W']
  [TopologicalSpace (ℂ ⊗[ℝ] W')] [IsComplexificationTopology W']

/-- The complexification `ℂ ⊗[ℝ] W → ℂ ⊗[ℝ] W'` of a real operator is Fredholm exactly when the
operator is. -/
@[simp]
theorem isFredholm_baseChangeComplex_iff {T : W →L[ℝ] W'} :
    T.baseChangeComplex.IsFredholm ↔ T.IsFredholm := by
  rw [← isFredholm_restrictScalars_real_iff,
    isFredholm_iff_of_comp_eq (S := T.prodMap T) (complexificationEquivProd W)
      (complexificationEquivProd W') (by ext u <;> simp),
    isFredholm_prodMap_iff, and_self]

end BaseChangeComplex

/-- The complexification `ℂ ⊗[ℝ] W → ℂ ⊗[ℝ] W'` of a real operator has the same index as the
operator. No Fredholm hypothesis is needed. -/
@[simp]
theorem index_baseChangeComplex {W W' : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
    [TopologicalSpace (ℂ ⊗[ℝ] W)] [IsComplexificationTopology W] [AddCommGroup W'] [Module ℝ W']
    [TopologicalSpace W'] [TopologicalSpace (ℂ ⊗[ℝ] W')] [IsComplexificationTopology W']
    (T : W →L[ℝ] W') : T.baseChangeComplex.index = T.index := by
  rw [index_def, index_def, toLinearMap_baseChangeComplex, LinearMap.index_baseChange]

section Complexify

variable {X Y : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X] [SeminormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- The complexification `TauCeti.Complexification X → TauCeti.Complexification Y` of a real
operator is Fredholm exactly when the operator is. -/
@[simp]
theorem isFredholm_complexify_iff {T : X →L[ℝ] Y} :
    T.complexify.IsFredholm ↔ T.IsFredholm := by
  rw [← isFredholm_restrictScalars_real_iff,
    isFredholm_iff_of_comp_eq (S := T.prodMap T) (Complexification.equivProd X)
      (Complexification.equivProd Y) (by ext z <;> simp),
    isFredholm_prodMap_iff, and_self]

/-- The complexification `TauCeti.Complexification X → TauCeti.Complexification Y` of a real
operator has the same index as the operator. No Fredholm hypothesis is needed. -/
@[simp]
theorem index_complexify (T : X →L[ℝ] Y) : T.complexify.index = T.index := by
  rw [index_def, index_def, coe_complexify,
    ← LinearMap.arrowCongr_tensorEquivComplexification_baseChange, LinearMap.index_arrowCongr,
    LinearMap.index_baseChange]

end Complexify

section ComplexifyL2

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- The Hilbert complexification `WithLp 2 (TauCeti.Complexification X) → WithLp 2
(TauCeti.Complexification Y)` of a real operator is Fredholm exactly when the operator is. -/
@[simp]
theorem isFredholm_complexifyL2_iff {T : X →L[ℝ] Y} :
    T.complexifyL2.IsFredholm ↔ T.IsFredholm := by
  have : ContinuousConstSMul ℂ (WithLp 2 (Complexification X)) :=
    ⟨WithLp.complexification_continuous_const_smul⟩
  rw [← isFredholm_restrictScalars_real_iff,
    isFredholm_iff_of_comp_eq (S := T.withLpProdMap 2 T)
      (WithLp.complexificationEquivProd X).toContinuousLinearEquiv
      (WithLp.complexificationEquivProd Y).toContinuousLinearEquiv (by ext z; simp),
    isFredholm_withLpProdMap_iff, and_self]

/-- The Hilbert complexification `WithLp 2 (TauCeti.Complexification X) → WithLp 2
(TauCeti.Complexification Y)` of a real operator has the same index as the operator. No Fredholm
hypothesis is needed. -/
@[simp]
theorem index_complexifyL2 (T : X →L[ℝ] Y) : T.complexifyL2.index = T.index := by
  rw [← index_complexify, index_def, index_def, coe_complexifyL2, LinearMap.index_arrowCongr]

end ComplexifyL2

end ContinuousLinearMap
