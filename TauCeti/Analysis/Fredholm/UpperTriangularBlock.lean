/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Prod
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.UpperTriangularBlock
import TauCeti.Analysis.Fredholm.Snake

/-!
# Fredholmness and index of upper-triangular block operators

Two-out-of-three Fredholmness for upper-triangular `2 × 2` block continuous linear operators
`ContinuousLinearMap.upperTriangularBlock A B D` between Hausdorff topological vector spaces over a
complete `NontriviallyNormedField`, proved via the shear factorization
`ContinuousLinearMap.upperTriangularBlock_eq_prodMap_comp_shear_comp_prodMap`, together with
index additivity `(upperTriangularBlock A B D).index = A.index + D.index` via the Fredholm snake
index theorems (`TauCeti.Analysis.Fredholm.Snake`).

## Main results

* `ContinuousLinearMap.IsFredholm.upperTriangularBlock`: if `A` and `D` are Fredholm, so is
  `upperTriangularBlock A B D` for any continuous `B`.
* `ContinuousLinearMap.IsFredholm.of_upperTriangularBlock_right`: if `upperTriangularBlock A B D`
  and `A` are Fredholm, then `D` is Fredholm.
* `ContinuousLinearMap.IsFredholm.of_upperTriangularBlock_left`: if `upperTriangularBlock A B D`
  and `D` are Fredholm, then `A` is Fredholm.
* `ContinuousLinearMap.index_upperTriangularBlock`,
  `ContinuousLinearMap.index_upperTriangularBlock_of_left`, and
  `ContinuousLinearMap.index_upperTriangularBlock_of_right`: index additivity for upper-triangular
  blocks.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A.1.
-/

public section

namespace ContinuousLinearMap

section TVSBlock

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E₁ E₂ F₁ F₂ : Type*}
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module 𝕜 E₂]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module 𝕜 F₁] [IsTopologicalAddGroup F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module 𝕜 F₂]
  [CompleteSpace 𝕜]
  [IsTopologicalAddGroup E₁] [ContinuousSMul 𝕜 E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul 𝕜 E₂] [T2Space E₂]
  [ContinuousSMul 𝕜 F₁] [T2Space F₁]
  [IsTopologicalAddGroup F₂] [ContinuousSMul 𝕜 F₂] [T2Space F₂]

/-- Between Hausdorff topological vector spaces over a complete `NontriviallyNormedField`, an
upper-triangular block operator with Fredholm diagonal blocks `A` and `D` is Fredholm for any
continuous off-diagonal block `B`. -/
theorem IsFredholm.upperTriangularBlock {A : E₁ →L[𝕜] F₁} (hA : A.IsFredholm) (B : E₂ →L[𝕜] F₁)
    {D : E₂ →L[𝕜] F₂} (hD : D.IsFredholm) :
    (ContinuousLinearMap.upperTriangularBlock A B D).IsFredholm := by
  rw [A.upperTriangularBlock_eq_prodMap_comp_shear_comp_prodMap B D]
  exact (IsFredholm.id.prodMap hD).comp ((hA.prodMap .id).equiv_comp B.upperTriangularBlockShear)

/-- Two-out-of-three for upper-triangular blocks (bottom-right block): if
`upperTriangularBlock A B D` and `A` are Fredholm between Hausdorff topological vector spaces over
a complete `NontriviallyNormedField`, then `D` is Fredholm. -/
theorem IsFredholm.of_upperTriangularBlock_right
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₁} {D : E₂ →L[𝕜] F₂}
    (hM : (ContinuousLinearMap.upperTriangularBlock A B D).IsFredholm) (hA : A.IsFredholm) :
    D.IsFredholm := by
  rw [A.upperTriangularBlock_eq_prodMap_comp_shear_comp_prodMap B D] at hM
  exact (((((hA.prodMap .id).equiv_comp B.upperTriangularBlockShear).comp_iff_left).mp
    hM)).of_prodMap_right

/-- Two-out-of-three for upper-triangular blocks (top-left block): if `upperTriangularBlock A B D`
and `D` are Fredholm between Hausdorff topological vector spaces over a complete
`NontriviallyNormedField`, then `A` is Fredholm. -/
theorem IsFredholm.of_upperTriangularBlock_left
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₁} {D : E₂ →L[𝕜] F₂}
    (hM : (ContinuousLinearMap.upperTriangularBlock A B D).IsFredholm) (hD : D.IsFredholm) :
    A.IsFredholm := by
  rw [A.upperTriangularBlock_eq_prodMap_comp_shear_comp_prodMap B D, ← comp_assoc] at hM
  exact (((((IsFredholm.id.prodMap hD).comp_equiv B.upperTriangularBlockShear).comp_iff_right).mp
    hM)).of_prodMap_left

end TVSBlock

section FredholmBlockIndex

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E₁ E₂ F₁ F₂ : Type*}
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module 𝕜 E₂]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module 𝕜 F₁] [ContinuousAdd F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module 𝕜 F₂]
  (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)

/-- The index of an upper-triangular block operator `[[A, B], [0, D]]` with Fredholm diagonal
blocks is `A.index + D.index`, independently of the off-diagonal block `B`. -/
theorem index_upperTriangularBlock (hA : A.IsFredholm) (hD : D.IsFredholm) :
    (upperTriangularBlock A B D).index = A.index + D.index :=
  hA.index_eq_add_of_exact hD .inl_snd .inl_snd LinearMap.inl_injective LinearMap.snd_surjective
    LinearMap.inl_injective LinearMap.snd_surjective
    (A.upperTriangularBlock_comp_inl B D).symm (A.snd_comp_upperTriangularBlock B D)

/-- Index additivity for `upperTriangularBlock A B D` when `A` and the block operator are
Fredholm. -/
theorem index_upperTriangularBlock_of_left
    (hA : A.IsFredholm) (hM : (upperTriangularBlock A B D).IsFredholm) :
    (upperTriangularBlock A B D).index = A.index + D.index :=
  hA.index_eq_add_of_exact_of_left_middle hM .inl_snd .inl_snd LinearMap.inl_injective
    LinearMap.snd_surjective LinearMap.inl_injective LinearMap.snd_surjective
    (A.upperTriangularBlock_comp_inl B D).symm (A.snd_comp_upperTriangularBlock B D)

/-- Index additivity for `upperTriangularBlock A B D` when the block operator and `D` are
Fredholm. -/
theorem index_upperTriangularBlock_of_right
    (hM : (upperTriangularBlock A B D).IsFredholm) (hD : D.IsFredholm) :
    (upperTriangularBlock A B D).index = A.index + D.index :=
  hM.index_eq_add_of_exact_of_middle_right hD .inl_snd .inl_snd LinearMap.inl_injective
    LinearMap.snd_surjective LinearMap.inl_injective LinearMap.snd_surjective
    (A.upperTriangularBlock_comp_inl B D).symm (A.snd_comp_upperTriangularBlock B D)

end FredholmBlockIndex

end ContinuousLinearMap
