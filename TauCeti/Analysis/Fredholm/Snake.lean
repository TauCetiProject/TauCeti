/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.ClosedRange
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Snake
import TauCeti.Analysis.Fredholm.Prod

/-!
# Fredholm snake index additivity and two-out-of-three theorems

Given a commuting diagram of continuous linear maps between two exact three-term rows
```text
      E₁ --f₁--> E₂ --f₂--> E₃ ⟶ 0
      |          |          |
     T₁         T₂         T₃
      v          v          v
0 ⟶ F₁ --g₁--> F₂ --g₂--> F₃
```
whose algebraic and topological connecting maps are constructed in
`TauCeti.Algebra.Module.LinearMap.Snake`,
`TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Snake`, and
`TauCeti.Analysis.Normed.Operator.Snake`, this module establishes the Fredholm consequences:

* **Index additivity along short exact sequences**: if any two of `T₁, T₂, T₃` are Fredholm in a
  short exact diagram over a `NontriviallyNormedField`, their indices satisfy
  `T₂.index = T₁.index + T₃.index` (`TauCeti.index_eq_add_of_isFredholm_left_right`,
  `TauCeti.index_eq_add_of_isFredholm_left_middle`,
  `TauCeti.index_eq_add_of_isFredholm_middle_right`), with no completeness assumptions.
* **Two-out-of-three Fredholmness on Banach spaces**: if the target column consists of Banach spaces
  over an `IsRCLikeNormedField` and the other two vertical maps are Fredholm, then the third
  vertical map is Fredholm (`TauCeti.isFredholm_middle_of_exact`,
  `TauCeti.isFredholm_right_of_exact`, `TauCeti.isFredholm_left_of_exact`).
* **Upper-triangular block operators**: for `ContinuousLinearMap.upperTriangularBlock A B D`, index
  additivity `(upperTriangularBlock A B D).index = A.index + D.index` holds whenever any two of
  `A`, `upperTriangularBlock A B D`, and `D` are Fredholm
  (`ContinuousLinearMap.index_upperTriangularBlock` and companions), while two-out-of-three
  Fredholmness holds on Hausdorff topological vector spaces over any complete
  `NontriviallyNormedField` via shear factorization
  (`ContinuousLinearMap.IsFredholm.upperTriangularBlock`,
  `ContinuousLinearMap.IsFredholm.of_upperTriangularBlock_right`,
  `ContinuousLinearMap.IsFredholm.of_upperTriangularBlock_left`; compare the compact-perturbation
  parametrix in `TauCeti.Analysis.Normed.Operator.Compact.UpperTriangularBlock`).
* **Composition snake diagram**: `ContinuousLinearMap.compSnakeMiddle T S` is Fredholm if and only
  if `S ∘L T` is Fredholm (`ContinuousLinearMap.isFredholm_compSnakeMiddle_iff`), recovering
  Atkinson index additivity `(S ∘L T).index = S.index + T.index` from the snake index formula.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §19.1,
  Theorem 19.1.2 and Corollary 19.1.7.
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A.1.
-/

public section

namespace TauCeti

section FredholmIndex

variable {𝕜 E₁ E₂ E₃ F₁ F₂ F₃ : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module 𝕜 E₂]
  [TopologicalSpace E₃] [AddCommGroup E₃] [Module 𝕜 E₃]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module 𝕜 F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module 𝕜 F₂]
  [TopologicalSpace F₃] [AddCommGroup F₃] [Module 𝕜 F₃]

/-- **Index additivity along short exact sequences** when the left and right vertical operators
are Fredholm: `T₂.index = T₁.index + T₃.index`. -/
theorem index_eq_add_of_isFredholm_left_right
    {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂} {T₃ : E₃ →L[𝕜] F₃}
    {f₁ : E₁ →L[𝕜] E₂} {f₂ : E₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] F₂} {g₂ : F₂ →L[𝕜] F₃}
    (hf₁ : Function.Injective f₁) (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂) (hg₂ : Function.Surjective g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    (hT₁ : T₁.IsFredholm) (hT₃ : T₃.IsFredholm) :
    T₂.index = T₁.index + T₃.index := by
  have := hT₁.finite_ker
  have := hT₃.finite_ker
  have := hT₁.finite_coker
  have := hT₃.finite_coker
  simp only [ContinuousLinearMap.index_def]
  exact index_eq_add_of_shortExact hf₁ hf hf₂ hg₁ hg hg₂
    (congrArg ContinuousLinearMap.toLinearMap h₁₂)
    (congrArg ContinuousLinearMap.toLinearMap h₂₃)

/-- Index additivity along short exact sequences when the left and middle vertical operators are
Fredholm. -/
theorem index_eq_add_of_isFredholm_left_middle
    {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂} {T₃ : E₃ →L[𝕜] F₃}
    {f₁ : E₁ →L[𝕜] E₂} {f₂ : E₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] F₂} {g₂ : F₂ →L[𝕜] F₃}
    (hf₁ : Function.Injective f₁) (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂) (hg₂ : Function.Surjective g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    (hT₁ : T₁.IsFredholm) (hT₂ : T₂.IsFredholm) :
    T₂.index = T₁.index + T₃.index := by
  have := hT₁.finite_ker
  have := hT₂.finite_ker
  have := hT₁.finite_coker
  have := hT₂.finite_coker
  simp only [ContinuousLinearMap.index_def]
  exact index_eq_add_of_shortExact_of_left_middle hf₁ hf hf₂ hg₁ hg hg₂
    (congrArg ContinuousLinearMap.toLinearMap h₁₂)
    (congrArg ContinuousLinearMap.toLinearMap h₂₃)

/-- Index additivity along short exact sequences when the middle and right vertical operators are
Fredholm. -/
theorem index_eq_add_of_isFredholm_middle_right
    {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂} {T₃ : E₃ →L[𝕜] F₃}
    {f₁ : E₁ →L[𝕜] E₂} {f₂ : E₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] F₂} {g₂ : F₂ →L[𝕜] F₃}
    (hf₁ : Function.Injective f₁) (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂) (hg₂ : Function.Surjective g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    (hT₂ : T₂.IsFredholm) (hT₃ : T₃.IsFredholm) :
    T₂.index = T₁.index + T₃.index := by
  have := hT₂.finite_ker
  have := hT₃.finite_ker
  have := hT₂.finite_coker
  have := hT₃.finite_coker
  simp only [ContinuousLinearMap.index_def]
  exact index_eq_add_of_shortExact_of_middle_right hf₁ hf hf₂ hg₁ hg hg₂
    (congrArg ContinuousLinearMap.toLinearMap h₁₂)
    (congrArg ContinuousLinearMap.toLinearMap h₂₃)

end FredholmIndex

section TwoOutOfThree

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]

/-- **Two-out-of-three Fredholmness (middle column)**: if the left and right vertical operators in
a snake diagram are Fredholm and the middle column consists of Banach spaces over an
`IsRCLikeNormedField`, then the middle vertical operator is Fredholm. -/
theorem isFredholm_middle_of_exact
    {E₁ E₂ E₃ F₁ F₂ F₃ : Type*}
    [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
    [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
    [TopologicalSpace E₃] [AddCommGroup E₃] [Module 𝕜 E₃]
    [TopologicalSpace F₁] [AddCommGroup F₁] [Module 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [CompleteSpace F₂]
    [TopologicalSpace F₃] [AddCommGroup F₃] [Module 𝕜 F₃]
    {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂} {T₃ : E₃ →L[𝕜] F₃}
    {f₁ : E₁ →L[𝕜] E₂} {f₂ : E₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] F₂} {g₂ : F₂ →L[𝕜] F₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    (hT₁ : T₁.IsFredholm) (hT₃ : T₃.IsFredholm) :
    T₂.IsFredholm := by
  have := hT₁.finite_ker
  have := hT₃.finite_ker
  have := hT₁.finite_coker
  have := hT₃.finite_coker
  exact .of_finite_ker_coker T₂
    (finiteDimensional_ker_middle hf hg₁
      (congrArg ContinuousLinearMap.toLinearMap h₁₂)
      (congrArg ContinuousLinearMap.toLinearMap h₂₃))
    (finiteDimensional_coker_middle hf₂ hg
      (congrArg ContinuousLinearMap.toLinearMap h₁₂)
      (congrArg ContinuousLinearMap.toLinearMap h₂₃))

/-- **Two-out-of-three Fredholmness (right column)**: if the left and middle vertical operators in
a snake diagram with surjective `g₂` are Fredholm and the right column consists of Banach spaces
over an `IsRCLikeNormedField`, then the right vertical operator is Fredholm. -/
theorem isFredholm_right_of_exact
    {E₁ E₂ E₃ F₁ F₂ F₃ : Type*}
    [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
    [TopologicalSpace E₂] [AddCommGroup E₂] [Module 𝕜 E₂]
    [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃] [CompleteSpace E₃]
    [TopologicalSpace F₁] [AddCommGroup F₁] [Module 𝕜 F₁]
    [TopologicalSpace F₂] [AddCommGroup F₂] [Module 𝕜 F₂]
    [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] [CompleteSpace F₃]
    {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂} {T₃ : E₃ →L[𝕜] F₃}
    {f₁ : E₁ →L[𝕜] E₂} {f₂ : E₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] F₂} {g₂ : F₂ →L[𝕜] F₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂) (hg₂ : Function.Surjective g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    (hT₁ : T₁.IsFredholm) (hT₂ : T₂.IsFredholm) :
    T₃.IsFredholm := by
  have := hT₂.finite_ker
  have := hT₁.finite_coker
  have := hT₂.finite_coker
  exact .of_finite_ker_coker T₃
    (finiteDimensional_ker_right hf hf₂ hg hg₁
      (congrArg ContinuousLinearMap.toLinearMap h₁₂)
      (congrArg ContinuousLinearMap.toLinearMap h₂₃))
    (finiteDimensional_coker_right hg₂ (congrArg ContinuousLinearMap.toLinearMap h₂₃))

/-- **Two-out-of-three Fredholmness (left column)**: if the middle and right vertical operators in
a snake diagram with injective `f₁` are Fredholm and the left column consists of Banach spaces
over an `IsRCLikeNormedField`, then the left vertical operator is Fredholm. -/
theorem isFredholm_left_of_exact
    {E₁ E₂ E₃ F₁ F₂ F₃ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
    [TopologicalSpace E₂] [AddCommGroup E₂] [Module 𝕜 E₂]
    [TopologicalSpace E₃] [AddCommGroup E₃] [Module 𝕜 E₃]
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [CompleteSpace F₁]
    [TopologicalSpace F₂] [AddCommGroup F₂] [Module 𝕜 F₂]
    [TopologicalSpace F₃] [AddCommGroup F₃] [Module 𝕜 F₃]
    {T₁ : E₁ →L[𝕜] F₁} {T₂ : E₂ →L[𝕜] F₂} {T₃ : E₃ →L[𝕜] F₃}
    {f₁ : E₁ →L[𝕜] E₂} {f₂ : E₂ →L[𝕜] E₃} {g₁ : F₁ →L[𝕜] F₂} {g₂ : F₂ →L[𝕜] F₃}
    (hf₁ : Function.Injective f₁) (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    (hT₂ : T₂.IsFredholm) (hT₃ : T₃.IsFredholm) :
    T₁.IsFredholm := by
  have := hT₂.finite_ker
  have := hT₃.finite_ker
  have := hT₂.finite_coker
  exact .of_finite_ker_coker T₁
    (finiteDimensional_ker_left hf₁ (congrArg ContinuousLinearMap.toLinearMap h₁₂))
    (finiteDimensional_coker_left hf hf₂ hg hg₁
      (congrArg ContinuousLinearMap.toLinearMap h₁₂)
      (congrArg ContinuousLinearMap.toLinearMap h₂₃))

end TwoOutOfThree

end TauCeti

namespace ContinuousLinearMap

section FredholmBlockIndex

variable {𝕜 E₁ E₂ F₁ F₂ : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module 𝕜 E₂]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module 𝕜 F₁] [ContinuousAdd F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module 𝕜 F₂]

/-- The index of an upper-triangular block operator `[[A, B], [0, D]]` with Fredholm diagonal
blocks is `A.index + D.index`, independently of the off-diagonal block `B`. -/
theorem index_upperTriangularBlock (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)
    (hA : A.IsFredholm) (hD : D.IsFredholm) :
    (upperTriangularBlock A B D).index = A.index + D.index :=
  TauCeti.index_eq_add_of_isFredholm_left_right
    LinearMap.inl_injective .inl_snd LinearMap.snd_surjective
    LinearMap.inl_injective .inl_snd LinearMap.snd_surjective
    (A.upperTriangularBlock_comp_inl B D).symm (A.snd_comp_upperTriangularBlock B D)
    hA hD

/-- Index additivity for `upperTriangularBlock A B D` when `A` and the block operator are
Fredholm. -/
theorem index_upperTriangularBlock_of_left (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)
    (hA : A.IsFredholm) (hM : (upperTriangularBlock A B D).IsFredholm) :
    (upperTriangularBlock A B D).index = A.index + D.index :=
  TauCeti.index_eq_add_of_isFredholm_left_middle
    LinearMap.inl_injective .inl_snd LinearMap.snd_surjective
    LinearMap.inl_injective .inl_snd LinearMap.snd_surjective
    (A.upperTriangularBlock_comp_inl B D).symm (A.snd_comp_upperTriangularBlock B D)
    hA hM

/-- Index additivity for `upperTriangularBlock A B D` when the block operator and `D` are
Fredholm. -/
theorem index_upperTriangularBlock_of_right (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)
    (hM : (upperTriangularBlock A B D).IsFredholm) (hD : D.IsFredholm) :
    (upperTriangularBlock A B D).index = A.index + D.index :=
  TauCeti.index_eq_add_of_isFredholm_middle_right
    LinearMap.inl_injective .inl_snd LinearMap.snd_surjective
    LinearMap.inl_injective .inl_snd LinearMap.snd_surjective
    (A.upperTriangularBlock_comp_inl B D).symm (A.snd_comp_upperTriangularBlock B D)
    hM hD

end FredholmBlockIndex

section TVSBlock

variable {𝕜 E₁ E₂ F₁ F₂ : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module 𝕜 E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module 𝕜 E₂]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module 𝕜 F₁] [IsTopologicalAddGroup F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module 𝕜 F₂]

private def blockShearEquiv (B : E₂ →L[𝕜] F₁) : (F₁ × E₂) ≃L[𝕜] (F₁ × E₂) :=
  ((ContinuousLinearEquiv.prodComm 𝕜 F₁ E₂).trans
    ((ContinuousLinearEquiv.refl 𝕜 E₂).skewProd (ContinuousLinearEquiv.refl 𝕜 F₁) B)).trans
    (ContinuousLinearEquiv.prodComm 𝕜 E₂ F₁)

private theorem upperTriangularBlock_eq_shear_comp
    (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂) :
    upperTriangularBlock A B D =
      ((ContinuousLinearMap.id 𝕜 F₁).prodMap D) ∘L
        (blockShearEquiv B : F₁ × E₂ →L[𝕜] F₁ × E₂) ∘L
          (A.prodMap (ContinuousLinearMap.id 𝕜 E₂)) := by
  apply ContinuousLinearMap.ext
  rintro ⟨x₁, x₂⟩
  ext <;> simp [blockShearEquiv]

variable [CompleteSpace 𝕜]
  [IsTopologicalAddGroup E₁] [ContinuousSMul 𝕜 E₁] [T2Space E₁]
  [IsTopologicalAddGroup E₂] [ContinuousSMul 𝕜 E₂] [T2Space E₂]
  [ContinuousSMul 𝕜 F₁] [T2Space F₁]
  [IsTopologicalAddGroup F₂] [ContinuousSMul 𝕜 F₂] [T2Space F₂]

/-- Between Hausdorff topological vector spaces over a complete `NontriviallyNormedField`, an
upper-triangular block operator with Fredholm diagonal blocks `A` and `D` is Fredholm for any
continuous off-diagonal block `B`. -/
theorem IsFredholm.upperTriangularBlock
    {A : E₁ →L[𝕜] F₁} (hA : A.IsFredholm) (B : E₂ →L[𝕜] F₁) {D : E₂ →L[𝕜] F₂}
    (hD : D.IsFredholm) :
    (ContinuousLinearMap.upperTriangularBlock A B D).IsFredholm := by
  rw [upperTriangularBlock_eq_shear_comp]
  exact (IsFredholm.id.prodMap hD).comp ((hA.prodMap .id).equiv_comp (blockShearEquiv B))

/-- Two-out-of-three for upper-triangular blocks (bottom-right block): if
`upperTriangularBlock A B D` and `A` are Fredholm between Hausdorff topological vector spaces over
a complete `NontriviallyNormedField`, then `D` is Fredholm. -/
theorem IsFredholm.of_upperTriangularBlock_right
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₁} {D : E₂ →L[𝕜] F₂}
    (hM : (ContinuousLinearMap.upperTriangularBlock A B D).IsFredholm) (hA : A.IsFredholm) :
    D.IsFredholm := by
  rw [upperTriangularBlock_eq_shear_comp] at hM
  exact (((((hA.prodMap .id).equiv_comp (blockShearEquiv B)).comp_iff_left).mp hM)).of_prodMap_right

/-- Two-out-of-three for upper-triangular blocks (top-left block): if `upperTriangularBlock A B D`
and `D` are Fredholm between Hausdorff topological vector spaces over a complete
`NontriviallyNormedField`, then `A` is Fredholm. -/
theorem IsFredholm.of_upperTriangularBlock_left
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₁} {D : E₂ →L[𝕜] F₂}
    (hM : (ContinuousLinearMap.upperTriangularBlock A B D).IsFredholm) (hD : D.IsFredholm) :
    A.IsFredholm := by
  rw [upperTriangularBlock_eq_shear_comp, ← comp_assoc] at hM
  exact (((((IsFredholm.id.prodMap hD).comp_equiv (blockShearEquiv B)).comp_iff_right).mp
    hM)).of_prodMap_left

end TVSBlock

section FredholmCompSnake

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [IsTopologicalAddGroup E]
  [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [IsTopologicalAddGroup F]
  [TopologicalSpace G] [AddCommGroup G] [Module 𝕜 G] [IsTopologicalAddGroup G]

/-- `compSnakeMiddle T S` is Fredholm if and only if the composite `S ∘L T` is Fredholm. Combined
with `index_compSnakeMiddle` and `index_upperTriangularBlock`, applying the snake index theorem to
`(T, compSnakeMiddle T S, S)` directly recovers `IsFredholm.index_comp`:
`(S ∘L T).index = (compSnakeMiddle T S).index = T.index + S.index = S.index + T.index`. -/
@[simp]
theorem isFredholm_compSnakeMiddle_iff (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    (compSnakeMiddle T S).IsFredholm ↔ (S ∘L T).IsFredholm := by
  let eCod : (F × G) ≃L[𝕜] (F × G) :=
    (ContinuousLinearEquiv.refl 𝕜 F).skewProd (ContinuousLinearEquiv.refl 𝕜 G) S
  let eDom : (F × E) ≃L[𝕜] (E × F) :=
    (ContinuousLinearEquiv.prodComm 𝕜 F E).trans
      ((ContinuousLinearEquiv.refl 𝕜 E).skewProd (ContinuousLinearEquiv.neg 𝕜) T)
  have h := isFredholm_iff_of_comp_eq eDom.symm eCod
    (T := compSnakeMiddle T S) (S := (ContinuousLinearMap.id 𝕜 F).prodMap (S ∘L T)) <| by
    apply ContinuousLinearMap.ext
    rintro ⟨x, y⟩
    ext <;> simp [eCod, eDom, sub_eq_add_neg, add_comm]
  rw [h, isFredholm_prodMap_iff]
  exact ⟨And.right, fun hST ↦ ⟨.id, hST⟩⟩

end FredholmCompSnake

end ContinuousLinearMap
