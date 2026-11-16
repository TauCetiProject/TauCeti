/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Fredholm.Snake.Index
public import TauCeti.LinearAlgebra.Exact

import Mathlib.Tactic.Abel
import TauCeti.Analysis.Fredholm.Prod

/-!
# Upper-triangular block Fredholm operators and the composition snake diagram

Specializing the Fredholm snake sequence of `TauCeti.Analysis.Fredholm.Snake.Index` to
`0 → E₁ → E₁ × E₂ → E₂ → 0` treats upper-triangular block operators
`upperTriangular A B D (x, y) = (A x + B y, D y)`. Their connecting map is `y ↦ [B y]`, which is a
bijection whenever the block operator is bijective. Comparing with the explicit block parametrix
`upperTriangular PA (-(PA ∘ B ∘ PD)) PD` gives the `(A, D) ↦ M` direction in general TVSs, while
the snake lemma supplies the converse two-out-of-three directions `(M, D) ↦ A` and `(M, A) ↦ D`.

Finally, for composable operators `T : E →L[𝕜] F` and `S : F →L[𝕜] G`, the block operator
`upperTriangular T (-id) S : E × F →L[𝕜] F × G` is conjugate by triangular coordinate equivalences
to `(S ∘ T).prodMap (-id)`. Its snake sequence matches `LinearMap.kerCompToKer`,
`-LinearMap.kerToCoker` and `LinearMap.cokerToCokerComp`, recovering
`ContinuousLinearMap.IsFredholm.index_comp` and its two-out-of-three index variants.

## Main definitions

* `ContinuousLinearMap.upperTriangular`: the upper-triangular block operator
  `(x, y) ↦ (A x + B y, D y)`.
* `ContinuousLinearMap.upperTriangularNegIdCodEquiv`,
  `ContinuousLinearMap.upperTriangularNegIdDomEquiv`: triangular coordinate equivalences
  diagonalizing `upperTriangular T (-id) S`.
* `ContinuousLinearMap.kerUpperTriangularNegIdEquiv`,
  `ContinuousLinearMap.cokerUpperTriangularNegIdEquiv`: identifications of the kernel and cokernel
  of `upperTriangular T (-id) S` with those of `S ∘L T`.

## Main results

* `ContinuousLinearMap.snakeDeltaL_upperTriangular`,
  `ContinuousLinearMap.bijective_mkQL_comp_of_bijective_upperTriangular`: connecting map of an
  upper-triangular block operator.
* `ContinuousLinearMap.isQuasiInverse_upperTriangular`,
  `ContinuousLinearMap.IsFredholm.upperTriangular`,
  `ContinuousLinearMap.isCompactOperator_upperTriangular_parametrix_left`, `parametrix_right`:
  explicit block quasi-inverse and compact-error parametrices.
* `ContinuousLinearMap.IsFredholm.of_upperTriangular_left`, `of_upperTriangular_right`,
  `ContinuousLinearMap.index_upperTriangular_of_diag`, `of_left`, `of_right`: two-out-of-three
  and index additivity for upper-triangular block operators.
* `ContinuousLinearMap.isFredholm_upperTriangular_neg_id_iff`,
  `ContinuousLinearMap.index_upperTriangular_neg_id`,
  `ContinuousLinearMap.IsFredholm.index_comp_of_left`, `index_comp_of_right`: comparison with
  `ContinuousLinearMap.IsFredholm.index_comp`.
-/

public section

open Function

noncomputable section

namespace ContinuousLinearMap

/-! ### Upper-triangular block operators and block parametrices -/

section UpperTriangularDefs

variable {𝕜 : Type*} [Semiring 𝕜]
variable {E₁ E₂ F₁ F₂ G₁ G₂ : Type*}
variable [AddCommMonoid E₁] [TopologicalSpace E₁] [Module 𝕜 E₁]
variable [AddCommMonoid E₂] [TopologicalSpace E₂] [Module 𝕜 E₂]
variable [AddCommMonoid F₁] [TopologicalSpace F₁] [Module 𝕜 F₁] [ContinuousAdd F₁]
variable [AddCommMonoid F₂] [TopologicalSpace F₂] [Module 𝕜 F₂]

/-- The product sequence `E₁ —inl→ E₁ × E₂ —snd→ E₂` of continuous linear maps is exact. -/
theorem exact_inl_snd : Exact (inl 𝕜 E₁ E₂) (snd 𝕜 E₁ E₂) :=
  Function.Exact.inl_snd

/-- The **upper-triangular block operator** `E₁ × E₂ →L[𝕜] F₁ × F₂` sending `(x, y)` to
`(A x + B y, D y)`. -/
def upperTriangular (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂) :
    E₁ × E₂ →L[𝕜] F₁ × F₂ :=
  (A.coprod B).prod (D.comp (snd 𝕜 E₁ E₂))

@[simp]
theorem upperTriangular_apply (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)
    (x : E₁) (y : E₂) :
    upperTriangular A B D (x, y) = (A x + B y, D y) := (rfl)

@[simp]
theorem upperTriangular_zero (A : E₁ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂) :
    upperTriangular A 0 D = A.prodMap D :=
  ContinuousLinearMap.ext fun ⟨_, _⟩ ↦ by simp

@[simp]
theorem upperTriangular_comp_inl (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂) :
    (upperTriangular A B D).comp (inl 𝕜 E₁ E₂) = (inl 𝕜 F₁ F₂).comp A :=
  ContinuousLinearMap.ext fun _ ↦ by simp

@[simp]
theorem snd_comp_upperTriangular (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂) :
    (snd 𝕜 F₁ F₂).comp (upperTriangular A B D) = D.comp (snd 𝕜 E₁ E₂) :=
  ContinuousLinearMap.ext fun ⟨_, _⟩ ↦ by simp

theorem upperTriangular_comp [AddCommMonoid G₁] [TopologicalSpace G₁] [Module 𝕜 G₁]
    [ContinuousAdd G₁] [AddCommMonoid G₂] [TopologicalSpace G₂] [Module 𝕜 G₂]
    (A₂ : F₁ →L[𝕜] G₁) (B₂ : F₂ →L[𝕜] G₁) (D₂ : F₂ →L[𝕜] G₂)
    (A₁ : E₁ →L[𝕜] F₁) (B₁ : E₂ →L[𝕜] F₁) (D₁ : E₂ →L[𝕜] F₂) :
    (upperTriangular A₂ B₂ D₂).comp (upperTriangular A₁ B₁ D₁) =
      upperTriangular (A₂.comp A₁) (A₂.comp B₁ + B₂.comp D₁) (D₂.comp D₁) :=
  ContinuousLinearMap.ext fun ⟨_, _⟩ ↦ by simp [map_add, add_assoc]

end UpperTriangularDefs

section UpperTriangularSnake

variable {𝕜 : Type*} [Ring 𝕜]
variable {E₁ E₂ F₁ F₂ : Type*}
variable [AddCommGroup E₁] [TopologicalSpace E₁] [Module 𝕜 E₁]
variable [AddCommGroup E₂] [TopologicalSpace E₂] [Module 𝕜 E₂]
variable [AddCommGroup F₁] [TopologicalSpace F₁] [Module 𝕜 F₁] [ContinuousAdd F₁]
variable [AddCommGroup F₂] [TopologicalSpace F₂] [Module 𝕜 F₂]

/-- **Connecting map of an upper-triangular block operator:** for `M = upperTriangular A B D`,
the snake connecting map `δ : ker D →L[𝕜] (F₁ ⧸ range A)` sends `y ∈ ker D` to `[B y]`. -/
theorem snakeDeltaL_upperTriangular (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂) :
    TauCeti.snakeDeltaL (i := inl 𝕜 E₁ E₂) (p := snd 𝕜 E₁ E₂)
      (j := inl 𝕜 F₁ F₂) (q := snd 𝕜 F₁ F₂)
      (T₁ := A) (T₂ := upperTriangular A B D) (T₃ := D)
      exact_inl_snd exact_inl_snd
      ⟨inr 𝕜 E₁ E₂, by intro _; simp⟩ ⟨fst 𝕜 F₁ F₂, by intro _; simp⟩
      (upperTriangular_comp_inl A B D) (snd_comp_upperTriangular A B D).symm =
      A.range.mkQL.comp (B.comp D.ker.subtypeL) :=
  (TauCeti.snakeDeltaL_eq_comp _ _ _ _ _ _ (s := inr 𝕜 E₁ E₂) (fun _ ↦ rfl)
    (r := fst 𝕜 F₁ F₂) (fun _ ↦ rfl)).trans <| ContinuousLinearMap.ext fun y ↦ by simp

/-- When `upperTriangular A B D` is bijective, `y ↦ [B y]` is a bijection `ker D → F₁ ⧸ range A`
(even if both spaces are infinite-dimensional). In particular, invertibility of the middle
operator alone places no Fredholm restriction on `A` or `D`. -/
theorem bijective_mkQL_comp_of_bijective_upperTriangular
    (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)
    (hbij : Bijective (upperTriangular A B D)) :
    Bijective (A.range.mkQL.comp (B.comp D.ker.subtypeL)) := by
  have h : (A.range.mkQL.comp (B.comp D.ker.subtypeL)).toLinearMap =
      TauCeti.snakeDelta exact_inl_snd LinearMap.snd_surjective
        exact_inl_snd LinearMap.inl_injective
        (congrArg ContinuousLinearMap.toLinearMap (upperTriangular_comp_inl A B D))
        (congrArg ContinuousLinearMap.toLinearMap (snd_comp_upperTriangular A B D).symm) :=
    (congrArg ContinuousLinearMap.toLinearMap (snakeDeltaL_upperTriangular A B D)).symm.trans
      (TauCeti.toLinearMap_snakeDeltaL _ _ _ _ _ _)
  rw [← ContinuousLinearMap.coe_coe, h]
  exact TauCeti.bijective_snakeDelta_of_bijective exact_inl_snd LinearMap.snd_surjective
    exact_inl_snd LinearMap.inl_injective
    (congrArg ContinuousLinearMap.toLinearMap (upperTriangular_comp_inl A B D))
    (congrArg ContinuousLinearMap.toLinearMap (snd_comp_upperTriangular A B D).symm) hbij

end UpperTriangularSnake

section UpperTriangularParametrix

variable {E₁ E₂ F₁ F₂ : Type*}
variable [AddCommGroup E₁] [AddCommGroup E₂] [AddCommGroup F₁] [AddCommGroup F₂]
variable [TopologicalSpace E₁] [TopologicalSpace E₂] [TopologicalSpace F₁] [TopologicalSpace F₂]

/-- **Block quasi-inverse:** if `PA` is a quasi-inverse of `A` and `PD` is a quasi-inverse of `D`,
then `upperTriangular PA (-(PA ∘L B ∘L PD)) PD` is a quasi-inverse of `upperTriangular A B D`. -/
theorem isQuasiInverse_upperTriangular {𝕜 : Type*} [CommRing 𝕜] [IsNoetherianRing 𝕜]
    [Module 𝕜 E₁] [Module 𝕜 E₂] [Module 𝕜 F₁] [Module 𝕜 F₂]
    [IsTopologicalAddGroup E₁] [ContinuousAdd F₁]
    (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)
    {PA : F₁ →L[𝕜] E₁} {PD : F₂ →L[𝕜] E₂}
    (hA : PA.toLinearMap.IsQuasiInverse A.toLinearMap)
    (hD : PD.toLinearMap.IsQuasiInverse D.toLinearMap) :
    (upperTriangular PA (-(PA.comp (B.comp PD))) PD).toLinearMap.IsQuasiInverse
      (upperTriangular A B D).toLinearMap := by
  have hPA_l : (PA.toLinearMap ∘ₗ A.toLinearMap - LinearMap.id).HasFiniteRange :=
    LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.1 hA.1
  have hPA_r : (A.toLinearMap ∘ₗ PA.toLinearMap - LinearMap.id).HasFiniteRange :=
    LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.1 hA.2
  have hPD_l : (PD.toLinearMap ∘ₗ D.toLinearMap - LinearMap.id).HasFiniteRange :=
    LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.1 hD.1
  have hPD_r : (D.toLinearMap ∘ₗ PD.toLinearMap - LinearMap.id).HasFiniteRange :=
    LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.1 hD.2
  constructor
  · rw [LinearMap.IsLeftQuasiInverse, LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange]
    have hdecomp :
        (upperTriangular PA (-(PA.comp (B.comp PD))) PD).toLinearMap ∘ₗ
          (upperTriangular A B D).toLinearMap - LinearMap.id =
        (LinearMap.inl 𝕜 E₁ E₂ ∘ₗ ((PA.toLinearMap ∘ₗ A.toLinearMap - LinearMap.id) ∘ₗ
            LinearMap.fst 𝕜 E₁ E₂)) +
        (LinearMap.inl 𝕜 E₁ E₂ ∘ₗ ((-(PA.toLinearMap ∘ₗ B.toLinearMap)) ∘ₗ
            ((PD.toLinearMap ∘ₗ D.toLinearMap - LinearMap.id) ∘ₗ LinearMap.snd 𝕜 E₁ E₂))) +
        (LinearMap.inr 𝕜 E₁ E₂ ∘ₗ ((PD.toLinearMap ∘ₗ D.toLinearMap - LinearMap.id) ∘ₗ
            LinearMap.snd 𝕜 E₁ E₂)) :=
      LinearMap.ext fun ⟨_, _⟩ ↦ by simp [map_add]; abel
    rw [hdecomp]
    exact (((hPA_l.comp_right _).comp_left _).add
      (((hPD_l.comp_right _).comp_left _).comp_left _)).add
      ((hPD_l.comp_right _).comp_left _)
  · rw [LinearMap.IsRightQuasiInverse, LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange]
    have hdecomp :
        (upperTriangular A B D).toLinearMap ∘ₗ
          (upperTriangular PA (-(PA.comp (B.comp PD))) PD).toLinearMap - LinearMap.id =
        (LinearMap.inl 𝕜 F₁ F₂ ∘ₗ ((A.toLinearMap ∘ₗ PA.toLinearMap - LinearMap.id) ∘ₗ
            LinearMap.fst 𝕜 F₁ F₂)) +
        (LinearMap.inl 𝕜 F₁ F₂ ∘ₗ ((-(A.toLinearMap ∘ₗ PA.toLinearMap - LinearMap.id)) ∘ₗ
            ((B.toLinearMap ∘ₗ PD.toLinearMap) ∘ₗ LinearMap.snd 𝕜 F₁ F₂))) +
        (LinearMap.inr 𝕜 F₁ F₂ ∘ₗ ((D.toLinearMap ∘ₗ PD.toLinearMap - LinearMap.id) ∘ₗ
            LinearMap.snd 𝕜 F₁ F₂)) :=
      LinearMap.ext fun ⟨_, _⟩ ↦ by simp [map_add]; abel
    rw [hdecomp]
    exact (((hPA_r.comp_right _).comp_left _).add
      ((hPA_r.neg.comp_right _).comp_left _)).add
      ((hPD_r.comp_right _).comp_left _)

/-- **Upper-triangular Fredholmness via the block quasi-inverse (general TVSs):**
over a complete nontrivially normed field, if `A` and `D` are Fredholm between Hausdorff
topological vector spaces, then `upperTriangular A B D` is Fredholm for any bounded `B`. -/
theorem IsFredholm.upperTriangular {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [Module 𝕜 E₁] [Module 𝕜 E₂] [Module 𝕜 F₁] [Module 𝕜 F₂]
    [IsTopologicalAddGroup E₁] [IsTopologicalAddGroup E₂]
    [IsTopologicalAddGroup F₁] [IsTopologicalAddGroup F₂]
    [ContinuousSMul 𝕜 E₁] [ContinuousSMul 𝕜 E₂] [ContinuousSMul 𝕜 F₁] [ContinuousSMul 𝕜 F₂]
    [T2Space E₁] [T2Space E₂] [T2Space F₁] [T2Space F₂]
    {A : E₁ →L[𝕜] F₁} {D : E₂ →L[𝕜] F₂}
    (hA : A.IsFredholm) (hD : D.IsFredholm) (B : E₂ →L[𝕜] F₁) :
    (A.upperTriangular B D).IsFredholm := by
  obtain ⟨PA, hPA⟩ := hA.exists_isQuasiInverse
  obtain ⟨PD, hPD⟩ := hD.exists_isQuasiInverse
  exact .of_isQuasiInverse (isQuasiInverse_upperTriangular A B D hPA hPD)

/-- **Left compact-error parametrix** for `upperTriangular A B D`. -/
theorem isCompactOperator_upperTriangular_parametrix_left {𝕜 : Type*} [Ring 𝕜]
    [Module 𝕜 E₁] [Module 𝕜 E₂] [Module 𝕜 F₁] [Module 𝕜 F₂]
    [IsTopologicalAddGroup E₁] [IsTopologicalAddGroup E₂] [ContinuousAdd F₁]
    (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)
    {PA : F₁ →L[𝕜] E₁} {PD : F₂ →L[𝕜] E₂}
    (hA : IsCompactOperator (PA.comp A - 1 : E₁ →L[𝕜] E₁))
    (hD : IsCompactOperator (PD.comp D - 1 : E₂ →L[𝕜] E₂)) :
    IsCompactOperator
      ((upperTriangular PA (-(PA.comp (B.comp PD))) PD).comp (upperTriangular A B D) - 1 :
        E₁ × E₂ →L[𝕜] E₁ × E₂) := by
  have h1 := (hA.comp_clm (fst 𝕜 E₁ E₂)).clm_comp (inl 𝕜 E₁ E₂)
  have h2 := (hD.comp_clm (snd 𝕜 E₁ E₂)).clm_comp ((inl 𝕜 E₁ E₂).comp (-(PA.comp B)))
  have h3 := (hD.comp_clm (snd 𝕜 E₁ E₂)).clm_comp (inr 𝕜 E₁ E₂)
  convert (h1.add h2).add h3 using 1
  exact funext fun ⟨_, _⟩ ↦ by simp [map_add]; abel

/-- **Right compact-error parametrix** for `upperTriangular A B D`. -/
theorem isCompactOperator_upperTriangular_parametrix_right {𝕜 : Type*} [Ring 𝕜]
    [Module 𝕜 E₁] [Module 𝕜 E₂] [Module 𝕜 F₁] [Module 𝕜 F₂]
    [IsTopologicalAddGroup E₁] [IsTopologicalAddGroup F₁] [IsTopologicalAddGroup F₂]
    (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)
    {PA : F₁ →L[𝕜] E₁} {PD : F₂ →L[𝕜] E₂}
    (hA : IsCompactOperator (A.comp PA - 1 : F₁ →L[𝕜] F₁))
    (hD : IsCompactOperator (D.comp PD - 1 : F₂ →L[𝕜] F₂)) :
    IsCompactOperator
      ((upperTriangular A B D).comp (upperTriangular PA (-(PA.comp (B.comp PD))) PD) - 1 :
        F₁ × F₂ →L[𝕜] F₁ × F₂) := by
  have h1 := (hA.comp_clm (fst 𝕜 F₁ F₂)).clm_comp (inl 𝕜 F₁ F₂)
  have h2 := (hA.comp_clm ((B.comp PD).comp (snd 𝕜 F₁ F₂))).clm_comp (-(inl 𝕜 F₁ F₂))
  have h3 := (hD.comp_clm (snd 𝕜 F₁ F₂)).clm_comp (inr 𝕜 F₁ F₂)
  convert (h1.add h2).add h3 using 1
  exact funext fun ⟨_, _⟩ ↦ by simp [map_add]; abel

end UpperTriangularParametrix

section UpperTriangularFredholm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E₁ E₂ F₁ F₂ : Type*}

/-- **Converse two-out-of-three for upper-triangular operators (left block):**
if `upperTriangular A B D` and `D` are Fredholm and `E₁, F₁` are Banach spaces, then `A` is
Fredholm. -/
theorem IsFredholm.of_upperTriangular_left [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
    [AddCommGroup E₂] [TopologicalSpace E₂] [Module 𝕜 E₂]
    [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [CompleteSpace F₁]
    [AddCommGroup F₂] [TopologicalSpace F₂] [Module 𝕜 F₂]
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₁} {D : E₂ →L[𝕜] F₂}
    (hM : (A.upperTriangular B D).IsFredholm) (hD : D.IsFredholm) :
    A.IsFredholm :=
  hM.of_shortExact_left hD LinearMap.inl_injective exact_inl_snd
    LinearMap.snd_surjective LinearMap.inl_injective exact_inl_snd
    (upperTriangular_comp_inl A B D) (snd_comp_upperTriangular A B D).symm

/-- **Converse two-out-of-three for upper-triangular operators (right block):**
if `upperTriangular A B D` and `A` are Fredholm and `E₂, F₂` are Banach spaces, then `D` is
Fredholm. -/
theorem IsFredholm.of_upperTriangular_right [IsRCLikeNormedField 𝕜]
    [AddCommGroup E₁] [TopologicalSpace E₁] [Module 𝕜 E₁]
    [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
    [AddCommGroup F₁] [TopologicalSpace F₁] [Module 𝕜 F₁] [ContinuousAdd F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [CompleteSpace F₂]
    {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₁} {D : E₂ →L[𝕜] F₂}
    (hM : (A.upperTriangular B D).IsFredholm) (hA : A.IsFredholm) :
    D.IsFredholm :=
  hA.of_shortExact_right hM exact_inl_snd LinearMap.snd_surjective
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    (upperTriangular_comp_inl A B D) (snd_comp_upperTriangular A B D).symm

section Index

variable [AddCommGroup E₁] [TopologicalSpace E₁] [Module 𝕜 E₁]
variable [AddCommGroup E₂] [TopologicalSpace E₂] [Module 𝕜 E₂]
variable [AddCommGroup F₁] [TopologicalSpace F₁] [Module 𝕜 F₁] [ContinuousAdd F₁]
variable [AddCommGroup F₂] [TopologicalSpace F₂] [Module 𝕜 F₂]

/-- **Index of an upper-triangular block operator** when `A` and `D` are Fredholm. -/
theorem index_upperTriangular_of_diag (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)
    (hA : A.IsFredholm) (hD : D.IsFredholm) :
    (upperTriangular A B D).index = A.index + D.index :=
  index_eq_add_of_shortExact_left_right (upperTriangular A B D)
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    (upperTriangular_comp_inl A B D) (snd_comp_upperTriangular A B D).symm hA hD

/-- **Index of an upper-triangular block operator** when `A` and the block operator are Fredholm. -/
theorem index_upperTriangular_of_left (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)
    (hA : A.IsFredholm) (hM : (upperTriangular A B D).IsFredholm) :
    (upperTriangular A B D).index = A.index + D.index :=
  index_eq_add_of_shortExact_left_middle (upperTriangular A B D)
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    (upperTriangular_comp_inl A B D) (snd_comp_upperTriangular A B D).symm hA hM

/-- **Index of an upper-triangular block operator** when the block operator and `D` are Fredholm. -/
theorem index_upperTriangular_of_right (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₁) (D : E₂ →L[𝕜] F₂)
    (hM : (upperTriangular A B D).IsFredholm) (hD : D.IsFredholm) :
    (upperTriangular A B D).index = A.index + D.index :=
  index_eq_add_of_shortExact_middle_right (upperTriangular A B D)
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    LinearMap.inl_injective exact_inl_snd LinearMap.snd_surjective
    (upperTriangular_comp_inl A B D) (snd_comp_upperTriangular A B D).symm hM hD

end Index

end UpperTriangularFredholm

/-! ### Composition snake diagram and comparison with `IsFredholm.index_comp` -/

section CompositionSnake

section Ring

variable {𝕜 : Type*} [Ring 𝕜]
variable {E F G : Type*}
variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
variable [AddCommGroup G] [TopologicalSpace G] [Module 𝕜 G]

/-- Target change of coordinates `(y, z) ↦ (z + S y, y)` from `F × G` to `G × F`. -/
def upperTriangularNegIdCodEquiv [IsTopologicalAddGroup G] (S : F →L[𝕜] G) :
    (F × G) ≃L[𝕜] (G × F) :=
  ContinuousLinearEquiv.equivOfInverse
    ((snd 𝕜 F G + S.comp (fst 𝕜 F G)).prod (fst 𝕜 F G))
    ((snd 𝕜 G F).prod (fst 𝕜 G F - S.comp (snd 𝕜 G F)))
    (fun ⟨_, _⟩ ↦ by simp) (fun ⟨_, _⟩ ↦ by simp)

@[simp]
theorem upperTriangularNegIdCodEquiv_apply [IsTopologicalAddGroup G] (S : F →L[𝕜] G)
    (y : F) (z : G) :
    upperTriangularNegIdCodEquiv S (y, z) = (z + S y, y) := (rfl)

@[simp]
theorem upperTriangularNegIdCodEquiv_symm_apply [IsTopologicalAddGroup G] (S : F →L[𝕜] G)
    (z : G) (y : F) :
    (upperTriangularNegIdCodEquiv S).symm (z, y) = (y, z - S y) := (rfl)

variable [IsTopologicalAddGroup F]

/-- Source change of coordinates `(x, y) ↦ (x, y + T x)` on `E × F`. -/
def upperTriangularNegIdDomEquiv (T : E →L[𝕜] F) : (E × F) ≃L[𝕜] (E × F) :=
  ContinuousLinearEquiv.equivOfInverse
    ((fst 𝕜 E F).prod (snd 𝕜 E F + T.comp (fst 𝕜 E F)))
    ((fst 𝕜 E F).prod (snd 𝕜 E F - T.comp (fst 𝕜 E F)))
    (fun ⟨_, _⟩ ↦ by simp) (fun ⟨_, _⟩ ↦ by simp)

@[simp]
theorem upperTriangularNegIdDomEquiv_apply (T : E →L[𝕜] F) (x : E) (y : F) :
    upperTriangularNegIdDomEquiv T (x, y) = (x, y + T x) := (rfl)

@[simp]
theorem upperTriangularNegIdDomEquiv_symm_apply (T : E →L[𝕜] F) (x : E) (y : F) :
    (upperTriangularNegIdDomEquiv T).symm (x, y) = (x, y - T x) := (rfl)

/-- **Diagonalization of the composition snake operator:** conjugating
`upperTriangular T (-id 𝕜 F) S` by the triangular coordinate equivalences yields
`(S ∘L T).prodMap (-id 𝕜 F)`. -/
theorem upperTriangularNegIdCodEquiv_comp_upperTriangular_comp_domEquiv [IsTopologicalAddGroup G]
    (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    ((upperTriangularNegIdCodEquiv S : F × G →L[𝕜] G × F).comp
      (upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S)).comp
      (upperTriangularNegIdDomEquiv T : E × F →L[𝕜] E × F) =
      (S.comp T).prodMap (-ContinuousLinearMap.id 𝕜 F) :=
  ContinuousLinearMap.ext fun ⟨_, _⟩ ↦ by simp [map_add]

/-- Identification of the kernel of `upperTriangular T (-id 𝕜 F) S` with `ker (S ∘L T)`,
sending `(x, y)` to `x` with inverse `x ↦ (x, T x)`. -/
def kerUpperTriangularNegIdEquiv (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    (upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).ker ≃L[𝕜]
      (S.toLinearMap ∘ₗ T.toLinearMap).ker :=
  ContinuousLinearEquiv.equivOfInverse
    (((fst 𝕜 E F).comp (upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).ker.subtypeL).codRestrict
      (S.toLinearMap ∘ₗ T.toLinearMap).ker fun ⟨⟨x, y⟩, h⟩ ↦ by
        rw [LinearMap.mem_ker] at h ⊢
        have h1 : T x - y = 0 := by simpa [sub_eq_add_neg] using congrArg Prod.fst h
        have hy : y = T x := (sub_eq_zero.1 h1).symm
        simpa [hy] using congrArg Prod.snd h)
    ((((ContinuousLinearMap.id 𝕜 E).prod T).comp
        (S.toLinearMap ∘ₗ T.toLinearMap).ker.subtypeL).codRestrict
      (upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).ker fun ⟨x, hx⟩ ↦ by
        rw [LinearMap.mem_ker] at hx ⊢
        refine Prod.ext ?_ hx
        simp only [coe_coe, comp_apply, Submodule.subtypeL_apply, prod_apply, id_apply,
          upperTriangular_apply, neg_apply, add_neg_cancel, Prod.fst_zero])
    (fun ⟨⟨x, y⟩, h⟩ ↦ by
      apply Subtype.ext
      have h1 : T x - y = 0 := by simpa [sub_eq_add_neg] using congrArg Prod.fst h
      exact Prod.ext rfl (sub_eq_zero.1 h1))
    (fun ⟨_, _⟩ ↦ rfl)

@[simp]
theorem coe_kerUpperTriangularNegIdEquiv_apply (T : E →L[𝕜] F) (S : F →L[𝕜] G)
    (v : (upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).ker) :
    (kerUpperTriangularNegIdEquiv T S v : E) = v.1.1 := (rfl)

@[simp]
theorem coe_kerUpperTriangularNegIdEquiv_symm_apply (T : E →L[𝕜] F) (S : F →L[𝕜] G)
    (x : (S.toLinearMap ∘ₗ T.toLinearMap).ker) :
    ((kerUpperTriangularNegIdEquiv T S).symm x : E × F) = (x.1, T x.1) := (rfl)

/-- Identification of the cokernel of `upperTriangular T (-id 𝕜 F) S` with `G ⧸ range (S ∘L T)`,
sending `[(y, z)]` to `[z + S y]` with inverse `[z] ↦ [(0, z)]`. -/
def cokerUpperTriangularNegIdEquiv (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    ((F × G) ⧸ (upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).range) ≃ₗ[𝕜]
      (G ⧸ (S.toLinearMap ∘ₗ T.toLinearMap).range) :=
  LinearEquiv.ofLinearMap
    ((upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).range.liftQ
      ((S.toLinearMap ∘ₗ T.toLinearMap).range.mkQ ∘ₗ
        (LinearMap.snd 𝕜 F G + S.toLinearMap ∘ₗ LinearMap.fst 𝕜 F G)) <| by
        rintro _ ⟨⟨x, y⟩, rfl⟩
        rw [LinearMap.mem_ker]
        refine (Submodule.Quotient.mk_eq_zero _).2 ⟨x, ?_⟩
        simp [map_add])
    ((S.toLinearMap ∘ₗ T.toLinearMap).range.liftQ
      ((upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).range.mkQ ∘ₗ LinearMap.inr 𝕜 F G) <| by
        rintro _ ⟨x, rfl⟩
        rw [LinearMap.mem_ker]
        refine (Submodule.Quotient.mk_eq_zero _).2 ⟨(x, T x), ?_⟩
        refine Prod.ext ?_ ?_ <;> simp)
    (Submodule.linearMap_qext _ <| LinearMap.ext fun z ↦ by
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
        LinearMap.inr_apply, LinearMap.add_apply, LinearMap.snd_apply, LinearMap.fst_apply,
        map_zero, add_zero, LinearMap.id_apply])
    (Submodule.linearMap_qext _ <| LinearMap.ext fun ⟨y, z⟩ ↦ by
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
        LinearMap.add_apply, LinearMap.snd_apply, LinearMap.fst_apply, LinearMap.inr_apply,
        LinearMap.id_apply]
      rw [Submodule.Quotient.eq]
      exact ⟨(0, y), Prod.ext (by simp) (by simp)⟩)

@[simp]
theorem cokerUpperTriangularNegIdEquiv_mk (T : E →L[𝕜] F) (S : F →L[𝕜] G) (y : F) (z : G) :
    cokerUpperTriangularNegIdEquiv T S (Submodule.Quotient.mk (y, z)) =
      Submodule.Quotient.mk (z + S y) := (rfl)

@[simp]
theorem cokerUpperTriangularNegIdEquiv_symm_mk (T : E →L[𝕜] F) (S : F →L[𝕜] G) (z : G) :
    (cokerUpperTriangularNegIdEquiv T S).symm (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (0, z) := (rfl)

/-- Under `kerUpperTriangularNegIdEquiv`, the first map of the composition snake sequence is the
inclusion `ker T → ker (S ∘L T)`. -/
theorem kerUpperTriangularNegIdEquiv_comp_kerMapOfComm (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    (kerUpperTriangularNegIdEquiv T S).toLinearMap ∘ₗ
      TauCeti.kerMapOfComm (congrArg ContinuousLinearMap.toLinearMap
        (upperTriangular_comp_inl T (-ContinuousLinearMap.id 𝕜 F) S)) =
      Submodule.inclusion (LinearMap.ker_le_ker_comp T.toLinearMap S.toLinearMap) :=
  LinearMap.ext fun _ ↦ Subtype.ext (by simp)

/-- Under `kerUpperTriangularNegIdEquiv`, the second map of the composition snake sequence is
`LinearMap.kerCompToKer T S`. -/
theorem kerMapOfComm_comp_kerUpperTriangularNegIdEquiv_symm (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    TauCeti.kerMapOfComm (congrArg ContinuousLinearMap.toLinearMap
      (snd_comp_upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).symm) ∘ₗ
      (kerUpperTriangularNegIdEquiv T S).symm.toLinearMap =
      T.toLinearMap.kerCompToKer S.toLinearMap :=
  LinearMap.ext fun _ ↦ Subtype.ext (by simp)

/-- The connecting map of the composition snake diagram `upperTriangular T (-id 𝕜 F) S` equals
`-T.toLinearMap.kerToCoker S.toLinearMap`. -/
theorem toLinearMap_snakeDeltaL_upperTriangular_neg_id (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    (TauCeti.snakeDeltaL (i := inl 𝕜 E F) (p := snd 𝕜 E F)
      (j := inl 𝕜 F G) (q := snd 𝕜 F G)
      (T₁ := T) (T₂ := upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S) (T₃ := S)
      exact_inl_snd exact_inl_snd
      ⟨inr 𝕜 E F, by intro _; simp⟩ ⟨fst 𝕜 F G, by intro _; simp⟩
      (upperTriangular_comp_inl T (-ContinuousLinearMap.id 𝕜 F) S)
      (snd_comp_upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).symm).toLinearMap =
      -(T.toLinearMap.kerToCoker S.toLinearMap) := by
  rw [snakeDeltaL_upperTriangular]
  ext y
  simp

/-- Under `cokerUpperTriangularNegIdEquiv`, the fourth map of the composition snake sequence is
`LinearMap.cokerToCokerComp T S`. -/
theorem cokerUpperTriangularNegIdEquiv_comp_cokerMapOfComm (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    (cokerUpperTriangularNegIdEquiv T S).toLinearMap ∘ₗ
      TauCeti.cokerMapOfComm (congrArg ContinuousLinearMap.toLinearMap
        (upperTriangular_comp_inl T (-ContinuousLinearMap.id 𝕜 F) S)) =
      T.toLinearMap.cokerToCokerComp S.toLinearMap :=
  Submodule.linearMap_qext _ <| LinearMap.ext fun _ ↦ by simp

/-- Under `cokerUpperTriangularNegIdEquiv`, the fifth map of the composition snake sequence is
`Submodule.factor (range_comp_le_range T S)`. -/
theorem cokerMapOfComm_comp_cokerUpperTriangularNegIdEquiv_symm (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    TauCeti.cokerMapOfComm (congrArg ContinuousLinearMap.toLinearMap
      (snd_comp_upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).symm) ∘ₗ
      (cokerUpperTriangularNegIdEquiv T S).symm.toLinearMap =
      Submodule.factor (LinearMap.range_comp_le_range T.toLinearMap S.toLinearMap) :=
  Submodule.linearMap_qext _ <| LinearMap.ext fun _ ↦ by simp

/-- The index of `upperTriangular T (-id 𝕜 F) S` unconditionally equals `(S ∘L T).index`. -/
theorem index_upperTriangular_neg_id (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    (upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).index = (S.comp T).index := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub, toLinearMap_comp,
    (kerUpperTriangularNegIdEquiv T S).toLinearEquiv.finrank_eq,
    (cokerUpperTriangularNegIdEquiv T S).finrank_eq]

end Ring

section NormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F G : Type*}
variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
variable [AddCommGroup G] [TopologicalSpace G] [Module 𝕜 G]

/-- The composition snake operator `upperTriangular T (-id 𝕜 F) S` is Fredholm if and only if
`S ∘L T` is Fredholm. -/
theorem isFredholm_upperTriangular_neg_id_iff [IsTopologicalAddGroup E] [IsTopologicalAddGroup F]
    [IsTopologicalAddGroup G] (T : E →L[𝕜] F) (S : F →L[𝕜] G) :
    (upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S).IsFredholm ↔ (S.comp T).IsFredholm := by
  have hconj := isFredholm_iff_of_comp_eq
    (T := upperTriangular T (-ContinuousLinearMap.id 𝕜 F) S)
    (S := (S.comp T).prodMap (-ContinuousLinearMap.id 𝕜 F))
    (upperTriangularNegIdDomEquiv T).symm (upperTriangularNegIdCodEquiv S) (by
      rw [← upperTriangularNegIdCodEquiv_comp_upperTriangular_comp_domEquiv T S]
      exact ContinuousLinearMap.ext fun ⟨_, _⟩ ↦ by simp)
  rw [hconj, isFredholm_prodMap_iff]
  have hneg : (-ContinuousLinearMap.id 𝕜 F).IsFredholm :=
    (ContinuousLinearEquiv.refl 𝕜 F).isFredholm.neg
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hneg⟩⟩

/-- **Composition index additivity (composite and left factor Fredholm):**
if `S ∘L T` and `S` are Fredholm, then `(S ∘L T).index = S.index + T.index`. Compare with
`ContinuousLinearMap.IsFredholm.index_comp`, which assumes `S` and `T` are Fredholm. -/
theorem IsFredholm.index_comp_of_left {T : E →L[𝕜] F} {S : F →L[𝕜] G}
    (hST : (S.comp T).IsFredholm) (hS : S.IsFredholm) :
    (S.comp T).index = S.index + T.index := by
  have : FiniteDimensional 𝕜 (S.toLinearMap ∘ₗ T.toLinearMap).ker := hST.finite_ker
  have : FiniteDimensional 𝕜 (G ⧸ (S.toLinearMap ∘ₗ T.toLinearMap).range) := hST.finite_coker
  have := hS.finite_ker; have := hS.finite_coker
  have : FiniteDimensional 𝕜 T.ker :=
    Module.Finite.of_injective _ (Submodule.inclusion_injective
      (LinearMap.ker_le_ker_comp T.toLinearMap S.toLinearMap))
  have : FiniteDimensional 𝕜 (F ⧸ T.range) :=
    TauCeti.finiteDimensional_of_exact (LinearMap.exact_kerToCoker_cokerToCokerComp T.toLinearMap
      S.toLinearMap)
  rw [index_def, index_def, index_def]
  exact LinearMap.index_comp S.toLinearMap T.toLinearMap

/-- **Composition index additivity (composite and right factor Fredholm):**
if `S ∘L T` and `T` are Fredholm, then `(S ∘L T).index = S.index + T.index`. -/
theorem IsFredholm.index_comp_of_right {T : E →L[𝕜] F} {S : F →L[𝕜] G}
    (hST : (S.comp T).IsFredholm) (hT : T.IsFredholm) :
    (S.comp T).index = S.index + T.index := by
  have : FiniteDimensional 𝕜 (S.toLinearMap ∘ₗ T.toLinearMap).ker := hST.finite_ker
  have : FiniteDimensional 𝕜 (G ⧸ (S.toLinearMap ∘ₗ T.toLinearMap).range) := hST.finite_coker
  have := hT.finite_ker; have := hT.finite_coker
  have : FiniteDimensional 𝕜 S.ker :=
    TauCeti.finiteDimensional_of_exact (LinearMap.exact_kerCompToKer_kerToCoker T.toLinearMap
      S.toLinearMap)
  have : FiniteDimensional 𝕜 (G ⧸ S.range) :=
    Module.Finite.of_surjective _ (Submodule.factor_surjective
      (LinearMap.range_comp_le_range T.toLinearMap S.toLinearMap))
  rw [index_def, index_def, index_def]
  exact LinearMap.index_comp S.toLinearMap T.toLinearMap

end NormedField

end CompositionSnake

end ContinuousLinearMap
