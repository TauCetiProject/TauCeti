/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module

/-!
# Sections of a direct-sum bundle

A section of the direct sum `E₁ ×ᵇ E₂` of two vector bundles is a pair of sections, one of each
summand, and it is smooth exactly when both components are
(`Bundle.contMDiffAt_section_prod_iff`). This file packages the two projections and the two
inclusions of sections,

`fst, snd : Γ(E₁ ×ᵇ E₂) → Γ(E₁), Γ(E₂)` and `inl, inr : Γ(E₁), Γ(E₂) → Γ(E₁ ×ᵇ E₂)`,

as linear maps (`ContMDiffSection.fstLinearMap`, `ContMDiffSection.sndLinearMap`,
`ContMDiffSection.inlLinearMap`, `ContMDiffSection.inrLinearMap`). The bundles are vector bundles
over a field `𝕜'` above the field `𝕜` of the base, such as complex bundles over a real manifold, and
the maps are `𝕜'`-linear. They are induced by fibrewise linear bundle maps, so they commute with
multiplication by `𝕜'`-valued functions (`ContMDiffSection.fstLinearMap_smul_function` and its
analogues), and they satisfy the identities of the biproduct: `fst (inl s) = s`,
`snd (inl s) = 0`, `fst (inr s) = 0`, `snd (inr s) = s` and `inl ∘ fst + inr ∘ snd = 1`.

An operator `P : Γ(E₁ ×ᵇ E₂) → Γ(F₁ ×ᵇ F₂)` between direct sums is therefore a `2 × 2` matrix of
operators `Pᵢⱼ : Γ(Eⱼ) → Γ(Fᵢ)`. The operator with matrix `Pᵢⱼ` is
`ContMDiffSection.blockLinearMap P₁₁ P₁₂ P₂₁ P₂₂`, sending `(s₁, s₂)` to
`(P₁₁ s₁ + P₁₂ s₂, P₂₁ s₁ + P₂₂ s₂)`. Its entries are recovered by the projections and inclusions
(`ContMDiffSection.fstLinearMap_comp_blockLinearMap_comp_inlLinearMap` and its analogues), and
every operator is the block operator of its entries
(`ContMDiffSection.blockLinearMap_entries`). Operators of this form are the folded operators of
index theory: the operator `[[0, P*], [P, 0]]` on `E₀ ⊕ E₁` built from an operator
`P : Γ(E₀) → Γ(E₁)`, and the operator `d + d*` from the even to the odd terms of an elliptic
complex.

## Main definitions

* `ContMDiffSection.fstLinearMap`, `ContMDiffSection.sndLinearMap`: the components of a section of
  a direct-sum bundle.
* `ContMDiffSection.inlLinearMap`, `ContMDiffSection.inrLinearMap`: the sections `(s, 0)` and
  `(0, s)`.
* `ContMDiffSection.blockLinearMap`: the operator between direct sums with a given matrix of
  operators.
-/

public section

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace ContMDiffSection

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']
  {EB HB B : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {I : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedSpace 𝕜' F₁]
  [IsScalarTower 𝕜 𝕜' F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [NormedSpace 𝕜' F₂]
  [IsScalarTower 𝕜 𝕜' F₂] {n : ℕ∞ω}
  {E₁ E₂ : B → Type*} [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, Module 𝕜' (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)] [∀ x, Module 𝕜' (E₂ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₁ E₁] [VectorBundle 𝕜 F₂ E₂]
  [VectorBundle 𝕜' F₁ E₁] [VectorBundle 𝕜' F₂ E₂]

/-! ### Projections and inclusions -/

variable (I F₁ F₂ E₁ E₂ n 𝕜') in
/-- The first component `x ↦ (s x).1` of a section `s` of the direct-sum bundle `E₁ ×ᵇ E₂`, as a
linear map. -/
def fstLinearMap : Cₛ^n⟮I; F₁ × F₂, E₁ ×ᵇ E₂⟯ →ₗ[𝕜'] Cₛ^n⟮I; F₁, E₁⟯ where
  toFun s := ⟨fun x ↦ (s x).1, Bundle.Prod.contMDiff_fst.comp s.contMDiff⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (I F₁ F₂ E₁ E₂ n 𝕜') in
/-- The second component `x ↦ (s x).2` of a section `s` of the direct-sum bundle `E₁ ×ᵇ E₂`, as a
linear map. -/
def sndLinearMap : Cₛ^n⟮I; F₁ × F₂, E₁ ×ᵇ E₂⟯ →ₗ[𝕜'] Cₛ^n⟮I; F₂, E₂⟯ where
  toFun s := ⟨fun x ↦ (s x).2, Bundle.Prod.contMDiff_snd.comp s.contMDiff⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (I F₁ F₂ E₁ E₂ n 𝕜') in
/-- The section `x ↦ (s x, 0)` of the direct-sum bundle `E₁ ×ᵇ E₂`, for a section `s` of `E₁`, as
a linear map. -/
def inlLinearMap : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[𝕜'] Cₛ^n⟮I; F₁ × F₂, E₁ ×ᵇ E₂⟯ where
  toFun s := ⟨fun x ↦ (s x, 0), Bundle.Prod.contMDiff_inl.comp s.contMDiff⟩
  map_add' s t := by ext x <;> simp
  map_smul' c s := by ext x <;> simp

variable (I F₁ F₂ E₁ E₂ n 𝕜') in
/-- The section `x ↦ (0, s x)` of the direct-sum bundle `E₁ ×ᵇ E₂`, for a section `s` of `E₂`, as
a linear map. -/
def inrLinearMap : Cₛ^n⟮I; F₂, E₂⟯ →ₗ[𝕜'] Cₛ^n⟮I; F₁ × F₂, E₁ ×ᵇ E₂⟯ where
  toFun s := ⟨fun x ↦ (0, s x), Bundle.Prod.contMDiff_inr.comp s.contMDiff⟩
  map_add' s t := by ext x <;> simp
  map_smul' c s := by ext x <;> simp

@[simp]
theorem fstLinearMap_apply (s : Cₛ^n⟮I; F₁ × F₂, E₁ ×ᵇ E₂⟯) (x : B) :
    fstLinearMap 𝕜' I F₁ F₂ n E₁ E₂ s x = (s x).1 :=
  (rfl)

@[simp]
theorem sndLinearMap_apply (s : Cₛ^n⟮I; F₁ × F₂, E₁ ×ᵇ E₂⟯) (x : B) :
    sndLinearMap 𝕜' I F₁ F₂ n E₁ E₂ s x = (s x).2 :=
  (rfl)

@[simp]
theorem inlLinearMap_apply (s : Cₛ^n⟮I; F₁, E₁⟯) (x : B) :
    inlLinearMap 𝕜' I F₁ F₂ n E₁ E₂ s x = (s x, 0) :=
  (rfl)

@[simp]
theorem inrLinearMap_apply (s : Cₛ^n⟮I; F₂, E₂⟯) (x : B) :
    inrLinearMap 𝕜' I F₁ F₂ n E₁ E₂ s x = (0, s x) :=
  (rfl)

/-! ### The biproduct identities -/

@[simp]
theorem fstLinearMap_inlLinearMap (s : Cₛ^n⟮I; F₁, E₁⟯) :
    fstLinearMap 𝕜' I F₁ F₂ n E₁ E₂ (inlLinearMap 𝕜' I F₁ F₂ n E₁ E₂ s) = s :=
  (rfl)

@[simp]
theorem sndLinearMap_inrLinearMap (s : Cₛ^n⟮I; F₂, E₂⟯) :
    sndLinearMap 𝕜' I F₁ F₂ n E₁ E₂ (inrLinearMap 𝕜' I F₁ F₂ n E₁ E₂ s) = s :=
  (rfl)

@[simp]
theorem sndLinearMap_inlLinearMap (s : Cₛ^n⟮I; F₁, E₁⟯) :
    sndLinearMap 𝕜' I F₁ F₂ n E₁ E₂ (inlLinearMap 𝕜' I F₁ F₂ n E₁ E₂ s) = 0 :=
  (rfl)

@[simp]
theorem fstLinearMap_inrLinearMap (s : Cₛ^n⟮I; F₂, E₂⟯) :
    fstLinearMap 𝕜' I F₁ F₂ n E₁ E₂ (inrLinearMap 𝕜' I F₁ F₂ n E₁ E₂ s) = 0 :=
  (rfl)

/-- A section of a direct-sum bundle is the sum of the inclusions of its two components. -/
theorem inlLinearMap_comp_fstLinearMap_add_inrLinearMap_comp_sndLinearMap :
    inlLinearMap 𝕜' I F₁ F₂ n E₁ E₂ ∘ₗ fstLinearMap 𝕜' I F₁ F₂ n E₁ E₂ +
        inrLinearMap 𝕜' I F₁ F₂ n E₁ E₂ ∘ₗ sndLinearMap 𝕜' I F₁ F₂ n E₁ E₂ = LinearMap.id := by
  ext s x <;> simp

/-! ### Multiplication by functions -/

section SMulFunction

variable [ContMDiffRing 𝓘(𝕜, 𝕜') n 𝕜'] (f : C^n⟮I, B; 𝓘(𝕜, 𝕜'), 𝕜'⟯)

theorem fstLinearMap_smul_function (s : Cₛ^n⟮I; F₁ × F₂, E₁ ×ᵇ E₂⟯) :
    fstLinearMap 𝕜' I F₁ F₂ n E₁ E₂ (f • s) = f • fstLinearMap 𝕜' I F₁ F₂ n E₁ E₂ s := by
  ext x
  simp

theorem sndLinearMap_smul_function (s : Cₛ^n⟮I; F₁ × F₂, E₁ ×ᵇ E₂⟯) :
    sndLinearMap 𝕜' I F₁ F₂ n E₁ E₂ (f • s) = f • sndLinearMap 𝕜' I F₁ F₂ n E₁ E₂ s := by
  ext x
  simp

theorem inlLinearMap_smul_function (s : Cₛ^n⟮I; F₁, E₁⟯) :
    inlLinearMap 𝕜' I F₁ F₂ n E₁ E₂ (f • s) = f • inlLinearMap 𝕜' I F₁ F₂ n E₁ E₂ s := by
  ext x <;> simp

theorem inrLinearMap_smul_function (s : Cₛ^n⟮I; F₂, E₂⟯) :
    inrLinearMap 𝕜' I F₁ F₂ n E₁ E₂ (f • s) = f • inrLinearMap 𝕜' I F₁ F₂ n E₁ E₂ s := by
  ext x <;> simp

end SMulFunction

/-! ### Operators between direct sums -/

section Block

variable {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace 𝕜 G₁] [NormedSpace 𝕜' G₁]
  [IsScalarTower 𝕜 𝕜' G₁]
  {G₂ : Type*} [NormedAddCommGroup G₂] [NormedSpace 𝕜 G₂] [NormedSpace 𝕜' G₂]
  [IsScalarTower 𝕜 𝕜' G₂]
  {Z₁ Z₂ : B → Type*} [∀ x, TopologicalSpace (Z₁ x)] [∀ x, TopologicalSpace (Z₂ x)]
  [∀ x, AddCommGroup (Z₁ x)] [∀ x, Module 𝕜 (Z₁ x)] [∀ x, Module 𝕜' (Z₁ x)]
  [∀ x, AddCommGroup (Z₂ x)] [∀ x, Module 𝕜 (Z₂ x)] [∀ x, Module 𝕜' (Z₂ x)]
  [TopologicalSpace (TotalSpace G₁ Z₁)] [TopologicalSpace (TotalSpace G₂ Z₂)]
  [FiberBundle G₁ Z₁] [FiberBundle G₂ Z₂] [VectorBundle 𝕜 G₁ Z₁] [VectorBundle 𝕜 G₂ Z₂]
  [VectorBundle 𝕜' G₁ Z₁] [VectorBundle 𝕜' G₂ Z₂]

/-- The operator `Γ(E₁ ×ᵇ E₂) → Γ(Z₁ ×ᵇ Z₂)` with matrix `[[P₁₁, P₁₂], [P₂₁, P₂₂]]`, sending a
section with components `s₁`, `s₂` to the section with components `P₁₁ s₁ + P₁₂ s₂` and
`P₂₁ s₁ + P₂₂ s₂`. -/
def blockLinearMap (P₁₁ : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[𝕜'] Cₛ^n⟮I; G₁, Z₁⟯)
    (P₁₂ : Cₛ^n⟮I; F₂, E₂⟯ →ₗ[𝕜'] Cₛ^n⟮I; G₁, Z₁⟯)
    (P₂₁ : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[𝕜'] Cₛ^n⟮I; G₂, Z₂⟯)
    (P₂₂ : Cₛ^n⟮I; F₂, E₂⟯ →ₗ[𝕜'] Cₛ^n⟮I; G₂, Z₂⟯) :
    Cₛ^n⟮I; F₁ × F₂, E₁ ×ᵇ E₂⟯ →ₗ[𝕜'] Cₛ^n⟮I; G₁ × G₂, Z₁ ×ᵇ Z₂⟯ :=
  inlLinearMap 𝕜' I G₁ G₂ n Z₁ Z₂ ∘ₗ
      (P₁₁ ∘ₗ fstLinearMap 𝕜' I F₁ F₂ n E₁ E₂ + P₁₂ ∘ₗ sndLinearMap 𝕜' I F₁ F₂ n E₁ E₂) +
    inrLinearMap 𝕜' I G₁ G₂ n Z₁ Z₂ ∘ₗ
      (P₂₁ ∘ₗ fstLinearMap 𝕜' I F₁ F₂ n E₁ E₂ + P₂₂ ∘ₗ sndLinearMap 𝕜' I F₁ F₂ n E₁ E₂)

variable (P₁₁ : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[𝕜'] Cₛ^n⟮I; G₁, Z₁⟯)
  (P₁₂ : Cₛ^n⟮I; F₂, E₂⟯ →ₗ[𝕜'] Cₛ^n⟮I; G₁, Z₁⟯)
  (P₂₁ : Cₛ^n⟮I; F₁, E₁⟯ →ₗ[𝕜'] Cₛ^n⟮I; G₂, Z₂⟯)
  (P₂₂ : Cₛ^n⟮I; F₂, E₂⟯ →ₗ[𝕜'] Cₛ^n⟮I; G₂, Z₂⟯)

/-- The block operator is `inl ∘ (P₁₁ ∘ fst + P₁₂ ∘ snd) + inr ∘ (P₂₁ ∘ fst + P₂₂ ∘ snd)`. -/
theorem blockLinearMap_def :
    blockLinearMap P₁₁ P₁₂ P₂₁ P₂₂ =
      inlLinearMap 𝕜' I G₁ G₂ n Z₁ Z₂ ∘ₗ
          (P₁₁ ∘ₗ fstLinearMap 𝕜' I F₁ F₂ n E₁ E₂ + P₁₂ ∘ₗ sndLinearMap 𝕜' I F₁ F₂ n E₁ E₂) +
        inrLinearMap 𝕜' I G₁ G₂ n Z₁ Z₂ ∘ₗ
          (P₂₁ ∘ₗ fstLinearMap 𝕜' I F₁ F₂ n E₁ E₂ + P₂₂ ∘ₗ sndLinearMap 𝕜' I F₁ F₂ n E₁ E₂) :=
  (rfl)

@[simp]
theorem blockLinearMap_apply (s : Cₛ^n⟮I; F₁ × F₂, E₁ ×ᵇ E₂⟯) (x : B) :
    blockLinearMap P₁₁ P₁₂ P₂₁ P₂₂ s x =
      (P₁₁ (fstLinearMap 𝕜' I F₁ F₂ n E₁ E₂ s) x + P₁₂ (sndLinearMap 𝕜' I F₁ F₂ n E₁ E₂ s) x,
        P₂₁ (fstLinearMap 𝕜' I F₁ F₂ n E₁ E₂ s) x + P₂₂ (sndLinearMap 𝕜' I F₁ F₂ n E₁ E₂ s) x) := by
  simp [blockLinearMap]

@[simp]
theorem fstLinearMap_comp_blockLinearMap_comp_inlLinearMap :
    fstLinearMap 𝕜' I G₁ G₂ n Z₁ Z₂ ∘ₗ blockLinearMap P₁₁ P₁₂ P₂₁ P₂₂ ∘ₗ
      inlLinearMap 𝕜' I F₁ F₂ n E₁ E₂ = P₁₁ := by
  ext s x
  simp

@[simp]
theorem fstLinearMap_comp_blockLinearMap_comp_inrLinearMap :
    fstLinearMap 𝕜' I G₁ G₂ n Z₁ Z₂ ∘ₗ blockLinearMap P₁₁ P₁₂ P₂₁ P₂₂ ∘ₗ
      inrLinearMap 𝕜' I F₁ F₂ n E₁ E₂ = P₁₂ := by
  ext s x
  simp

@[simp]
theorem sndLinearMap_comp_blockLinearMap_comp_inlLinearMap :
    sndLinearMap 𝕜' I G₁ G₂ n Z₁ Z₂ ∘ₗ blockLinearMap P₁₁ P₁₂ P₂₁ P₂₂ ∘ₗ
      inlLinearMap 𝕜' I F₁ F₂ n E₁ E₂ = P₂₁ := by
  ext s x
  simp

@[simp]
theorem sndLinearMap_comp_blockLinearMap_comp_inrLinearMap :
    sndLinearMap 𝕜' I G₁ G₂ n Z₁ Z₂ ∘ₗ blockLinearMap P₁₁ P₁₂ P₂₁ P₂₂ ∘ₗ
      inrLinearMap 𝕜' I F₁ F₂ n E₁ E₂ = P₂₂ := by
  ext s x
  simp

/-- Every operator between direct sums is the block operator of its four entries. -/
theorem blockLinearMap_entries
    (P : Cₛ^n⟮I; F₁ × F₂, E₁ ×ᵇ E₂⟯ →ₗ[𝕜'] Cₛ^n⟮I; G₁ × G₂, Z₁ ×ᵇ Z₂⟯) :
    blockLinearMap
        (fstLinearMap 𝕜' I G₁ G₂ n Z₁ Z₂ ∘ₗ P ∘ₗ inlLinearMap 𝕜' I F₁ F₂ n E₁ E₂)
        (fstLinearMap 𝕜' I G₁ G₂ n Z₁ Z₂ ∘ₗ P ∘ₗ inrLinearMap 𝕜' I F₁ F₂ n E₁ E₂)
        (sndLinearMap 𝕜' I G₁ G₂ n Z₁ Z₂ ∘ₗ P ∘ₗ inlLinearMap 𝕜' I F₁ F₂ n E₁ E₂)
        (sndLinearMap 𝕜' I G₁ G₂ n Z₁ Z₂ ∘ₗ P ∘ₗ inrLinearMap 𝕜' I F₁ F₂ n E₁ E₂) = P := by
  refine LinearMap.ext fun s ↦ ?_
  conv_rhs => rw [← LinearMap.id_apply (R := 𝕜') s,
    ← inlLinearMap_comp_fstLinearMap_add_inrLinearMap_comp_sndLinearMap]
  ext x <;> simp

end Block

end ContMDiffSection
