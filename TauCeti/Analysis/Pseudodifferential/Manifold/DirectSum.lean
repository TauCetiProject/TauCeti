/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Prod

/-!
# Pseudodifferential operators between direct sums of vector bundles

Let `M` be a manifold modelled on `ℝⁿ` and `E₁`, `E₂`, `F₁`, `F₂` smooth complex vector bundles
over `M` with finite-dimensional model fibres. An operator `P : Γ(E₁ ⊕ E₂) → Γ(F₁ ⊕ F₂)` between
the sections of the direct sums `E₁ ×ᵇ E₂` and `F₁ ×ᵇ F₂` is a `2 × 2` matrix of operators
`Pᵢⱼ : Γ(Eⱼ) → Γ(Fᵢ)` (`ContMDiffSection.blockLinearMap`,
`ContMDiffSection.blockLinearMap_entries`).
This file proves that `P` is a classical pseudodifferential operator of order `m`
(`TauCeti.sectionClassicalPseudodifferentialOperators`) exactly when its four entries are
(`TauCeti.blockLinearMap_mem_sectionClassicalPseudodifferentialOperators_iff`,
`TauCeti.mem_sectionClassicalPseudodifferentialOperators_prod_iff`).

The projections `Γ(E₁ ×ᵇ E₂) → Γ(Eⱼ)` and the inclusions `Γ(Eⱼ) → Γ(E₁ ×ᵇ E₂)` are linear over the
smooth functions, so they are pseudodifferential operators of order `0`
(`TauCeti.mem_sectionClassicalPseudodifferentialOperators_zero_of_map_smul`). The entries of `P`
are the compositions of `P` with them, and `P` is the sum of the compositions `inᵢ ∘ Pᵢⱼ ∘ prⱼ`.
Both directions are therefore instances of the composition theorem for operators between bundles
(`TauCeti.comp_mem_sectionClassicalPseudodifferentialOperators`), whose middle bundles here are
the summands and the direct sums, all with finite-dimensional fibres.

Operators between direct sums occur as the folded operators of index theory. For
`P : Γ(E₀) → Γ(E₁)` with formal adjoint `P* : Γ(E₁) → Γ(E₀)`, the formally self-adjoint operator
`D_P = [[0, P*], [P, 0]]` on `Γ(E₀ ⊕ E₁)` has order `m` exactly when `P` and `P*` do
(`TauCeti.blockLinearMap_zero₁₁_zero₂₂_mem_sectionClassicalPseudodifferentialOperators_iff`). The
direct sum `P₁ ⊕ P₂` of two operators has order `m` exactly when `P₁` and `P₂` do
(`TauCeti.blockLinearMap_zero₁₂_zero₂₁_mem_sectionClassicalPseudodifferentialOperators_iff`). For a
complex of operators of order `m` with two even and two odd terms, the operator `d + d*` from the
even to the odd terms is a block operator whose entries are differentials, formal adjoints of
differentials and zeros; longer complexes need iterated block decompositions.

## Main results

* `TauCeti.fstLinearMap_mem_sectionClassicalPseudodifferentialOperators`,
  `TauCeti.sndLinearMap_mem_sectionClassicalPseudodifferentialOperators`,
  `TauCeti.inlLinearMap_mem_sectionClassicalPseudodifferentialOperators`,
  `TauCeti.inrLinearMap_mem_sectionClassicalPseudodifferentialOperators`: the projections and
  inclusions of sections of a direct sum have order `0`.
* `TauCeti.blockLinearMap_mem_sectionClassicalPseudodifferentialOperators_iff`: the block operator
  with entries `Pᵢⱼ` has order `m` exactly when every `Pᵢⱼ` does.
* `TauCeti.mem_sectionClassicalPseudodifferentialOperators_prod_iff`: an operator between direct
  sums has order `m` exactly when its four entries do.
* `TauCeti.blockLinearMap_zero₁₁_zero₂₂_mem_sectionClassicalPseudodifferentialOperators_iff` and
  `TauCeti.blockLinearMap_zero₁₂_zero₂₁_mem_sectionClassicalPseudodifferentialOperators_iff`: the
  antidiagonal operator `[[0, Q], [P, 0]]` and the diagonal operator `[[P₁, 0], [0, P₂]]`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1
  (pseudodifferential operators between sections of vector bundles, defined through their matrix
  entries in local frames).
* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968), §7
  (the operator `d + d*` of an elliptic complex) and §9 (the operator `[[0, P*], [P, 0]]` in the
  product of two elliptic operators).
-/

public section

noncomputable section

open Bundle ContMDiffSection TauCeti
open scoped ContDiff Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  {V₁ : Type*} [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [FiniteDimensional ℂ V₁]
  {E₁ : M → Type*} [TopologicalSpace (TotalSpace V₁ E₁)] [∀ x, AddCommGroup (E₁ x)]
  [∀ x, Module ℝ (E₁ x)] [∀ x, Module ℂ (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle V₁ E₁] [VectorBundle ℝ V₁ E₁] [VectorBundle ℂ V₁ E₁]
  [ContMDiffVectorBundle ∞ V₁ E₁ 𝓘(ℝ, CoordinateSpace n)]
  {V₂ : Type*} [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [FiniteDimensional ℂ V₂]
  {E₂ : M → Type*} [TopologicalSpace (TotalSpace V₂ E₂)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module ℝ (E₂ x)] [∀ x, Module ℂ (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle V₂ E₂] [VectorBundle ℝ V₂ E₂] [VectorBundle ℂ V₂ E₂]
  [ContMDiffVectorBundle ∞ V₂ E₂ 𝓘(ℝ, CoordinateSpace n)]
  {W₁ : Type*} [NormedAddCommGroup W₁] [NormedSpace ℂ W₁] [FiniteDimensional ℂ W₁]
  {F₁ : M → Type*} [TopologicalSpace (TotalSpace W₁ F₁)] [∀ x, AddCommGroup (F₁ x)]
  [∀ x, Module ℝ (F₁ x)] [∀ x, Module ℂ (F₁ x)] [∀ x, TopologicalSpace (F₁ x)]
  [FiberBundle W₁ F₁] [VectorBundle ℝ W₁ F₁] [VectorBundle ℂ W₁ F₁]
  [ContMDiffVectorBundle ∞ W₁ F₁ 𝓘(ℝ, CoordinateSpace n)]
  {W₂ : Type*} [NormedAddCommGroup W₂] [NormedSpace ℂ W₂] [FiniteDimensional ℂ W₂]
  {F₂ : M → Type*} [TopologicalSpace (TotalSpace W₂ F₂)] [∀ x, AddCommGroup (F₂ x)]
  [∀ x, Module ℝ (F₂ x)] [∀ x, Module ℂ (F₂ x)] [∀ x, TopologicalSpace (F₂ x)]
  [FiberBundle W₂ F₂] [VectorBundle ℝ W₂ F₂] [VectorBundle ℂ W₂ F₂]
  [ContMDiffVectorBundle ∞ W₂ F₂ 𝓘(ℝ, CoordinateSpace n)]

namespace TauCeti

/-! ### Projections and inclusions -/

omit [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₂] in
/-- The projection `Γ(E₁ ×ᵇ E₂) → Γ(E₁)` is a classical pseudodifferential operator of order `0`. -/
theorem fstLinearMap_mem_sectionClassicalPseudodifferentialOperators :
    fstLinearMap ℂ 𝓘(ℝ, CoordinateSpace n) V₁ V₂ ∞ E₁ E₂ ∈
      sectionClassicalPseudodifferentialOperators 0 :=
  mem_sectionClassicalPseudodifferentialOperators_zero_of_map_smul
    (fstLinearMap_smul_function · ·)

omit [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₂] in
/-- The projection `Γ(E₁ ×ᵇ E₂) → Γ(E₂)` is a classical pseudodifferential operator of order `0`. -/
theorem sndLinearMap_mem_sectionClassicalPseudodifferentialOperators :
    sndLinearMap ℂ 𝓘(ℝ, CoordinateSpace n) V₁ V₂ ∞ E₁ E₂ ∈
      sectionClassicalPseudodifferentialOperators 0 :=
  mem_sectionClassicalPseudodifferentialOperators_zero_of_map_smul
    (sndLinearMap_smul_function · ·)

omit [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₂] in
/-- The inclusion `Γ(E₁) → Γ(E₁ ×ᵇ E₂)` is a classical pseudodifferential operator of order `0`. -/
theorem inlLinearMap_mem_sectionClassicalPseudodifferentialOperators :
    inlLinearMap ℂ 𝓘(ℝ, CoordinateSpace n) V₁ V₂ ∞ E₁ E₂ ∈
      sectionClassicalPseudodifferentialOperators 0 :=
  mem_sectionClassicalPseudodifferentialOperators_zero_of_map_smul
    (inlLinearMap_smul_function · ·)

omit [FiniteDimensional ℂ V₁] [FiniteDimensional ℂ V₂] in
/-- The inclusion `Γ(E₂) → Γ(E₁ ×ᵇ E₂)` is a classical pseudodifferential operator of order `0`. -/
theorem inrLinearMap_mem_sectionClassicalPseudodifferentialOperators :
    inrLinearMap ℂ 𝓘(ℝ, CoordinateSpace n) V₁ V₂ ∞ E₁ E₂ ∈
      sectionClassicalPseudodifferentialOperators 0 :=
  mem_sectionClassicalPseudodifferentialOperators_zero_of_map_smul
    (inrLinearMap_smul_function · ·)

/-! ### Block operators -/

variable {m : ℝ}

/-- **Block operators.** The operator `Γ(E₁ ×ᵇ E₂) → Γ(F₁ ×ᵇ F₂)` with matrix
`[[P₁₁, P₁₂], [P₂₁, P₂₂]]` is a classical pseudodifferential operator of order `m` exactly when its
four entries `Pᵢⱼ : Γ(Eⱼ) → Γ(Fᵢ)` are. -/
theorem blockLinearMap_mem_sectionClassicalPseudodifferentialOperators_iff
    {P₁₁ : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V₁, E₁⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W₁, F₁⟯}
    {P₁₂ : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V₂, E₂⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W₁, F₁⟯}
    {P₂₁ : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V₁, E₁⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W₂, F₂⟯}
    {P₂₂ : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V₂, E₂⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W₂, F₂⟯} :
    blockLinearMap P₁₁ P₁₂ P₂₁ P₂₂ ∈ sectionClassicalPseudodifferentialOperators m ↔
      P₁₁ ∈ sectionClassicalPseudodifferentialOperators m ∧
        P₁₂ ∈ sectionClassicalPseudodifferentialOperators m ∧
          P₂₁ ∈ sectionClassicalPseudodifferentialOperators m ∧
            P₂₂ ∈ sectionClassicalPseudodifferentialOperators m := by
  refine ⟨fun h ↦ ⟨?_, ?_, ?_, ?_⟩, fun ⟨h₁₁, h₁₂, h₂₁, h₂₂⟩ ↦ ?_⟩
  -- each entry is the block operator between a projection and an inclusion
  · simpa using comp_comp_mem_sectionClassicalPseudodifferentialOperators
      fstLinearMap_mem_sectionClassicalPseudodifferentialOperators h
      inlLinearMap_mem_sectionClassicalPseudodifferentialOperators
  · simpa using comp_comp_mem_sectionClassicalPseudodifferentialOperators
      fstLinearMap_mem_sectionClassicalPseudodifferentialOperators h
      inrLinearMap_mem_sectionClassicalPseudodifferentialOperators
  · simpa using comp_comp_mem_sectionClassicalPseudodifferentialOperators
      sndLinearMap_mem_sectionClassicalPseudodifferentialOperators h
      inlLinearMap_mem_sectionClassicalPseudodifferentialOperators
  · simpa using comp_comp_mem_sectionClassicalPseudodifferentialOperators
      sndLinearMap_mem_sectionClassicalPseudodifferentialOperators h
      inrLinearMap_mem_sectionClassicalPseudodifferentialOperators
  -- the block operator is the sum of the four operators `inᵢ ∘ Pᵢⱼ ∘ prⱼ`
  rw [blockLinearMap_def, LinearMap.comp_add, LinearMap.comp_add]
  exact add_mem
    (add_mem
      (comp_comp_mem_sectionClassicalPseudodifferentialOperators
        inlLinearMap_mem_sectionClassicalPseudodifferentialOperators h₁₁
        fstLinearMap_mem_sectionClassicalPseudodifferentialOperators)
      (comp_comp_mem_sectionClassicalPseudodifferentialOperators
        inlLinearMap_mem_sectionClassicalPseudodifferentialOperators h₁₂
        sndLinearMap_mem_sectionClassicalPseudodifferentialOperators))
    (add_mem
      (comp_comp_mem_sectionClassicalPseudodifferentialOperators
        inrLinearMap_mem_sectionClassicalPseudodifferentialOperators h₂₁
        fstLinearMap_mem_sectionClassicalPseudodifferentialOperators)
      (comp_comp_mem_sectionClassicalPseudodifferentialOperators
        inrLinearMap_mem_sectionClassicalPseudodifferentialOperators h₂₂
        sndLinearMap_mem_sectionClassicalPseudodifferentialOperators))

/-- **Operators between direct sums.** An operator `P : Γ(E₁ ×ᵇ E₂) → Γ(F₁ ×ᵇ F₂)` is a classical
pseudodifferential operator of order `m` exactly when its four entries `prᵢ ∘ P ∘ inⱼ` are. -/
theorem mem_sectionClassicalPseudodifferentialOperators_prod_iff
    {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V₁ × V₂, E₁ ×ᵇ E₂⟯ →ₗ[ℂ]
      Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W₁ × W₂, F₁ ×ᵇ F₂⟯} :
    P ∈ sectionClassicalPseudodifferentialOperators m ↔
      fstLinearMap ℂ 𝓘(ℝ, CoordinateSpace n) W₁ W₂ ∞ F₁ F₂ ∘ₗ P ∘ₗ
          inlLinearMap ℂ 𝓘(ℝ, CoordinateSpace n) V₁ V₂ ∞ E₁ E₂ ∈
        sectionClassicalPseudodifferentialOperators m ∧
      fstLinearMap ℂ 𝓘(ℝ, CoordinateSpace n) W₁ W₂ ∞ F₁ F₂ ∘ₗ P ∘ₗ
          inrLinearMap ℂ 𝓘(ℝ, CoordinateSpace n) V₁ V₂ ∞ E₁ E₂ ∈
        sectionClassicalPseudodifferentialOperators m ∧
      sndLinearMap ℂ 𝓘(ℝ, CoordinateSpace n) W₁ W₂ ∞ F₁ F₂ ∘ₗ P ∘ₗ
          inlLinearMap ℂ 𝓘(ℝ, CoordinateSpace n) V₁ V₂ ∞ E₁ E₂ ∈
        sectionClassicalPseudodifferentialOperators m ∧
      sndLinearMap ℂ 𝓘(ℝ, CoordinateSpace n) W₁ W₂ ∞ F₁ F₂ ∘ₗ P ∘ₗ
          inrLinearMap ℂ 𝓘(ℝ, CoordinateSpace n) V₁ V₂ ∞ E₁ E₂ ∈
        sectionClassicalPseudodifferentialOperators m := by
  conv_lhs => rw [← blockLinearMap_entries P]
  exact blockLinearMap_mem_sectionClassicalPseudodifferentialOperators_iff

/-- **Antidiagonal operators.** For `P : Γ(E₁) → Γ(F₂)` and `Q : Γ(E₂) → Γ(F₁)`, the operator
`[[0, Q], [P, 0]] : Γ(E₁ ×ᵇ E₂) → Γ(F₁ ×ᵇ F₂)` is a classical pseudodifferential operator of
order `m` exactly when `P` and `Q` are. With `F₁ = E₁`, `F₂ = E₂` and `Q` a formal adjoint of `P`,
this is the formally self-adjoint operator `[[0, P*], [P, 0]]` on `Γ(E₁ ⊕ E₂)`. -/
theorem blockLinearMap_zero₁₁_zero₂₂_mem_sectionClassicalPseudodifferentialOperators_iff
    {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V₁, E₁⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W₂, F₂⟯}
    {Q : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V₂, E₂⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W₁, F₁⟯} :
    blockLinearMap 0 Q P 0 ∈ sectionClassicalPseudodifferentialOperators m ↔
      P ∈ sectionClassicalPseudodifferentialOperators m ∧
        Q ∈ sectionClassicalPseudodifferentialOperators m := by
  simp [blockLinearMap_mem_sectionClassicalPseudodifferentialOperators_iff, zero_mem, and_comm]

/-- **Diagonal operators.** For `P₁ : Γ(E₁) → Γ(F₁)` and `P₂ : Γ(E₂) → Γ(F₂)`, the direct sum
`[[P₁, 0], [0, P₂]] : Γ(E₁ ×ᵇ E₂) → Γ(F₁ ×ᵇ F₂)` is a classical pseudodifferential operator of
order `m` exactly when `P₁` and `P₂` are. -/
theorem blockLinearMap_zero₁₂_zero₂₁_mem_sectionClassicalPseudodifferentialOperators_iff
    {P₁ : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V₁, E₁⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W₁, F₁⟯}
    {P₂ : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V₂, E₂⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W₂, F₂⟯} :
    blockLinearMap P₁ 0 0 P₂ ∈ sectionClassicalPseudodifferentialOperators m ↔
      P₁ ∈ sectionClassicalPseudodifferentialOperators m ∧
        P₂ ∈ sectionClassicalPseudodifferentialOperators m := by
  simp [blockLinearMap_mem_sectionClassicalPseudodifferentialOperators_iff, zero_mem]

end TauCeti
