/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Smoothing

/-!
# Parametrices of pseudodifferential operators between vector bundles

Let `M` be a manifold modelled on `ℝⁿ` and let `E`, `F` be smooth complex vector bundles over `M`
whose model fibres `V`, `W` are finite-dimensional. A **parametrix** of a classical
pseudodifferential operator `P : Γ(E) → Γ(F)`
(`TauCeti.sectionClassicalPseudodifferentialOperators`) is a classical pseudodifferential operator
`Q : Γ(F) → Γ(E)` inverting `P` modulo the operators of order `-∞`
(`TauCeti.sectionSmoothingPseudodifferentialOperators`): `P ∘ Q - 1` and `Q ∘ P - 1` have order
`-∞`. This file proves the algebraic half of the parametrix theory between bundles, which uses only
that the operators of order `-∞` form a two-sided ideal
(`TauCeti.comp_mem_sectionSmoothingPseudodifferentialOperators_of_left`,
`TauCeti.comp_mem_sectionSmoothingPseudodifferentialOperators_of_right`). These are the bundle
forms of the scalar results in `TauCeti.Analysis.Pseudodifferential.Manifold.Parametrix`.

**Left and right parametrices agree.** If `L` is a left parametrix and `R` a right parametrix of
`P`, then `L - R` has order `-∞`
(`TauCeti.sub_mem_sectionSmoothingPseudodifferentialOperators_of_comp_sub_id`), because

`L - R = (L ∘ P - 1) ∘ R - L ∘ (P ∘ R - 1)`.

Consequently each of them is a two-sided parametrix
(`TauCeti.right_comp_sub_id_mem_sectionSmoothingPseudodifferentialOperators`,
`TauCeti.comp_left_sub_id_mem_sectionSmoothingPseudodifferentialOperators`). So a parametrix of an
elliptic operator between bundles may be built one side at a time, for instance from the left and
right inverse-symbol recursions.

**Uniqueness.** A two-sided parametrix is unique modulo operators of order `-∞`: given one
parametrix `Q` of `P`, a classical pseudodifferential operator `Q'` is another exactly when
`Q' - Q` has order `-∞`
(`comp_sub_id_mem_and_comp_sub_id_mem_iff_sub_mem_sectionSmoothingPseudodifferentialOperators`).
Dually, the parametrices of `P` only depend on `P` modulo operators of order `-∞`
(`comp_sub_id_mem_and_comp_sub_id_mem_iff_of_sub_mem_sectionSmoothingPseudodifferentialOperators`).

## Main results

* `TauCeti.sub_mem_sectionSmoothingPseudodifferentialOperators_of_comp_sub_id`: a left and a right
  parametrix of the same operator differ by an operator of order `-∞`.
* `TauCeti.right_comp_sub_id_mem_sectionSmoothingPseudodifferentialOperators`,
  `TauCeti.comp_left_sub_id_mem_sectionSmoothingPseudodifferentialOperators`: if an operator has
  both a left and a right parametrix, each of them is a two-sided parametrix.
* `comp_sub_id_mem_and_comp_sub_id_mem_iff_sub_mem_sectionSmoothingPseudodifferentialOperators`:
  two-sided parametrices are unique modulo operators of order `-∞`.
* `comp_sub_id_mem_and_comp_sub_id_mem_iff_of_sub_mem_sectionSmoothingPseudodifferentialOperators`:
  operators which agree modulo order `-∞` have the same two-sided parametrices.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (parametrices
  of elliptic operators, and the discussion after Definition 18.1.20).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §4,
  (4.1)–(4.6).
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M] [T2Space M]
  [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle V E]
  [VectorBundle ℝ V E] [VectorBundle ℂ V E] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F] [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  {m : ℝ}
  {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}
  {Q L R : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯}

/-! ### Left and right parametrices -/

section LeftRight

variable {m' m'' : ℝ} (hL : L ∈ sectionClassicalPseudodifferentialOperators m')
  (hR : R ∈ sectionClassicalPseudodifferentialOperators m'')
  (hLP : L ∘ₗ P - LinearMap.id ∈ sectionSmoothingPseudodifferentialOperators)
  (hPR : P ∘ₗ R - LinearMap.id ∈ sectionSmoothingPseudodifferentialOperators)

include hL hR hLP hPR

/-- **Left and right parametrices agree modulo order `-∞`.** If `L, R : Γ(F) → Γ(E)` are classical
pseudodifferential operators between bundles of finite rank such that `L ∘ P - 1` and `P ∘ R - 1`
have order `-∞`, then `L - R` has order `-∞`, since `L - R = (L ∘ P - 1) ∘ R - L ∘ (P ∘ R - 1)`.
No hypothesis on `P` is needed. -/
theorem sub_mem_sectionSmoothingPseudodifferentialOperators_of_comp_sub_id :
    L - R ∈ sectionSmoothingPseudodifferentialOperators := by
  have h : L - R = (L ∘ₗ P - LinearMap.id) ∘ₗ R - L ∘ₗ (P ∘ₗ R - LinearMap.id) := by
    ext u : 1
    simp
  rw [h]
  exact sub_mem (comp_mem_sectionSmoothingPseudodifferentialOperators_of_left hLP hR)
    (comp_mem_sectionSmoothingPseudodifferentialOperators_of_right hL hPR)

/-- **A right parametrix is a left parametrix.** If a classical pseudodifferential operator `P`
between bundles of finite rank has a left parametrix `L` and a right parametrix `R`, then
`R ∘ P - 1` has order `-∞`. -/
theorem right_comp_sub_id_mem_sectionSmoothingPseudodifferentialOperators
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) :
    R ∘ₗ P - LinearMap.id ∈ sectionSmoothingPseudodifferentialOperators := by
  have h : R ∘ₗ P - LinearMap.id = (L ∘ₗ P - LinearMap.id) - (L - R) ∘ₗ P := by
    ext u : 1
    simp
  rw [h]
  exact sub_mem hLP (comp_mem_sectionSmoothingPseudodifferentialOperators_of_left
    (sub_mem_sectionSmoothingPseudodifferentialOperators_of_comp_sub_id hL hR hLP hPR) hP)

/-- **A left parametrix is a right parametrix.** If a classical pseudodifferential operator `P`
between bundles of finite rank has a left parametrix `L` and a right parametrix `R`, then
`P ∘ L - 1` has order `-∞`. -/
theorem comp_left_sub_id_mem_sectionSmoothingPseudodifferentialOperators
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) :
    P ∘ₗ L - LinearMap.id ∈ sectionSmoothingPseudodifferentialOperators := by
  have h : P ∘ₗ L - LinearMap.id = (P ∘ₗ R - LinearMap.id) + P ∘ₗ (L - R) := by
    ext u : 1
    simp
  rw [h]
  exact add_mem hPR (comp_mem_sectionSmoothingPseudodifferentialOperators_of_right hP
    (sub_mem_sectionSmoothingPseudodifferentialOperators_of_comp_sub_id hL hR hLP hPR))

end LeftRight

/-! ### Uniqueness of parametrices -/

/-- **Parametrices are unique modulo operators of order `-∞`.** Let `Q` be a two-sided parametrix
of a classical pseudodifferential operator `P` between bundles of finite rank, modulo operators of
order `-∞`. A classical pseudodifferential operator `Q'` is also a two-sided parametrix of `P`
exactly when `Q' - Q` has order `-∞`. -/
theorem
    comp_sub_id_mem_and_comp_sub_id_mem_iff_sub_mem_sectionSmoothingPseudodifferentialOperators
    {m' m'' : ℝ}
    {Q' : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯}
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hQ : Q ∈ sectionClassicalPseudodifferentialOperators m')
    (hQ' : Q' ∈ sectionClassicalPseudodifferentialOperators m'')
    (hPQ : P ∘ₗ Q - LinearMap.id ∈ sectionSmoothingPseudodifferentialOperators)
    (hQP : Q ∘ₗ P - LinearMap.id ∈ sectionSmoothingPseudodifferentialOperators) :
    (P ∘ₗ Q' - LinearMap.id ∈ sectionSmoothingPseudodifferentialOperators ∧
      Q' ∘ₗ P - LinearMap.id ∈ sectionSmoothingPseudodifferentialOperators) ↔
      Q' - Q ∈ sectionSmoothingPseudodifferentialOperators := by
  refine ⟨fun ⟨_, hQ'P⟩ ↦
    sub_mem_sectionSmoothingPseudodifferentialOperators_of_comp_sub_id hQ' hQ hQ'P hPQ,
    fun h ↦ ⟨?_, ?_⟩⟩
  · rw [show P ∘ₗ Q' - LinearMap.id = (P ∘ₗ Q - LinearMap.id) + P ∘ₗ (Q' - Q) by
      ext u : 1; simp]
    exact add_mem hPQ (comp_mem_sectionSmoothingPseudodifferentialOperators_of_right hP h)
  · rw [show Q' ∘ₗ P - LinearMap.id = (Q ∘ₗ P - LinearMap.id) + (Q' - Q) ∘ₗ P by
      ext u : 1; simp]
    exact add_mem hQP (comp_mem_sectionSmoothingPseudodifferentialOperators_of_left h hP)

/-- **Parametrices only see an operator modulo order `-∞`.** If `P, P' : Γ(E) → Γ(F)` differ by an
operator of order `-∞`, between bundles of finite rank, then a classical pseudodifferential operator
`Q` is a two-sided parametrix of `P'` exactly when it is one of `P`. -/
theorem
    comp_sub_id_mem_and_comp_sub_id_mem_iff_of_sub_mem_sectionSmoothingPseudodifferentialOperators
    {m' : ℝ}
    {P' : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}
    (hQ : Q ∈ sectionClassicalPseudodifferentialOperators m')
    (h : P' - P ∈ sectionSmoothingPseudodifferentialOperators) :
    (P' ∘ₗ Q - LinearMap.id ∈ sectionSmoothingPseudodifferentialOperators ∧
      Q ∘ₗ P' - LinearMap.id ∈ sectionSmoothingPseudodifferentialOperators) ↔
      (P ∘ₗ Q - LinearMap.id ∈ sectionSmoothingPseudodifferentialOperators ∧
        Q ∘ₗ P - LinearMap.id ∈ sectionSmoothingPseudodifferentialOperators) := by
  have hPQ : P' ∘ₗ Q - LinearMap.id = (P ∘ₗ Q - LinearMap.id) + (P' - P) ∘ₗ Q := by
    ext u : 1
    simp
  have hQP : Q ∘ₗ P' - LinearMap.id = (Q ∘ₗ P - LinearMap.id) + Q ∘ₗ (P' - P) := by
    ext u : 1
    simp
  rw [hPQ, hQP, Submodule.add_mem_iff_left _
      (comp_mem_sectionSmoothingPseudodifferentialOperators_of_left h hQ),
    Submodule.add_mem_iff_left _
      (comp_mem_sectionSmoothingPseudodifferentialOperators_of_right hQ h)]

end TauCeti
