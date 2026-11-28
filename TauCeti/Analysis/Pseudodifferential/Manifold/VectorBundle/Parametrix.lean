/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.AsymptoticSum
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Composition
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Smoothing
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.SymbolQuantization

/-!
# Parametrices of pseudodifferential operators between vector bundles

Let `M` be a manifold modelled on `ℝⁿ` and `E`, `F` smooth complex vector bundles over `M` with
finite-dimensional model fibres `V` and `W`. A classical pseudodifferential operator
`P : Γ(E) → Γ(F)` of order `m` (`TauCeti.sectionClassicalPseudodifferentialOperators`) is
elliptic (`TauCeti.IsSectionClassicalElliptic`) when its principal symbol
`σ_m(P)(x, ξ) : E_x → F_x` is bijective at every nonzero covector `ξ ∈ T*ₓM`. This file constructs
parametrices of elliptic operators between bundles on a compact manifold: operators
`Q : Γ(F) → Γ(E)` of order `-m` inverting `P` on both sides modulo operators of order `-∞`. They
are the bundle counterpart of the scalar parametrices of `Manifold/Parametrix.lean`, and the input
of the elliptic estimates and of the Fredholm theory of `P` between Sobolev spaces of sections.

**The inverse principal symbol is a symbol.** The fibrewise inverses `σ_m(P)(x, ξ)⁻¹ : F_x → E_x`
form a smooth positively homogeneous `Hom(F, E)`-valued symbol of degree `-m`
(`TauCeti.IsSectionClassicalElliptic.exists_mem_sectionHomogeneousCotangentSymbols_comp_eq_id`), in
the sense of `TauCeti.sectionHomogeneousCotangentSymbols`. This is the general fact that the
fibrewise inverse of a smooth homogeneous symbol bijective at nonzero covectors is again one
(`TauCeti.exists_mem_sectionHomogeneousCotangentSymbols_comp_eq_id`), applied to `σ_m(P)`. The
scalar statement is
`TauCeti.IsClassicalElliptic.inv_classicalPrincipalSymbol_mem_homogeneousCotangentSymbols`.

**Parametrices.** On a compact manifold every smooth homogeneous `Hom(F, E)`-valued symbol is a
principal symbol (`TauCeti.sectionClassicalPrincipalSymbolLinearMap_surjective`), so there is an
operator `Q₀` of order `-m` with principal symbol `σ_m(P)⁻¹`
(`TauCeti.IsSectionClassicalElliptic.exists_sectionClassicalPrincipalSymbol_comp_eq_id`). The
principal symbols of `P Q₀` and `Q₀ P` are those of the identities, so `P Q₀ = 1 - R` and
`Q₀ P = 1 - L` with `R` and `L` of order `-1`. The Neumann series on a bundle
(`exists_forall_one_sub_mul_sub_one_mem_sectionClassicalPseudodifferentialOperators`) inverts
`1 - R` and `1 - L` modulo operators of every order `-N`, by operators `S` and `S'`. Then
`Q = Q₀ S` is a right parametrix and `Q' = S' Q₀` a left parametrix, and they agree modulo order
`-∞`, since `Q' - Q = Q' (1 - P Q) + (Q' P - 1) Q`. So `Q` is a two-sided parametrix:
`P Q - 1` and `Q P - 1` have every order `-N`
(`IsSectionClassicalElliptic.exists_comp_sub_id_mem_sectionClassicalPseudodifferentialOperators`).
Conversely an operator with such a parametrix is elliptic
(`TauCeti.IsSectionClassicalEllipticAt.of_comp_sub_id_mem`), so on a compact manifold the elliptic
operators between bundles are exactly those invertible modulo operators of order `-∞`
(`TauCeti.isSectionClassicalElliptic_iff_exists_comp_sub_id_mem`).

The algebraic half of the theory uses only that the operators of order `-∞`
(`TauCeti.sectionSmoothingPseudodifferentialOperators`) form a two-sided ideal
(`TauCeti.comp_mem_sectionSmoothingPseudodifferentialOperators_of_left`,
`TauCeti.comp_mem_sectionSmoothingPseudodifferentialOperators_of_right`), and needs no compactness.

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
* `TauCeti.IsSectionClassicalElliptic.exists_mem_sectionHomogeneousCotangentSymbols_comp_eq_id`:
  the inverse principal symbol of an elliptic operator between bundles is a smooth positively
  homogeneous `Hom(F, E)`-valued symbol of degree `-m`.
* `TauCeti.IsSectionClassicalElliptic.exists_sectionClassicalPrincipalSymbol_comp_eq_id`: on a
  compact manifold, it is the principal symbol of an operator of order `-m`.
* `IsSectionClassicalElliptic.exists_comp_sub_id_mem_sectionClassicalPseudodifferentialOperators`:
  on a compact manifold, an elliptic operator between bundles has a two-sided parametrix of order
  `-m` modulo operators of every order `-N`.
* `TauCeti.isSectionClassicalElliptic_iff_exists_comp_sub_id_mem`: on a compact manifold,
  ellipticity is invertibility modulo operators of order `-∞`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (parametrices
  of elliptic operators, and operators between vector bundles after Definition 18.1.20).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §4,
  (4.1)–(4.6), and §8.
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3.
-/

public section

noncomputable section

open Bundle Filter Module Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
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

/-! ### The inverse principal symbol -/

/-- **The inverse principal symbol.** If `P : Γ(E) → Γ(F)` is elliptic of order `m`, the fibrewise
inverses `σ_m(P)(x, ξ)⁻¹ : F_x → E_x` at nonzero covectors form a smooth positively homogeneous
`Hom(F, E)`-valued symbol of degree `-m`: there is `s` in
`TauCeti.sectionHomogeneousCotangentSymbols n W F V E (-m)` with `s(x, ξ) ∘ σ_m(P)(x, ξ) = 1` and
`σ_m(P)(x, ξ) ∘ s(x, ξ) = 1` for every nonzero covector `ξ ∈ T*ₓM`. -/
theorem IsSectionClassicalElliptic.exists_mem_sectionHomogeneousCotangentSymbols_comp_eq_id
    (hPe : IsSectionClassicalElliptic m P) :
    ∃ s ∈ sectionHomogeneousCotangentSymbols n W F V E (-m), ∀ x ξ, ξ ≠ 0 →
      s x ξ ∘ₗ sectionClassicalPrincipalSymbol m P x ξ = LinearMap.id ∧
        sectionClassicalPrincipalSymbol m P x ξ ∘ₗ s x ξ = LinearMap.id :=
  TauCeti.exists_mem_sectionHomogeneousCotangentSymbols_comp_eq_id
    sectionClassicalPrincipalSymbol_mem_sectionHomogeneousCotangentSymbols fun x ξ hξ ↦
      isSectionClassicalEllipticAt_iff.1 (isSectionClassicalElliptic_iff.1 hPe x) ξ hξ

/-- **Quantizing the inverse principal symbol.** On a compact manifold, an elliptic operator
`P : Γ(E) → Γ(F)` of order `m` has an operator `Q : Γ(F) → Γ(E)` of order `-m` whose principal
symbol is the fibrewise inverse of that of `P`: `σ_{-m}(Q)(x, ξ) ∘ σ_m(P)(x, ξ) = 1` and
`σ_m(P)(x, ξ) ∘ σ_{-m}(Q)(x, ξ) = 1` at every nonzero covector `ξ ∈ T*ₓM`. -/
theorem IsSectionClassicalElliptic.exists_sectionClassicalPrincipalSymbol_comp_eq_id
    [CompactSpace M] (hPe : IsSectionClassicalElliptic m P) :
    ∃ Q ∈ sectionClassicalPseudodifferentialOperators (V := W) (E := F) (W := V) (F := E) (-m),
      ∀ x ξ, ξ ≠ 0 →
        sectionClassicalPrincipalSymbol (-m) Q x ξ ∘ₗ sectionClassicalPrincipalSymbol m P x ξ =
          LinearMap.id ∧
        sectionClassicalPrincipalSymbol m P x ξ ∘ₗ sectionClassicalPrincipalSymbol (-m) Q x ξ =
          LinearMap.id := by
  obtain ⟨s, hs, hsP⟩ := hPe.exists_mem_sectionHomogeneousCotangentSymbols_comp_eq_id
  obtain ⟨⟨Q, hQ⟩, hQs⟩ := sectionClassicalPrincipalSymbolLinearMap_surjective
    (n := n) (V := W) (E := F) (W := V) (F := E) (m := -m) ⟨s, hs⟩
  have hσ : sectionClassicalPrincipalSymbol (-m) Q = s := by
    simpa using congrArg Subtype.val hQs
  exact ⟨Q, hQ, fun x ξ hξ ↦ hσ ▸ hsP x ξ hξ⟩

/-! ### Parametrices -/

/-- **Inverting the principal symbol.** On a compact manifold, an elliptic operator `P` of order
`m` between bundles has an inverse modulo operators of order `-1`: an operator `Q` of order `-m`
whose principal symbol is the inverse of that of `P`. -/
private theorem IsSectionClassicalElliptic.exists_comp_sub_id_mem_neg_one [CompactSpace M]
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hPe : IsSectionClassicalElliptic m P) :
    ∃ Q ∈ sectionClassicalPseudodifferentialOperators (V := W) (E := F) (W := V) (F := E) (-m),
      P ∘ₗ Q - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-1) ∧
        Q ∘ₗ P - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-1) := by
  obtain ⟨Q, hQ, hσ⟩ := hPe.exists_sectionClassicalPrincipalSymbol_comp_eq_id
  have hPQ : P ∘ₗ Q ∈ sectionClassicalPseudodifferentialOperators 0 := by
    simpa using comp_mem_sectionClassicalPseudodifferentialOperators hP hQ
  have hQP : Q ∘ₗ P ∈ sectionClassicalPseudodifferentialOperators 0 := by
    simpa using comp_mem_sectionClassicalPseudodifferentialOperators hQ hP
  -- Both products have the principal symbol of the identity.
  rw [show (-1 : ℝ) = 0 - 1 by norm_num]
  refine ⟨Q, hQ,
    sub_mem_sectionClassicalPseudodifferentialOperators_of_sectionClassicalPrincipalSymbol_eq hPQ
      id_mem_sectionClassicalPseudodifferentialOperators fun x ξ ↦ ?_,
    sub_mem_sectionClassicalPseudodifferentialOperators_of_sectionClassicalPrincipalSymbol_eq hQP
      id_mem_sectionClassicalPseudodifferentialOperators fun x ξ ↦ ?_⟩
  · rcases eq_or_ne ξ 0 with rfl | hξ
    · simp
    · have h := sectionClassicalPrincipalSymbol_comp hP hQ x ξ
      rw [add_neg_cancel] at h
      rw [h, (hσ x ξ hξ).2, sectionClassicalPrincipalSymbol_id x hξ]
  · rcases eq_or_ne ξ 0 with rfl | hξ
    · simp
    · have h := sectionClassicalPrincipalSymbol_comp hQ hP x ξ
      rw [neg_add_cancel] at h
      rw [h, (hσ x ξ hξ).1, sectionClassicalPrincipalSymbol_id x hξ]

/-- **Parametrices of elliptic operators between bundles.** On a compact manifold, let
`P : Γ(E) → Γ(F)` be an elliptic classical pseudodifferential operator of order `m` between
bundles with finite-dimensional fibres. Then there is a classical pseudodifferential operator
`Q : Γ(F) → Γ(E)` of order `-m` that inverts `P` on both sides modulo operators of order `-∞`:
`P ∘ Q - 1` and `Q ∘ P - 1` have every order `-N`. -/
theorem
    IsSectionClassicalElliptic.exists_comp_sub_id_mem_sectionClassicalPseudodifferentialOperators
    [CompactSpace M] (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hPe : IsSectionClassicalElliptic m P) :
    ∃ Q ∈ sectionClassicalPseudodifferentialOperators (V := W) (E := F) (W := V) (F := E) (-m),
      ∀ N : ℕ, P ∘ₗ Q - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-N) ∧
        Q ∘ₗ P - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-N) := by
  obtain ⟨Q₀, hQ₀, hPQ₀, hQ₀P⟩ := hPe.exists_comp_sub_id_mem_neg_one hP
  -- With `P Q₀ = 1 - R` and `Q₀ P = 1 - L`, both `R` and `L` of order `-1`, the Neumann series
  -- inverts `1 - R` and `1 - L` modulo order `-∞`; so `Q = Q₀ S` is a right parametrix and
  -- `Q' = S' Q₀` a left parametrix.
  obtain ⟨S, hS, hSN⟩ :=
    exists_forall_one_sub_mul_sub_one_mem_sectionClassicalPseudodifferentialOperators
      (R := LinearMap.id - P ∘ₗ Q₀) (by simpa using neg_mem hPQ₀)
  obtain ⟨S', hS', hS'N⟩ :=
    exists_forall_one_sub_mul_sub_one_mem_sectionClassicalPseudodifferentialOperators
      (R := LinearMap.id - Q₀ ∘ₗ P) (by simpa using neg_mem hQ₀P)
  have hQ : Q₀ ∘ₗ S ∈ sectionClassicalPseudodifferentialOperators (-m) := by
    simpa using comp_mem_sectionClassicalPseudodifferentialOperators hQ₀ hS
  have hQ' : S' ∘ₗ Q₀ ∈ sectionClassicalPseudodifferentialOperators (-m) := by
    simpa using comp_mem_sectionClassicalPseudodifferentialOperators hS' hQ₀
  have hPQ (N : ℕ) :
      P ∘ₗ (Q₀ ∘ₗ S) - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-N) := by
    simpa [Module.End.mul_eq_comp, Module.End.one_eq_id, LinearMap.comp_assoc] using (hSN N).1
  have hQ'P (N : ℕ) :
      (S' ∘ₗ Q₀) ∘ₗ P - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-N) := by
    simpa [Module.End.mul_eq_comp, Module.End.one_eq_id, LinearMap.comp_assoc] using (hS'N N).2
  -- The left and right parametrices agree modulo order `-∞`:
  -- `Q' - Q = Q' (1 - P Q) + (Q' P - 1) Q`, so `(Q' - Q) P` has every order `-N`.
  have hdiff (N : ℕ) : (S' ∘ₗ Q₀ - Q₀ ∘ₗ S) ∘ₗ P ∈
      sectionClassicalPseudodifferentialOperators (-N) := by
    have h₁ := comp_mem_sectionClassicalPseudodifferentialOperators hQ' (neg_mem (hPQ N))
    have h₂ := comp_mem_sectionClassicalPseudodifferentialOperators (hQ'P N) hQ
    rw [add_comm] at h₂
    have h := comp_mem_sectionClassicalPseudodifferentialOperators (add_mem h₁ h₂) hP
    rw [show -m + -(N : ℝ) + m = -N by ring] at h
    convert h using 1
    ext u : 1
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply,
      LinearMap.id_apply, map_neg, map_sub]
    abel
  refine ⟨Q₀ ∘ₗ S, hQ, fun N ↦ ⟨hPQ N, ?_⟩⟩
  rw [show (Q₀ ∘ₗ S) ∘ₗ P - LinearMap.id =
      ((S' ∘ₗ Q₀) ∘ₗ P - LinearMap.id) - (S' ∘ₗ Q₀ - Q₀ ∘ₗ S) ∘ₗ P by
    ext u : 1
    simp]
  exact sub_mem (hQ'P N) (hdiff N)

/-- **Ellipticity is invertibility modulo order `-∞`.** On a compact manifold, a classical
pseudodifferential operator `P : Γ(E) → Γ(F)` of order `m` between bundles with
finite-dimensional fibres is elliptic exactly when it has a two-sided parametrix of order `-m`: an
operator `Q : Γ(F) → Γ(E)` of order `-m` with `P ∘ Q - 1` and `Q ∘ P - 1` of every order `-N`. -/
theorem isSectionClassicalElliptic_iff_exists_comp_sub_id_mem
    [CompactSpace M] (hP : P ∈ sectionClassicalPseudodifferentialOperators m) :
    IsSectionClassicalElliptic m P ↔
      ∃ Q ∈ sectionClassicalPseudodifferentialOperators (V := W) (E := F) (W := V) (F := E) (-m),
        ∀ N : ℕ, P ∘ₗ Q - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-N) ∧
          Q ∘ₗ P - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-N) :=
  ⟨fun hPe ↦ hPe.exists_comp_sub_id_mem_sectionClassicalPseudodifferentialOperators hP,
    fun ⟨Q, hQ, hN⟩ ↦ isSectionClassicalElliptic_iff.2 fun x ↦
      IsSectionClassicalEllipticAt.of_comp_sub_id_mem hQ hP (neg_add_cancel m)
        (by simpa using (hN 1).2) (by simpa using (hN 1).1) x⟩

end TauCeti
