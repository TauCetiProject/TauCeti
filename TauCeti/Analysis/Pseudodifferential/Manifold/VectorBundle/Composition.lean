/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.PrincipalSymbol
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Smoothing
import TauCeti.Geometry.Manifold.BumpFunction
import TauCeti.Topology.Algebra.Support
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Principal symbols of compositions of pseudodifferential operators between vector bundles

Let `M` be a manifold modelled on `ℝⁿ` and `E`, `F`, `G` smooth complex vector bundles over `M`
with finite-dimensional model fibres. If `P : Γ(E) → Γ(F)` and `R : Γ(F) → Γ(G)` are classical
pseudodifferential operators of orders `m` and `m'`, then `R ∘ P` has order `m' + m`
(`TauCeti.comp_mem_sectionClassicalPseudodifferentialOperators`). This file shows that its
principal symbol is the composition of the principal symbols
(`TauCeti.sectionClassicalPrincipalSymbol_comp`):

`σ_{m'+m}(R ∘ P)(x, ξ) = σ_{m'}(R)(x, ξ) ∘ σ_m(P)(x, ξ) : E_x → G_x`.

This is the bundle form of the scalar `TauCeti.classicalPrincipalSymbol_comp`. In contrast with the
scalar case, the principal symbols are linear maps between the fibres, which need not commute, so
the order of the factors matters.

## The argument

The principal symbol is read off from the matrix entries `f ↦ χ ℓ(t'' (R (P (f ψ t⁻¹ v))))` of
`R ∘ P` (`TauCeti.sectionClassicalPrincipalSymbol_eq_iff`). Insert a frame of `F` near `x`: for a
trivialization `t'` of `F` at `x`, a cutoff `ρ` supported in its base set and a cutoff `θ` supported
where `ρ = 1`, every section `s` of `F` is

`s = ∑ⱼ θ ρ bⱼ*(t' s) · ρ t'⁻¹ bⱼ + (1 - θ) s`

(`Bundle.Trivialization.smul_eq_sum_smul_cutoffFrameSection_add`). Applied to `s = P (f ψ t⁻¹ v)`,
this writes the entry of `R ∘ P` as the sum over `j` of the compositions of an entry of `R`, the
multiplication by `θ` and an entry of `P`, plus the entry of `R (1 - θ) P`. The scalar composition
theorem computes the principal symbols of the first terms, and their sum over `j` is the matrix
product of the entries of `σ(R)` and `σ(P)`. Near `x`, where a cutoff `θ₀` with `θ = 1` near its
support equals `1`, the last entry agrees with that of `θ₀ R (1 - θ) P`, and `θ₀ R (1 - θ)` has
order `-∞` by pseudolocality
(`TauCeti.smul_comp_smul_mem_sectionSmoothingPseudodifferentialOperators`); so it does not
contribute to the principal symbol at `x`.

## Main results

* `TauCeti.sectionClassicalPrincipalSymbol_smul_left`,
  `TauCeti.sectionClassicalPrincipalSymbol_comp_smul`: multiplying an operator by a smooth function
  `g` on either side multiplies its principal symbol at `x` by `g(x)`.
* `TauCeti.sectionClassicalPrincipalSymbol_comp`: the principal symbol of a composition is the
  composition of the principal symbols.
* `TauCeti.IsSectionClassicalEllipticAt.comp`, `TauCeti.IsSectionClassicalElliptic.comp`: a
  composition of elliptic operators is elliptic.
* `TauCeti.sectionClassicalPrincipalSymbol_comp_eq_id_of_comp_sub_id_mem`: if `Q ∘ P - 1` has
  order `-1`, with orders adding up to `0`, then `σ(Q) ∘ σ(P) = 1` at nonzero covectors.
* `TauCeti.IsSectionClassicalEllipticAt.of_comp_sub_id_mem`: an operator which is invertible
  modulo order `-1`, with an inverse on both sides, is elliptic.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (the principal
  symbol of a composition of pseudodifferential operators between sections of vector bundles).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

noncomputable section

open Bundle Filter Module Set TauCeti
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

/-! ### Multiplication by smooth functions -/

/-- If every entry of `Q` has, at `ξ ∈ T*ₓM`, `c` times the principal symbol of the corresponding
entry of `P`, then `σ_m(Q)(x, ξ) = c σ_m(P)(x, ξ)`. -/
private theorem sectionClassicalPrincipalSymbol_eq_smul_of_forall
    {Q : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hQ : Q ∈ sectionClassicalPseudodifferentialOperators m) {x : M}
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) (c : ℂ)
    (h : ∀ (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
      (ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hψ : tsupport ψ ⊆ t.baseSet) (v : V)
      (t' : Trivialization W (π W F)) [MemTrivializationAtlas t']
      (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hχ : tsupport χ ⊆ t'.baseSet) (ℓ : W →L[ℂ] ℂ),
      classicalPrincipalSymbol m (sectionEntry t ψ hψ v t' χ hχ ℓ Q) x ξ =
        c * classicalPrincipalSymbol m (sectionEntry t ψ hψ v t' χ hχ ℓ P) x ξ) :
    sectionClassicalPrincipalSymbol m Q x ξ = c • sectionClassicalPrincipalSymbol m P x ξ := by
  set t := trivializationAt V E x
  set t' := trivializationAt W F x
  obtain ⟨ρ, hρ, hρx⟩ := ContMDiffMap.exists_tsupport_subset_eventually_eq_one
    (I := 𝓘(ℝ, CoordinateSpace n)) (n := ∞)
    (inter_mem (t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt V E x))
      (t'.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt W F x)))
  have hρ1 : ρ x = 1 := hρx.self_of_nhds
  refine (sectionClassicalPrincipalSymbol_eq_iff hQ t ρ (hρ.trans inter_subset_left) t' ρ
    (hρ.trans inter_subset_right) (by simp [hρ1]) (by simp [hρ1]) ξ _).2 fun v ℓ ↦ ?_
  rw [h, classicalPrincipalSymbol_sectionEntry hP]
  simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
  ring

/-- **Multiplication on the left.** For a complex-valued smooth function `g`, the principal symbol
of `s ↦ g P s` is `σ_m(g P)(x, ξ) = g(x) σ_m(P)(x, ξ)`. -/
theorem sectionClassicalPrincipalSymbol_smul_left
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    sectionClassicalPrincipalSymbol m (g • P) x ξ =
      g x • sectionClassicalPrincipalSymbol m P x ξ := by
  refine sectionClassicalPrincipalSymbol_eq_smul_of_forall hP
    (smul_mem_sectionClassicalPseudodifferentialOperators hP g) ξ (g x)
    fun t _ ψ hψ v t' _ χ hχ ℓ ↦ ?_
  -- The entries of `g P` are those of `P` multiplied by `g` on the left.
  have hentry : sectionEntry t ψ hψ v t' χ hχ ℓ (g • P) =
      LinearMap.mulLeft ℂ g ∘ₗ sectionEntry t ψ hψ v t' χ hχ ℓ P := by
    ext f y
    simp [mul_left_comm]
  rw [hentry, classicalPrincipalSymbol_mulLeft_comp
    ((mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).2 t ψ hψ v t' χ hχ ℓ)]

/-- **Multiplication on the right.** For a complex-valued smooth function `g`, the principal symbol
of `s ↦ P (g s)` is `σ_m(P g)(x, ξ) = g(x) σ_m(P)(x, ξ)`. -/
theorem sectionClassicalPrincipalSymbol_comp_smul
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    sectionClassicalPrincipalSymbol m (P ∘ₗ (g • LinearMap.id)) x ξ =
      g x • sectionClassicalPrincipalSymbol m P x ξ := by
  refine sectionClassicalPrincipalSymbol_eq_smul_of_forall hP
    (comp_smul_mem_sectionClassicalPseudodifferentialOperators hP g) ξ (g x)
    fun t _ ψ hψ v t' _ χ hχ ℓ ↦ ?_
  -- The entries of `P g` are those of `P` composed with the multiplication by `g`.
  have hentry : sectionEntry t ψ hψ v t' χ hχ ℓ (P ∘ₗ (g • LinearMap.id)) =
      sectionEntry t ψ hψ v t' χ hχ ℓ P ∘ₗ LinearMap.mulLeft ℂ g := by
    ext f y
    simp [mul_smul]
  rw [hentry, classicalPrincipalSymbol_comp_mulLeft
    ((mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).2 t ψ hψ v t' χ hχ ℓ), mul_comm]

/-! ### Composition -/

section Composition

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U] [FiniteDimensional ℂ U]
  {G : M → Type*} [TopologicalSpace (TotalSpace U G)] [∀ x, AddCommGroup (G x)]
  [∀ x, Module ℝ (G x)] [∀ x, Module ℂ (G x)] [∀ x, TopologicalSpace (G x)] [FiberBundle U G]
  [VectorBundle ℝ U G] [VectorBundle ℂ U G] [ContMDiffVectorBundle ∞ U G 𝓘(ℝ, CoordinateSpace n)]
  {m' : ℝ}
  {R : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); U, G⟯}

omit [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [FiniteDimensional ℂ V]
  [FiniteDimensional ℂ U] in
/-- **Splitting an entry of a composition along a frame of the middle bundle.** Let `ρ` be a cutoff
supported in the base set of a trivialization `t'` of `F`, and `θ` a cutoff supported where `ρ = 1`.
Then the entry `f ↦ χ ℓ(t'' (R (P (f ψ t⁻¹ v))))` of `R ∘ P` is the sum over a basis `(bⱼ)` of `W`
of the compositions of the entry of `R` with input frame `ρ t'⁻¹ bⱼ`, the multiplication by `θ`
and the entry of `P` with output coordinate `ρ bⱼ*(t' ·)`, plus the entry of `R (1 - θ) P`. -/
private theorem sectionEntry_comp_eq_sum_add
    (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
    (ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hψ : tsupport ψ ⊆ t.baseSet) (v : V)
    (t' : Trivialization W (π W F)) [MemTrivializationAtlas t']
    (ρ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hρ : tsupport ρ ⊆ t'.baseSet)
    (θ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hθ : tsupport θ ⊆ {y | ρ y = 1} ∩ t'.baseSet)
    (t'' : Trivialization U (π U G)) [MemTrivializationAtlas t'']
    (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hχ : tsupport χ ⊆ t''.baseSet) (ℓ : U →L[ℂ] ℂ)
    (P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯)
    (R : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); U, G⟯) :
    sectionEntry t ψ hψ v t'' χ hχ ℓ (R ∘ₗ P) =
      ∑ j, sectionEntry t' ρ hρ (finBasis ℂ W j) t'' χ hχ ℓ R ∘ₗ
          (LinearMap.mulLeft ℂ (ContMDiffMap.ofReal θ) ∘ₗ sectionEntry t ψ hψ v t' ρ hρ
            ((finBasis ℂ W).coord j).toContinuousLinearMap P) +
        sectionEntry t ψ hψ v t'' χ hχ ℓ
          ((R ∘ₗ ((1 - ContMDiffMap.ofReal θ) • LinearMap.id)) ∘ₗ P) := by
  refine LinearMap.ext fun f ↦ ?_
  have hs := t'.smul_eq_sum_smul_cutoffFrameSection_add ρ hρ (finBasis ℂ W) θ hθ
    (P (f • t.cutoffFrameSection ψ hψ v)) 1
  rw [one_smul] at hs
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, sectionEntry_apply_eq_cutoffFrameCoeff, LinearMap.smul_apply,
    LinearMap.id_apply]
  conv_lhs => rw [hs]
  simp only [map_add, map_sum, mul_one]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ U] in
/-- **The part of a composition away from a point.** If the cutoff `θ` equals `1` near `x`, then
every entry of `R (1 - θ) P` has principal symbol `0` of order `m' + m` at `x`: near `x` it agrees
with the corresponding entry of `θ₀ R (1 - θ) P` for a cutoff `θ₀` equal to `1` near `x` with
`θ = 1` near its support, and `θ₀ R (1 - θ)` has order `-∞` by pseudolocality. -/
private theorem classicalPrincipalSymbol_sectionEntry_comp_one_sub_comp_eq_zero
    (hR : R ∈ sectionClassicalPseudodifferentialOperators m')
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
    (ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hψ : tsupport ψ ⊆ t.baseSet) (v : V)
    (t'' : Trivialization U (π U G)) [MemTrivializationAtlas t'']
    (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hχ : tsupport χ ⊆ t''.baseSet) (ℓ : U →L[ℂ] ℂ)
    {θ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯} {x : M} (hθx : ∀ᶠ y in 𝓝 x, θ y = 1)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol (m' + m) (sectionEntry t ψ hψ v t'' χ hχ ℓ
      ((R ∘ₗ ((1 - ContMDiffMap.ofReal θ) • LinearMap.id)) ∘ₗ P)) x ξ = 0 := by
  obtain ⟨θ₀, hθ₀, hθ₀x⟩ := ContMDiffMap.exists_tsupport_subset_eventually_eq_one
    (I := 𝓘(ℝ, CoordinateSpace n)) (n := ∞)
    (isOpen_setOfPred_eventually_nhds.mem_nhds hθx)
  set θc := ContMDiffMap.ofReal θ
  set θ₀c := ContMDiffMap.ofReal θ₀
  have hdisj : Disjoint (tsupport θ₀c) (tsupport ⇑(1 - θc)) := by
    refine disjoint_tsupport_iff_eventuallyEq.2 (eventually_nhdsSet_iff_forall.2 fun y hy ↦ ?_)
    have hsupp : Function.support θ₀c ⊆ Function.support θ₀ := fun z hz h ↦
      Function.mem_support.1 hz (by simp [θ₀c, ContMDiffMap.ofReal_apply, h])
    filter_upwards [hθ₀ (closure_mono hsupp hy)] with z hz
    simp [θc, ContMDiffMap.ofReal_apply, hz]
  set S := (R ∘ₗ ((1 - θc) • LinearMap.id)) ∘ₗ P
  set S' := (θ₀c • (R ∘ₗ ((1 - θc) • LinearMap.id))) ∘ₗ P
  have hS : S ∈ sectionClassicalPseudodifferentialOperators (m' + m) :=
    comp_mem_sectionClassicalPseudodifferentialOperators
      (comp_smul_mem_sectionClassicalPseudodifferentialOperators hR _) hP
  have hS' : S' ∈ sectionClassicalPseudodifferentialOperators (m' + m - 1) := by
    have h := comp_mem_sectionClassicalPseudodifferentialOperators
      (sectionSmoothingPseudodifferentialOperators_le_sectionClassicalPseudodifferentialOperators
        (m' - 1) (smul_comp_smul_mem_sectionSmoothingPseudodifferentialOperators hR hdisj)) hP
    rwa [sub_add_eq_add_sub] at h
  have hloc : ∀ᶠ y in 𝓝 x, ∀ f, sectionEntry t ψ hψ v t'' χ hχ ℓ S f y =
      sectionEntry t ψ hψ v t'' χ hχ ℓ S' f y := by
    filter_upwards [hθ₀x] with y hy f
    simp [S, S', θ₀c, ContMDiffMap.ofReal_apply, hy]
  have hS'e := (mem_sectionClassicalPseudodifferentialOperators_iff.1 hS').2 t ψ hψ v t'' χ hχ ℓ
  rw [classicalPrincipalSymbol_eq_of_eventually_apply_eq
    ((mem_sectionClassicalPseudodifferentialOperators_iff.1 hS).2 t ψ hψ v t'' χ hχ ℓ)
    (classicalPseudodifferentialOperators_le 1 (by norm_num) hS'e) hloc ξ,
    classicalPrincipalSymbol_eq_zero_of_mem_sub_one hS'e]

/-- **The principal symbol of a composition** is the composition of the principal symbols:
`σ_{m'+m}(R ∘ P)(x, ξ) = σ_{m'}(R)(x, ξ) ∘ σ_m(P)(x, ξ)` for classical pseudodifferential
operators `P : Γ(E) → Γ(F)` of order `m` and `R : Γ(F) → Γ(G)` of order `m'`. -/
theorem sectionClassicalPrincipalSymbol_comp
    (hR : R ∈ sectionClassicalPseudodifferentialOperators m')
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    sectionClassicalPrincipalSymbol (m' + m) (R ∘ₗ P) x ξ =
      sectionClassicalPrincipalSymbol m' R x ξ ∘ₗ sectionClassicalPrincipalSymbol m P x ξ := by
  set t := trivializationAt V E x
  set t' := trivializationAt W F x
  set t'' := trivializationAt U G x
  have hxF : x ∈ t'.baseSet := FiberBundle.mem_baseSet_trivializationAt W F x
  -- Cutoffs at `x`: `ψ` and `χ` for the frames of `E` and `G`, `ρ` for the frame of `F`, and `θ`
  -- supported where `ρ = 1`.
  obtain ⟨ψ, hψ, hψx⟩ := ContMDiffMap.exists_tsupport_subset_eventually_eq_one
    (I := 𝓘(ℝ, CoordinateSpace n)) (n := ∞)
    (t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt V E x))
  obtain ⟨χ, hχ, hχx⟩ := ContMDiffMap.exists_tsupport_subset_eventually_eq_one
    (I := 𝓘(ℝ, CoordinateSpace n)) (n := ∞)
    (t''.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt U G x))
  obtain ⟨ρ, hρ, hρx⟩ := ContMDiffMap.exists_tsupport_subset_eventually_eq_one
    (I := 𝓘(ℝ, CoordinateSpace n)) (n := ∞) (t'.open_baseSet.mem_nhds hxF)
  obtain ⟨θ, hθ, hθx⟩ := ContMDiffMap.exists_tsupport_subset_eventually_eq_one
    (I := 𝓘(ℝ, CoordinateSpace n)) (n := ∞)
    (inter_mem hρx (t'.open_baseSet.mem_nhds hxF))
  set b := finBasis ℂ W
  refine (sectionClassicalPrincipalSymbol_eq_iff
    (comp_mem_sectionClassicalPseudodifferentialOperators hR hP) t ψ hψ t'' χ hχ
    (by simp [hψx.self_of_nhds]) (by simp [hχx.self_of_nhds]) ξ _).2 fun v ℓ ↦ ?_
  have hRj (j : Fin (finrank ℂ W)) :=
    (mem_sectionClassicalPseudodifferentialOperators_iff.1 hR).2 t' ρ hρ (b j) t'' χ hχ ℓ
  have hPj (j : Fin (finrank ℂ W)) := (mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).2
    t ψ hψ v t' ρ hρ (b.coord j).toContinuousLinearMap
  have hθPj (j : Fin (finrank ℂ W)) :=
    mulLeft_comp_mem_classicalPseudodifferentialOperators (hPj j) (ContMDiffMap.ofReal θ)
  -- Split the entry of `R ∘ P` along the frame of `F`; the remainder `R (1 - θ) P` does not
  -- contribute, and the scalar composition theorem computes the other terms.
  rw [sectionEntry_comp_eq_sum_add t ψ hψ v t' ρ hρ θ hθ t'' χ hχ ℓ P R,
    classicalPrincipalSymbol_add
      (Submodule.sum_mem _ fun j _ ↦ comp_mem_classicalPseudodifferentialOperators (hRj j)
        (hθPj j))
      ((mem_sectionClassicalPseudodifferentialOperators_iff.1
        (comp_mem_sectionClassicalPseudodifferentialOperators
          (comp_smul_mem_sectionClassicalPseudodifferentialOperators hR _) hP)).2
        t ψ hψ v t'' χ hχ ℓ),
    classicalPrincipalSymbol_sectionEntry_comp_one_sub_comp_eq_zero hR hP t ψ hψ v t'' χ hχ ℓ hθx,
    add_zero,
    classicalPrincipalSymbol_sum _ fun j _ ↦ comp_mem_classicalPseudodifferentialOperators (hRj j)
      (hθPj j)]
  simp_rw [classicalPrincipalSymbol_comp (hRj _) (hθPj _),
    classicalPrincipalSymbol_mulLeft_comp (hPj _), classicalPrincipalSymbol_sectionEntry hR,
    classicalPrincipalSymbol_sectionEntry hP]
  -- Expand `σ(P) (t⁻¹ v)` in the frame `t'⁻¹ bⱼ` of `F` at `x`.
  rw [LinearMap.comp_apply]
  conv_rhs => rw [← t'.sum_repr_smul_symmL b hxF
    (sectionClassicalPrincipalSymbol m P x ξ (t.symm x v))]
  simp only [map_sum, map_smul, Finset.mul_sum, smul_eq_mul, ContMDiffMap.ofReal_apply,
    hρx.self_of_nhds, hθx.self_of_nhds, t'.symmL_apply (R := ℂ) hxF, Basis.coord_apply,
    LinearMap.coe_toContinuousLinearMap']
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  push_cast
  ring

/-! ### Ellipticity -/

/-- **Compositions of elliptic operators are elliptic.** If `P : Γ(E) → Γ(F)` of order `m` and
`R : Γ(F) → Γ(G)` of order `m'` are elliptic at `x`, then so is `R ∘ P`, of order `m' + m`. -/
theorem IsSectionClassicalEllipticAt.comp
    (hR : R ∈ sectionClassicalPseudodifferentialOperators m')
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) {x : M}
    (hRx : IsSectionClassicalEllipticAt m' R x) (hPx : IsSectionClassicalEllipticAt m P x) :
    IsSectionClassicalEllipticAt (m' + m) (R ∘ₗ P) x :=
  isSectionClassicalEllipticAt_iff.2 fun ξ hξ ↦ by
    rw [sectionClassicalPrincipalSymbol_comp hR hP, LinearMap.coe_comp]
    exact (isSectionClassicalEllipticAt_iff.1 hRx ξ hξ).comp
      (isSectionClassicalEllipticAt_iff.1 hPx ξ hξ)

/-- **Compositions of elliptic operators are elliptic.** -/
theorem IsSectionClassicalElliptic.comp
    (hR : R ∈ sectionClassicalPseudodifferentialOperators m')
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hRe : IsSectionClassicalElliptic m' R) (hPe : IsSectionClassicalElliptic m P) :
    IsSectionClassicalElliptic (m' + m) (R ∘ₗ P) :=
  isSectionClassicalElliptic_iff.2 fun x ↦
    (isSectionClassicalElliptic_iff.1 hRe x).comp hR hP (isSectionClassicalElliptic_iff.1 hPe x)

end Composition

/-! ### Inverses modulo lower order -/

section Inverse

variable {m' : ℝ}
  {Q : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯}

/-- **Left inverses modulo lower order.** Let `P : Γ(E) → Γ(F)` have order `m` and
`Q : Γ(F) → Γ(E)` order `m'`, with `m' + m = 0`. If `Q ∘ P - 1` has order `-1`, then
`σ_{m'}(Q)(x, ξ) ∘ σ_m(P)(x, ξ)` is the identity of `E_x` at every nonzero covector `ξ`. -/
theorem sectionClassicalPrincipalSymbol_comp_eq_id_of_comp_sub_id_mem
    (hQ : Q ∈ sectionClassicalPseudodifferentialOperators m')
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) (hm : m' + m = 0)
    (h : Q ∘ₗ P - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-1)) (x : M)
    {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    sectionClassicalPrincipalSymbol m' Q x ξ ∘ₗ sectionClassicalPrincipalSymbol m P x ξ =
      LinearMap.id := by
  have hQP : Q ∘ₗ P = LinearMap.id + (Q ∘ₗ P - LinearMap.id) := by abel
  rw [← sectionClassicalPrincipalSymbol_comp hQ hP, hm, hQP,
    sectionClassicalPrincipalSymbol_add_of_mem_sub_one (by rwa [zero_sub]),
    sectionClassicalPrincipalSymbol_id x hξ]

/-- **Operators invertible modulo lower order are elliptic.** Let `P : Γ(E) → Γ(F)` have order `m`
and `Q : Γ(F) → Γ(E)` order `m'`, with `m' + m = 0`. If `Q ∘ P - 1` and `P ∘ Q - 1` have
order `-1`, then `P` is elliptic of order `m` at every point. -/
theorem IsSectionClassicalEllipticAt.of_comp_sub_id_mem
    (hQ : Q ∈ sectionClassicalPseudodifferentialOperators m')
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) (hm : m' + m = 0)
    (hQP : Q ∘ₗ P - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-1))
    (hPQ : P ∘ₗ Q - LinearMap.id ∈ sectionClassicalPseudodifferentialOperators (-1)) (x : M) :
    IsSectionClassicalEllipticAt m P x := isSectionClassicalEllipticAt_iff.2 fun ξ hξ ↦ by
  have hl := sectionClassicalPrincipalSymbol_comp_eq_id_of_comp_sub_id_mem hQ hP hm hQP x hξ
  have hr := sectionClassicalPrincipalSymbol_comp_eq_id_of_comp_sub_id_mem hP hQ
    (by rw [add_comm, hm]) hPQ x hξ
  exact ⟨Function.LeftInverse.injective fun u ↦ LinearMap.congr_fun hl u,
    Function.RightInverse.surjective fun u ↦ LinearMap.congr_fun hr u⟩

end Inverse

end TauCeti
