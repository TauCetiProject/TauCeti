/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.SymbolQuantization
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.PrincipalSymbol
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact

/-!
# Quantization of principal symbols between vector bundles

Let `M` be a manifold modelled on `ℝⁿ` and `E`, `F` smooth complex vector bundles over `M` with
finite-dimensional model fibres `V` and `W`. The principal symbol `σ_m(P)` of a classical
pseudodifferential operator `P : Γ(E) → Γ(F)` of order `m`
(`TauCeti.sectionClassicalPrincipalSymbol`) assigns a linear map `E_x → F_x` to every covector
`ξ ∈ T*ₓM`. This file identifies the space of such principal symbols and shows that, on a compact
manifold, the principal symbol map completes the **principal symbol exact sequence**

`0 → Ψ^{m-1}(E, F) → Ψ^m(E, F) → S^m_hom(T*M \ 0; Hom(E, F)) → 0`.

The target is the space of **smooth positively homogeneous `Hom(E, F)`-valued symbols of degree
`m`** (`TauCeti.sectionHomogeneousCotangentSymbols`): the families `s(x, ξ) : E_x → F_x` whose
readings

`(x, ξ) ↦ χ(x) ψ(x) ℓ(t'ₓ (s(x, ξ) (t⁻¹ₓ v)))`

in all trivializations `t` of `E` and `t'` of `F`, for cutoffs `ψ` and `χ` supported in their base
sets, vectors `v ∈ V` and functionals `ℓ` on `W`, are smooth positively homogeneous functions of
degree `m` on the cotangent bundle (`TauCeti.homogeneousCotangentSymbols`). The principal symbol
of every operator is such a symbol, since by the transformation law
`TauCeti.classicalPrincipalSymbol_sectionEntry` its readings are the principal symbols of the
matrix entries of the operator
(`TauCeti.sectionClassicalPrincipalSymbol_mem_sectionHomogeneousCotangentSymbols`). This gives the
principal symbol map `TauCeti.sectionClassicalPrincipalSymbolLinearMap`, whose kernel is the
operators of order `m - 1` (`TauCeti.ker_sectionClassicalPrincipalSymbolLinearMap`).

Conversely every such symbol vanishing over the complement of a compact set is a principal symbol
(`exists_mem_sectionClassicalPseudodifferentialOperators_sectionClassicalPrincipalSymbol_eq`),
so the principal symbol map is surjective on a compact manifold
(`TauCeti.sectionClassicalPrincipalSymbolLinearMap_surjective`). The operator is assembled from
scalar operators tensored with cut-off frames. For a scalar classical pseudodifferential operator
`A` of order `m`, a cut-off frame coefficient `ρ ℓ(t s)` of the sections `s` of `E` and a smooth
section `σ` of `F`, the operator `s ↦ A (ρ ℓ(t s)) σ` has the rank-one principal symbol

`σ_m(x, ξ) u = σ_m(A)(x, ξ) ρ(x) ℓ(tₓ u) σ(x)`

(`TauCeti.sectionClassicalPrincipalSymbol_toSpanSingleton_comp_comp_cutoffFrameCoeff`). Take a
finite partition of unity `ρᵢ` on the compact set, subordinate to the common base sets of
trivializations `tᵢ` of `E` and `t'ᵢ` of `F`, cutoffs `θᵢ` equal to `1` near the supports of the
`ρᵢ`, and bases `(bₖ)` of `V` and `(cⱼ)` of `W`. The scalar readings
`ρᵢ(x) cⱼ*(t'ᵢ (s(x, ξ) (tᵢ⁻¹ bₖ)))` of `s` are the principal symbols of scalar operators `Aᵢⱼₖ`
(`TauCeti.exists_mem_classicalPseudodifferentialOperators_classicalPrincipalSymbol_eq`), and

`P s = ∑ᵢ ∑ⱼ ∑ₖ Aᵢⱼₖ (θᵢ bₖ*(tᵢ s)) θᵢ t'ᵢ⁻¹ cⱼ`

has principal symbol `∑ᵢ ρᵢ(x) s(x, ξ) = s(x, ξ)`: in the frames `tᵢ` and `t'ᵢ` the matrix
entries of `s(x, ξ)` reassemble the linear map.

The quantization of principal symbols is how parametrices of elliptic operators between bundles
start: the inverse of the principal symbol is quantized, and the error is then removed by a
Neumann series.

## Main definitions

* `TauCeti.sectionHomogeneousCotangentSymbols n V E W F m`: the smooth positively homogeneous
  `Hom(E, F)`-valued symbols of degree `m` on the cotangent bundle.
* `TauCeti.sectionClassicalPrincipalSymbolLinearMap n V E W F m`: the principal symbol map
  `Ψ^m(E, F) → S^m_hom(T*M \ 0; Hom(E, F))`.

## Main results

* `TauCeti.sectionClassicalPrincipalSymbol_mem_sectionHomogeneousCotangentSymbols`: principal
  symbols are smooth homogeneous symbols.
* `TauCeti.ker_sectionClassicalPrincipalSymbolLinearMap`: the kernel of the principal symbol map
  is the operators of order `m - 1`.
* `TauCeti.sectionClassicalPrincipalSymbol_toSpanSingleton_comp_comp_cutoffFrameCoeff`: the
  principal symbol of a scalar operator tensored with cut-off frames.
* `exists_mem_sectionClassicalPseudodifferentialOperators_sectionClassicalPrincipalSymbol_eq`:
  every smooth homogeneous symbol vanishing over the complement of a compact set is the principal
  symbol of a classical pseudodifferential operator between the bundles.
* `TauCeti.sectionClassicalPrincipalSymbolLinearMap_surjective`: on a compact manifold the
  principal symbol map is surjective.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, Theorem 18.1.17
  and the discussion after Definition 18.1.20.
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3, Proposition 5.2.
-/

public section

noncomputable section

open Bundle Module Set TauCeti
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle V E] [VectorBundle ℂ V E]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F] [VectorBundle ℂ W F]
  {m : ℝ}

/-! ### Smooth homogeneous symbols with values in `Hom(E, F)` -/

variable (n V E W F m) in
/-- The **smooth positively homogeneous `Hom(E, F)`-valued symbols of degree `m`** on the
cotangent bundle, where the principal symbols of the classical pseudodifferential operators of
order `m` from `Γ(E)` to `Γ(F)` live: the families of linear maps `s(x, ξ) : E_x → F_x`, for
`x ∈ M` and `ξ ∈ T*ₓM`, whose readings `χ(x) ψ(x) ℓ(t'ₓ (s(x, ξ) (t⁻¹ₓ v)))` in all trivializations
`t` of `E` and `t'` of `F` in their atlases, for real smooth functions `ψ`, `χ` supported in their
base sets, `v ∈ V` and complex-linear `ℓ : W → ℂ`, lie in `TauCeti.homogeneousCotangentSymbols`. -/
def sectionHomogeneousCotangentSymbols :
    Submodule ℂ ((x : M) → (TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) → E x →ₗ[ℂ] F x) where
  carrier := {s | ∀ (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
    (ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (_ : tsupport ψ ⊆ t.baseSet) (v : V)
    (t' : Trivialization W (π W F)) [MemTrivializationAtlas t']
    (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (_ : tsupport χ ⊆ t'.baseSet) (ℓ : W →L[ℂ] ℂ),
      (fun x ξ ↦ ((χ x * ψ x : ℝ) : ℂ) * ℓ (t'.continuousLinearMapAt ℂ x (s x ξ (t.symm x v)))) ∈
        homogeneousCotangentSymbols n M m}
  zero_mem' _ _ _ _ _ _ _ _ _ _ := by
    convert zero_mem (homogeneousCotangentSymbols n M m) using 1
    ext x ξ
    simp
  add_mem' {s s'} hs hs' t _ ψ hψ v t' _ χ hχ ℓ := by
    convert add_mem (hs t ψ hψ v t' χ hχ ℓ) (hs' t ψ hψ v t' χ hχ ℓ) using 1
    ext x ξ
    simp [mul_add]
  smul_mem' c s hs t _ ψ hψ v t' _ χ hχ ℓ := by
    convert Submodule.smul_mem _ c (hs t ψ hψ v t' χ hχ ℓ) using 1
    ext x ξ
    simp [mul_left_comm]

omit [NormedSpace ℂ V] [VectorBundle ℂ V E] in
theorem mem_sectionHomogeneousCotangentSymbols_iff
    {s : (x : M) → (TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) → E x →ₗ[ℂ] F x} :
    s ∈ sectionHomogeneousCotangentSymbols n V E W F m ↔
      ∀ (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
        (ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (_ : tsupport ψ ⊆ t.baseSet) (v : V)
        (t' : Trivialization W (π W F)) [MemTrivializationAtlas t']
        (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (_ : tsupport χ ⊆ t'.baseSet) (ℓ : W →L[ℂ] ℂ),
        (fun x ξ ↦ ((χ x * ψ x : ℝ) : ℂ) *
          ℓ (t'.continuousLinearMapAt ℂ x (s x ξ (t.symm x v)))) ∈
            homogeneousCotangentSymbols n M m :=
  Iff.rfl

variable [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  [FiniteDimensional ℂ V] [∀ x, Module ℝ (E x)] [VectorBundle ℝ V E]
  [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  [FiniteDimensional ℂ W] [∀ x, Module ℝ (F x)] [VectorBundle ℝ W F]
  [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}

/-- **Principal symbols are smooth homogeneous symbols.** The principal symbol of order `m` of an
operator `P : Γ(E) → Γ(F)` is a smooth positively homogeneous `Hom(E, F)`-valued symbol of degree
`m`: its readings in frames are the principal symbols of the matrix entries of `P`. -/
theorem sectionClassicalPrincipalSymbol_mem_sectionHomogeneousCotangentSymbols :
    sectionClassicalPrincipalSymbol m P ∈ sectionHomogeneousCotangentSymbols n V E W F m := by
  by_cases hP : P ∈ sectionClassicalPseudodifferentialOperators m
  · intro t _ ψ hψ v t' _ χ hχ ℓ
    convert classicalPrincipalSymbol_mem_homogeneousCotangentSymbols
      (P := sectionEntry t ψ hψ v t' χ hχ ℓ P) using 1
    ext x ξ
    exact (classicalPrincipalSymbol_sectionEntry hP t ψ hψ v t' χ hχ ℓ x ξ).symm
  · have h0 : sectionClassicalPrincipalSymbol m P = 0 :=
      funext fun x ↦ funext fun ξ ↦ sectionClassicalPrincipalSymbol_of_notMem hP x ξ
    rw [h0]
    exact zero_mem _

/-! ### The principal symbol map -/

variable (n V E W F m) in
/-- **The principal symbol map** `σ_m` from the classical pseudodifferential operators of order
`m` from `Γ(E)` to `Γ(F)` to the smooth positively homogeneous `Hom(E, F)`-valued symbols of
degree `m`. Its kernel is the operators of order `m - 1`
(`TauCeti.ker_sectionClassicalPrincipalSymbolLinearMap`). -/
def sectionClassicalPrincipalSymbolLinearMap :
    sectionClassicalPseudodifferentialOperators (n := n) (V := V) (E := E) (W := W) (F := F) m
      →ₗ[ℂ] sectionHomogeneousCotangentSymbols n V E W F m where
  toFun P := ⟨sectionClassicalPrincipalSymbol (V := V) (W := W) m P,
    sectionClassicalPrincipalSymbol_mem_sectionHomogeneousCotangentSymbols⟩
  map_add' P Q := Subtype.ext <| funext fun x ↦ funext fun ξ ↦
    sectionClassicalPrincipalSymbol_add P.property Q.property x ξ
  map_smul' c P := Subtype.ext <| funext fun x ↦ funext fun ξ ↦
    sectionClassicalPrincipalSymbol_smul P.property c x ξ

@[simp]
theorem coe_sectionClassicalPrincipalSymbolLinearMap_apply
    (P : sectionClassicalPseudodifferentialOperators (n := n) (V := V) (E := E) (W := W) (F := F)
      m) :
    (sectionClassicalPrincipalSymbolLinearMap n V E W F m P :
      (x : M) → (TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) → E x →ₗ[ℂ] F x) =
      sectionClassicalPrincipalSymbol (V := V) (W := W) m P :=
  (rfl)

variable (n V E W F m) in
/-- **The kernel of the principal symbol map** is the classical pseudodifferential operators of
order `m - 1`. -/
theorem ker_sectionClassicalPrincipalSymbolLinearMap :
    LinearMap.ker (sectionClassicalPrincipalSymbolLinearMap n V E W F m) =
      (sectionClassicalPseudodifferentialOperators (m - 1)).comap
        (sectionClassicalPseudodifferentialOperators m).subtype := by
  ext P
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
    ← sectionClassicalPrincipalSymbol_eq_zero_iff P.property, ← Submodule.coe_eq_zero,
    coe_sectionClassicalPrincipalSymbolLinearMap_apply]
  simp only [funext_iff, Pi.zero_apply]

/-! ### Scalar operators tensored with cut-off frames -/

/-- **The principal symbol of a scalar operator tensored with cut-off frames.** Let `A` be a
classical pseudodifferential operator of order `m` on the complex-valued smooth functions on `M`,
`ρ ℓ(t s)` a cut-off frame coefficient of the sections `s` of `E` and `σ` a smooth section of `F`.
The principal symbol of `s ↦ A (ρ ℓ(t s)) σ` at `ξ ∈ T*ₓM` is the rank-one map
`u ↦ σ_m(A)(x, ξ) ρ(x) ℓ(tₓ u) σ(x)`. -/
theorem sectionClassicalPrincipalSymbol_toSpanSingleton_comp_comp_cutoffFrameCoeff
    {A : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hA : A ∈ classicalPseudodifferentialOperators m)
    (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
    (ρ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hρ : tsupport ρ ⊆ t.baseSet) (ℓ : V →L[ℂ] ℂ)
    (σ : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) (u : E x) :
    sectionClassicalPrincipalSymbol m
        ((LinearMap.toSpanSingleton _ _ σ).restrictScalars ℂ ∘ₗ A ∘ₗ t.cutoffFrameCoeff ρ hρ ℓ)
        x ξ u =
      (classicalPrincipalSymbol m A x ξ * ((ρ x : ℂ) * ℓ (t.continuousLinearMapAt ℂ x u))) •
        σ x := by
  have hP :=
    toSpanSingleton_comp_comp_cutoffFrameCoeff_mem_sectionClassicalPseudodifferentialOperators
      hA t ρ hρ ℓ σ
  -- Read the principal symbol in the preferred frames at `x`, through cutoffs equal to `1` at `x`.
  set t₀ := trivializationAt V E x
  set t₀' := trivializationAt W F x
  obtain ⟨ψ₀, hψ₀, hψ₁, -, hψ, -⟩ :=
    isCompact_singleton.exists_contMDiff_one_nhds_tsupport_subset 𝓘(ℝ, CoordinateSpace n)
      t₀.open_baseSet (singleton_subset_iff.2 (FiberBundle.mem_baseSet_trivializationAt V E x))
  obtain ⟨χ₀, hχ₀, hχ₁, -, hχ, -⟩ :=
    isCompact_singleton.exists_contMDiff_one_nhds_tsupport_subset 𝓘(ℝ, CoordinateSpace n)
      t₀'.open_baseSet (singleton_subset_iff.2 (FiberBundle.mem_baseSet_trivializationAt W F x))
  set ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ := ⟨ψ₀, hψ₀⟩
  set χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ := ⟨χ₀, hχ₀⟩
  have hψx : ψ x = 1 := hψ₁.self_of_nhdsSet x rfl
  have hχx : χ x = 1 := hχ₁.self_of_nhdsSet x rfl
  -- The candidate rank-one map.
  set B : E x →ₗ[ℂ] F x := LinearMap.toSpanSingleton ℂ (F x) (σ x) ∘ₗ
    ((classicalPrincipalSymbol m A x ξ * ρ x) • (ℓ ∘L t.continuousLinearMapAt ℂ x).toLinearMap)
  suffices h : sectionClassicalPrincipalSymbol m
      ((LinearMap.toSpanSingleton _ _ σ).restrictScalars ℂ ∘ₗ A ∘ₗ t.cutoffFrameCoeff ρ hρ ℓ)
      x ξ = B by
    rw [h]
    simp [B, mul_assoc]
  refine (sectionClassicalPrincipalSymbol_eq_iff hP t₀ ψ hψ t₀' χ hχ (by simp [hψx])
    (by simp [hχx]) ξ B).2 fun v ℓ' ↦ ?_
  -- The matrix entry is `A` multiplied on both sides by smooth functions.
  rw [sectionEntry_toSpanSingleton_comp_comp_cutoffFrameCoeff, classicalPrincipalSymbol_mulLeft_comp
      (comp_mulLeft_mem_classicalPseudodifferentialOperators hA _),
    classicalPrincipalSymbol_comp_mulLeft hA]
  simp only [B, Bundle.Trivialization.cutoffFrameCoeff_apply,
    Bundle.Trivialization.cutoffFrameSection_apply, hψx, hχx, one_smul, mul_one,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp, LinearMap.toSpanSingleton_apply,
    map_smul, smul_eq_mul, Complex.real_smul, Complex.ofReal_one, one_mul]
  ring

/-! ### Quantization of principal symbols -/

/-- **Quantization over a common base set.** Let `t` and `t'` be trivializations of `E` and `F` in
their atlases and `ρ` a real smooth function whose support is compact and contained in both base
sets. For a smooth positively homogeneous `Hom(E, F)`-valued symbol `s` of degree `m`, the symbol
`ρ s` is the principal symbol of the operator `s ↦ ∑ⱼ ∑ₖ Aⱼₖ (θ bₖ*(t s)) θ t'⁻¹ cⱼ` built from
scalar operators `Aⱼₖ` quantizing the readings `ρ(x) cⱼ*(t'ₓ (s(x, ξ) (t⁻¹ₓ bₖ)))` of `s`, for bases
`(bₖ)` of `V` and `(cⱼ)` of `W` and a cutoff `θ` equal to `1` near the support of `ρ`. -/
private theorem exists_mem_sectionClassicalPseudodifferentialOperators_eq_smul
    {s : (x : M) → (TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) → E x →ₗ[ℂ] F x}
    (hs : s ∈ sectionHomogeneousCotangentSymbols n V E W F m) (t : Trivialization V (π V E))
    [MemTrivializationAtlas t] (t' : Trivialization W (π W F)) [MemTrivializationAtlas t']
    (ρ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hρc : IsCompact (tsupport ρ))
    (hρ : tsupport ρ ⊆ t.baseSet ∩ t'.baseSet) :
    ∃ P ∈ sectionClassicalPseudodifferentialOperators (V := V) (W := W) m,
      ∀ x ξ, sectionClassicalPrincipalSymbol m P x ξ = (ρ x : ℂ) • s x ξ := by
  obtain ⟨θ₀, hθ₀, hθ₁, -, hθt, -⟩ := hρc.exists_contMDiff_one_nhds_tsupport_subset
    𝓘(ℝ, CoordinateSpace n) (t.open_baseSet.inter t'.open_baseSet) hρ
  set θ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ := ⟨θ₀, hθ₀⟩
  have hθE : tsupport θ ⊆ t.baseSet := hθt.trans inter_subset_left
  have hθF : tsupport θ ⊆ t'.baseSet := hθt.trans inter_subset_right
  -- The scalar readings `ρ θ cⱼ*(t' (s (t⁻¹ bₖ)))` of `s` are principal symbols of scalar
  -- operators `Aⱼₖ`.
  choose A hA hAs using fun (j : Fin (finrank ℂ W)) (k : Fin (finrank ℂ V)) ↦
    exists_mem_classicalPseudodifferentialOperators_classicalPrincipalSymbol_eq
      (hs t θ hθE (finBasis ℂ V k) t' ρ (hρ.trans inter_subset_right)
        ((finBasis ℂ W).coord j).toContinuousLinearMap) hρc
      fun x hx ↦ funext fun ξ ↦ by simp [image_eq_zero_of_notMem_tsupport hx]
  set Q := fun (j : Fin (finrank ℂ W)) (k : Fin (finrank ℂ V)) ↦
    (LinearMap.toSpanSingleton _ _ (t'.cutoffFrameSection θ hθF (finBasis ℂ W j))).restrictScalars
      ℂ ∘ₗ A j k ∘ₗ t.cutoffFrameCoeff θ hθE ((finBasis ℂ V).coord k).toContinuousLinearMap
  have hQ (j : Fin (finrank ℂ W)) (k : Fin (finrank ℂ V)) :
      Q j k ∈ sectionClassicalPseudodifferentialOperators m :=
    toSpanSingleton_comp_comp_cutoffFrameCoeff_mem_sectionClassicalPseudodifferentialOperators
      (hA j k) _ _ _ _ _
  have hQs (j : Fin (finrank ℂ W)) : ∑ k, Q j k ∈ sectionClassicalPseudodifferentialOperators m :=
    Submodule.sum_mem _ fun k _ ↦ hQ j k
  refine ⟨∑ j, ∑ k, Q j k, Submodule.sum_mem _ fun j _ ↦ hQs j, fun x ξ ↦ LinearMap.ext fun u ↦ ?_⟩
  have hsum (j : Fin (finrank ℂ W)) :=
    sectionClassicalPrincipalSymbol_sum Finset.univ (fun k _ ↦ hQ j k) x ξ
  have hQ' (j : Fin (finrank ℂ W)) (k : Fin (finrank ℂ V)) :
      sectionClassicalPrincipalSymbol m (Q j k) x ξ u =
        (classicalPrincipalSymbol m (A j k) x ξ *
          ((θ x : ℂ) * (finBasis ℂ V).coord k (t.continuousLinearMapAt ℂ x u))) •
          t'.cutoffFrameSection θ hθF (finBasis ℂ W j) x :=
    sectionClassicalPrincipalSymbol_toSpanSingleton_comp_comp_cutoffFrameCoeff (hA j k) _ _ _ _ _
      x ξ u
  rw [sectionClassicalPrincipalSymbol_sum _ fun j _ ↦ hQs j, LinearMap.sum_apply]
  simp only [hsum, LinearMap.sum_apply, hQ', hAs, Bundle.Trivialization.cutoffFrameSection_apply,
    LinearMap.smul_apply]
  by_cases hx : ρ x = 0
  · simp [hx]
  -- At a point of the support of `ρ`, `θ = 1` and the matrix entries reassemble `s(x, ξ)`.
  obtain ⟨hxE, hxF⟩ := hρ (subset_tsupport _ hx)
  have hθx : θ x = 1 := hθ₁.self_of_nhdsSet x (subset_tsupport _ hx)
  rw [hθx, ← t.sum_sum_coord_smul_symm t' (finBasis ℂ V) (finBasis ℂ W) hxE hxF (s x ξ) u,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [one_smul, smul_smul]
  congr 1
  simp only [LinearMap.coe_toContinuousLinearMap', Complex.ofReal_one, mul_one]
  ring

/-- **Quantization of principal symbols between bundles.** Every smooth positively homogeneous
`Hom(E, F)`-valued symbol `s` of degree `m` on the cotangent bundle of `M` that vanishes over the
complement of a compact set is the principal symbol of a classical pseudodifferential operator of
order `m` from `Γ(E)` to `Γ(F)`. -/
theorem exists_mem_sectionClassicalPseudodifferentialOperators_sectionClassicalPrincipalSymbol_eq
    {s : (x : M) → (TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) → E x →ₗ[ℂ] F x}
    (hs : s ∈ sectionHomogeneousCotangentSymbols n V E W F m) {K : Set M} (hK : IsCompact K)
    (hsK : ∀ x ∉ K, s x = 0) :
    ∃ P ∈ sectionClassicalPseudodifferentialOperators (V := V) (W := W) m,
      sectionClassicalPrincipalSymbol m P = s := by
  -- A finite partition of unity `ρᵢ` on `K` subordinate to the common base sets of the
  -- trivializations of `E` and `F` at points `cᵢ`; each `ρᵢ s` is a principal symbol.
  obtain ⟨ι, _, f, hf⟩ := hK.exists_smoothBumpCovering_isSubordinate 𝓘(ℝ, CoordinateSpace n)
    (U := fun x ↦ (trivializationAt V E x).baseSet ∩ (trivializationAt W F x).baseSet)
    fun x _ ↦ Filter.inter_mem ((trivializationAt V E x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt V E x))
      ((trivializationAt W F x).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt W F x))
  set ρ := f.toSmoothPartitionOfUnity
  choose P hP hPs using fun i ↦ exists_mem_sectionClassicalPseudodifferentialOperators_eq_smul hs
    (trivializationAt V E (f.c i)) (trivializationAt W F (f.c i)) (ρ i)
    ((f i).hasCompactSupport.isCompact.of_isClosed_subset (isClosed_tsupport _)
      (closure_mono (f.support_toSmoothPartitionOfUnity_subset i)))
    (hf.toSmoothPartitionOfUnity i)
  refine ⟨∑ i, P i, Submodule.sum_mem _ fun i _ ↦ hP i, ?_⟩
  ext x ξ u
  rw [sectionClassicalPrincipalSymbol_sum _ fun i _ ↦ hP i, LinearMap.sum_apply]
  simp only [hPs, LinearMap.smul_apply]
  rw [← Finset.sum_smul, ← Complex.ofReal_sum]
  by_cases hxK : x ∈ K
  · rw [show ∑ i, ρ i x = 1 by simpa [← finsum_eq_sum_of_fintype] using ρ.sum_eq_one hxK,
      Complex.ofReal_one, one_smul]
  · simp [hsK x hxK]

/-- **The principal symbol map is surjective on a compact manifold**: every smooth positively
homogeneous `Hom(E, F)`-valued symbol of degree `m` on the cotangent bundle is the principal
symbol of a classical pseudodifferential operator of order `m` from `Γ(E)` to `Γ(F)`. With
`TauCeti.ker_sectionClassicalPrincipalSymbolLinearMap`, this is the exactness of
`0 → Ψ^{m-1}(E, F) → Ψ^m(E, F) → S^m_hom(T*M \ 0; Hom(E, F)) → 0`. -/
theorem sectionClassicalPrincipalSymbolLinearMap_surjective [CompactSpace M] :
    Function.Surjective (sectionClassicalPrincipalSymbolLinearMap n V E W F m) := by
  rintro ⟨s, hs⟩
  obtain ⟨P, hP, hPs⟩ :=
    exists_mem_sectionClassicalPseudodifferentialOperators_sectionClassicalPrincipalSymbol_eq hs
      isCompact_univ fun x hx ↦ absurd (mem_univ x) hx
  exact ⟨⟨P, hP⟩, Subtype.ext hPs⟩

end TauCeti
