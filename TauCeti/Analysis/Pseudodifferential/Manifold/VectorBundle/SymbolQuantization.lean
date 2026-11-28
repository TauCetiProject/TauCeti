/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.SymbolQuantization
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.PrincipalSymbol
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Topology.VectorBundle.Trivialization

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

The fibrewise inverse of a smooth homogeneous symbol `s` of degree `m` that is bijective at every
nonzero covector is a smooth homogeneous `Hom(F, E)`-valued symbol of degree `-m`
(`TauCeti.exists_mem_sectionHomogeneousCotangentSymbols_comp_eq_id`), the bundle counterpart of
`TauCeti.inv_mem_homogeneousCotangentSymbols`. Homogeneity of the inverse follows from that of `s`
at points where the cutoffs of a reading do not vanish. For smoothness near a point `x` of the
support of a reading, take a cutoff `φ` equal to `1` near `x` and supported in the common base set
of the trivializations. The readings of `s` through `φ` in bases of `V` and `W` are smooth, and
near `x` they are the entries of the matrix `A(x, ξ) = t'ₓ ∘ s(x, ξ) ∘ tₓ⁻¹ : V → W`. The reading
of the inverse is read off from `A(x, ξ)⁻¹`
(`Bundle.Trivialization.inverse_apply_of_bijective_conj`), and inversion is smooth on the
invertible maps `V → W` (`ContDiffWithinAt.clm_inverse`).

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
* `TauCeti.exists_mem_sectionHomogeneousCotangentSymbols_comp_eq_id`: the fibrewise inverse of a
  smooth homogeneous symbol bijective at nonzero covectors is a smooth homogeneous symbol.
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

/-! ### The inverse of a bijective symbol -/

section Inverse

variable {s : (x : M) → (TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) → E x →ₗ[ℂ] F x}

/-- The fibrewise inverse `s(x, ξ)⁻¹ : F_x → E_x` of a family of linear maps
`s(x, ξ) : E_x → F_x`, at the nonzero covectors where it is bijective, and `0` elsewhere. -/
private def inverseSymbol
    (s : (x : M) → (TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) → E x →ₗ[ℂ] F x) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) : F x →ₗ[ℂ] E x :=
  open Classical in
  if h : ξ ≠ 0 ∧ Function.Bijective (s x ξ) then
    (LinearEquiv.ofBijective _ h.2).symm.toLinearMap
  else 0

omit [∀ x, TopologicalSpace (E x)] [∀ x, TopologicalSpace (F x)] in
private theorem apply_inverseSymbol_apply {x : M}
    {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ} (hξ : ξ ≠ 0)
    (h : Function.Bijective (s x ξ)) (y : F x) : s x ξ (inverseSymbol s x ξ y) = y := by
  simp only [inverseSymbol, hξ, h, ne_eq, not_false_eq_true, and_self, ↓reduceDIte,
    LinearEquiv.coe_coe, LinearEquiv.apply_ofBijective_symm_apply]

omit [∀ x, TopologicalSpace (E x)] [∀ x, TopologicalSpace (F x)] in
private theorem inverseSymbol_apply_apply {x : M}
    {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ} (hξ : ξ ≠ 0)
    (h : Function.Bijective (s x ξ)) (u : E x) : inverseSymbol s x ξ (s x ξ u) = u := by
  simp only [inverseSymbol, hξ, h, ne_eq, not_false_eq_true, and_self, ↓reduceDIte,
    LinearEquiv.coe_coe, LinearEquiv.ofBijective_symm_apply_apply]

omit [∀ x, TopologicalSpace (E x)] [∀ x, TopologicalSpace (F x)] in
/-- Where `s` is positively homogeneous of degree `m` at `ξ`, its fibrewise inverse is positively
homogeneous of degree `-m` at `ξ`. -/
private theorem inverseSymbol_smul_covector {x : M}
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hsc : s x (c • ξ) = ((c ^ m : ℝ) : ℂ) • s x ξ) :
    inverseSymbol s x (c • ξ) = (((c ^ m : ℝ) : ℂ))⁻¹ • inverseSymbol s x ξ := by
  have hcm : ((c ^ m : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hc m).ne'
  by_cases hξ : ξ = 0
  · simp [inverseSymbol, hξ]
  have hcξ : c • ξ ≠ 0 := smul_ne_zero hc.ne' hξ
  by_cases h : Function.Bijective (s x ξ)
  · have h' : Function.Bijective (s x (c • ξ)) := by
      rw [hsc, LinearMap.coe_smul]
      exact (MulAction.bijective (Units.mk0 _ hcm)).comp h
    refine LinearMap.ext fun y ↦ h'.1 ?_
    rw [apply_inverseSymbol_apply hcξ h', LinearMap.smul_apply, map_smul, hsc,
      LinearMap.smul_apply, apply_inverseSymbol_apply hξ h, smul_smul, inv_mul_cancel₀ hcm,
      one_smul]
  · have h' : ¬ Function.Bijective (s x (c • ξ)) := by
      rw [hsc, LinearMap.coe_smul]
      exact fun h' ↦ h ((MulAction.bijective (Units.mk0 _ hcm)).of_comp_iff' _ |>.1 h')
    simp only [inverseSymbol, h, h', and_false, ↓reduceDIte, smul_zero]

variable [FiniteDimensional ℂ W]

/-- **Pointwise homogeneity.** At a point `x` where cutoffs `ψ` and `χ`, supported in the base sets
of trivializations `t` of `E` and `t'` of `F`, do not vanish, a smooth homogeneous symbol `s` of
degree `m` satisfies `s(x, c ξ) = c ^ m s(x, ξ)` for `c > 0`: its readings in `t` and `t'` are. -/
private theorem apply_smul_covector_of_mul_ne_zero
    (hs : s ∈ sectionHomogeneousCotangentSymbols n V E W F m)
    {t : Trivialization V (π V E)} [MemTrivializationAtlas t]
    {ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯} (hψ : tsupport ψ ⊆ t.baseSet)
    {t' : Trivialization W (π W F)} [MemTrivializationAtlas t']
    {χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯} (hχ : tsupport χ ⊆ t'.baseSet) {x : M}
    (hx : χ x * ψ x ≠ 0) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) {c : ℝ}
    (hc : 0 < c) :
    s x (c • ξ) = ((c ^ m : ℝ) : ℂ) • s x ξ := by
  have hxψ : x ∈ t.baseSet := hψ (subset_tsupport _ (right_ne_zero_of_mul hx))
  have hxχ : x ∈ t'.baseSet := hχ (subset_tsupport _ (left_ne_zero_of_mul hx))
  have hx' : ((χ x * ψ x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx
  refine t.linearMap_ext ℂ t' hxψ hxχ fun v ↦ (finBasis ℂ W).ext_elem fun j ↦ ?_
  have h := (mem_homogeneousCotangentSymbols_iff.1 (hs t ψ hψ v t' χ hχ
    ((finBasis ℂ W).coord j).toContinuousLinearMap)).2.1 x ξ c hc
  simp only [LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply] at h
  rw [LinearMap.smul_apply, map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_left_cancel₀ hx' (by rw [h]; ring)

variable [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [FiniteDimensional ℂ V]

omit [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- **The matrix of a symbol in a pair of frames.** Let `s` be a smooth homogeneous symbol that is
bijective at nonzero covectors. In a chart `e` of the maximal atlas, let `φ` be a smooth function
supported in the common base set of trivializations `t'` of `E` and `t` of `F`. There is a smooth
family `A(y, η) : V → W` over `e.target × {η ≠ 0}` which, wherever `φ(x) = 1` with `x = e⁻¹ y` and
`ξ = ⟪η, ·⟫ ∘ de_x`, reads `s(x, ξ)` in these frames; so `A(y, η)` is invertible there and its
inverse reads `s(x, ξ)⁻¹`.

Its entries are the readings of `s` through `φ`, which are smooth since `s` is a smooth homogeneous
symbol. -/
private theorem exists_contDiffOn_frameMatrix
    (hs : s ∈ sectionHomogeneousCotangentSymbols n V E W F m)
    (hb : ∀ x ξ, ξ ≠ 0 → Function.Bijective (s x ξ))
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    {t' : Trivialization V (π V E)} [MemTrivializationAtlas t']
    {t : Trivialization W (π W F)} [MemTrivializationAtlas t]
    {φ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯} (hφU : tsupport φ ⊆ t'.baseSet ∩ t.baseSet) :
    ∃ A : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W,
      ContDiffOn ℝ ∞ A (e.target ×ˢ {η | η ≠ 0}) ∧
      ∀ q ∈ e.target ×ˢ {η | η ≠ 0}, φ (e.symm q.1) = 1 → (A q).IsInvertible ∧ ∀ w,
        (A q).inverse w = t'.continuousLinearMapAt ℂ (e.symm q.1)
          (inverseSymbol s (e.symm q.1) ((innerSL ℝ q.2).comp
            (mvfderiv 𝓘(ℝ, CoordinateSpace n) e (e.symm q.1))) (t.symm (e.symm q.1) w)) := by
  set b := finBasis ℂ V
  set c := finBasis ℂ W
  set G := fun (j : Fin (finrank ℂ W)) (k : Fin (finrank ℂ V))
      (q : CoordinateSpace n × CoordinateSpace n) ↦
    ((φ (e.symm q.1) * φ (e.symm q.1) : ℝ) : ℂ) * (c.coord j).toContinuousLinearMap
      (t.continuousLinearMapAt ℂ (e.symm q.1) (s (e.symm q.1)
        ((innerSL ℝ q.2).comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e (e.symm q.1)))
        (t'.symm (e.symm q.1) (b k))))
  refine ⟨fun q ↦ ∑ j, ∑ k, G j k q • (b.coord k).toContinuousLinearMap.smulRight (c j),
    ContDiffOn.sum fun j _ ↦ ContDiffOn.sum fun k _ ↦ ContDiffOn.smul (f := G j k)
      (((mem_homogeneousCotangentSymbols_iff.1 (mem_sectionHomogeneousCotangentSymbols_iff.1 hs
          t' φ (hφU.trans inter_subset_left) (b k) t φ (hφU.trans inter_subset_right)
          (c.coord j).toContinuousLinearMap)).2.2 e he).congr
        fun q _ ↦ by rw [chartCotangentSymbol_apply]) contDiffOn_const,
    fun q hq hφq ↦ ?_⟩
  have hqU : e.symm q.1 ∈ t'.baseSet ∩ t.baseSet :=
    hφU (subset_tsupport _ (by simp [hφq]))
  have hξ := (innerSL_comp_mvfderiv_eq_zero_iff
    (IsManifold.maximalAtlas_subset_of_le (by simp) he) (e.map_target hq.1)).not.2 hq.2
  have hbq := hb _ _ hξ
  -- Where `φ = 1`, the matrix entries are those of `s` read in the frames.
  have hA : ∀ v, (∑ j, ∑ k, G j k q • (b.coord k).toContinuousLinearMap.smulRight (c j) :
      V →L[ℂ] W) v = t.continuousLinearMapAt ℂ (e.symm q.1) (s (e.symm q.1)
        ((innerSL ℝ q.2).comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e (e.symm q.1)))
        (t'.symm (e.symm q.1) v)) := fun v ↦ by
    rw [← t'.symmL_apply (R := ℂ) hqU.1]
    set L : V →ₗ[ℂ] W := (t.continuousLinearMapAt ℂ (e.symm q.1)).toLinearMap ∘ₗ
      s (e.symm q.1) ((innerSL ℝ q.2).comp
        (mvfderiv 𝓘(ℝ, CoordinateSpace n) e (e.symm q.1))) ∘ₗ
      (t'.symmL ℂ (e.symm q.1)).toLinearMap
    have hL : ((∑ j, ∑ k, G j k q • (b.coord k).toContinuousLinearMap.smulRight (c j) :
        V →L[ℂ] W) : V →ₗ[ℂ] W) = L := b.ext fun k ↦ by
      simp [G, hφq, L, t'.symmL_apply hqU.1, Finsupp.single_apply, c.sum_repr]
    exact congr($hL v)
  exact ⟨t'.isInvertible_of_bijective_conj hqU.1 hqU.2 hbq hA,
    t'.inverse_apply_of_bijective_conj hqU.1 hqU.2 hbq (apply_inverseSymbol_apply hξ hbq) hA⟩

/-- **Smoothness of the inverse reading at a point of the support.** Let `s` be a smooth
homogeneous symbol that is bijective at nonzero covectors. In a chart `e` of the maximal atlas, let
`g` be a smooth function supported in the common base set of trivializations `t'` of `E` and `t`
of `F`. The reading `(y, η) ↦ g(x) ℓ(t'ₓ (s(x, ξ)⁻¹ (tₓ⁻¹ w)))`, with `x = e⁻¹ y` and
`ξ = ⟪η, ·⟫ ∘ de_x`, is smooth near every point of `e.target × {η ≠ 0}` over the support of `g`:
near such a point it is read from the inverse of the matrix of `s`, and inversion is smooth on the
invertible maps `V → W`. -/
private theorem contDiffWithinAt_inverseSymbol_reading
    (hs : s ∈ sectionHomogeneousCotangentSymbols n V E W F m)
    (hb : ∀ x ξ, ξ ≠ 0 → Function.Bijective (s x ξ))
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    {t' : Trivialization V (π V E)} [MemTrivializationAtlas t']
    {t : Trivialization W (π W F)} [MemTrivializationAtlas t]
    {g : M → ℝ} (hg : ContMDiff 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ) ∞ g)
    (hgt : tsupport g ⊆ t'.baseSet ∩ t.baseSet) (w : W) (ℓ : V →L[ℂ] ℂ)
    {p : CoordinateSpace n × CoordinateSpace n} (hp : p ∈ e.target ×ˢ {η | η ≠ 0})
    (hpg : e.symm p.1 ∈ tsupport g) :
    ContDiffWithinAt ℝ ∞ (fun q : CoordinateSpace n × CoordinateSpace n ↦
      (g (e.symm q.1) : ℂ) * ℓ (t'.continuousLinearMapAt ℂ (e.symm q.1)
        (inverseSymbol s (e.symm q.1) ((innerSL ℝ q.2).comp
          (mvfderiv 𝓘(ℝ, CoordinateSpace n) e (e.symm q.1))) (t.symm (e.symm q.1) w))))
      (e.target ×ˢ {η | η ≠ 0}) p := by
  -- A cutoff `φ` equal to `1` near `e⁻¹ p.1`, and the matrix `A` of `s` read through it.
  obtain ⟨φ, hφU, hφ1⟩ := ContMDiffMap.exists_tsupport_subset_eventually_eq_one
    (I := 𝓘(ℝ, CoordinateSpace n)) (n := ∞)
    ((t'.open_baseSet.inter t.open_baseSet).mem_nhds (hgt hpg))
  obtain ⟨A, hA, hAinv⟩ := exists_contDiffOn_frameMatrix hs hb he hφU
  have hev : ∀ᶠ q in 𝓝 p, φ (e.symm q.1) = 1 :=
    Filter.Tendsto.eventually ((e.continuousAt_symm hp.1).comp continuousAt_fst) hφ1
  -- So the reading agrees near `p` with `g(x) ℓ(A⁻¹ w)`, which is smooth at `p`.
  have hge : ContDiffOn ℝ ∞ (g ∘ e.symm) e.target :=
    contMDiffOn_iff_contDiffOn.1 (hg.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he))
  have hinv := (hA p hp).clm_inverse (hAinv p hp hev.self_of_nhds).1
  refine ((Complex.ofRealCLM.contDiff.contDiffAt.comp_contDiffWithinAt p
      ((hge.comp contDiffOn_fst mapsTo_fst_prod) p hp)).mul
    (((ℓ.comp (ContinuousLinearMap.apply ℂ V w)).restrictScalars ℝ).contDiff.contDiffAt
      |>.comp_contDiffWithinAt p hinv)).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hev]
      with q hq hqφ
    simp [(hAinv q hq hqφ).2 w]
  · simp [(hAinv p hp hev.self_of_nhds).2 w]

/-- **The inverse of a bijective symbol is a smooth homogeneous symbol.** -/
private theorem inverseSymbol_mem_sectionHomogeneousCotangentSymbols
    (hs : s ∈ sectionHomogeneousCotangentSymbols n V E W F m)
    (hb : ∀ x ξ, ξ ≠ 0 → Function.Bijective (s x ξ)) :
    inverseSymbol s ∈ sectionHomogeneousCotangentSymbols n W F V E (-m) := by
  refine mem_sectionHomogeneousCotangentSymbols_iff.2 fun t _ ψ hψ w t' _ χ hχ ℓ ↦ ?_
  refine mem_homogeneousCotangentSymbols_iff.2 ⟨fun x ↦ ?_, fun x ξ c hc ↦ ?_, fun e he p hp ↦ ?_⟩
  · simp [inverseSymbol]
  · by_cases hx : χ x * ψ x = 0
    · simp [hx]
    rw [inverseSymbol_smul_covector ξ hc
        (apply_smul_covector_of_mul_ne_zero hs hχ hψ (by rwa [mul_comm]) ξ hc),
      LinearMap.smul_apply, map_smul, map_smul, smul_eq_mul, Real.rpow_neg hc.le,
      Complex.ofReal_inv]
    ring
  have hgt : tsupport (fun y ↦ χ y * ψ y) ⊆ t'.baseSet ∩ t.baseSet := fun y hy ↦
    ⟨hχ (tsupport_mul_subset_left hy), hψ (tsupport_mul_subset_right hy)⟩
  by_cases hpg : e.symm p.1 ∈ tsupport (fun y ↦ χ y * ψ y)
  · exact (contDiffWithinAt_inverseSymbol_reading hs hb he (χ.contMDiff.mul ψ.contMDiff)
      hgt w ℓ hp hpg).congr (fun q _ ↦ chartCotangentSymbol_apply _ e q)
        (chartCotangentSymbol_apply _ e p)
  · -- Off the support of `χ ψ`, the reading vanishes near `p`.
    have hc : ∀ᶠ q in 𝓝 p, χ (e.symm (q : CoordinateSpace n × CoordinateSpace n).1) *
        ψ (e.symm q.1) = 0 := by
      filter_upwards [((e.continuousAt_symm hp.1).comp continuousAt_fst).preimage_mem_nhds
        ((isClosed_tsupport _).isOpen_compl.mem_nhds hpg)] with q hq
      exact image_eq_zero_of_notMem_tsupport (f := fun y ↦ χ y * ψ y) hq
    exact (contDiffWithinAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      (eventually_nhdsWithin_of_eventually_nhds
        (hc.mono fun q hq ↦ by rw [chartCotangentSymbol_apply]; simp [hq]))
      (by rw [chartCotangentSymbol_apply]; simp [image_eq_zero_of_notMem_tsupport hpg])

/-- **The inverse of a bijective symbol.** If a smooth positively homogeneous `Hom(E, F)`-valued
symbol `s` of degree `m` is bijective at every nonzero covector, its fibrewise inverses
`s(x, ξ)⁻¹ : F_x → E_x` form a smooth positively homogeneous `Hom(F, E)`-valued symbol of degree
`-m`: there is `s'` in `TauCeti.sectionHomogeneousCotangentSymbols n W F V E (-m)` with
`s'(x, ξ) ∘ s(x, ξ) = 1` and `s(x, ξ) ∘ s'(x, ξ) = 1` for every nonzero covector `ξ ∈ T*ₓM`. This
is the bundle counterpart of `TauCeti.inv_mem_homogeneousCotangentSymbols`. -/
theorem exists_mem_sectionHomogeneousCotangentSymbols_comp_eq_id
    (hs : s ∈ sectionHomogeneousCotangentSymbols n V E W F m)
    (hb : ∀ x ξ, ξ ≠ 0 → Function.Bijective (s x ξ)) :
    ∃ s' ∈ sectionHomogeneousCotangentSymbols n W F V E (-m), ∀ x ξ, ξ ≠ 0 →
      s' x ξ ∘ₗ s x ξ = LinearMap.id ∧ s x ξ ∘ₗ s' x ξ = LinearMap.id :=
  ⟨inverseSymbol s, inverseSymbol_mem_sectionHomogeneousCotangentSymbols hs hb,
    fun x ξ hξ ↦ ⟨LinearMap.ext (inverseSymbol_apply_apply hξ (hb x ξ hξ)),
      LinearMap.ext (apply_inverseSymbol_apply hξ (hb x ξ hξ))⟩⟩

end Inverse

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
