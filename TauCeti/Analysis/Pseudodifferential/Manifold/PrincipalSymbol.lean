/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Basic
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Pseudodifferential.CoordinateChange.Chart
import TauCeti.Analysis.Pseudodifferential.OutputSupport.Basic
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# The principal symbol of a classical pseudodifferential operator on a manifold

Let `P` be a classical pseudodifferential operator of order `m` on a manifold `M` modelled on
`ℝⁿ` (`TauCeti.classicalPseudodifferentialOperators`). In every chart `e` and for all cutoffs
`φ`, `ψ`, its chart compression is `Op(a)` for a classical symbol `a` of order `m`, which is unique
because a symbol is determined by its quantization. This file shows that the principal symbols of
all these chart symbols come from one function on the cotangent bundle of `M`, the **principal
symbol** `σ_m(P)` (`TauCeti.classicalPrincipalSymbol`):

`σ(a)(e x, η) = φ(e x) ψ(e x) σ_m(P)(x, ⟪η, ·⟫ ∘ de_x)`

for every `x` in the source of `e` and every frequency `η`
(`TauCeti.coefficient_principal_eq_classicalPrincipalSymbol`). Frequencies `η ∈ ℝⁿ` are read as
covectors through the inner product, and pulled back to `T*ₓM` by the differential of the chart.

The function `σ_m(P)(x, ·)` is read off in the preferred chart at `x` with a cutoff equal to `1`
near `x`. That it does not depend on these choices is the change of coordinates theorem for
classical symbols between open sets of `ℝⁿ`
(`TauCeti.ClassicalSymbol.exists_smul_quantizeSchwartzValue_comp_eq`): under the transition map
`κ` between two charts, the principal symbol transforms as `σ(a)(κ y, (Dκ(y)*)⁻¹ η)`, which is the
transformation law of a function on the cotangent bundle. The comparison is made with cutoffs
supported near the point, which is possible because the principal symbol of a chart compression
depends on the cutoffs only through their values at the point.

## Main results

* `TauCeti.classicalPrincipalSymbol m P x ξ`: the principal symbol of order `m` of `P` at a
  covector `ξ ∈ T*ₓM`, a complex number.
* `TauCeti.coefficient_principal_eq_classicalPrincipalSymbol`: the principal symbol of the symbol
  of every chart compression of `P` is read from `σ_m(P)`, at the covector `⟪η, ·⟫ ∘ de_x`.
* `TauCeti.coefficient_principal_apply_eq_classicalPrincipalSymbol`: the same statement read at a
  given covector `ξ`, whose chart frequency is the vector dual to `ξ ∘ (de_x)⁻¹`.
* `TauCeti.classicalPrincipalSymbol_smul_covector` and
  `TauCeti.classicalPrincipalSymbol_zero_covector`: `σ_m(P)(x, ·)` is positively homogeneous of
  degree `m` and vanishes at the zero covector.
* `TauCeti.classicalPrincipalSymbol_add`, `TauCeti.classicalPrincipalSymbol_smul`: the principal
  symbol is linear in the operator.
* `TauCeti.classicalPrincipalSymbol_neg`, `TauCeti.classicalPrincipalSymbol_sub`: the principal
  symbol commutes with negation and subtraction of operators.
* `TauCeti.classicalPrincipalSymbol_id`: the principal symbol of order `0` of the identity is `1`
  at nonzero covectors.
* `TauCeti.classicalPrincipalSymbol_eq_zero_of_mem_sub_one`: an operator of order `m - 1` has
  principal symbol `0` in order `m`.
* `TauCeti.classicalPrincipalSymbol_eq_zero_iff`: conversely, the principal symbol of an operator
  of order `m` vanishes exactly when it has order `m - 1`; so two operators with the same principal
  symbol differ by an operator of order `m - 1`
  (`TauCeti.sub_mem_classicalPseudodifferentialOperators_of_classicalPrincipalSymbol_eq`).
* `TauCeti.homogeneousCotangentSymbols m`: the smooth positively homogeneous functions of degree
  `m` on the cotangent bundle, read in charts. Every principal symbol lies there
  (`TauCeti.classicalPrincipalSymbol_mem_homogeneousCotangentSymbols`), and
  `TauCeti.classicalPrincipalSymbolLinearMap` is the principal symbol as a linear map from the
  operators of order `m` to it, with kernel the operators of order `m - 1`
  (`TauCeti.ker_classicalPrincipalSymbolLinearMap`). The pointwise inverse of such a function that
  vanishes at no nonzero covector has degree `-m` (`TauCeti.inv_mem_homogeneousCotangentSymbols`).
* `TauCeti.classicalPrincipalSymbol_complexifyLinearMap`: the principal symbol of the
  complexification of a differential operator `D` of order at most `m` is `i ^ m` times its
  geometric principal symbol (`TauCeti.smoothPrincipalSymbol`) at nonzero covectors, the
  angular-frequency convention `σ(∂ⱼ) = i ξⱼ`.
* `TauCeti.classicalPrincipalSymbol_conj`: naturality under diffeomorphisms. Transporting `P`
  along a diffeomorphism `Φ : N → M` pulls its principal symbol back by the cotangent map,
  `σ_m(Φ^* P)(y, η ∘ dΦ_y) = σ_m(P)(Φ y, η)`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, Theorem 18.1.17
  and the discussion after Definition 18.1.20.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Manifold Distributions SchwartzMap Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] {m : ℝ}
  {P Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-! ### Chart symbols -/

/-- `a` is the symbol of the chart compression of `P` by `φ` and `ψ` in the chart `e`. -/
private def IsChartSymbol
    (P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯)
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (a : ClassicalSymbol n ℂ ℂ m) : Prop :=
  ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n),
    quantizeSchwartzValue a.toSymbol.coefficient u x =
      e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x

/-- A choice of the symbol of the chart compression of `P` by `φ` and `ψ` in the chart `e`. -/
private def chartSymbol (hP : P ∈ classicalPseudodifferentialOperators m)
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) : ClassicalSymbol n ℂ ℂ m :=
  ((mem_classicalPseudodifferentialOperators_iff.1 hP).2 e he φ ψ).choose

private theorem isChartSymbol_chartSymbol (hP : P ∈ classicalPseudodifferentialOperators m)
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    IsChartSymbol P he φ ψ (chartSymbol hP he φ ψ) :=
  ((mem_classicalPseudodifferentialOperators_iff.1 hP).2 e he φ ψ).choose_spec

/-- The symbol of a chart compression is unique. -/
private theorem IsChartSymbol.eq {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    {he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
    {φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} {a b : ClassicalSymbol n ℂ ℂ m}
    (ha : IsChartSymbol P he φ ψ a) (hb : IsChartSymbol P he φ ψ b) : a = b :=
  ClassicalSymbol.ext <| Symbol.ext <| Symbol.coefficient_eq_of_forall_quantizeSchwartzValue_eq
    fun u _ ↦ funext fun x ↦ (ha u x).trans (hb u x).symm

/-! ### Changes of chart -/

/-- Pulling back through two overlapping charts. Let `κ = e₂ ∘ e₁⁻¹` be the transition, `ψ₁` a
cutoff supported in its source and `ψ₂` a cutoff equal to `1` on the image of the support of `ψ₁`.
If `v = (ψ₁ u) ∘ κ⁻¹` on the target of `κ` and `0` off it, then pulling back `v` through `e₂` by
`ψ₂` gives the same function on `M` as pulling back `u` through `e₁` by `ψ₁`. -/
private theorem complexCutoffPullback_eq_of_transition
    {e₁ e₂ : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he₁ : e₁ ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (he₂ : e₂ ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    {ψ₁ : 𝓓(⟨e₁.target, e₁.open_target⟩, ℝ)} {ψ₂ : 𝓓(⟨e₂.target, e₂.open_target⟩, ℝ)}
    (hψ₁ : tsupport ψ₁ ⊆ (e₁.symm.trans e₂).source)
    (hψ₂ : ∀ y ∈ tsupport ψ₁, ψ₂ (e₂ (e₁.symm y)) = 1) {u v : 𝓢(CoordinateSpace n, ℂ)}
    (hv : ∀ y ∈ (e₁.symm.trans e₂).source, v (e₁.symm.trans e₂ y) = ψ₁ y • u y)
    (hv0 : ∀ z ∉ (e₁.symm.trans e₂).target, v z = 0) :
    e₂.complexCutoffPullback he₂ ψ₂ (ContMDiffMap.ofContDiff v (v.smooth ⊤)) =
      e₁.complexCutoffPullback he₁ ψ₁ (ContMDiffMap.ofContDiff u (u.smooth ⊤)) := by
  ext p
  by_cases hp₁ : p ∈ e₁.source <;> by_cases hp₂ : p ∈ e₂.source
  · have hpκ : e₁ p ∈ (e₁.symm.trans e₂).source := by
      simp [e₁.map_source hp₁, e₁.left_inv hp₁, hp₂]
    have hvp := hv _ hpκ
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, e₁.left_inv hp₁] at hvp
    simp only [OpenPartialHomeomorph.complexCutoffPullback_apply_of_mem he₂ _ _ hp₂,
      OpenPartialHomeomorph.complexCutoffPullback_apply_of_mem he₁ _ _ hp₁,
      ContMDiffMap.coe_ofContDiff, hvp]
    by_cases hψ : ψ₁ (e₁ p) = 0
    · simp [hψ]
    · have h1 := hψ₂ _ (subset_tsupport _ hψ)
      rw [e₁.left_inv hp₁] at h1
      rw [h1, one_smul]
  · -- The point `e₁ p` lies outside the source of `κ`, so outside the support of `ψ₁`.
    have hψ : ψ₁ (e₁ p) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hp₂ <| by
      simpa [e₁.left_inv hp₁] using (hψ₁ h).2
    simp [OpenPartialHomeomorph.complexCutoffPullback_apply_of_notMem he₂ _ _ hp₂,
      OpenPartialHomeomorph.complexCutoffPullback_apply_of_mem he₁ _ _ hp₁, hψ]
  · -- The point `e₂ p` lies outside the target of `κ`, where `v` vanishes.
    have hv' : v (e₂ p) = 0 := hv0 _ fun h ↦ hp₁ <| by
      simpa [e₂.left_inv hp₂] using h.2
    simp [OpenPartialHomeomorph.complexCutoffPullback_apply_of_mem he₂ _ _ hp₂,
      OpenPartialHomeomorph.complexCutoffPullback_apply_of_notMem he₁ _ _ hp₁, hv']
  · simp [OpenPartialHomeomorph.complexCutoffPullback_apply_of_notMem he₂ _ _ hp₂,
      OpenPartialHomeomorph.complexCutoffPullback_apply_of_notMem he₁ _ _ hp₁]

/-- **Changes of chart for chart symbols.** Let `a₁` and `a₂` be the symbols of the chart
compressions of `P` in the charts `e₁` and `e₂`. If the cutoffs `φ₁`, `ψ₁` are supported in the
source of the transition `κ = e₂ ∘ e₁⁻¹`, and `φ₂`, `ψ₂` equal `1` on the images of their
supports, then `σ(a₁)(y, η) = φ₁(y) ψ₁(y) σ(a₂)(κ y, (Dκ(y)*)⁻¹ η)`. -/
private theorem coefficient_principal_eq_of_isChartSymbol
    {e₁ e₂ : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he₁ : e₁ ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (he₂ : e₂ ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    {φ₁ ψ₁ : 𝓓(⟨e₁.target, e₁.open_target⟩, ℝ)} {φ₂ ψ₂ : 𝓓(⟨e₂.target, e₂.open_target⟩, ℝ)}
    (hφ₁ : tsupport φ₁ ⊆ (e₁.symm.trans e₂).source)
    (hψ₁ : tsupport ψ₁ ⊆ (e₁.symm.trans e₂).source)
    (hφ₂ : ∀ y ∈ tsupport φ₁, φ₂ (e₂ (e₁.symm y)) = 1)
    (hψ₂ : ∀ y ∈ tsupport ψ₁, ψ₂ (e₂ (e₁.symm y)) = 1) {a₁ a₂ : ClassicalSymbol n ℂ ℂ m}
    (ha₁ : IsChartSymbol P he₁ φ₁ ψ₁ a₁) (ha₂ : IsChartSymbol P he₂ φ₂ ψ₂ a₂)
    (y η : CoordinateSpace n) :
    a₁.principal.coefficient (y, η) = (φ₁ y * ψ₁ y) • a₂.principal.coefficient
      (e₂ (e₁.symm y),
        ContinuousLinearMap.adjoint (Ring.inverse (fderiv ℝ (e₁.symm.trans e₂) y)) η) := by
  set κ := e₁.symm.trans e₂ with hκdef
  have hκ : ContDiffOn ℝ ∞ κ κ.source := contDiffOn_symm_trans_of_mem_maximalAtlas he₁ he₂
  have hκ' : ContDiffOn ℝ ∞ κ.symm κ.target := by
    rw [← OpenPartialHomeomorph.symm_source, hκdef,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
    exact contDiffOn_symm_trans_of_mem_maximalAtlas he₂ he₁
  obtain ⟨b, hb, hop⟩ := a₂.exists_smul_quantizeSchwartzValue_comp_eq κ hκ hκ' φ₁.contDiff
    φ₁.hasCompactSupport hφ₁ ψ₁.contDiff ψ₁.hasCompactSupport hψ₁
  -- The transported operator `u ↦ φ₁ · Op(a₂) ((ψ₁ u) ∘ κ⁻¹) ∘ κ` is the chart compression in `e₁`.
  suffices hab : IsChartSymbol P he₁ φ₁ ψ₁ b by
    rw [ha₁.eq hab, hb]
    simp only [κ, OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  intro u x
  obtain ⟨v, hv, hv0⟩ := exists_schwartzMap_apply_eq_smul hκ' ψ₁.contDiff ψ₁.hasCompactSupport
    hψ₁ u
  rw [← hop u v hv hv0 x, ha₂ v (κ x), OpenPartialHomeomorph.complexChartCompression_apply,
    OpenPartialHomeomorph.complexChartCompression_apply,
    complexCutoffPullback_eq_of_transition he₁ he₂ hψ₁ hψ₂ hv hv0]
  by_cases hx : φ₁ x = 0
  · simp [hx]
  have hxκ : x ∈ κ.source := hφ₁ (subset_tsupport _ hx)
  have hxs : e₁.symm x ∈ e₂.source := by simpa [κ] using hxκ.2
  simp only [κ, OpenPartialHomeomorph.coe_trans, Function.comp_apply, e₂.left_inv hxs,
    hφ₂ x (subset_tsupport _ hx), one_smul]

/-- **Changes of cutoffs for chart symbols.** In a fixed chart `e`, if the cutoffs `φ'`, `ψ'`
equal `1` on the supports of `φ`, `ψ`, then the principal symbols of the symbols of the chart
compressions are related by `σ(a)(y, η) = φ(y) ψ(y) σ(a')(y, η)`. -/
private theorem coefficient_principal_eq_smul_of_isChartSymbol
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    {φ ψ φ' ψ' : 𝓓(⟨e.target, e.open_target⟩, ℝ)} (hφ' : ∀ y ∈ tsupport φ, φ' y = 1)
    (hψ' : ∀ y ∈ tsupport ψ, ψ' y = 1) {a a' : ClassicalSymbol n ℂ ℂ m}
    (ha : IsChartSymbol P he φ ψ a) (ha' : IsChartSymbol P he φ' ψ' a')
    {y : CoordinateSpace n} (hy : y ∈ e.target) (η : CoordinateSpace n) :
    a.principal.coefficient (y, η) = (φ y * ψ y) • a'.principal.coefficient (y, η) := by
  -- The transition from `e` to itself is defined on the whole chart target.
  have hsource (χ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
      tsupport χ ⊆ (e.symm.trans e).source := fun z hz ↦ by
    have hzt := χ.tsupport_subset hz
    simpa [e.map_target hzt] using hzt
  have h := coefficient_principal_eq_of_isChartSymbol he he (hsource φ) (hsource ψ)
    (fun z hz ↦ by rw [e.right_inv (φ.tsupport_subset hz), hφ' z hz])
    (fun z hz ↦ by rw [e.right_inv (ψ.tsupport_subset hz), hψ' z hz]) ha ha' y η
  rwa [e.right_inv hy, OpenPartialHomeomorph.coe_trans,
    adjoint_ringInverse_fderiv_comp_symm_eq_one hy, one_apply_eq_self] at h

omit [T2Space M] in
/-- A cutoff in the preferred chart at `x`, equal to `1` near the image of `x`. -/
private theorem exists_cutoff_chartAt (x : M) :
    ∃ χ : 𝓓(⟨(chartAt (CoordinateSpace n) x).target,
      (chartAt (CoordinateSpace n) x).open_target⟩, ℝ),
      ∀ᶠ z in 𝓝 (chartAt (CoordinateSpace n) x x), χ z = 1 :=
  TestFunction.exists_eventually_eq_one_nhds (mem_chart_target (CoordinateSpace n) x)

/-! ### Smooth homogeneous functions on the cotangent bundle -/

omit [T2Space M] in
variable (n M) in
/-- The **smooth positively homogeneous functions of degree `m` on the cotangent bundle** of `M`,
where the principal symbols of order `m` live: the functions `s(x, ξ)` of a point `x ∈ M` and a
covector `ξ ∈ T*ₓM` that vanish at the zero covector, satisfy `s(x, t ξ) = t ^ m s(x, ξ)` for
`t > 0`, and are smooth away from the zero section, in the sense that in every chart `e` of the
maximal smooth atlas the function `(y, η) ↦ s(e⁻¹ y, ⟪η, ·⟫ ∘ de)` is smooth on the chart target
times the nonzero frequencies. -/
def homogeneousCotangentSymbols (m : ℝ) :
    Submodule ℂ ((x : M) → (TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) → ℂ) where
  carrier := {s | (∀ x, s x 0 = 0) ∧ (∀ x ξ (t : ℝ), 0 < t → s x (t • ξ) = (t ^ m : ℝ) * s x ξ) ∧
    ∀ e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M,
      ContDiffOn ℝ ∞ (fun p : CoordinateSpace n × CoordinateSpace n ↦
        s (e.symm p.1) ((innerSL ℝ p.2).comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e (e.symm p.1))))
        (e.target ×ˢ {η | η ≠ 0})}
  zero_mem' := ⟨fun _ ↦ rfl, fun _ _ _ _ ↦ by simp, fun _ _ ↦ contDiffOn_const⟩
  add_mem' {s s'} hs hs' := ⟨fun x ↦ by simp [hs.1 x, hs'.1 x],
    fun x ξ t ht ↦ by simp [hs.2.1 x ξ t ht, hs'.2.1 x ξ t ht, mul_add],
    fun e he ↦ (hs.2.2 e he).add (hs'.2.2 e he)⟩
  smul_mem' c s hs := ⟨fun x ↦ by simp [hs.1 x],
    fun x ξ t ht ↦ by simp [hs.2.1 x ξ t ht, mul_left_comm],
    fun e he ↦ (hs.2.2 e he).const_smul c⟩

omit [T2Space M] in
theorem mem_homogeneousCotangentSymbols_iff
    {s : (x : M) → (TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) → ℂ} :
    s ∈ homogeneousCotangentSymbols n M m ↔ (∀ x, s x 0 = 0) ∧
      (∀ x ξ (t : ℝ), 0 < t → s x (t • ξ) = (t ^ m : ℝ) * s x ξ) ∧
      ∀ e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M,
        ContDiffOn ℝ ∞ (fun p : CoordinateSpace n × CoordinateSpace n ↦
          s (e.symm p.1) ((innerSL ℝ p.2).comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e (e.symm p.1))))
          (e.target ×ˢ {η | η ≠ 0}) :=
  Iff.rfl

omit [T2Space M] in
/-- **Inverting a homogeneous function on the cotangent bundle.** If a smooth positively
homogeneous function `s` of degree `m` on the cotangent bundle vanishes at no nonzero covector,
its pointwise inverse `s⁻¹` is a smooth positively homogeneous function of degree `-m`; at the zero
covector it is `0⁻¹ = 0`. This is the inverse principal symbol of an elliptic operator. -/
theorem inv_mem_homogeneousCotangentSymbols
    {s : (x : M) → (TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) → ℂ}
    (hs : s ∈ homogeneousCotangentSymbols n M m) (hs0 : ∀ x ξ, ξ ≠ 0 → s x ξ ≠ 0) :
    (fun x ξ ↦ (s x ξ)⁻¹) ∈ homogeneousCotangentSymbols n M (-m) := by
  refine ⟨fun x ↦ by simp [hs.1 x], fun x ξ t ht ↦ ?_, fun e he ↦ (hs.2.2 e he).inv ?_⟩
  · simp only [hs.2.1 x ξ t ht, mul_inv, Real.rpow_neg ht.le, Complex.ofReal_inv]
  -- In a chart, a nonzero frequency `η` gives the nonzero covector `⟪η, ·⟫ ∘ de`.
  rintro ⟨y, η⟩ ⟨hy, hη⟩
  exact hs0 _ _ ((innerSL_comp_mvfderiv_eq_zero_iff
    (IsManifold.maximalAtlas_subset_of_le (by simp) he) (e.map_target hy)).not.2 hη)

/-! ### The principal symbol on the cotangent bundle -/

variable [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

/-- The chart symbol of `P` that defines `σ_m(P)(x, ·)`: the symbol of the chart compression of
`P` in the preferred chart at `x`, with the chosen cutoff equal to `1` near the image of `x`. -/
private def preferredChartSymbol (hP : P ∈ classicalPseudodifferentialOperators m) (x : M) :
    ClassicalSymbol n ℂ ℂ m :=
  chartSymbol hP (IsManifold.chart_mem_maximalAtlas x) (exists_cutoff_chartAt x).choose
    (exists_cutoff_chartAt x).choose

/-- `preferredChartSymbol hP x` is the symbol of its chart compression. -/
private theorem isChartSymbol_preferredChartSymbol
    (hP : P ∈ classicalPseudodifferentialOperators m) (x : M) :
    IsChartSymbol P (IsManifold.chart_mem_maximalAtlas x) (exists_cutoff_chartAt x).choose
      (exists_cutoff_chartAt x).choose (preferredChartSymbol hP x) :=
  isChartSymbol_chartSymbol hP _ _ _

variable (m P) in
/-- **The principal symbol** of order `m` of a classical pseudodifferential operator `P` of order
`m` on `M`, at a covector `ξ ∈ T*ₓM`. In every chart `e` the principal symbol of the symbol of
the chart compression of `P` by cutoffs `φ`, `ψ` is `φ(e x) ψ(e x) σ_m(P)(x, ξ)` at the frequency
dual to `ξ ∘ (de_x)⁻¹` (`TauCeti.coefficient_principal_apply_eq_classicalPrincipalSymbol`). It
is `0` when `P` is not a classical pseudodifferential operator of order `m`. -/
def classicalPrincipalSymbol (x : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) : ℂ :=
  open Classical in
  if hP : P ∈ classicalPseudodifferentialOperators m then
    (preferredChartSymbol hP x).principal.coefficient
        (chartAt (CoordinateSpace n) x x, (InnerProductSpace.toDual ℝ (CoordinateSpace n)).symm
          (ξ.comp (mvfderiv 𝓘(ℝ, CoordinateSpace n)
            (chartAt (CoordinateSpace n) x) x).inverse)) 1
  else 0

/-- The principal symbol of order `m` of an operator that is not a classical pseudodifferential
operator of order `m` is `0`, by convention. -/
theorem classicalPrincipalSymbol_of_notMem (hP : P ∉ classicalPseudodifferentialOperators m)
    (x : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m P x ξ = 0 := by
  simp [classicalPrincipalSymbol, hP]

/-- **The principal symbol in a chart.** Let `P` be a classical pseudodifferential operator of
order `m` on `M`, and `a` the symbol of its chart compression `u ↦ φ · (P ((ψ u) ∘ e)) ∘ e⁻¹` in a
chart `e`. At every point `x` of the chart source and every frequency `η`, the principal symbol of
`a` is `φ(e x) ψ(e x)` times the principal symbol of `P` at the covector `⟪η, ·⟫ ∘ de_x`. -/
theorem coefficient_principal_eq_classicalPrincipalSymbol
    (hP : P ∈ classicalPseudodifferentialOperators m)
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {a : ClassicalSymbol n ℂ ℂ m}
    (ha : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    {x : M} (hx : x ∈ e.source) (η : CoordinateSpace n) :
    a.principal.coefficient (e x, η) =
      (((φ (e x) * ψ (e x) : ℝ) : ℂ) * classicalPrincipalSymbol m P x ((innerSL ℝ η).comp
        (mvfderiv 𝓘(ℝ, CoordinateSpace n) e x))) •
        ContinuousLinearMap.id ℂ ℂ := by
  -- The preferred chart `e₂` at `x`, its cutoff `χ` and the symbol `a₂` defining `σ_m(P)(x, ·)`.
  set e₂ := chartAt (CoordinateSpace n) x
  have he₂ : e₂ ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas x
  have hx₂ : x ∈ e₂.source := mem_chart_source _ x
  set χ := (exists_cutoff_chartAt (n := n) x).choose
  obtain ⟨N, hNχ, hN, hxN⟩ := eventually_nhds_iff.1 (exists_cutoff_chartAt (n := n) x).choose_spec
  set κ := e.symm.trans e₂
  have hyκ : e x ∈ κ.source := by simp [κ, e.map_source hx, e.left_inv hx, hx₂]
  -- A cutoff `θ` in `e`, equal to `1` at `e x` and supported where `κ` lands in `{χ = 1}`.
  set W := κ.source ∩ κ ⁻¹' N
  have hW : IsOpen W := κ.continuousOn.isOpen_inter_preimage κ.open_source hN
  have hyW : e x ∈ W := ⟨hyκ, by simpa [κ, e.left_inv hx] using hxN⟩
  obtain ⟨θ, hθW, hθy⟩ := TestFunction.exists_tsupport_subset_apply_eq
    (Ω := ⟨e.target, e.open_target⟩) (n := ⊤) (hW.mem_nhds hyW) (fun z hz ↦ hz.1.1) (1 : ℝ)
  -- A cutoff `χ'` in `e`, equal to `1` on the supports of `φ`, `ψ` and `θ`.
  obtain ⟨χ', hχ', -⟩ := TestFunction.exists_eventually_eq_one (Ω := ⟨e.target, e.open_target⟩)
    (n := ⊤) ((φ.hasCompactSupport.isCompact.union ψ.hasCompactSupport.isCompact).union
      θ.hasCompactSupport.isCompact)
    (union_subset (union_subset φ.tsupport_subset ψ.tsupport_subset) θ.tsupport_subset)
  have hχ'1 : ∀ z ∈ tsupport φ ∪ tsupport ψ ∪ tsupport θ, χ' z = 1 := fun z hz ↦
    (hχ'.filter_mono (nhds_le_nhdsSet hz)).self_of_nhds
  -- Compare `a` with the symbol for `χ'`, then that with the symbol for `θ`, and the latter with
  -- `a₂` through the transition `κ`.
  have h₁ := coefficient_principal_eq_smul_of_isChartSymbol he
    (fun z hz ↦ hχ'1 z (.inl (.inl hz))) (fun z hz ↦ hχ'1 z (.inl (.inr hz))) ha
    (isChartSymbol_chartSymbol hP he χ' χ') (e.map_source hx) η
  have h₂ := coefficient_principal_eq_smul_of_isChartSymbol he
    (fun z hz ↦ hχ'1 z (.inr hz)) (fun z hz ↦ hχ'1 z (.inr hz))
    (isChartSymbol_chartSymbol hP he θ θ) (isChartSymbol_chartSymbol hP he χ' χ')
    (e.map_source hx) η
  have h₃ := coefficient_principal_eq_of_isChartSymbol he he₂ (fun z hz ↦ (hθW hz).1)
    (fun z hz ↦ (hθW hz).1) (fun z hz ↦ hNχ _ (hθW hz).2) (fun z hz ↦ hNχ _ (hθW hz).2)
    (isChartSymbol_chartSymbol hP he θ θ) (isChartSymbol_chartSymbol hP he₂ χ χ) (e x) η
  rw [hθy, one_mul, one_smul] at h₂ h₃
  rw [h₁, ← h₂, h₃, e.left_inv hx, classicalPrincipalSymbol, dite_eq_left hP, preferredChartSymbol,
    ← toDual_symm_comp_inverse_mvfderiv (IsManifold.maximalAtlas_subset_of_le (by simp) he)
      (IsManifold.maximalAtlas_subset_of_le (by simp) he₂) hx hx₂ η]
  refine ContinuousLinearMap.ext_ring ?_
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply,
    Complex.real_smul, smul_eq_mul, mul_one]
  -- Both sides now read the same symbol `chartSymbol hP he₂ χ χ`, once through the local names
  -- `e₂` and `χ` and once through the preferred chart and its chosen cutoff that they abbreviate.
  rfl

/-- **The principal symbol in a chart, at a covector.** Let `a` be the symbol of the chart
compression of `P` by `φ` and `ψ` in a chart `e`. At a point `x` of the chart source and a covector
`ξ ∈ T*ₓM`, the principal symbol of `a` at the frequency dual to `ξ ∘ (de_x)⁻¹` is
`φ(e x) ψ(e x) σ_m(P)(x, ξ)`. -/
theorem coefficient_principal_apply_eq_classicalPrincipalSymbol
    (hP : P ∈ classicalPseudodifferentialOperators m)
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {a : ClassicalSymbol n ℂ ℂ m}
    (ha : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    {x : M} (hx : x ∈ e.source) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    a.principal.coefficient (e x, (InnerProductSpace.toDual ℝ (CoordinateSpace n)).symm
        (ξ.comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e x).inverse)) 1 =
      (φ (e x) * ψ (e x) : ℝ) * classicalPrincipalSymbol m P x ξ := by
  rw [coefficient_principal_eq_classicalPrincipalSymbol hP he φ ψ ha hx,
    innerSL_toDual_symm_comp_inverse_mvfderiv (IsManifold.maximalAtlas_subset_of_le (by simp) he)
      hx]
  simp

/-! ### Homogeneity -/

/-- The principal symbol vanishes at the zero covector. -/
@[simp]
theorem classicalPrincipalSymbol_zero_covector (x : M) :
    classicalPrincipalSymbol m P x 0 = 0 := by
  unfold classicalPrincipalSymbol
  split_ifs <;> simp

/-- **Homogeneity.** The principal symbol of order `m` is positively homogeneous of degree `m` in
the covector: `σ_m(P)(x, t ξ) = t ^ m σ_m(P)(x, ξ)` for `t > 0`. -/
theorem classicalPrincipalSymbol_smul_covector (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) {t : ℝ} (ht : 0 < t) :
    classicalPrincipalSymbol m P x (t • ξ) = (t ^ m : ℝ) * classicalPrincipalSymbol m P x ξ := by
  unfold classicalPrincipalSymbol
  split_ifs
  · rw [ContinuousLinearMap.smul_comp, map_smulₛₗ, starRingEnd_apply, star_trivial,
      HomogeneousSymbol.homogeneous _ _ _ _ ht]
    simp [Complex.real_smul]
  · simp

/-! ### Linearity and order -/

/-- In the preferred chart at `x`, with a cutoff equal to `1` near the image of `x`, the principal
symbol of every chart symbol of `P` is `σ_m(P)` at `x`. -/
private theorem classicalPrincipalSymbol_eq_coefficient_principal
    (hP : P ∈ classicalPseudodifferentialOperators m) (x : M) {a : ClassicalSymbol n ℂ ℂ m}
    (ha : IsChartSymbol P (IsManifold.chart_mem_maximalAtlas x)
      (exists_cutoff_chartAt x).choose (exists_cutoff_chartAt x).choose a)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m P x ξ = a.principal.coefficient
      (chartAt (CoordinateSpace n) x x, (InnerProductSpace.toDual ℝ (CoordinateSpace n)).symm
        (ξ.comp (mvfderiv 𝓘(ℝ, CoordinateSpace n)
          (chartAt (CoordinateSpace n) x) x).inverse)) 1 := by
  rw [coefficient_principal_apply_eq_classicalPrincipalSymbol hP _ _ _ ha
    (mem_chart_source _ x), (exists_cutoff_chartAt x).choose_spec.self_of_nhds]
  simp

/-- The principal symbol is additive in the operator. -/
theorem classicalPrincipalSymbol_add (hP : P ∈ classicalPseudodifferentialOperators m)
    (hQ : Q ∈ classicalPseudodifferentialOperators m) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (P + Q) x ξ =
      classicalPrincipalSymbol m P x ξ + classicalPrincipalSymbol m Q x ξ := by
  have ha := isChartSymbol_preferredChartSymbol hP x
  have hb := isChartSymbol_preferredChartSymbol hQ x
  rw [classicalPrincipalSymbol_eq_coefficient_principal (add_mem hP hQ) x
      (a := preferredChartSymbol hP x + preferredChartSymbol hQ x)
      fun u y ↦ by rw [ClassicalSymbol.quantizeSchwartzValue_toSymbol_add, ha, hb]; simp,
    classicalPrincipalSymbol_eq_coefficient_principal hP x ha,
    classicalPrincipalSymbol_eq_coefficient_principal hQ x hb]
  simp [ClassicalSymbol.principal_add]

/-- The principal symbol is homogeneous in the operator: `σ_m(c P) = c σ_m(P)`. -/
theorem classicalPrincipalSymbol_smul (hP : P ∈ classicalPseudodifferentialOperators m) (c : ℂ)
    (x : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (c • P) x ξ = c * classicalPrincipalSymbol m P x ξ := by
  have ha := isChartSymbol_preferredChartSymbol hP x
  rw [classicalPrincipalSymbol_eq_coefficient_principal (Submodule.smul_mem _ c hP) x
      (a := c • preferredChartSymbol hP x) fun u y ↦ by
        rw [ClassicalSymbol.quantizeSchwartzValue_toSymbol_smul, ha]; simp,
    classicalPrincipalSymbol_eq_coefficient_principal hP x ha]
  simp [ClassicalSymbol.principal_smul]

/-- The principal symbol of the zero operator is `0`. -/
@[simp]
theorem classicalPrincipalSymbol_zero (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (0 : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) x ξ = 0 := by
  simpa using classicalPrincipalSymbol_smul (m := m) (zero_mem _) 0 x ξ

/-- **The principal symbol of the identity** is `1` at every nonzero covector. In the preferred
chart at `x`, the compression of the identity by a cutoff `χ` is multiplication by `χ²`, whose
principal symbol is `χ²` at nonzero frequencies. -/
@[simp]
theorem classicalPrincipalSymbol_id (x : M) {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ}
    (hξ : ξ ≠ 0) :
    classicalPrincipalSymbol 0 (LinearMap.id : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) x ξ = 1 := by
  set e := chartAt (CoordinateSpace n) x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source _ x
  set χ := (exists_cutoff_chartAt (n := n) x).choose
  have hχ : χ (e x) = 1 := (exists_cutoff_chartAt (n := n) x).choose_spec.self_of_nhds
  have h := coefficient_principal_apply_eq_classicalPrincipalSymbol
    id_mem_classicalPseudodifferentialOperators he χ χ
    (ClassicalSymbol.quantizeSchwartzValue_ofSpatial_eq_complexChartCompression_id he χ χ) hx ξ
  rw [ClassicalSymbol.coefficient_principal_ofSpatial _ _ (toDual_symm_comp_inverse_mvfderiv_ne_zero
    (IsManifold.maximalAtlas_subset_of_le (by simp) he) hx hξ), hχ] at h
  simpa using h.symm

/-- **Operators of lower order.** A classical pseudodifferential operator of order `m - 1` has
principal symbol `0` in order `m`: its chart symbols, read in order `m`, have no term of order
`m`. -/
theorem classicalPrincipalSymbol_eq_zero_of_mem_sub_one
    (hP : P ∈ classicalPseudodifferentialOperators (m - 1)) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m P x ξ = 0 := by
  have hk : m - 1 = m - ((0 + 1 : ℕ) : ℝ) := by norm_num
  have ha := isChartSymbol_preferredChartSymbol hP x
  rw [classicalPrincipalSymbol_eq_coefficient_principal
      (classicalPseudodifferentialOperators_le 1 (by norm_num) hP) x
      (a := ClassicalSymbol.inclusion (0 + 1) hk (preferredChartSymbol hP x)) fun u y ↦ by
        rw [ClassicalSymbol.toSymbol_inclusion, Symbol.coefficient_inclusion, ha],
    ClassicalSymbol.principal_inclusion_succ]
  simp

/-- The principal symbol of `-P` is minus that of `P`. -/
theorem classicalPrincipalSymbol_neg (x : M) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (-P) x ξ = -classicalPrincipalSymbol m P x ξ := by
  by_cases hP : P ∈ classicalPseudodifferentialOperators m
  · rw [← neg_one_smul ℂ P, classicalPrincipalSymbol_smul hP, neg_one_mul]
  · rw [classicalPrincipalSymbol_of_notMem hP,
      classicalPrincipalSymbol_of_notMem (by rwa [neg_mem_iff]), neg_zero]

/-- The principal symbol of `P - Q` is the difference of those of `P` and `Q`. -/
theorem classicalPrincipalSymbol_sub (hP : P ∈ classicalPseudodifferentialOperators m)
    (hQ : Q ∈ classicalPseudodifferentialOperators m) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (P - Q) x ξ =
      classicalPrincipalSymbol m P x ξ - classicalPrincipalSymbol m Q x ξ := by
  rw [sub_eq_add_neg, classicalPrincipalSymbol_add hP (neg_mem hQ), classicalPrincipalSymbol_neg,
    ← sub_eq_add_neg]

/-- **The kernel of the principal symbol.** A classical pseudodifferential operator of order `m`
has vanishing principal symbol exactly when it is a classical pseudodifferential operator of order
`m - 1`. -/
theorem classicalPrincipalSymbol_eq_zero_iff (hP : P ∈ classicalPseudodifferentialOperators m) :
    (∀ x ξ, classicalPrincipalSymbol m P x ξ = 0) ↔
      P ∈ classicalPseudodifferentialOperators (m - 1) := by
  refine ⟨fun h ↦ ?_, fun h x ξ ↦ classicalPrincipalSymbol_eq_zero_of_mem_sub_one h x ξ⟩
  have hP' := mem_classicalPseudodifferentialOperators_iff.1 hP
  refine mem_classicalPseudodifferentialOperators_iff.2 ⟨hP'.1, fun e he φ ψ ↦ ?_⟩
  -- In every chart, the principal symbol of the local symbol vanishes: on the chart target by
  -- `coefficient_principal_eq_classicalPrincipalSymbol`, and off it because there the output
  -- cutoff, and hence the symbol, vanishes.
  obtain ⟨a, ha⟩ := hP'.2 e he φ ψ
  have h0 : a.principal = 0 := by
    refine HomogeneousSymbol.ext_of_ne_zero fun y η _ ↦ ?_
    rw [HomogeneousSymbol.coefficient_zero, Pi.zero_apply]
    by_cases hy : y ∈ e.target
    · rw [← e.right_inv hy,
        coefficient_principal_eq_classicalPrincipalSymbol hP he φ ψ ha (e.map_target hy), h]
      simp
    · obtain ⟨C, hC⟩ := a.toSymbol.exists_norm_coefficient_le {y} isCompact_singleton
      refine a.coefficient_principal_eq_zero_of_forall (fun ζ ↦
        eq_zero_of_forall_quantizeSchwartzValue_eq_zero
          (a.toSymbol.continuous_coefficient_slice y) (hC y rfl) (fun u _ ↦ ?_) ζ) η
      rw [ha, OpenPartialHomeomorph.complexChartCompression_apply,
        image_eq_zero_of_notMem_tsupport fun h ↦ hy (φ.tsupport_subset h), zero_smul]
  obtain ⟨b, rfl⟩ := (ClassicalSymbol.principal_eq_zero_iff_exists_inclusion a).1 h0
  exact ⟨b, fun u x ↦ by
    rw [← ha, ClassicalSymbol.toSymbol_inclusion, Symbol.coefficient_inclusion]⟩

/-- Two classical pseudodifferential operators of order `m` with the same principal symbol differ
by an operator of order `m - 1`. -/
theorem sub_mem_classicalPseudodifferentialOperators_of_classicalPrincipalSymbol_eq
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hQ : Q ∈ classicalPseudodifferentialOperators m)
    (h : ∀ x ξ, classicalPrincipalSymbol m P x ξ = classicalPrincipalSymbol m Q x ξ) :
    P - Q ∈ classicalPseudodifferentialOperators (m - 1) :=
  (classicalPrincipalSymbol_eq_zero_iff (sub_mem hP hQ)).1 fun x ξ ↦ by
    rw [classicalPrincipalSymbol_sub hP hQ, h, sub_self]

/-- The principal symbol of a finite sum of operators of order `m` is the sum of their principal
symbols. -/
theorem classicalPrincipalSymbol_sum {ι : Type*} (s : Finset ι)
    {P : ι → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hP : ∀ i ∈ s, P i ∈ classicalPseudodifferentialOperators m) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (∑ i ∈ s, P i) x ξ =
      ∑ i ∈ s, classicalPrincipalSymbol m (P i) x ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      classicalPrincipalSymbol_add (hP i (Finset.mem_insert_self i s))
        (Submodule.sum_mem _ fun j hj ↦ hP j (Finset.mem_insert_of_mem hj)),
      ih fun j hj ↦ hP j (Finset.mem_insert_of_mem hj)]

/-! ### The principal symbol map -/

/-- **The principal symbol is smooth.** The principal symbol of order `m` of every operator is a
smooth positively homogeneous function of degree `m` on the cotangent bundle. -/
theorem classicalPrincipalSymbol_mem_homogeneousCotangentSymbols :
    classicalPrincipalSymbol m P ∈ homogeneousCotangentSymbols n M m := by
  refine ⟨classicalPrincipalSymbol_zero_covector, fun x ξ t ht ↦
    classicalPrincipalSymbol_smul_covector x ξ ht, fun e he ↦ ?_⟩
  by_cases hP : P ∈ classicalPseudodifferentialOperators m
  swap
  · simp only [classicalPrincipalSymbol_of_notMem hP]
    exact contDiffOn_const
  -- In a chart `e`, near every point of the chart target, the principal symbol is the principal
  -- symbol of the symbol of a chart compression of `P` by cutoffs equal to `1` there, which is
  -- smooth away from the zero frequency.
  rintro ⟨y, η⟩ ⟨hy, hη⟩
  -- A cutoff `χ` in `e`, equal to `1` near `y`, and the symbol `a` of the compression by `χ`.
  obtain ⟨χ, hχ⟩ := TestFunction.exists_eventually_eq_one_nhds (Ω := ⟨e.target, e.open_target⟩)
    (n := ⊤) hy
  obtain ⟨a, ha⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hP).2 e he χ χ
  -- Near `(y, η)`, the function is the value at `1` of the principal symbol of `a`.
  have hev :
      (fun p : CoordinateSpace n × CoordinateSpace n ↦ a.principal.coefficient p 1) =ᶠ[𝓝 (y, η)]
      fun p ↦ classicalPrincipalSymbol m P (e.symm p.1)
        ((innerSL ℝ p.2).comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e (e.symm p.1))) := by
    filter_upwards [continuous_fst.continuousAt.eventually (hχ.and (e.open_target.mem_nhds hy))]
      with p hp
    have h := coefficient_principal_eq_classicalPrincipalSymbol hP he χ χ ha
      (e.map_target hp.2) p.2
    rw [e.right_inv hp.2, hp.1] at h
    simp [h]
  exact ((((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).restrictScalars ℝ).contDiff.comp_contDiffAt _
    (a.principal.contDiffAt_coefficient hη)).congr_of_eventuallyEq hev.symm).contDiffWithinAt

variable (n M m) in
/-- **The principal symbol map** `σ_m` from the classical pseudodifferential operators of order
`m` on `M` to the smooth positively homogeneous functions of degree `m` on the cotangent bundle.
Its kernel is the operators of order `m - 1` (`TauCeti.ker_classicalPrincipalSymbolLinearMap`). -/
def classicalPrincipalSymbolLinearMap :
    classicalPseudodifferentialOperators (n := n) (M := M) m →ₗ[ℂ]
      homogeneousCotangentSymbols n M m where
  toFun P :=
    ⟨classicalPrincipalSymbol m P, classicalPrincipalSymbol_mem_homogeneousCotangentSymbols⟩
  map_add' P Q := Subtype.ext <| funext fun x ↦ funext fun ξ ↦
    classicalPrincipalSymbol_add P.property Q.property x ξ
  map_smul' c P := Subtype.ext <| funext fun x ↦ funext fun ξ ↦
    classicalPrincipalSymbol_smul P.property c x ξ

@[simp]
theorem coe_classicalPrincipalSymbolLinearMap_apply
    (P : classicalPseudodifferentialOperators (n := n) (M := M) m) :
    (classicalPrincipalSymbolLinearMap n M m P :
      (x : M) → (TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) → ℂ) =
      classicalPrincipalSymbol m P :=
  (rfl)

variable (n M m) in
/-- **The kernel of the principal symbol map** is the classical pseudodifferential operators of
order `m - 1`. -/
theorem ker_classicalPrincipalSymbolLinearMap :
    LinearMap.ker (classicalPrincipalSymbolLinearMap n M m) =
      (classicalPseudodifferentialOperators (m - 1)).comap
        (classicalPseudodifferentialOperators m).subtype := by
  ext P
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
    ← classicalPrincipalSymbol_eq_zero_iff P.property, ← Submodule.coe_eq_zero,
    coe_classicalPrincipalSymbolLinearMap_apply]
  simp only [funext_iff, Pi.zero_apply]

/-! ### Differential operators -/

/-- **The principal symbol of a differential operator.** Let `D` be a differential operator of
order at most `m` on the real-valued smooth functions on `M`, in Grothendieck's sense. At every
nonzero covector `ξ ∈ T*ₓM`, the principal symbol of order `m` of its complexification is
`i ^ m σ(D)(ξ)`, where `σ(D)` is the geometric principal symbol of `D`
(`TauCeti.smoothPrincipalSymbol`): this is the angular-frequency convention `σ(∂ⱼ) = i ξⱼ`. -/
theorem classicalPrincipalSymbol_complexifyLinearMap {m : ℕ}
    {D : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯}
    (hD : D ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯ m) (x : M)
    {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    classicalPrincipalSymbol m (ContMDiffMap.complexifyLinearMap D) x ξ =
      Complex.I ^ m * smoothPrincipalSymbol 𝓘(ℝ, CoordinateSpace n)
        BoundarylessManifold.isInteriorPoint ⟨D, hD⟩ ξ := by
  set e := chartAt (CoordinateSpace n) x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source _ x
  set χ := (exists_cutoff_chartAt (n := n) x).choose
  have hχ : χ (e x) = 1 := (exists_cutoff_chartAt (n := n) x).choose_spec.self_of_nhds
  -- The chart frequency `η` of `ξ`, which is nonzero since `⟪η, ·⟫ ∘ de_x = ξ`.
  set η := (InnerProductSpace.toDual ℝ (CoordinateSpace n)).symm
    (ξ.comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e x).inverse)
  have he₁ : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  have hηξ := innerSL_toDual_symm_comp_inverse_mvfderiv he₁ hx ξ
  have hη : η ≠ 0 := toDual_symm_comp_inverse_mvfderiv_ne_zero he₁ hx hξ
  -- Compare the two descriptions of the principal symbol of the polynomial symbol of `D` in `e`.
  have h₁ := coefficient_principal_eq_classicalPrincipalSymbol
    (complexifyLinearMap_mem_classicalPseudodifferentialOperators hD) he χ χ
    (ClassicalSymbol.quantizeSchwartzValue_ofDifferentialOperator_eq_complexChartCompression he χ χ
      ⟨D, hD⟩) hx η
  have h₂ := ClassicalSymbol.coefficient_principal_ofDifferentialOperator_chartCompression
    (V := ℂ) he χ χ ⟨D, hD⟩ (e.map_source hx) hη
  -- `mvfderiv` is `mfderiv` followed by the identification of the tangent spaces of `ℝⁿ` with
  -- `ℝⁿ`, which is the identity.
  have hmv : (innerSL ℝ η).comp (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) e x) =
      (innerSL ℝ η).comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e x) := by
    ext v
    exact congrArg (innerSL ℝ η) (mvfderiv_apply_eq_mfderiv_apply _ x v).symm
  rw [e.left_inv hx, hmv] at h₂
  rw [h₁, hηξ, hχ] at h₂
  have h := congrArg (fun L : ℂ →L[ℂ] ℂ ↦ L 1) h₂
  simpa [hχ] using h

/-! ### Invariance under diffeomorphisms -/

section Diffeomorph

variable {N : Type*} [TopologicalSpace N] [ChartedSpace (CoordinateSpace n) N] [T2Space N]
  [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ N]

/-- **Naturality of the principal symbol under diffeomorphisms.** Transport an operator `P` on `M`
to `N` along a diffeomorphism `Φ : N → M`, by conjugation `f ↦ (P (f ∘ Φ⁻¹)) ∘ Φ` with the
pullback. Its principal symbol of order `m` at `y` on the pullback `η ∘ dΦ_y` of a covector `η` at
`Φ y` is the principal symbol of `P` at `Φ y` on `η`:

`σ_m(Φ^* P)(y, η ∘ dΦ_y) = σ_m(P)(Φ y, η)`.

So the principal symbol transforms as a function on the cotangent bundle. When `P` is not a
classical pseudodifferential operator of order `m`, neither is its transport, and both sides
are `0`. -/
theorem classicalPrincipalSymbol_conj
    (Φ : N ≃ₘ⟮𝓘(ℝ, CoordinateSpace n), 𝓘(ℝ, CoordinateSpace n)⟯ M)
    (P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (y : N)
    (η : TangentSpace 𝓘(ℝ, CoordinateSpace n) (Φ y) →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (Φ.compRightComplexAlgEquiv.toLinearEquiv.conj P) y
        (η.comp (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) Φ y)) =
      classicalPrincipalSymbol m P (Φ y) η := by
  by_cases hP : P ∈ classicalPseudodifferentialOperators m
  swap
  · rw [classicalPrincipalSymbol_of_notMem hP, classicalPrincipalSymbol_of_notMem
      ((conj_mem_classicalPseudodifferentialOperators_iff Φ).not.2 hP)]
  have hQ := conj_mem_classicalPseudodifferentialOperators Φ hP
  -- The preferred chart `e` at `y`, its cutoff `χ`, and the chart `e' = e ∘ Φ⁻¹` of `M` at `Φ y`.
  set e := chartAt (CoordinateSpace n) y
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ N :=
    IsManifold.chart_mem_maximalAtlas y
  have hy : y ∈ e.source := mem_chart_source _ y
  set e' := Φ.symm.toHomeomorph.transOpenPartialHomeomorph e
  have he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    Φ.symm.transOpenPartialHomeomorph_mem_maximalAtlas le_rfl he
  have hy' : Φ y ∈ e'.source := by simpa [e'] using hy
  have he'y : e' (Φ y) = e y := by simp [e']
  set χ := (exists_cutoff_chartAt (n := n) y).choose
  have hχ : χ (e y) = 1 := (exists_cutoff_chartAt (n := n) y).choose_spec.self_of_nhds
  -- The chart symbol of the transport of `P` in `e` is also the chart symbol of `P` in `e'`.
  have ha := isChartSymbol_chartSymbol hQ he χ χ
  have ha' : IsChartSymbol P he' χ χ (chartSymbol hQ he χ χ) := fun u x ↦ (ha u x).trans
    (DFunLike.congr_fun (LinearMap.congr_fun (e.complexChartCompression_conj he Φ χ χ P) _) x)
  -- The chart frequency `ζ` of `η ∘ dΦ_y` in `e` is also the chart frequency of `η` in `e'`.
  set ζ := (InnerProductSpace.toDual ℝ (CoordinateSpace n)).symm
    ((η.comp (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) Φ y)).comp
      (mvfderiv 𝓘(ℝ, CoordinateSpace n) e y).inverse)
  have hζ := innerSL_toDual_symm_comp_inverse_mvfderiv
    (IsManifold.maximalAtlas_subset_of_le (by simp) he) hy
    (η.comp (mfderiv 𝓘(ℝ, CoordinateSpace n) 𝓘(ℝ, CoordinateSpace n) Φ y))
  -- `d(e')_{Φ y} = de_y ∘ dΦ⁻¹_{Φ y}`, compared on vectors since the tangent spaces at
  -- `Φ⁻¹ (Φ y)` and at `y` agree only up to `Φ.symm_apply_apply`.
  have hζ' : (innerSL ℝ ζ).comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e' (Φ y)) = η := by
    ext v
    rw [ContinuousLinearMap.comp_apply, show ⇑e' = e ∘ Φ.symm by simp [e'],
      mvfderiv_comp_apply_of_eq _ (mdifferentiableAt_of_mem_maximalAtlas
        (IsManifold.maximalAtlas_subset_of_le (by simp) he) hy)
        ((Φ.symm.mdifferentiable (by simp)) _) (Φ.symm_apply_apply y)]
    exact (DFunLike.congr_fun hζ _).trans
      (congrArg η (Φ.mfderiv_apply_mfderiv_symm_apply (by simp) y v))
  -- Read the principal symbol of this chart symbol at `(e y, ζ)` in both charts.
  have h₁ := coefficient_principal_eq_classicalPrincipalSymbol hQ he χ χ ha hy ζ
  have h₂ := coefficient_principal_eq_classicalPrincipalSymbol hP he' χ χ ha' hy' ζ
  -- In `h₂` the cutoff `χ` is read as a test function on the target of `e'`.
  have hχ' : DFunLike.coe (F := 𝓓(⟨e'.target, e'.open_target⟩, ℝ)) χ (e' (Φ y)) = 1 := by
    rw [he'y]
    exact hχ
  rw [hχ', he'y, h₁, hζ, hζ', hχ] at h₂
  have h := congrArg (fun L : ℂ →L[ℂ] ℂ ↦ L 1) h₂
  simpa using h

end Diffeomorph

end TauCeti
