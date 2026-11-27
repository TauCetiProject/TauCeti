/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Trivial.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Transport
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Prod

/-!
# Reduction of the Cauchy–Riemann index to line bundles

Let `M` be a complex curve without boundary with a finite bundle atlas `A` of a complex vector
bundle `V` (so `M` is compact). This file reduces the index of a smooth real Cauchy–Riemann
operator on `V` to that of an operator on a line bundle, following McDuff–Salamon, proof of
Theorem C.1.10, steps 1 and 2:

* if `V` is isomorphic to a direct sum `V₁ ×ᵇ V₂`, then the realization `W^{1,p} → Lᵖ` of a smooth
  real Cauchy–Riemann operator on `V` has the sum of the indices of the realizations of any smooth
  real Cauchy–Riemann operators on `V₁` and `V₂`
  (`TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_eq_add_of_bundleEquiv`);
* on the trivial bundle with fibre `ℂᵐ`, the index is `m` times the index of `∂bar` on functions
  (`TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_trivial_pi`);
* hence if `V ≅ ℂᵐ ⊕ L`, the index on `V` is the index of any smooth real Cauchy–Riemann operator
  on `L` plus `m` times the index of `∂bar` on functions
  (`TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_eq_mul_add_of_bundleEquiv_trivialProd`).

The proofs combine invariance of the index under the choice of operator
(`TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_eq`), under bundle isomorphisms
(`TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_sectionTransport`) and additivity under direct
sums (`TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_prod`). All Sobolev spaces are built on
the charts of `A` (`TauCeti.FiniteBundleAtlas.ofBaseSet`), which for the trivial bundle needs no
condition on the chart domains (`TauCeti.FiniteBundleAtlas.closure_dom_subset_baseSet_trivial`).

With a splitting `V ≅ ℂⁿ⁻¹ ⊕ L`, this reduces the Riemann–Roch index formula on `V` to the line
bundle `L` and to `∂bar` on functions.

## Main results

* `TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_eq_add_of_bundleEquiv`: the index on a
  bundle isomorphic to a direct sum is the sum of the indices on the summands.
* `TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_trivial_pi`: the index on the trivial bundle
  with fibre `ℂᵐ` is `m` times the index of `∂bar` on functions.
* `TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_eq_mul_add_of_bundleEquiv_trivialProd`: the
  index on a bundle isomorphic to `ℂᵐ ⊕ L`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Theorem C.1.10 and its proof, steps 1 and 2.
-/

public section

noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

open SmoothAlmostComplexStructure

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedSpace ℂ F₁]
  [IsScalarTower ℝ ℂ F₁] [FiniteDimensional ℝ F₁]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, AddCommGroup (V₁ x)]
  [∀ x, Module ℝ (V₁ x)] [∀ x, Module ℂ (V₁ x)] [∀ x, IsScalarTower ℝ ℂ (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [∀ x, IsTopologicalAddGroup (V₁ x)]
  [∀ x, ContinuousSMul ℝ (V₁ x)] [FiberBundle F₁ V₁] [VectorBundle ℂ F₁ V₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedSpace ℂ F₂]
  [IsScalarTower ℝ ℂ F₂] [FiniteDimensional ℝ F₂]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, AddCommGroup (V₂ x)]
  [∀ x, Module ℝ (V₂ x)] [∀ x, Module ℂ (V₂ x)] [∀ x, IsScalarTower ℝ ℂ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
  [∀ x, ContinuousSMul ℝ (V₂ x)] [FiberBundle F₂ V₂] [VectorBundle ℂ F₂ V₂]

local instance instVectorBundleRealSplitting : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

local instance instVectorBundleRealSplitting₁ : VectorBundle ℝ F₁ V₁ :=
  VectorBundle.restrictScalars ℝ ℂ F₁ V₁

local instance instVectorBundleRealSplitting₂ : VectorBundle ℝ F₂ V₂ :=
  VectorBundle.restrictScalars ℝ ℂ F₂ V₂

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] [ContMDiffVectorBundle ∞ F₁ V₁ 𝓘(ℝ, ℂ)]
  [ContMDiffVectorBundle ∞ F₂ V₂ 𝓘(ℝ, ℂ)]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace IsRealCauchyRiemannOperator

/-- **The index on a bundle isomorphic to a direct sum** (McDuff–Salamon, proof of Theorem C.1.10,
step 1). Let `Φ : V ≃ V₁ ×ᵇ V₂` be a smooth isomorphism of complex vector bundles over a closed
surface. Then for `1 < p < ∞` the realization `W^{1,p} → Lᵖ` of a smooth real Cauchy–Riemann
operator on `V` has the sum of the indices of the realizations of any smooth real Cauchy–Riemann
operators on `V₁` and `V₂`, all on the charts of the same atlas `A`. -/
theorem index_sobolevL_eq_add_of_bundleEquiv (A : FiniteBundleAtlas ℂ M F V)
    (h₁ : ∀ i, closure (A.dom i) ⊆ (trivializationAt F₁ V₁ (A.center i)).baseSet)
    (h₂ : ∀ i, closure (A.dom i) ⊆ (trivializationAt F₂ V₂ (A.center i)).baseSet)
    {Φ : ∀ x, V x ≃L[ℂ] (V₁ ×ᵇ V₂) x}
    (hΦ : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F →L[ℝ] F₁ × F₂)) ∞ fun x ↦
      TotalSpace.mk' (F →L[ℝ] F₁ × F₂) (E := fun x ↦ V x →L[ℝ] (V₁ ×ᵇ V₂) x) x
        ((Φ x).restrictScalars' ℝ : V x →L[ℝ] (V₁ ×ᵇ V₂) x))
    {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
    (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
    {D₁ : (Π x : M, V₁ x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V₁ x}
    (hD₁ : IsRealCauchyRiemannOperator F₁ (ofComplexManifold ℂ M) D₁)
    (hD₁s : ContMDiffCovariantDerivativeOn F₁ ∞ D₁ univ)
    {D₂ : (Π x : M, V₂ x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V₂ x}
    (hD₂ : IsRealCauchyRiemannOperator F₂ (ofComplexManifold ℂ M) D₂)
    (hD₂s : ContMDiffCovariantDerivativeOn F₂ ∞ D₂ univ) (hp : 1 < p) (hp_top : p ≠ ⊤) :
    (hD.sobolevL A hDs volume p).index =
      (hD₁.sobolevL (A.ofBaseSet h₁) hD₁s volume p).index +
        (hD₂.sobolevL (A.ofBaseSet h₂) hD₂s volume p).index := by
  have hW : ∀ i, closure (A.dom i) ⊆
      (trivializationAt (F₁ × F₂) (V₁ ×ᵇ V₂) (A.center i)).baseSet :=
    fun i ↦ subset_inter (h₁ i) (h₂ i)
  have hprod := index_sobolevL_prod (A := A.ofBaseSet h₁) (h := h₂) hD₁ hD₂ hD₁s hD₂s p hp hp_top
  rw [FiniteBundleAtlas.ofBaseSet_prod A h₁ h₂ hW,
    FiniteBundleAtlas.ofBaseSet_ofBaseSet (A := A) (h := h₁) h₂ h₂] at hprod
  rw [← index_sobolevL_sectionTransport volume p hΦ A hW hD hDs hp_top]
  exact (index_sobolevL_eq (A.ofBaseSet hW) (hD₁.prod hD₂) (hD₁s.sectionProdMap hD₂s)
    (hD.transport_of_contMDiff hΦ) (hDs.sectionTransport_of_contMDiff hΦ) hp hp_top).trans hprod

/-! ### The trivial bundle -/

section Trivial

/-- **The index on the trivial bundle of rank `m + 1`.** On a closed surface, the realization of
a smooth real Cauchy–Riemann operator on the trivial bundle with fibre `ℂᵐ⁺¹` has the index of
`∂bar` on complex functions plus the index of `∂bar` on functions with values in `ℂᵐ`. -/
private theorem index_sobolevL_trivial_succ {m : ℕ}
    (B : FiniteBundleAtlas ℂ M (Fin (m + 1) → ℂ) (Trivial M (Fin (m + 1) → ℂ)))
    {D : (Π x : M, Trivial M (Fin (m + 1) → ℂ) x) →
      Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] Trivial M (Fin (m + 1) → ℂ) x}
    (hD : IsRealCauchyRiemannOperator (Fin (m + 1) → ℂ) (ofComplexManifold ℂ M) D)
    (hDs : ContMDiffCovariantDerivativeOn (Fin (m + 1) → ℂ) ∞ D univ)
    (hp : 1 < p) (hp_top : p ≠ ⊤) :
    (hD.sobolevL B hDs volume p).index =
      ((ofComplexManifold ℂ M).isRealCauchyRiemannOperator_dbarFunction.sobolevL
        (B.ofBaseSet (B.closure_dom_subset_baseSet_trivial ℂ))
        ((ofComplexManifold ℂ M).contMDiffCovariantDerivativeOn_dbarFunction le_rfl)
        volume p).index +
      ((ofComplexManifold ℂ M).isRealCauchyRiemannOperator_dbarFunction.sobolevL
        (B.ofBaseSet (B.closure_dom_subset_baseSet_trivial (Fin m → ℂ)))
        ((ofComplexManifold ℂ M).contMDiffCovariantDerivativeOn_dbarFunction le_rfl)
        volume p).index := by
  let e : (Fin (m + 1) → ℂ) ≃L[ℂ] ℂ × (Fin m → ℂ) :=
    (Fin.consLinearEquiv ℂ fun _ : Fin (m + 1) ↦ ℂ).symm.toContinuousLinearEquiv
  have hΦ := contMDiff_const_trivialProdHom (B := M) (IB := 𝓘(ℝ, ℂ)) (n := ∞)
    (F₁ := Fin (m + 1) → ℂ) (F₂ := ℂ) (F₃ := Fin m → ℂ) (e.restrictScalars' ℝ)
  have := index_sobolevL_eq_add_of_bundleEquiv (V₁ := Trivial M ℂ) (V₂ := Trivial M (Fin m → ℂ))
    B (B.closure_dom_subset_baseSet_trivial ℂ)
    (B.closure_dom_subset_baseSet_trivial (Fin m → ℂ)) (Φ := fun _ ↦ e) hΦ hD hDs
    (ofComplexManifold ℂ M).isRealCauchyRiemannOperator_dbarFunction
    ((ofComplexManifold ℂ M).contMDiffCovariantDerivativeOn_dbarFunction le_rfl)
    (ofComplexManifold ℂ M).isRealCauchyRiemannOperator_dbarFunction
    ((ofComplexManifold ℂ M).contMDiffCovariantDerivativeOn_dbarFunction le_rfl) hp hp_top
  exact this

/-- **The index on a trivial bundle** (McDuff–Salamon, proof of Theorem C.1.10, step 1). On a
closed surface, the realization `W^{1,p} → Lᵖ`, `1 < p < ∞`, of a smooth real Cauchy–Riemann
operator on the trivial bundle with fibre `ℂᵐ` has `m` times the index of the realization of
`∂bar` on complex functions, on the charts of the same atlas. -/
theorem index_sobolevL_trivial_pi (m : ℕ)
    (B : FiniteBundleAtlas ℂ M (Fin m → ℂ) (Trivial M (Fin m → ℂ)))
    {D : (Π x : M, Trivial M (Fin m → ℂ) x) →
      Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] Trivial M (Fin m → ℂ) x}
    (hD : IsRealCauchyRiemannOperator (Fin m → ℂ) (ofComplexManifold ℂ M) D)
    (hDs : ContMDiffCovariantDerivativeOn (Fin m → ℂ) ∞ D univ)
    (hp : 1 < p) (hp_top : p ≠ ⊤) :
    (hD.sobolevL B hDs volume p).index =
      m * ((ofComplexManifold ℂ M).isRealCauchyRiemannOperator_dbarFunction.sobolevL
        (B.ofBaseSet (B.closure_dom_subset_baseSet_trivial ℂ))
        ((ofComplexManifold ℂ M).contMDiffCovariantDerivativeOn_dbarFunction le_rfl)
        volume p).index := by
  induction m with
  | zero =>
    -- The fibre `ℂ⁰` is isomorphic to `ℂ⁰ × ℂ⁰`, so the index is twice itself.
    let e : (Fin 0 → ℂ) ≃L[ℂ] (Fin 0 → ℂ) × (Fin 0 → ℂ) :=
      (LinearEquiv.ofSubsingleton _ _).toContinuousLinearEquiv
    have hΦ := contMDiff_const_trivialProdHom (B := M) (IB := 𝓘(ℝ, ℂ)) (n := ∞)
      (F₁ := Fin 0 → ℂ) (F₂ := Fin 0 → ℂ) (F₃ := Fin 0 → ℂ) (e.restrictScalars' ℝ)
    have h := index_sobolevL_eq_add_of_bundleEquiv (V₁ := Trivial M (Fin 0 → ℂ))
      (V₂ := Trivial M (Fin 0 → ℂ)) B B.closure_dom_subset_baseSet
      B.closure_dom_subset_baseSet (Φ := fun _ ↦ e) hΦ hD hDs hD hDs hD hDs hp hp_top
    rw [FiniteBundleAtlas.ofBaseSet_self] at h
    rw [Nat.cast_zero, zero_mul]
    omega
  | succ m ih =>
    rw [index_sobolevL_trivial_succ B hD hDs hp hp_top, ih,
      FiniteBundleAtlas.ofBaseSet_ofBaseSet (A := B)
        (h := B.closure_dom_subset_baseSet_trivial (Fin m → ℂ))
        (FiniteBundleAtlas.closure_dom_subset_baseSet_trivial _ ℂ)
        (B.closure_dom_subset_baseSet_trivial ℂ)]
    push_cast
    ring

end Trivial

/-- **Reduction of the index to a line bundle** (McDuff–Salamon, proof of Theorem C.1.10, steps 1
and 2). Let `Φ : V ≃ ℂᵐ ⊕ L` be a smooth isomorphism of complex vector bundles over a closed
surface. Then for `1 < p < ∞` the realization `W^{1,p} → Lᵖ` of a smooth real Cauchy–Riemann
operator on `V` has the index of the realization of any smooth real Cauchy–Riemann operator on `L`
plus `m` times the index of the realization of `∂bar` on complex functions, all on the charts of
the same atlas `A`. -/
theorem index_sobolevL_eq_mul_add_of_bundleEquiv_trivialProd {m : ℕ}
    (A : FiniteBundleAtlas ℂ M F V)
    (h₂ : ∀ i, closure (A.dom i) ⊆ (trivializationAt F₂ V₂ (A.center i)).baseSet)
    {Φ : ∀ x, V x ≃L[ℂ] (Trivial M (Fin m → ℂ) ×ᵇ V₂) x}
    (hΦ : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F →L[ℝ] (Fin m → ℂ) × F₂)) ∞ fun x ↦
      TotalSpace.mk' (F →L[ℝ] (Fin m → ℂ) × F₂)
        (E := fun x ↦ V x →L[ℝ] (Trivial M (Fin m → ℂ) ×ᵇ V₂) x) x
        ((Φ x).restrictScalars' ℝ : V x →L[ℝ] (Trivial M (Fin m → ℂ) ×ᵇ V₂) x))
    {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
    (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
    {D₂ : (Π x : M, V₂ x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V₂ x}
    (hD₂ : IsRealCauchyRiemannOperator F₂ (ofComplexManifold ℂ M) D₂)
    (hD₂s : ContMDiffCovariantDerivativeOn F₂ ∞ D₂ univ) (hp : 1 < p) (hp_top : p ≠ ⊤) :
    (hD.sobolevL A hDs volume p).index =
      m * ((ofComplexManifold ℂ M).isRealCauchyRiemannOperator_dbarFunction.sobolevL
        (A.ofBaseSet (A.closure_dom_subset_baseSet_trivial ℂ))
        ((ofComplexManifold ℂ M).contMDiffCovariantDerivativeOn_dbarFunction le_rfl)
        volume p).index +
        (hD₂.sobolevL (A.ofBaseSet h₂) hD₂s volume p).index := by
  rw [index_sobolevL_eq_add_of_bundleEquiv A
    (A.closure_dom_subset_baseSet_trivial (Fin m → ℂ)) h₂ hΦ hD hDs
    (ofComplexManifold ℂ M).isRealCauchyRiemannOperator_dbarFunction
    ((ofComplexManifold ℂ M).contMDiffCovariantDerivativeOn_dbarFunction le_rfl) hD₂ hD₂s hp hp_top,
    index_sobolevL_trivial_pi m _ _ _ hp hp_top,
    FiniteBundleAtlas.ofBaseSet_ofBaseSet (A := A)
      (h := A.closure_dom_subset_baseSet_trivial (Fin m → ℂ))
      (FiniteBundleAtlas.closure_dom_subset_baseSet_trivial _ ℂ)
      (A.closure_dom_subset_baseSet_trivial ℂ)]

end IsRealCauchyRiemannOperator

end TauCeti
