/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Complex.FirstChernClass
public import TauCeti.Topology.VectorBundle.Orientation.DisjointZeros

/-!
# Additivity of the first Chern class from sections with disjoint zero sets

Let `L₁`, `L₂` and `L₃` be complex line bundles over a base `B`, with continuous sections `s₁`,
`s₂` and `s₃`. Suppose that the zeros of `s₁` and `s₂` lie in disjoint closed sets `Z₁` and `Z₂`,
and that off `Z₂` complex-linear isomorphisms `L₁ ≃ L₃` carry `s₁` to `s₃`, and off `Z₁`
complex-linear isomorphisms `L₂ ≃ L₃` carry `s₂` to `s₃`. Then

`c₁(L₃) = c₁(L₁) + c₁(L₂)`

(`TauCeti.lineFirstChernClass_eq_add_of_disjoint`), and more generally
`e(E₃) = e(E₁) + e(E₂)` for the Euler classes of complex vector bundles of any common rank
(`TauCeti.complexEulerClass_eq_add_of_disjoint`).

For `L₃ = L₁ ⊗ L₂` and `s₃ = s₁ ⊗ s₂` the isomorphisms are `v ↦ v ⊗ s₂(b)` off `Z₂` and
`w ↦ s₁(b) ⊗ w` off `Z₁`, so this is the additivity `c₁(L₁ ⊗ L₂) = c₁(L₁) + c₁(L₂)` for lines
having sections with disjoint zero sets. It is the complex case of
`TauCeti.VectorBundleOrientation.eulerClass_eq_add_of_disjoint`: complex-linear isomorphisms
preserve the complex orientations (`TauCeti.VectorBundleOrientation.map_complex`). Only the values
of the isomorphisms off `Z₂`, resp. off `Z₁`, enter the hypotheses.

## Main results

* `TauCeti.complexEulerClass_eq_add_of_disjoint`: `e(E₃) = e(E₁) + e(E₂)`.
* `TauCeti.lineFirstChernClass_eq_add_of_disjoint`: `c₁(L₃) = c₁(L₁) + c₁(L₂)`.

## References

* R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics 82,
  Springer (1982), §20 (the first Chern class of a tensor product of line bundles).
-/

public section

noncomputable section

open Bundle Module Set

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {r : ℕ}
  {F₁ : Type w} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedSpace ℂ F₁]
  [IsScalarTower ℝ ℂ F₁] [FiniteDimensional ℂ F₁]
  {E₁ : B → Type w} [TopologicalSpace (TotalSpace F₁ E₁)] [∀ b, AddCommGroup (E₁ b)]
  [∀ b, Module ℝ (E₁ b)] [∀ b, Module ℂ (E₁ b)] [∀ b, IsScalarTower ℝ ℂ (E₁ b)]
  [∀ b, TopologicalSpace (E₁ b)] [FiberBundle F₁ E₁] [VectorBundle ℂ F₁ E₁]
  {F₂ : Type w} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedSpace ℂ F₂]
  [IsScalarTower ℝ ℂ F₂] [FiniteDimensional ℂ F₂]
  {E₂ : B → Type w} [TopologicalSpace (TotalSpace F₂ E₂)] [∀ b, AddCommGroup (E₂ b)]
  [∀ b, Module ℝ (E₂ b)] [∀ b, Module ℂ (E₂ b)] [∀ b, IsScalarTower ℝ ℂ (E₂ b)]
  [∀ b, TopologicalSpace (E₂ b)] [FiberBundle F₂ E₂] [VectorBundle ℂ F₂ E₂]
  {F₃ : Type w} [NormedAddCommGroup F₃] [NormedSpace ℝ F₃] [NormedSpace ℂ F₃]
  [IsScalarTower ℝ ℂ F₃] [FiniteDimensional ℂ F₃]
  {E₃ : B → Type w} [TopologicalSpace (TotalSpace F₃ E₃)] [∀ b, AddCommGroup (E₃ b)]
  [∀ b, Module ℝ (E₃ b)] [∀ b, Module ℂ (E₃ b)] [∀ b, IsScalarTower ℝ ℂ (E₃ b)]
  [∀ b, TopologicalSpace (E₃ b)] [FiberBundle F₃ E₃] [VectorBundle ℂ F₃ E₃]

local instance instVectorBundleRealDisjointZeros₁ : VectorBundle ℝ F₁ E₁ :=
  VectorBundle.restrictScalars ℝ ℂ F₁ E₁

local instance instVectorBundleRealDisjointZeros₂ : VectorBundle ℝ F₂ E₂ :=
  VectorBundle.restrictScalars ℝ ℂ F₂ E₂

local instance instVectorBundleRealDisjointZeros₃ : VectorBundle ℝ F₃ E₃ :=
  VectorBundle.restrictScalars ℝ ℂ F₃ E₃

/-- **Euler classes of complex bundles from sections with disjoint zero sets.** Let `s₁`, `s₂` and
`s₃` be continuous sections of complex vector bundles `E₁`, `E₂` and `E₃` of complex rank `r + 1`,
with `s₁` nonzero off `Z₁` and `s₂` nonzero off `Z₂`, for disjoint closed sets `Z₁` and `Z₂`.
If off `Z₂` complex-linear isomorphisms `φ₁ b : E₁ b ≃ E₃ b`, continuous on the total space there,
carry `s₁` to `s₃`, and off `Z₁` such isomorphisms `φ₂ b : E₂ b ≃ E₃ b` carry `s₂` to `s₃`, then
`e(E₃) = e(E₁) + e(E₂)`. -/
theorem complexEulerClass_eq_add_of_disjoint (hF₁ : finrank ℂ F₁ = r + 1)
    (hF₂ : finrank ℂ F₂ = r + 1) (hF₃ : finrank ℂ F₃ = r + 1) {Z₁ Z₂ : Set B}
    (hZ₁ : IsClosed Z₁) (hZ₂ : IsClosed Z₂) (hZ : Disjoint Z₁ Z₂) {s₁ : ∀ b, E₁ b}
    (hs₁ : Continuous fun b ↦ TotalSpace.mk' F₁ b (s₁ b)) (hs₁₀ : ∀ b ∉ Z₁, s₁ b ≠ 0)
    {s₂ : ∀ b, E₂ b} (hs₂ : Continuous fun b ↦ TotalSpace.mk' F₂ b (s₂ b))
    (hs₂₀ : ∀ b ∉ Z₂, s₂ b ≠ 0) {s₃ : ∀ b, E₃ b}
    (hs₃ : Continuous fun b ↦ TotalSpace.mk' F₃ b (s₃ b)) {φ₁ : ∀ b, E₁ b ≃L[ℂ] E₃ b}
    (hφ₁ : ContinuousOn (fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₃ v.proj (φ₁ v.proj v.snd))
      (π F₁ E₁ ⁻¹' Z₂ᶜ))
    (hs₁₃ : ∀ b ∉ Z₂, φ₁ b (s₁ b) = s₃ b) {φ₂ : ∀ b, E₂ b ≃L[ℂ] E₃ b}
    (hφ₂ : ContinuousOn (fun v : TotalSpace F₂ E₂ ↦ TotalSpace.mk' F₃ v.proj (φ₂ v.proj v.snd))
      (π F₂ E₂ ⁻¹' Z₁ᶜ))
    (hs₂₃ : ∀ b ∉ Z₁, φ₂ b (s₂ b) = s₃ b) :
    complexEulerClass F₃ E₃ hF₃ = complexEulerClass F₁ E₁ hF₁ + complexEulerClass F₂ E₂ hF₂ := by
  rw [complexEulerClass_def, complexEulerClass_def, complexEulerClass_def]
  exact VectorBundleOrientation.eulerClass_eq_add_of_disjoint _ _ _ _ _ _ hZ₁ hZ₂ hZ hs₁ hs₁₀
    hs₂ hs₂₀ hs₃ (φ₁ := fun b ↦ (φ₁ b).restrictScalars' ℝ)
    (by simpa only [ContinuousLinearEquiv.coe_restrictScalars'] using hφ₁)
    (fun b _ ↦ VectorBundleOrientation.map_reindex_complex hF₃ hF₁ (φ₁ b))
    (by simpa only [ContinuousLinearEquiv.coe_restrictScalars'] using hs₁₃)
    (φ₂ := fun b ↦ (φ₂ b).restrictScalars' ℝ)
    (by simpa only [ContinuousLinearEquiv.coe_restrictScalars'] using hφ₂)
    (fun b _ ↦ VectorBundleOrientation.map_reindex_complex hF₃ hF₂ (φ₂ b))
    (by simpa only [ContinuousLinearEquiv.coe_restrictScalars'] using hs₂₃)

/-- **Additivity of the first Chern class from sections with disjoint zero sets.** Let `s₁`, `s₂`
and `s₃` be continuous sections of complex line bundles `L₁`, `L₂` and `L₃`, with `s₁` nonzero off
`Z₁` and `s₂` nonzero off `Z₂`, for disjoint closed sets `Z₁` and `Z₂`. If off `Z₂`
complex-linear isomorphisms `L₁ b ≃ L₃ b`, continuous on the total space there, carry `s₁` to `s₃`,
and off `Z₁` complex-linear isomorphisms `L₂ b ≃ L₃ b` carry `s₂` to `s₃`, then
`c₁(L₃) = c₁(L₁) + c₁(L₂)`. For `L₃ = L₁ ⊗ L₂` and `s₃ = s₁ ⊗ s₂` these isomorphisms are
`v ↦ v ⊗ s₂ b` and `w ↦ s₁ b ⊗ w`. -/
theorem lineFirstChernClass_eq_add_of_disjoint (hF₁ : finrank ℂ F₁ = 1)
    (hF₂ : finrank ℂ F₂ = 1) (hF₃ : finrank ℂ F₃ = 1) {Z₁ Z₂ : Set B}
    (hZ₁ : IsClosed Z₁) (hZ₂ : IsClosed Z₂) (hZ : Disjoint Z₁ Z₂) {s₁ : ∀ b, E₁ b}
    (hs₁ : Continuous fun b ↦ TotalSpace.mk' F₁ b (s₁ b)) (hs₁₀ : ∀ b ∉ Z₁, s₁ b ≠ 0)
    {s₂ : ∀ b, E₂ b} (hs₂ : Continuous fun b ↦ TotalSpace.mk' F₂ b (s₂ b))
    (hs₂₀ : ∀ b ∉ Z₂, s₂ b ≠ 0) {s₃ : ∀ b, E₃ b}
    (hs₃ : Continuous fun b ↦ TotalSpace.mk' F₃ b (s₃ b)) {φ₁ : ∀ b, E₁ b ≃L[ℂ] E₃ b}
    (hφ₁ : ContinuousOn (fun v : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₃ v.proj (φ₁ v.proj v.snd))
      (π F₁ E₁ ⁻¹' Z₂ᶜ))
    (hs₁₃ : ∀ b ∉ Z₂, φ₁ b (s₁ b) = s₃ b) {φ₂ : ∀ b, E₂ b ≃L[ℂ] E₃ b}
    (hφ₂ : ContinuousOn (fun v : TotalSpace F₂ E₂ ↦ TotalSpace.mk' F₃ v.proj (φ₂ v.proj v.snd))
      (π F₂ E₂ ⁻¹' Z₁ᶜ))
    (hs₂₃ : ∀ b ∉ Z₁, φ₂ b (s₂ b) = s₃ b) :
    lineFirstChernClass F₃ E₃ hF₃ =
      lineFirstChernClass F₁ E₁ hF₁ + lineFirstChernClass F₂ E₂ hF₂ := by
  rw [lineFirstChernClass_def, lineFirstChernClass_def, lineFirstChernClass_def]
  exact complexEulerClass_eq_add_of_disjoint hF₁ hF₂ hF₃ hZ₁ hZ₂ hZ hs₁ hs₁₀ hs₂ hs₂₀ hs₃ hφ₁
    hs₁₃ hφ₂ hs₂₃

end TauCeti
