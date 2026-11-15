/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Conormal.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Prod

/-!
# Conormal sets of products and slices

Under the canonical diffeomorphism `TauCeti.CotangentBundle.prodDiffeomorph` identifying
`T*(M₁ × M₂)` with `T*M₁ × T*M₂`, the splitting `TauCeti.CotangentBundle.cotangentRel_prodMap_iff`
of the cotangent relation of a product map yields componentwise descriptions of conormal sets:

* `TauCeti.CotangentBundle.image_prodDiffeomorph_conormal_prodMap`: `prodDiffeomorph` carries the
  conormal set of `Prod.map i₁ i₂` onto `conormal J₁ I₁ i₁ ×ˢ conormal J₂ I₂ i₂`.
* `TauCeti.CotangentBundle.image_prodDiffeomorph_conormal_prodMkLeft` and
  `TauCeti.CotangentBundle.image_prodDiffeomorph_conormal_prodMkRight`: the conormal set of a
  slice `M₁ × {y₀}` or `{x₀} × M₂` corresponds to the product of the zero section on the varying
  factor with the cotangent fibre over the fixed coordinate.

No finite-dimensionality or boundarylessness assumptions are needed.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 3.3.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 11.
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace TauCeti.CotangentBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ E₂ F₁ F₂ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {H₁ H₂ G₁ G₂ : Type*}
  [TopologicalSpace H₁] [TopologicalSpace H₂]
  [TopologicalSpace G₁] [TopologicalSpace G₂]
  {I₁ : ModelWithCorners 𝕜 E₁ H₁} {I₂ : ModelWithCorners 𝕜 E₂ H₂}
  {J₁ : ModelWithCorners 𝕜 F₁ G₁} {J₂ : ModelWithCorners 𝕜 F₂ G₂}
  {M₁ M₂ Q₁ Q₂ : Type*}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [TopologicalSpace Q₁] [ChartedSpace G₁ Q₁]
  [TopologicalSpace Q₂] [ChartedSpace G₂ Q₂]

section ProductMap

variable [IsManifold I₁ 2 M₁] [IsManifold I₂ 2 M₂]
  [IsManifold J₁ 2 Q₁] [IsManifold J₂ 2 Q₂]

/-- A covector `w` on `M₁ × M₂` is conormal to `Prod.map i₁ i₂` if and only if `prodDiffeomorph w`
lies in the product of the conormal sets of `i₁` and `i₂`. -/
theorem prodDiffeomorph_mem_prod_conormal_iff {i₁ : Q₁ → M₁} {i₂ : Q₂ → M₂}
    (hi₁ : MDifferentiable J₁ I₁ i₁) (hi₂ : MDifferentiable J₂ I₂ i₂)
    (w : CotangentBundle (I₁.prod I₂) (M₁ × M₂)) :
    prodDiffeomorph I₁ I₂ M₁ M₂ w ∈ conormal J₁ I₁ i₁ ×ˢ conormal J₂ I₂ i₂ ↔
      w ∈ conormal (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) := by
  simp only [mem_prod, mem_conormal_iff_exists_cotangentRel, Prod.exists]
  refine ⟨fun ⟨⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩⟩ ↦ ⟨q₁, q₂, ?_⟩, fun ⟨q₁, q₂, hq⟩ ↦ ?_⟩
  · rw [cotangentRel_prodMap_iff _ w (hi₁ q₁) (hi₂ q₂), prodDiffeomorph_zeroSection]
    exact ⟨hq₁, hq₂⟩
  · rw [cotangentRel_prodMap_iff _ w (hi₁ q₁) (hi₂ q₂), prodDiffeomorph_zeroSection] at hq
    exact ⟨⟨q₁, hq.1⟩, ⟨q₂, hq.2⟩⟩

/-- **The conormal set of a product map is the product of the conormal sets.** -/
@[simp]
theorem image_prodDiffeomorph_conormal_prodMap {i₁ : Q₁ → M₁} {i₂ : Q₂ → M₂}
    (hi₁ : MDifferentiable J₁ I₁ i₁) (hi₂ : MDifferentiable J₂ I₂ i₂) :
    prodDiffeomorph I₁ I₂ M₁ M₂ '' conormal (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) =
      conormal J₁ I₁ i₁ ×ˢ conormal J₂ I₂ i₂ := by
  ext p
  refine ⟨fun ⟨w, hw, hwp⟩ ↦ hwp ▸ (prodDiffeomorph_mem_prod_conormal_iff hi₁ hi₂ w).mpr hw,
    fun hp ↦ ⟨(prodDiffeomorph I₁ I₂ M₁ M₂).symm p,
      (prodDiffeomorph_mem_prod_conormal_iff hi₁ hi₂ _).mp
        (by rwa [(prodDiffeomorph I₁ I₂ M₁ M₂).apply_symm_apply]),
      (prodDiffeomorph I₁ I₂ M₁ M₂).apply_symm_apply p⟩⟩

/-- The inverse of `prodDiffeomorph` carries the product of two conormal sets onto the conormal set
of the product map. -/
@[simp]
theorem symm_image_prodDiffeomorph_conormal {i₁ : Q₁ → M₁} {i₂ : Q₂ → M₂}
    (hi₁ : MDifferentiable J₁ I₁ i₁) (hi₂ : MDifferentiable J₂ I₂ i₂) :
    (prodDiffeomorph I₁ I₂ M₁ M₂).symm '' (conormal J₁ I₁ i₁ ×ˢ conormal J₂ I₂ i₂) =
      conormal (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) := by
  rw [← image_prodDiffeomorph_conormal_prodMap hi₁ hi₂, Set.image_image]; simp

end ProductMap

section Slices

variable [IsManifold I₁ 2 M₁] [IsManifold I₂ 2 M₂]

/-- **Conormal set of a horizontal slice `M₁ × {y₀}`.** Under `prodDiffeomorph`, the conormal set
of `x ↦ (x, y₀)` is the product of the zero section of `T*M₁` with the cotangent fibre over
`y₀`. -/
@[simp]
theorem image_prodDiffeomorph_conormal_prodMkLeft (y₀ : M₂) :
    prodDiffeomorph I₁ I₂ M₁ M₂ '' conormal I₁ (I₁.prod I₂) (fun x : M₁ ↦ (x, y₀)) =
      range (zeroSection (E₁ →L[𝕜] 𝕜) (fun x : M₁ ↦ TangentSpace I₁ x →L[𝕜] 𝕜)) ×ˢ
        (π (E₂ →L[𝕜] 𝕜) (fun y : M₂ ↦ TangentSpace I₂ y →L[𝕜] 𝕜) ⁻¹' {y₀}) := by
  have : Nonempty M₂ := ⟨y₀⟩
  have hslice : conormal I₁ (I₁.prod I₂) (fun x : M₁ ↦ (x, y₀)) =
      conormal (I₁.prod I₂) (I₁.prod I₂) (Prod.map (id : M₁ → M₁) fun _ : M₂ ↦ y₀) :=
    (conormal_comp_of_surjective (g := Prod.fst) (i := fun x : M₁ ↦ (x, y₀))
      mdifferentiable_fst (mdifferentiable_id.prodMk mdifferentiable_const)
      (fun x ↦ ⟨(x, y₀), rfl⟩) fun p u ↦ ⟨(u, 0), by rw [mfderiv_fst]; rfl⟩).symm
  rw [hslice, image_prodDiffeomorph_conormal_prodMap mdifferentiable_id mdifferentiable_const,
    conormal_id, conormal_const]

/-- **Conormal set of a vertical slice `{x₀} × M₂`.** Under `prodDiffeomorph`, the conormal set of
`y ↦ (x₀, y)` is the product of the cotangent fibre over `x₀` with the zero section of `T*M₂`. -/
@[simp]
theorem image_prodDiffeomorph_conormal_prodMkRight (x₀ : M₁) :
    prodDiffeomorph I₁ I₂ M₁ M₂ '' conormal I₂ (I₁.prod I₂) (fun y : M₂ ↦ (x₀, y)) =
      (π (E₁ →L[𝕜] 𝕜) (fun x : M₁ ↦ TangentSpace I₁ x →L[𝕜] 𝕜) ⁻¹' {x₀}) ×ˢ
        range (zeroSection (E₂ →L[𝕜] 𝕜) (fun y : M₂ ↦ TangentSpace I₂ y →L[𝕜] 𝕜)) := by
  have : Nonempty M₁ := ⟨x₀⟩
  have hslice : conormal I₂ (I₁.prod I₂) (fun y : M₂ ↦ (x₀, y)) =
      conormal (I₁.prod I₂) (I₁.prod I₂) (Prod.map (fun _ : M₁ ↦ x₀) (id : M₂ → M₂)) :=
    (conormal_comp_of_surjective (g := Prod.snd) (i := fun y : M₂ ↦ (x₀, y))
      mdifferentiable_snd (mdifferentiable_const.prodMk mdifferentiable_id)
      (fun y ↦ ⟨(x₀, y), rfl⟩) fun p u ↦ ⟨(0, u), by rw [mfderiv_snd]; rfl⟩).symm
  rw [hslice, image_prodDiffeomorph_conormal_prodMap mdifferentiable_const mdifferentiable_id,
    conormal_const, conormal_id]

end Slices

end TauCeti.CotangentBundle
