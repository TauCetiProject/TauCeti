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
`T*(M₁ × M₂)` with `T*M₁ × T*M₂`, cotangent relations and conormal sets split componentwise:

* `TauCeti.CotangentBundle.cotangentRel_prodMap_iff`: the cotangent relation of `Prod.map i₁ i₂`
  holds at `(z, w)` if and only if the cotangent relations of `i₁` and `i₂` hold on the two
  factors of `prodDiffeomorph z` and `prodDiffeomorph w`.
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

private theorem mfderiv_prodMap_comp_prodMkLeft {i₁ : Q₁ → M₁} {i₂ : Q₂ → M₂}
    {q₁ : Q₁} {q₂ : Q₂} (hi₁ : MDifferentiableAt J₁ I₁ i₁ q₁)
    (hi₂ : MDifferentiableAt J₂ I₂ i₂ q₂) (u₁ : TangentSpace J₁ q₁) :
    mfderiv (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) (q₁, q₂)
        (mfderiv J₁ (J₁.prod J₂) (fun q₁' : Q₁ ↦ (q₁', q₂)) q₁ u₁) =
      mfderiv I₁ (I₁.prod I₂) (fun x₁' : M₁ ↦ (x₁', i₂ q₂)) (i₁ q₁)
        (mfderiv J₁ I₁ i₁ q₁ u₁) := by
  have hdiff : MDifferentiableAt (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) (q₁, q₂) :=
    (hi₁.comp (q₁, q₂) mdifferentiableAt_fst).prodMk (hi₂.comp (q₁, q₂) mdifferentiableAt_snd)
  exact (mfderiv_comp_apply q₁ hdiff (mdifferentiableAt_id.prodMk mdifferentiableAt_const) u₁).symm
    |>.trans (mfderiv_comp_apply q₁ (mdifferentiableAt_id.prodMk mdifferentiableAt_const) hi₁ u₁)

private theorem mfderiv_prodMap_comp_prodMkRight {i₁ : Q₁ → M₁} {i₂ : Q₂ → M₂}
    {q₁ : Q₁} {q₂ : Q₂} (hi₁ : MDifferentiableAt J₁ I₁ i₁ q₁)
    (hi₂ : MDifferentiableAt J₂ I₂ i₂ q₂) (u₂ : TangentSpace J₂ q₂) :
    mfderiv (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) (q₁, q₂)
        (mfderiv J₂ (J₁.prod J₂) (fun q₂' : Q₂ ↦ (q₁, q₂')) q₂ u₂) =
      mfderiv I₂ (I₁.prod I₂) (fun x₂' : M₂ ↦ (i₁ q₁, x₂')) (i₂ q₂)
        (mfderiv J₂ I₂ i₂ q₂ u₂) := by
  have hdiff : MDifferentiableAt (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) (q₁, q₂) :=
    (hi₁.comp (q₁, q₂) mdifferentiableAt_fst).prodMk (hi₂.comp (q₁, q₂) mdifferentiableAt_snd)
  exact (mfderiv_comp_apply q₂ hdiff (mdifferentiableAt_const.prodMk mdifferentiableAt_id) u₂).symm
    |>.trans (mfderiv_comp_apply q₂ (mdifferentiableAt_const.prodMk mdifferentiableAt_id) hi₂ u₂)

section ProductMap

variable [IsManifold I₁ 2 M₁] [IsManifold I₂ 2 M₂]
  [IsManifold J₁ 2 Q₁] [IsManifold J₂ 2 Q₂]

/-- **The cotangent relation of a product map splits under `prodDiffeomorph`.** Assuming `i₁` and
`i₂` are differentiable at the two components of `z.proj`, `Prod.map i₁ i₂` relates `z` to `w` if
and only if `i₁` and `i₂` relate the corresponding factors of `prodDiffeomorph z` and
`prodDiffeomorph w`. -/
theorem cotangentRel_prodMap_iff {i₁ : Q₁ → M₁} {i₂ : Q₂ → M₂}
    (z : CotangentBundle (J₁.prod J₂) (Q₁ × Q₂))
    (w : CotangentBundle (I₁.prod I₂) (M₁ × M₂))
    (hi₁ : MDifferentiableAt J₁ I₁ i₁ z.proj.1)
    (hi₂ : MDifferentiableAt J₂ I₂ i₂ z.proj.2) :
    cotangentRel (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) z w ↔
      cotangentRel J₁ I₁ i₁ (prodDiffeomorph J₁ J₂ Q₁ Q₂ z).1
        (prodDiffeomorph I₁ I₂ M₁ M₂ w).1 ∧
      cotangentRel J₂ I₂ i₂ (prodDiffeomorph J₁ J₂ Q₁ Q₂ z).2
        (prodDiffeomorph I₁ I₂ M₁ M₂ w).2 := by
  obtain ⟨⟨q₁, q₂⟩, α⟩ := z
  obtain ⟨⟨x₁, x₂⟩, β⟩ := w
  have hdiff : MDifferentiableAt (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) (q₁, q₂) :=
    (hi₁.comp (q₁, q₂) mdifferentiableAt_fst).prodMk (hi₂.comp (q₁, q₂) mdifferentiableAt_snd)
  rw [prodDiffeomorph_fst, prodDiffeomorph_fst, prodDiffeomorph_snd, prodDiffeomorph_snd]
  simp only [cotangentRel_iff]
  constructor
  · rintro ⟨hproj, hrel⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hproj
    refine ⟨⟨rfl, ContinuousLinearMap.ext fun u₁ ↦ ?_⟩, ⟨rfl, ContinuousLinearMap.ext fun u₂ ↦ ?_⟩⟩
    · exact (DFunLike.congr_fun hrel _).trans
        (congrArg β (mfderiv_prodMap_comp_prodMkLeft hi₁ hi₂ u₁))
    · exact (DFunLike.congr_fun hrel _).trans
        (congrArg β (mfderiv_prodMap_comp_prodMkRight hi₁ hi₂ u₂))
  · rintro ⟨⟨rfl, hrel₁⟩, ⟨rfl, hrel₂⟩⟩
    refine ⟨rfl, ContinuousLinearMap.ext fun v ↦ ?_⟩
    rw [ContinuousLinearMap.comp_apply]
    have hz := snd_apply_eq_prodDiffeomorph_add (I := J₁) (J := J₂) ⟨(q₁, q₂), α⟩ v
    have hw := snd_apply_eq_prodDiffeomorph_add (I := I₁) (J := I₂) ⟨(i₁ q₁, i₂ q₂), β⟩
      (mfderiv (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) (q₁, q₂) v)
    rw [prodDiffeomorph_fst, prodDiffeomorph_snd] at hz hw
    dsimp only at hz hw
    rw [hz, hw]
    have h₁ : mfderiv (I₁.prod I₂) I₁ Prod.fst (i₁ q₁, i₂ q₂)
        (mfderiv (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) (q₁, q₂) v) =
        mfderiv J₁ I₁ i₁ q₁ (mfderiv (J₁.prod J₂) J₁ Prod.fst (q₁, q₂) v) :=
      (mfderiv_comp_apply (q₁, q₂) (mdifferentiableAt_fst (x := (i₁ q₁, i₂ q₂))) hdiff v).symm
        |>.trans (mfderiv_comp_apply (q₁, q₂) hi₁ mdifferentiableAt_fst v)
    have h₂ : mfderiv (I₁.prod I₂) I₂ Prod.snd (i₁ q₁, i₂ q₂)
        (mfderiv (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) (q₁, q₂) v) =
        mfderiv J₂ I₂ i₂ q₂ (mfderiv (J₁.prod J₂) J₂ Prod.snd (q₁, q₂) v) :=
      (mfderiv_comp_apply (q₁, q₂) (mdifferentiableAt_snd (x := (i₁ q₁, i₂ q₂))) hdiff v).symm
        |>.trans (mfderiv_comp_apply (q₁, q₂) hi₂ mdifferentiableAt_snd v)
    rw [h₁, h₂]
    exact congrArg₂ (· + ·) (DFunLike.congr_fun hrel₁ _) (DFunLike.congr_fun hrel₂ _)

/-- A covector `w` on `M₁ × M₂` is conormal to `Prod.map i₁ i₂` if and only if `prodDiffeomorph w`
lies in the product of the conormal sets of `i₁` and `i₂`. -/
theorem prodDiffeomorph_mem_prod_conormal_iff {i₁ : Q₁ → M₁} {i₂ : Q₂ → M₂}
    (hi₁ : MDifferentiable J₁ I₁ i₁) (hi₂ : MDifferentiable J₂ I₂ i₂)
    (w : CotangentBundle (I₁.prod I₂) (M₁ × M₂)) :
    prodDiffeomorph I₁ I₂ M₁ M₂ w ∈ conormal J₁ I₁ i₁ ×ˢ conormal J₂ I₂ i₂ ↔
      w ∈ conormal (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) := by
  simp only [mem_prod, mem_conormal_iff_exists_cotangentRel]
  constructor
  · rintro ⟨⟨q₁, hq₁⟩, ⟨q₂, hq₂⟩⟩
    refine ⟨(q₁, q₂), ?_⟩
    rw [cotangentRel_prodMap_iff _ w (hi₁ q₁) (hi₂ q₂), prodDiffeomorph_zeroSection]
    exact ⟨hq₁, hq₂⟩
  · rintro ⟨⟨q₁, q₂⟩, hq⟩
    rw [cotangentRel_prodMap_iff _ w (hi₁ q₁) (hi₂ q₂), prodDiffeomorph_zeroSection] at hq
    exact ⟨⟨q₁, hq.1⟩, ⟨q₂, hq.2⟩⟩

/-- **The conormal set of a product map is the product of the conormal sets.** -/
@[simp]
theorem image_prodDiffeomorph_conormal_prodMap {i₁ : Q₁ → M₁} {i₂ : Q₂ → M₂}
    (hi₁ : MDifferentiable J₁ I₁ i₁) (hi₂ : MDifferentiable J₂ I₂ i₂) :
    prodDiffeomorph I₁ I₂ M₁ M₂ ''
        conormal (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) =
      conormal J₁ I₁ i₁ ×ˢ conormal J₂ I₂ i₂ := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨w, hw, hwab⟩
    rw [← hwab]
    exact (prodDiffeomorph_mem_prod_conormal_iff hi₁ hi₂ w).mpr hw
  · intro hab
    refine ⟨(prodDiffeomorph I₁ I₂ M₁ M₂).symm (a, b), ?_,
      (prodDiffeomorph I₁ I₂ M₁ M₂).apply_symm_apply (a, b)⟩
    apply (prodDiffeomorph_mem_prod_conormal_iff hi₁ hi₂ _).mp
    rwa [(prodDiffeomorph I₁ I₂ M₁ M₂).apply_symm_apply]

/-- The inverse of `prodDiffeomorph` carries the product of two conormal sets onto the conormal set
of the product map. -/
@[simp]
theorem symm_image_prodDiffeomorph_conormal {i₁ : Q₁ → M₁} {i₂ : Q₂ → M₂}
    (hi₁ : MDifferentiable J₁ I₁ i₁) (hi₂ : MDifferentiable J₂ I₂ i₂) :
    (prodDiffeomorph I₁ I₂ M₁ M₂).symm '' (conormal J₁ I₁ i₁ ×ˢ conormal J₂ I₂ i₂) =
      conormal (J₁.prod J₂) (I₁.prod I₂) (Prod.map i₁ i₂) := by
  rw [← image_prodDiffeomorph_conormal_prodMap hi₁ hi₂, Set.image_image]
  simp

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
