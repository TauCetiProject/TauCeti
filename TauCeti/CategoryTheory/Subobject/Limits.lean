/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Basic
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Additional limit and colimit lemmas for subobjects

This file collects general lemmas relating `Subobject` to kernels, cokernels, images, products,
and coproducts:

* `CategoryTheory.Limits.kernelSubobject_eq_top_iff`: `kernelSubobject f = ⊤ ↔ f = 0`.
* `CategoryTheory.Limits.imageSubobject_eq_bot_iff`: `imageSubobject f = ⊥ ↔ f = 0`.
* `CategoryTheory.Limits.kernelSubobject_cokernel_π`: in a normal-mono category, the kernel
  subobject of `cokernel.π f` for a monomorphism `f` is `Subobject.mk f`.
* `CategoryTheory.Subobject.isGLB_kernelSubobject_piLift`: in a normal-mono category with
  cokernels, if `∏ᵢ cokernel (S i).arrow` and the kernel of the induced map
  `A ⟶ ∏ᵢ cokernel (S i).arrow` exist, that kernel subobject is the greatest lower bound of
  `Set.range S` in `Subobject A` (without assuming well-poweredness).
* `CategoryTheory.Subobject.isLUB_imageSubobject_sigmaDesc`: if `∐ᵢ (S i : C)` and the image of
  the induced map `∐ᵢ (S i : C) ⟶ A` exist, that image subobject is the least upper bound of
  `Set.range S` in `Subobject A`.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- The kernel subobject of `f` is `⊤` if and only if `f = 0`. -/
@[simp]
theorem kernelSubobject_eq_top_iff [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) [HasKernel f] :
    kernelSubobject f = ⊤ ↔ f = 0 := by
  constructor
  · intro h
    have : IsIso (kernelSubobject f).arrow := (Subobject.isIso_arrow_iff_eq_top _).mpr h
    rw [← Category.id_comp f, ← IsIso.inv_hom_id (kernelSubobject f).arrow, Category.assoc,
      kernelSubobject_arrow_comp, comp_zero]
  · rintro rfl
    exact kernelSubobject_zero

/-- The image subobject of `f` is `⊥` if and only if `f = 0`. -/
@[simp]
theorem imageSubobject_eq_bot_iff [HasZeroMorphisms C] [HasZeroObject C] {X Y : C} (f : X ⟶ Y)
    [HasImage f] :
    imageSubobject f = ⊥ ↔ f = 0 := by
  constructor
  · intro h
    rw [← imageSubobject_arrow_comp f]
    have h0 : (imageSubobject f).arrow = 0 := by
      rw [h, Subobject.bot_arrow]
    rw [h0, comp_zero]
  · rintro rfl
    exact imageSubobject_zero

/-- In a normal-mono category, the kernel subobject of `cokernel.π f` for a monomorphism `f` is
`Subobject.mk f`. -/
@[simp]
theorem kernelSubobject_cokernel_π [HasZeroMorphisms C] [IsNormalMonoCategory C] {X Y : C}
    (f : X ⟶ Y) [Mono f] [HasCokernel f] [HasKernel (cokernel.π f)] :
    kernelSubobject (cokernel.π f) = Subobject.mk f := by
  refine le_antisymm ?_ ?_
  · obtain ⟨hf⟩ := IsNormalMonoCategory.normalMonoOfMono f
    have hg : (kernelSubobject (cokernel.π f)).arrow ≫ hf.g = 0 := by
      have hfac : cokernel.π f ≫ cokernel.desc f hf.g hf.w = hf.g := cokernel.π_desc _ _ _
      rw [← hfac, kernelSubobject_arrow_comp_assoc, zero_comp]
    obtain ⟨l, hl⟩ := NormalMono.lift' f (kernelSubobject (cokernel.π f)).arrow hg
    exact Subobject.le_mk_of_comm l hl
  · refine le_kernelSubobject (cokernel.π f) (Subobject.mk f) ?_
    rw [← Subobject.underlyingIso_hom_comp_eq_mk f, Category.assoc, cokernel.condition, comp_zero]

end CategoryTheory.Limits

namespace CategoryTheory.Subobject

variable {C : Type u} [Category.{v} C]

/-- In a normal-mono category with cokernels, the kernel subobject of the canonical map
`A ⟶ ∏ᵢ cokernel (S i).arrow` is the greatest lower bound of the family `S : ι → Subobject A` in
`Subobject A`. -/
theorem isGLB_kernelSubobject_piLift [HasZeroMorphisms C] [HasCokernels C] [IsNormalMonoCategory C]
    {A : C} {ι : Type*} (S : ι → Subobject A) [HasProduct fun i ↦ cokernel (S i).arrow]
    [HasKernel (Pi.lift fun i ↦ cokernel.π (S i).arrow)] :
    IsGLB (Set.range S) (kernelSubobject (Pi.lift fun i ↦ cokernel.π (S i).arrow)) := by
  set φ : A ⟶ ∏ᶜ fun i ↦ cokernel (S i).arrow := Pi.lift fun i ↦ cokernel.π (S i).arrow
  refine ⟨?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    have hcomp : (kernelSubobject φ).arrow ≫ cokernel.π (S i).arrow = 0 := by
      have h : (kernelSubobject φ).arrow ≫ φ ≫ Pi.π (fun j ↦ cokernel (S j).arrow) i = 0 := by
        rw [kernelSubobject_arrow_comp_assoc, zero_comp]
      simpa [φ] using h
    obtain ⟨hf⟩ := IsNormalMonoCategory.normalMonoOfMono (S i).arrow
    have hg : (kernelSubobject φ).arrow ≫ hf.g = 0 := by
      have hfac : cokernel.π (S i).arrow ≫ cokernel.desc (S i).arrow hf.g hf.w = hf.g :=
        cokernel.π_desc _ _ _
      rw [← hfac, reassoc_of% hcomp, zero_comp]
    obtain ⟨l, hl⟩ := NormalMono.lift' (S i).arrow (kernelSubobject φ).arrow hg
    exact le_of_comm l hl
  · intro T hT
    refine le_kernelSubobject φ T ?_
    ext i
    simp only [φ, Category.assoc, Pi.lift_comp_π, zero_comp]
    rw [← ofLE_arrow (hT (Set.mem_range_self i)), Category.assoc, cokernel.condition, comp_zero]

/-- The image subobject of the canonical map `∐ᵢ (S i : C) ⟶ A` is the least upper bound of the
family `S : ι → Subobject A` in `Subobject A`. -/
theorem isLUB_imageSubobject_sigmaDesc {A : C} {ι : Type*} (S : ι → Subobject A)
    [HasCoproduct fun i ↦ (S i : C)] [HasImage (Sigma.desc fun i ↦ (S i).arrow)] :
    IsLUB (Set.range S) (imageSubobject (Sigma.desc fun i ↦ (S i).arrow)) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact le_of_comm
      (Sigma.ι (fun j ↦ (S j : C)) i ≫ factorThruImageSubobject (Sigma.desc fun j ↦ (S j).arrow))
      (by simp)
  · intro T hT
    exact imageSubobject_le _ (Sigma.desc fun i ↦ ofLE (S i) T (hT (Set.mem_range_self i)))
      (by ext i; simp)

end CategoryTheory.Subobject
