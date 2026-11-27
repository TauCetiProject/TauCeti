/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Basic
public import Mathlib.CategoryTheory.Subobject.Limits
import TauCeti.CategoryTheory.Limits.Shapes.NormalMono.Basic

/-!
# Additional limit and colimit lemmas for subobjects

Lemmas relating `Subobject` to kernels, cokernels, images, products, and coproducts.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- The kernel subobject of `f` is `⊤` if and only if `f = 0`. -/
@[simp]
theorem kernelSubobject_eq_top_iff [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) [HasKernel f] :
    kernelSubobject f = ⊤ ↔ f = 0 :=
  ⟨fun h ↦ by
    have : IsIso (kernelSubobject f).arrow := (Subobject.isIso_arrow_iff_eq_top _).mpr h
    rw [← cancel_epi (kernelSubobject f).arrow]
    simp,
   fun h ↦ h ▸ kernelSubobject_zero⟩

/-- The image subobject of `f` is `⊥` if and only if `f = 0`. -/
@[simp]
theorem imageSubobject_eq_bot_iff [HasZeroMorphisms C] [HasZeroObject C] {X Y : C} (f : X ⟶ Y)
    [HasImage f] : imageSubobject f = ⊥ ↔ f = 0 :=
  ⟨fun h ↦ by
    have harrow : (imageSubobject f).arrow = 0 := by rw [h, Subobject.bot_arrow]
    rw [← imageSubobject_arrow_comp f, harrow, comp_zero],
   fun h ↦ h ▸ imageSubobject_zero⟩

/-- In a normal-mono category, the kernel subobject of `cokernel.π f` for a mono `f` is `mk f`. -/
@[simp]
theorem kernelSubobject_cokernel_π [HasZeroMorphisms C] [IsNormalMonoCategory C] {X Y : C}
    (f : X ⟶ Y) [Mono f] [HasCokernel f] [HasKernel (cokernel.π f)] :
    kernelSubobject (cokernel.π f) = Subobject.mk f := by
  refine le_antisymm ?_ (le_kernelSubobject _ _ (by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk f, Category.assoc, cokernel.condition, comp_zero]))
  let := normalMonoOfMono f
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' (NormalMono.isLimitKernelForkCokernelπ f)
    (kernelSubobject (cokernel.π f)).arrow (kernelSubobject_arrow_comp _)
  exact Subobject.le_mk_of_comm l hl

/-- An image subobject `imageSubobject f` lies below `S` if and only if `f` factors through `S`. -/
theorem imageSubobject_le_iff_factors {X Y : C} (f : X ⟶ Y) [HasImage f] (S : Subobject Y) :
    imageSubobject f ≤ S ↔ S.Factors f :=
  ⟨fun h ↦ Subobject.factors_of_le f h (by simpa using imageSubobject_factors_comp_self f (𝟙 _)),
   fun h ↦ imageSubobject_le f (S.factorThru f h) (Subobject.factorThru_arrow _ _ _)⟩

end CategoryTheory.Limits

namespace CategoryTheory.Subobject

variable {C : Type u} [Category.{v} C]

/-- If `(Subobject.exists f).obj S ≤ T`, then `S.arrow ≫ f` factors through `T`. -/
theorem factors_of_exists_le [HasImages C] {X Y : C} {f : X ⟶ Y}
    {S : Subobject X} {T : Subobject Y} (h : (Subobject.exists f).obj S ≤ T) :
    T.Factors (S.arrow ≫ f) :=
  factors_of_le _ h ((Subobject.imageFactorisation f S).F.fac ▸
    factors_comp_arrow (Subobject.imageFactorisation f S).F.e)

/-- In a normal-mono category with cokernels, the kernel subobject of `A ⟶ ∏ᵢ cokernel (S i).arrow`
is the greatest lower bound of `S : ι → Subobject A`. -/
theorem isGLB_kernelSubobject_piLift [HasZeroMorphisms C] [HasCokernels C] [IsNormalMonoCategory C]
    {A : C} {ι : Type*} (S : ι → Subobject A) [HasProduct fun i ↦ cokernel (S i).arrow]
    [HasKernel (Pi.lift fun i ↦ cokernel.π (S i).arrow)] :
    IsGLB (Set.range S) (kernelSubobject (Pi.lift fun i ↦ cokernel.π (S i).arrow)) := by
  set φ : A ⟶ ∏ᶜ fun i ↦ cokernel (S i).arrow := Pi.lift fun i ↦ cokernel.π (S i).arrow
  refine ⟨?_, fun T hT ↦ le_kernelSubobject φ T (by
    ext i; simp only [φ, Category.assoc, Pi.lift_comp_π, zero_comp]
    rw [← ofLE_arrow (hT (Set.mem_range_self i)), Category.assoc, cokernel.condition, comp_zero])⟩
  rintro _ ⟨i, rfl⟩
  have hcomp : (kernelSubobject φ).arrow ≫ cokernel.π (S i).arrow = 0 := by
    have hpi : (kernelSubobject φ).arrow ≫ φ ≫ Pi.π (fun j ↦ cokernel (S j).arrow) i = 0 := by
      rw [kernelSubobject_arrow_comp_assoc, zero_comp]
    simpa [φ] using hpi
  have : HasKernel (cokernel.π (S i).arrow) :=
    let := normalMonoOfMono (S i).arrow
    ⟨⟨⟨KernelFork.ofι (S i).arrow (cokernel.condition _),
      NormalMono.isLimitKernelForkCokernelπ (S i).arrow⟩⟩⟩
  rw [← Subobject.mk_arrow (S i), ← kernelSubobject_cokernel_π (S i).arrow]
  exact le_kernelSubobject _ _ hcomp

/-- The image subobject of `∐ᵢ (S i : C) ⟶ A` is the least upper bound of `S : ι → Subobject A`. -/
theorem isLUB_imageSubobject_sigmaDesc {A : C} {ι : Type*} (S : ι → Subobject A)
    [HasCoproduct fun i ↦ (S i : C)] [HasImage (Sigma.desc fun i ↦ (S i).arrow)] :
    IsLUB (Set.range S) (imageSubobject (Sigma.desc fun i ↦ (S i).arrow)) :=
  ⟨fun _ ⟨i, hi⟩ ↦ hi ▸ le_of_comm
      (Sigma.ι (fun j ↦ (S j : C)) i ≫ factorThruImageSubobject _) (by simp),
   fun T hT ↦ imageSubobject_le _ (Sigma.desc fun i ↦ ofLE (S i) T (hT (Set.mem_range_self i)))
      (by ext i; simp)⟩

end CategoryTheory.Subobject
