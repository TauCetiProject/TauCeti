/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Meets and joins of families of subobjects from products and coproducts

In `Mathlib.CategoryTheory.Subobject.Lattice`, arbitrary meets and joins in `Subobject X` are
constructed assuming well-poweredness together with all small limits or coproducts. For an indexed
family `P : ι → Subobject X` over a specific index type `ι` (such as a countable family under
`HasCountableProducts` or `HasCountableCoproducts`), the meet and join can be formed directly
without well-poweredness:

* `CategoryTheory.Subobject.iInfCokernel`: in an abelian category, the kernel subobject of the map
  `X ⟶ ∏ i, cokernel (P i).arrow` is the greatest lower bound of `P` whenever that product exists.
* `CategoryTheory.Subobject.iSupImage`: in any category with images, the image subobject of the map
  `(∐ i, (P i : C)) ⟶ X` is the least upper bound of `P` whenever that coproduct exists.
* `CategoryTheory.Limits.kernelSubobject_eq_top_iff` and
  `CategoryTheory.Limits.imageSubobject_eq_bot_iff`: a morphism vanishes if and only if its kernel
  subobject is `⊤`, or equivalently its image subobject is `⊥`.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.Subobject

universe w v u

variable {C : Type u} [Category.{v} C] {X : C} {ι : Type w}

section Meet

variable [Abelian C] (P : ι → Subobject X) [HasProduct fun i ↦ cokernel (P i).arrow]

/-- The meet of an indexed family of subobjects in an abelian category, built as the kernel
subobject of the product of the cokernel projections `X ⟶ ∏ i, cokernel (P i).arrow`. -/
noncomputable def iInfCokernel : Subobject X :=
  kernelSubobject (Pi.lift fun i ↦ cokernel.π (P i).arrow)

lemma iInfCokernel_le (i : ι) : iInfCokernel P ≤ P i := by
  have hzero : (iInfCokernel P).arrow ≫ cokernel.π (P i).arrow = 0 := by
    calc
      (iInfCokernel P).arrow ≫ cokernel.π (P i).arrow
          = (iInfCokernel P).arrow ≫ (Pi.lift fun j ↦ cokernel.π (P j).arrow) ≫ Pi.π _ i := by
            simp
      _ = 0 := by
            rw [← Category.assoc, iInfCokernel, kernelSubobject_arrow_comp, zero_comp]
  exact le_of_comm (Abelian.monoLift (P i).arrow (iInfCokernel P).arrow hzero)
    (Abelian.monoLift_comp _ _ _)

lemma le_iInfCokernel {W : Subobject X} (h : ∀ i, W ≤ P i) : W ≤ iInfCokernel P := by
  refine le_kernelSubobject _ _ (Limits.Pi.hom_ext _ _ fun i ↦ ?_)
  rw [Category.assoc, Pi.lift_comp_π, zero_comp, ← ofLE_arrow (h i), Category.assoc,
    cokernel.condition, comp_zero]

/-- `iInfCokernel P` is the greatest lower bound of the family `P` in `Subobject X`. -/
theorem isGLB_iInfCokernel : IsGLB (Set.range P) (iInfCokernel P) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact iInfCokernel_le P i
  · intro W hW
    exact le_iInfCokernel P fun i ↦ hW ⟨i, rfl⟩

end Meet

section Join

variable [HasImages C] (P : ι → Subobject X) [HasCoproduct fun i ↦ (P i : C)]

/-- The join of an indexed family of subobjects in a category with images, built as the image
subobject of the coproduct map `(∐ i, (P i : C)) ⟶ X`. -/
noncomputable def iSupImage : Subobject X :=
  imageSubobject (Sigma.desc fun i ↦ (P i).arrow)

lemma le_iSupImage (i : ι) : P i ≤ iSupImage P := by
  have hle : imageSubobject (Sigma.ι (fun j ↦ (P j : C)) i ≫
      Sigma.desc fun j ↦ (P j).arrow) ≤ iSupImage P := imageSubobject_comp_le _ _
  rw [Sigma.ι_comp_desc, imageSubobject_mono, mk_arrow] at hle
  exact hle

lemma iSupImage_le {W : Subobject X} (h : ∀ i, P i ≤ W) : iSupImage P ≤ W :=
  imageSubobject_le _ (Sigma.desc fun i ↦ ofLE (P i) W (h i)) (by
    ext i
    simp)

/-- `iSupImage P` is the least upper bound of the family `P` in `Subobject X`. -/
theorem isLUB_iSupImage : IsLUB (Set.range P) (iSupImage P) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact le_iSupImage P i
  · intro W hW
    exact iSupImage_le P fun i ↦ hW ⟨i, rfl⟩

end Join

section PullbackExists

variable {Y : C}

lemma le_pullback_iff [HasPullbacks C] (f : X ⟶ Y) (X' : Subobject X) (Y' : Subobject Y) :
    X' ≤ (pullback f).obj Y' ↔ Y'.Factors (X'.arrow ≫ f) := by
  refine ⟨fun h ↦ (pullback_factors_iff f Y' X'.arrow).mp
    (factors_of_le X'.arrow h (factors_self X')), fun h ↦ ?_⟩
  exact le_pullback_of_comm f (Y'.factorThru (X'.arrow ≫ f) h) (Y'.factorThru_arrow _ h)

lemma exists_le_iff [HasPullbacks C] [HasImages C] (f : X ⟶ Y) (X' : Subobject X)
    (Y' : Subobject Y) :
    («exists» f).obj X' ≤ Y' ↔ Y'.Factors (X'.arrow ≫ f) :=
  ((existsPullbackAdj f).gc X' Y').trans (le_pullback_iff f X' Y')

end PullbackExists

end CategoryTheory.Subobject

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C]

/-- The kernel subobject of a morphism `f` is `⊤` if and only if `f = 0`. -/
@[simp]
lemma kernelSubobject_eq_top_iff [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) [HasKernel f] :
    kernelSubobject f = ⊤ ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ kernelSubobject_zero⟩
  have hcomp : (⊤ : Subobject X).arrow ≫ f = 0 := by
    rw [← Subobject.ofLE_arrow h.symm.le, Category.assoc, kernelSubobject_arrow_comp, comp_zero]
  simpa using (cancel_epi (⊤ : Subobject X).arrow).1 (by simpa using hcomp)

/-- The image subobject of a morphism `f` is `⊥` if and only if `f = 0`. -/
@[simp]
lemma imageSubobject_eq_bot_iff [HasZeroMorphisms C] [HasZeroObject C] {X Y : C} (f : X ⟶ Y)
    [HasImage f] : imageSubobject f = ⊥ ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ imageSubobject_zero⟩
  rw [← imageSubobject_arrow_comp f, ← Subobject.ofLE_arrow h.le]
  simp

end CategoryTheory.Limits
