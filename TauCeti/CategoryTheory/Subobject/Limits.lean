/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Subobject.Limits
import TauCeti.CategoryTheory.Abelian.Subobject

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

/-- Defining formula for `iInfCokernel P` as a kernel subobject. -/
lemma iInfCokernel_def :
    iInfCokernel P = kernelSubobject (Pi.lift fun i ↦ cokernel.π (P i).arrow) :=
  (rfl)

lemma iInfCokernel_le (i : ι) : iInfCokernel P ≤ P i := by
  have h := kernelSubobject_comp_le (Pi.lift fun j ↦ cokernel.π (P j).arrow)
    (Pi.π (fun j ↦ cokernel (P j).arrow) i)
  rwa [Pi.lift_comp_π, kernelSubobject_cokernel_π, mk_arrow] at h

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

/-- Defining formula for `iSupImage P` as an image subobject. -/
lemma iSupImage_def :
    iSupImage P = imageSubobject (Sigma.desc fun i ↦ (P i).arrow) :=
  (rfl)

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

end CategoryTheory.Subobject
