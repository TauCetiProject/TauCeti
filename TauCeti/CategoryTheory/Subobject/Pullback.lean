/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Pullbacks of subobjects

Every pullback of a subobject along a morphism `p` contains the kernel of `p`, which is the
pullback of `⊥` (`Subobject.pullback_bot`).

A subobject `Z` of `A` identifies the subobjects of the object `(Z : C)` with the subobjects of `A`
below `Z`, by `Subobject.map Z.arrow` with inverse `Subobject.pullback Z.arrow` (Mathlib's
`Subobject.subobjectOrderIso`). This file records how the two functors act on a subobject
`S ≤ Z` of `A`, and when the inclusion `S ⟶ Z` is the kernel of a morphism out of `Z`.

## Main results

* `CategoryTheory.Subobject.kernelSubobject_le_pullback`: every pullback along `p` contains the
  kernel of `p`.
* `CategoryTheory.Subobject.pullback_arrow_of_le`: for `S ≤ Z`, the pullback of `S` along
  `Z.arrow` is the subobject represented by the inclusion `Subobject.ofLE S Z`.
* `CategoryTheory.Subobject.map_pullback_arrow_of_le`: for `S ≤ Z`, mapping back the
  pullback of `S` along `Z.arrow` gives `S`.
* `CategoryTheory.Subobject.isLimitKernelForkOfLE`: if the kernel of a morphism `g` out of `Z` is
  the pullback of `S ≤ Z`, then the inclusion `S ⟶ Z` is a kernel of `g`.
* `CategoryTheory.Subobject.le_pullback_iff` and `CategoryTheory.Subobject.exists_le_iff`:
  characterizations of `X' ≤ (pullback f).obj Y'` and `(exists f).obj X' ≤ Y'` via factoring.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Subobject

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {A : C}

/-- The pullback of a subobject `S ≤ Z` along `Z.arrow` is represented by the inclusion
`S ⟶ Z`. -/
lemma pullback_arrow_of_le {S Z : Subobject A} (h : S ≤ Z) :
    (pullback Z.arrow).obj S = mk (ofLE S Z h) := by
  have : S = (map Z.arrow).obj (mk (ofLE S Z h)) := by
    simp only [map_mk, ofLE_arrow, mk_arrow]
  conv_lhs => rw [this]
  exact pullback_map_self _ _

/-- Mapping back along `Z.arrow` the pullback of a subobject `S ≤ Z` gives `S`. -/
lemma map_pullback_arrow_of_le {S Z : Subobject A} (h : S ≤ Z) :
    (map Z.arrow).obj ((pullback Z.arrow).obj S) = S := by
  rw [← inf_eq_map_pullback, inf_eq_right.2 h]

section Kernel

variable [HasZeroMorphisms C]

/-- The preimage of any subobject contains the kernel. -/
lemma kernelSubobject_le_pullback {X Y : C} (p : Y ⟶ X) [HasKernel p]
    (K : Subobject X) : kernelSubobject p ≤ (pullback p).obj K :=
  le_of_factors (pullback_factors p K _ (by rw [kernelSubobject_arrow_comp]; exact factors_zero))

/-- The kernel of a morphism is the preimage of the bottom subobject. -/
@[simp]
lemma pullback_bot [HasZeroObject C] {X Y : C} (p : Y ⟶ X)
    [HasKernel p] : (pullback p).obj ⊥ = kernelSubobject p :=
  le_antisymm (le_kernelSubobject _ _ ((bot_factors_iff_zero _).1
    ((pullback_factors_iff p ⊥ _).1 (factors_self _)))) (kernelSubobject_le_pullback p ⊥)

variable {S Z : Subobject A} (h : S ≤ Z) {X : C} (g : (Z : C) ⟶ X)
  [HasKernel g] (hg : kernelSubobject g = (pullback Z.arrow).obj S)

include hg in
/-- The inclusion `S ⟶ Z` composes to zero with a morphism out of `Z` whose kernel is the
pullback of `S`. -/
lemma ofLE_comp_eq_zero_of_kernelSubobject_eq : ofLE S Z h ≫ g = 0 := by
  rw [← kernelSubobject_factors_iff, hg, pullback_factors_iff, ofLE_arrow]
  exact factors_self S

/-- The inclusion `S ⟶ Z` is a kernel of a morphism `g` out of `Z` whose kernel is the pullback of
`S`. -/
noncomputable def isLimitKernelForkOfLE :
    IsLimit (KernelFork.ofι (ofLE S Z h) (ofLE_comp_eq_zero_of_kernelSubobject_eq h g hg)) :=
  KernelFork.IsLimit.ofι' _ _ fun k hk ↦
    have hk' : S.Factors (k ≫ Z.arrow) := by
      rw [← pullback_factors_iff, ← hg]
      exact kernelSubobject_factors _ _ hk
    ⟨S.factorThru _ hk', by rw [← cancel_mono Z.arrow, Category.assoc, ofLE_arrow,
      factorThru_arrow]⟩

end Kernel

section PullbackExists

variable {X Y : C}

lemma le_pullback_iff (f : X ⟶ Y) (X' : Subobject X) (Y' : Subobject Y) :
    X' ≤ (pullback f).obj Y' ↔ Y'.Factors (X'.arrow ≫ f) := by
  refine ⟨fun h ↦ (pullback_factors_iff f Y' X'.arrow).mp
    (factors_of_le X'.arrow h (factors_self X')), fun h ↦ ?_⟩
  exact le_pullback_of_comm f (Y'.factorThru (X'.arrow ≫ f) h) (Y'.factorThru_arrow _ h)

lemma exists_le_iff [HasImages C] (f : X ⟶ Y) (X' : Subobject X) (Y' : Subobject Y) :
    («exists» f).obj X' ≤ Y' ↔ Y'.Factors (X'.arrow ≫ f) :=
  ((existsPullbackAdj f).gc X' Y').trans (le_pullback_iff f X' Y')

end PullbackExists

end CategoryTheory.Subobject
