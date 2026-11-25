/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Kernels under functors to modules

For a functor `F : C ⥤ ModuleCat R` preserving the kernel of a morphism `f`, the fibre of
`kernel f` maps onto the kernel of the linear map `F.map f`: every element killed by `F.map f`
is the image of an element of `F.obj (kernel f)` under `F.map (kernel.ι f)`.

## Main results

* `CategoryTheory.Functor.exists_map_kernel_ι_eq`: an element killed by `F.map f` comes from the
  fibre of `kernel f`.
* `CategoryTheory.Functor.map_map_apply_eq_zero`: on values, `F.map g` kills the image of
  `F.map f` when `f ≫ g = 0`.
-/

public section

namespace CategoryTheory.Functor

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {R : Type*} [Ring R]

/-- For a functor to modules preserving the kernel of `f`, an element killed by `F.map f` comes
from the fibre of the kernel of `f`. -/
theorem exists_map_kernel_ι_eq (F : C ⥤ ModuleCat R) [F.PreservesZeroMorphisms] {P Y : C}
    (f : P ⟶ Y) [HasKernel f] [PreservesLimit (parallelPair f 0) F] (x : F.obj P)
    (hx : (F.map f).hom x = 0) : ∃ y, (F.map (kernel.ι f)).hom y = x :=
  ⟨(PreservesKernel.iso F f).inv.hom ((ModuleCat.kernelIsoKer (F.map f)).inv.hom ⟨x, hx⟩), by
    rw [← ModuleCat.comp_apply, PreservesKernel.iso_inv_ι,
      ModuleCat.kernelIsoKer_inv_kernel_ι_apply]⟩

/-- For a functor to modules preserving zero morphisms, `F.map g` kills the image of `F.map f`
when `f ≫ g = 0`. -/
theorem map_map_apply_eq_zero (F : C ⥤ ModuleCat R) [F.PreservesZeroMorphisms] {A B Y : C}
    {f : A ⟶ B} {g : B ⟶ Y} (h : f ≫ g = 0) (u : F.obj A) :
    (F.map g).hom ((F.map f).hom u) = 0 := by
  rw [← ModuleCat.comp_apply, ← F.map_comp, h]
  simp

end CategoryTheory.Functor
