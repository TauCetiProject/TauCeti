/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction

/-!
# Unipotent radicals and quotient images

This file supplies the common reduction used to identify a unipotent radical with the kernel of a
quotient homomorphism. Once the image of the radical in the target is trivial, maximality gives one
ideal containment and triviality gives the other.

## Main declaration

* `TauCeti.FiniteTypeCommHopfAlgCat.
    unipotentRadicalDefiningIdeal_eq_kernelHopfIdeal_of_quotient_image_eq_augmentation`:
  a unipotent-radical candidate kernel is the radical when the radical has trivial image.

This reduction supports identifying kernels of quotient homomorphisms with unipotent radicals.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- A unipotent-radical candidate kernel is the unipotent radical if the image of the radical in
the target is trivial. The image is represented by the kernel of the composite coordinate map. -/
theorem unipotentRadicalDefiningIdeal_eq_kernelHopfIdeal_of_quotient_image_eq_augmentation
    (H D : FiniteTypeCommHopfAlgCat.{u, u} k) (f : D.obj ⟶ H.obj)
    (hf : HopfIdeal.IsUnipotentRadicalCandidate H
      (CommHopfAlgCat.kernelHopfIdeal f))
    (himage : HopfIdeal.ker
        (f ≫ CommHopfAlgCat.mkQuotient H.obj (unipotentRadicalDefiningIdeal H)).hom =
      HopfIdeal.augmentation k D) :
    unipotentRadicalDefiningIdeal H = CommHopfAlgCat.kernelHopfIdeal f := by
  apply le_antisymm
  · exact unipotentRadicalDefiningIdeal_le H _ hf
  · rw [CommHopfAlgCat.kernelHopfIdeal_le_iff]
    let J := unipotentRadicalDefiningIdeal H
    let Q := quotient H J
    let g : D.obj ⟶ Q.obj := f ≫ CommHopfAlgCat.mkQuotient H.obj J
    have himage' : HopfIdeal.ker g.hom = HopfIdeal.augmentation k D := himage
    have hg : g = _root_.CommHopfAlgCat.ofHom
        ((Bialgebra.unitBialgHom k Q.obj).comp
          (Bialgebra.counitBialgHom k D)) := by
      rw [← Category.id_comp g]
      apply (CommHopfAlgCat.comp_eq_unit_comp_counit_iff (𝟙 D.obj) g).mpr
      rw [CommHopfAlgCat.kernelHopfIdeal_eq_augmentation_of_surjective
          (𝟙 D.obj) Function.surjective_id,
        ← himage', HopfIdeal.ker_toIdeal]
      exact fun _ hx ↦ hx
    exact hg

end FiniteTypeCommHopfAlgCat

end

end TauCeti
