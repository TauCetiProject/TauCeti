/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Unipotent
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Smooth

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
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (D : CommHopfAlgCat.{u} k) (f : D ⟶ H.obj)
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
    let g : D ⟶ Q.obj := f ≫ CommHopfAlgCat.mkQuotient H.obj J
    have himage' : HopfIdeal.ker g.hom = HopfIdeal.augmentation k D := himage
    have hg : g = _root_.CommHopfAlgCat.ofHom
        ((Bialgebra.unitBialgHom k Q.obj).comp
          (Bialgebra.counitBialgHom k D)) := by
      rw [← Category.id_comp g]
      apply (CommHopfAlgCat.comp_eq_unit_comp_counit_iff (𝟙 D) g).mpr
      rw [CommHopfAlgCat.kernelHopfIdeal_eq_augmentation_of_surjective
          (𝟙 D) Function.surjective_id,
        ← himage', HopfIdeal.ker_toIdeal]
      exact fun _ hx ↦ hx
    exact hg

/-- The image of the unipotent radical under a homomorphism out of its ambient group is smooth
and geometrically unipotent. -/
theorem smoothUnipotent_image_quotient_unipotentRadical
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) {D : CommHopfAlgCat.{u} k}
    [Algebra.FiniteType k D] (f : D ⟶ H.obj) :
    smoothCommHopfAlgProperty k
        (CommHopfAlgCat.image
          (f ≫ CommHopfAlgCat.mkQuotient H.obj (unipotentRadicalDefiningIdeal H))) ∧
      geometricallyUnipotentPointsCommHopfAlgProperty k
        (CommHopfAlgCat.image
          (f ≫ CommHopfAlgCat.mkQuotient H.obj (unipotentRadicalDefiningIdeal H))) := by
  let Q := quotient H (unipotentRadicalDefiningIdeal H)
  have hQ := smoothUnipotent_unipotentRadical H
  have hQ' := (smoothUnipotentCommHopfAlgProperty_iff k Q).mp hQ
  let _ : Algebra.Smooth k Q := hQ'.1
  let _ : IsReduced Q := isReduced_of_smooth_of_field k Q
  refine ⟨smoothCommHopfAlgProperty.image _ ((smoothCommHopfAlgProperty_iff _).mpr hQ'.1), ?_⟩
  apply geometricallyUnipotentPointsCommHopfAlgProperty.image_of_reduced
  exact (geometricallyUnipotentPointsCommHopfAlgProperty_iff k Q.obj).mpr hQ'.2

end FiniteTypeCommHopfAlgCat

end

end TauCeti
