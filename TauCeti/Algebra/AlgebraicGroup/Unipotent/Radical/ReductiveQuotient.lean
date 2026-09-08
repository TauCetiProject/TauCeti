/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Image
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Smooth
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Unipotent

/-!
# Unipotent radicals and reductive quotients

A reductive finite-type affine group has trivial unipotent radical over its ground field, not
only after extension to an algebraic closure. Faithfully flat scalar extension reflects equality
of Hopf ideals, so this follows from the geometric definition of reductivity and the base-change
inclusion for the unipotent radical.

This file applies that fact to an exact-sequence criterion. Suppose a homomorphism of affine
groups is represented contravariantly by an injective coordinate map `f : D ⟶ H`. If its
kernel is connected, normal, smooth, and unipotent, and the quotient group represented by `D` is
reductive, then the kernel is the unipotent radical of the group represented by `H`.

The reverse containment sends the unipotent radical through the quotient map. Its
scheme-theoretic image remains connected, smooth, and unipotent; injectivity of `f` makes it
normal in the quotient. Reductivity therefore makes that image trivial.

## Main declarations

* `TauCeti.reductiveCommHopfAlgProperty.unipotentRadicalDefiningIdeal_eq_augmentation`:
  a reductive group's unipotent radical over the ground field is trivial.
* `TauCeti.FiniteTypeCommHopfAlgCat.
    unipotentRadicalDefiningIdeal_eq_kernelHopfIdeal_of_reductive`:
  a connected normal smooth unipotent kernel with reductive quotient is the unipotent radical.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and §§6.45--6.46.
* A. Borel, *Linear Algebraic Groups*, §11.21.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace reductiveCommHopfAlgProperty

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The unipotent radical of a reductive finite-type affine group over its ground field is the
identity subgroup.

The definition of reductivity kills the radical after extension to an algebraic closure. The
base-changed ground-field radical lies in that geometric radical, while every Hopf ideal lies in
the augmentation ideal. Faithfully flat base change then reflects the resulting equality. -/
theorem unipotentRadicalDefiningIdeal_eq_augmentation
    (hH : reductiveCommHopfAlgProperty k H) :
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal H =
      HopfIdeal.augmentation k H := by
  have hgeometric :
      FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
          (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) =
        HopfIdeal.augmentation (AlgebraicClosure k)
          (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H) :=
    (reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation
      k H).mp hH |>.2.2
  apply CommHopfAlgCat.baseChangeHopfIdeal_injective (K := AlgebraicClosure k)
  rw [CommHopfAlgCat.baseChangeHopfIdeal_augmentation]
  apply le_antisymm
  · exact HopfIdeal.le_augmentation (AlgebraicClosure k) _ _
  · rw [← hgeometric]
    exact FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_baseChange_le H

/-- Every connected normal smooth unipotent closed subgroup of a reductive group over the ground
field is the identity subgroup. -/
theorem eq_augmentation_of_isUnipotentRadicalCandidate
    (hH : reductiveCommHopfAlgProperty k H) (I : HopfIdeal k H)
    (hI : HopfIdeal.IsUnipotentRadicalCandidate H I) :
    I = HopfIdeal.augmentation k H := by
  apply le_antisymm (HopfIdeal.le_augmentation k H I)
  rw [← hH.unipotentRadicalDefiningIdeal_eq_augmentation]
  exact FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_le H I hI

end reductiveCommHopfAlgProperty

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- A connected normal smooth unipotent kernel of a quotient homomorphism to a reductive group is
the unipotent radical.

The coordinate map `f : D ⟶ H` is contravariant. Its injectivity says that the represented
homomorphism from the group with coordinate algebra `H` to the group with coordinate algebra `D`
is schematically dominant; it is used to preserve normality when the radical is mapped into the
target. -/
theorem unipotentRadicalDefiningIdeal_eq_kernelHopfIdeal_of_reductive
    (H D : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hD : reductiveCommHopfAlgProperty k D)
    (f : D.obj ⟶ H.obj) (hf_injective : Function.Injective f.hom)
    (hf : HopfIdeal.IsUnipotentRadicalCandidate H
      (CommHopfAlgCat.kernelHopfIdeal f)) :
    unipotentRadicalDefiningIdeal H = CommHopfAlgCat.kernelHopfIdeal f := by
  apply le_antisymm
  · exact unipotentRadicalDefiningIdeal_le H _ hf
  · rw [CommHopfAlgCat.kernelHopfIdeal_le_iff]
    let J := unipotentRadicalDefiningIdeal H
    let Q := quotient H J
    let q : H.obj ⟶ Q.obj := CommHopfAlgCat.mkQuotient H.obj J
    let g : D.obj ⟶ Q.obj := f ≫ q
    have hQ := smoothUnipotent_unipotentRadical H
    have hQ' := (smoothUnipotentCommHopfAlgProperty_iff k Q).mp hQ
    let _ : Algebra.Smooth k Q := hQ'.1
    let _ : IsReduced Q := isReduced_of_smooth_of_field k Q
    have hQunipotent : geometricallyUnipotentPointsCommHopfAlgProperty k Q.obj := by
      rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff]
      exact hQ'.2
    have hker : HopfIdeal.ker g.hom = J.comap f.hom := by
      ext x
      rw [HopfIdeal.mem_ker, HopfIdeal.mem_comap]
      -- The category coercion hides the quotient morphism from its application lemma.
      change (CommHopfAlgCat.mkQuotient H.obj J).hom (f.hom x) = 0 ↔ f.hom x ∈ J
      rw [CommHopfAlgCat.mkQuotient_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      rfl
    have himageNormal : (HopfIdeal.ker g.hom).IsNormal := by
      rw [hker]
      exact (isNormal_unipotentRadicalDefiningIdeal H).comap_of_injective
        f.hom hf_injective
    have himageConnected : geometricallyConnectedCommHopfAlgProperty k
        (CommHopfAlgCat.image g) :=
      geometricallyConnectedCommHopfAlgProperty.image g
        (geometricallyConnected_unipotentRadical H)
    have himageSmooth : smoothCommHopfAlgProperty k (CommHopfAlgCat.image g) :=
      smoothCommHopfAlgProperty.image g
        ((smoothCommHopfAlgProperty_iff Q.obj).mpr hQ'.1)
    have himageUnipotent : geometricallyUnipotentPointsCommHopfAlgProperty k
        (CommHopfAlgCat.image g) :=
      geometricallyUnipotentPointsCommHopfAlgProperty.image_of_reduced g hQunipotent
    have himageCandidate : HopfIdeal.IsUnipotentRadicalCandidate D
        (HopfIdeal.ker g.hom) := by
      refine HopfIdeal.IsUnipotentRadicalCandidate.mk himageNormal himageConnected ?_
      rw [smoothUnipotentCommHopfAlgProperty_iff]
      refine ⟨(smoothCommHopfAlgProperty_iff _).mp himageSmooth, ?_⟩
      rw [← geometricallyUnipotentPointsCommHopfAlgProperty_iff]
      exact himageUnipotent
    have hkerAugmentation : HopfIdeal.ker g.hom = HopfIdeal.augmentation k D :=
      hD.eq_augmentation_of_isUnipotentRadicalCandidate _ himageCandidate
    have hg : g = _root_.CommHopfAlgCat.ofHom
        ((Bialgebra.unitBialgHom k Q.obj).comp
          (Bialgebra.counitBialgHom k D)) := by
      rw [← Category.id_comp g]
      apply (CommHopfAlgCat.comp_eq_unit_comp_counit_iff (𝟙 D.obj) g).mpr
      rw [CommHopfAlgCat.kernelHopfIdeal_eq_augmentation_of_surjective
          (𝟙 D.obj) Function.surjective_id,
        ← hkerAugmentation, HopfIdeal.ker_toIdeal]
      exact fun _ hx ↦ hx
    exact hg

end FiniteTypeCommHopfAlgCat

end

end TauCeti
