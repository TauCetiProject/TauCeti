/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.RingHom.Integral

/-!
# Residue fields of points of a fibre product

Let `t` be a point of `X ×_S Y` lying over `x ∈ X`, `y ∈ Y` and `s ∈ S`. Mathlib's
`AlgebraicGeometry.Scheme.Pullback.ofPointTensor` is the canonical map
`κ(x) ⊗[κ(s)] κ(y) ⟶ κ(t)`. In general `κ(t)` is only the fraction field of the image of this
map. If `κ(x)` is integral over `κ(s)`, for instance if `X → S` is finite, or unramified and
locally of finite type, then the map is surjective. So `κ(t)` is then generated as a ring by the
images of `κ(x)` and `κ(y)`. The proof uses that `κ(x) ⊗[κ(s)] κ(y)` is integral over the field
`κ(y)`, so all of its primes are maximal.

For a base change of a finite étale cover, this shows that each residue field of the base change
is a quotient of a base change of a residue field of the cover, as used in the proof of Stacks,
Lemma 58.31.1 (0EYD).

## Main results

* `AlgebraicGeometry.Scheme.Pullback.ofPointTensor_surjective`: `κ(x) ⊗[κ(s)] κ(y) ⟶ κ(t)` is
  surjective when `κ(x)` is integral over `κ(s)`.
* `AlgebraicGeometry.Scheme.Pullback.closure_range_residueFieldMap_eq_top`: in that case `κ(t)`
  is generated as a ring by the images of `κ(x)` and `κ(y)`.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Pullback

universe u

variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

/-- If `t` is a point of `X ×_S Y` over `x ∈ X` and `κ(x)` is integral over `κ(f x)`, then the
canonical map `κ(x) ⊗[κ(s)] κ(y) ⟶ κ(t)` is surjective. -/
theorem ofPointTensor_surjective (t : ↑(pullback f g))
    (h : (f.residueFieldMap (pullback.fst f g t)).hom.IsIntegral) :
    Function.Surjective (ofPointTensor t) := by
  -- A pushout of commutative rings is integral over its second factor if the first map is.
  have hinr {R A B : CommRingCat.{u}} (a : R ⟶ A) (b : R ⟶ B) (ha : a.hom.IsIntegral) :
      (pushout.inr a b).hom.IsIntegral := by
    rw [← inl_comp_pushoutSymmetry_hom, CommRingCat.hom_comp]
    exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_isStableUnderBaseChange.pushout_inl
      RingHom.isIntegral_respectsIso _ _ ha) (RingHom.isIntegral_of_surjective _
        (ConcreteCategory.bijective_of_isIso (pushoutSymmetry b a).hom).2)
  -- At every point `p` of `Spec (κ(x) ⊗[κ(s)] κ(y))` the residue field `κ(p)` is a quotient of
  -- the tensor product, as `p` is maximal, and it factors through `κ` of the image point.
  have key (T : Triplet f g) (hT : T.tensorInr.hom.IsIntegral) (p : Spec T.tensor) :
      Function.Surjective (ofPointTensor (T.SpecTensorTo p)) := by
    have := p.isPrime
    have hp : p.asIdeal.IsMaximal := by
      refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ hT p.asIdeal ?_
      rw [Ideal.eq_bot_of_prime (Ideal.comap _ p.asIdeal)]
      exact Ideal.bot_isMaximal
    have e := T.Spec_ofPointTensor_SpecTensorTo p
    rw [← Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp, ← Spec.map_comp,
      ← Spec.map_comp, Spec.map_inj] at e
    intro z
    obtain ⟨w₀, hw₀⟩ := (ConcreteCategory.bijective_of_isIso
      (Spec.residueFieldIso T.tensor p).inv).2 (T.SpecTensorTo.residueFieldMap p z)
    obtain ⟨w, rfl⟩ := p.asIdeal.algebraMap_residueField_surjective w₀
    refine ⟨(Triplet.tensorCongr (T.ofPoint_SpecTensorTo p).symm).hom w,
      (T.SpecTensorTo.residueFieldMap p).hom.injective ?_⟩
    rw [← hw₀]
    exact congr($e w)
  have := key (Triplet.ofPoint t) (hinr _ _ (RingHom.IsIntegral.trans _ _
    (RingHom.isIntegral_of_surjective _ fun x ↦ ⟨x, rfl⟩) h)) (SpecOfPoint t)
  rwa [SpecTensorTo_SpecOfPoint] at this

/-- If `t` is a point of `X ×_S Y` over `x ∈ X` and `y ∈ Y`, and `κ(x)` is integral over
`κ(f x)`, then the residue field `κ(t)` is generated as a ring by the images of `κ(x)` and
`κ(y)`. -/
theorem closure_range_residueFieldMap_eq_top (t : ↑(pullback f g))
    (h : (f.residueFieldMap (pullback.fst f g t)).hom.IsIntegral) :
    Subring.closure (Set.range ((pullback.fst f g).residueFieldMap t) ∪
      Set.range ((pullback.snd f g).residueFieldMap t)) = ⊤ := by
  set R := Subring.closure (Set.range ((pullback.fst f g).residueFieldMap t) ∪
    Set.range ((pullback.snd f g).residueFieldMap t))
  have h₁ (a) : (pullback.fst f g).residueFieldMap t a ∈ R :=
    Subring.subset_closure (.inl ⟨a, rfl⟩)
  have h₂ (b) : (pullback.snd f g).residueFieldMap t b ∈ R :=
    Subring.subset_closure (.inr ⟨b, rfl⟩)
  -- The map `κ(x) ⊗[κ(s)] κ(y) ⟶ κ(t)` factors through `R`.
  let i₁ : X.residueField (Triplet.ofPoint t).x ⟶ .of R :=
    CommRingCat.ofHom (((pullback.fst f g).residueFieldMap t).hom.codRestrict R h₁)
  let i₂ : Y.residueField (Triplet.ofPoint t).y ⟶ .of R :=
    CommRingCat.ofHom (((pullback.snd f g).residueFieldMap t).hom.codRestrict R h₂)
  have hw : ((S.residueFieldCongr (Triplet.ofPoint t).hx).inv ≫
      f.residueFieldMap (Triplet.ofPoint t).x) ≫ i₁ =
      ((S.residueFieldCongr (Triplet.ofPoint t).hy).inv ≫
      g.residueFieldMap (Triplet.ofPoint t).y) ≫ i₂ := by
    ext a
    exact congr($(residueFieldCongr_inv_residueFieldMap_ofPoint t) a)
  have hd : pushout.desc i₁ i₂ hw ≫
      (CommRingCat.ofHom R.subtype : .of R ⟶ (pullback f g).residueField t) = ofPointTensor t := by
    apply pushout.hom_ext
    · rw [pushout.inl_desc_assoc]
      exact (pushout.inl_desc _ _ _).symm
    · rw [pushout.inr_desc_assoc]
      exact (pushout.inr_desc _ _ _).symm
  refine eq_top_iff.mpr fun z _ ↦ ?_
  obtain ⟨w, rfl⟩ := ofPointTensor_surjective t h z
  rw [← hd]
  exact (pushout.desc i₁ i₂ hw w).2

end AlgebraicGeometry.Scheme.Pullback
