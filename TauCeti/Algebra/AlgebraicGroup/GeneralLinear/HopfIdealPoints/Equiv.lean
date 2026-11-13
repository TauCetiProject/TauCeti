/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Presentation

/-!
# Equivalences of value rings on presented matrix points

An equivalence of commutative value rings induces an equivalence on any matrix point group
presented by a fixed integral Hopf ideal. The inverse applies the inverse ring equivalence
entrywise; this in particular lifts inverse Frobenius to points over perfect rings.

The construction uses `IntegralPointsPresentation.map` and its identity and composition laws.
It does not require surjectivity of points under a quotient of value rings.
-/

public section

namespace TauCeti.GeneralLinear.IntegralPointsPresentation

universe v w z

noncomputable section

variable {n : ℕ} {I : HopfIdeal ℤ (coordinateHopfAlgebra ℤ n)}
variable {A : Type v} {B : Type w} {C : Type z}
variable [CommRing A] [CommRing B] [CommRing C]

/-- An equivalence of value rings induces an equivalence of presented point groups. -/
def mapEquiv (P : IntegralPointsPresentation n I A) (Q : IntegralPointsPresentation n I B)
    (e : A ≃+* B) : P.val ≃* Q.val where
  toFun := P.map Q e.toRingHom
  invFun := Q.map P e.symm.toRingHom
  left_inv g := by
    have h := P.map_comp Q P e.toRingHom e.symm.toRingHom
    simp only [RingEquiv.symm_toRingHom_comp_toRingHom, map_id, MonoidHom.ext_iff,
      MonoidHom.comp_apply, MonoidHom.id_apply] at h
    exact (h g).symm
  right_inv g := by
    have h := Q.map_comp P Q e.symm.toRingHom e.toRingHom
    simp only [RingEquiv.toRingHom_comp_symm_toRingHom, map_id, MonoidHom.ext_iff,
      MonoidHom.comp_apply, MonoidHom.id_apply] at h
    exact (h g).symm
  map_mul' := (P.map Q e.toRingHom).map_mul

/-- The forward map of the value-ring equivalence is the usual map of points. -/
@[simp]
theorem mapEquiv_apply (P : IntegralPointsPresentation n I A)
    (Q : IntegralPointsPresentation n I B) (e : A ≃+* B) (g : P.val) :
    P.mapEquiv Q e g = P.map Q e.toRingHom g :=
  (rfl)

/-- Inverting the value-ring equivalence inverts the induced point-group equivalence. -/
@[simp]
theorem mapEquiv_symm (P : IntegralPointsPresentation n I A)
    (Q : IntegralPointsPresentation n I B) (e : A ≃+* B) :
    (P.mapEquiv Q e).symm = Q.mapEquiv P e.symm :=
  (rfl)

/-- The identity ring equivalence induces the identity on points. -/
@[simp]
theorem mapEquiv_refl (P : IntegralPointsPresentation n I A) :
    P.mapEquiv P (RingEquiv.refl A) = MulEquiv.refl P.val := by
  ext g
  simp

/-- Composing value-ring equivalences composes the induced point-group equivalences. -/
theorem mapEquiv_trans (P : IntegralPointsPresentation n I A)
    (Q : IntegralPointsPresentation n I B) (S : IntegralPointsPresentation n I C)
    (e : A ≃+* B) (f : B ≃+* C) :
    P.mapEquiv S (e.trans f) = (P.mapEquiv Q e).trans (Q.mapEquiv S f) := by
  ext g
  simp [RingEquiv.toRingHom_trans, map_comp P Q S]

end

end TauCeti.GeneralLinear.IntegralPointsPresentation
