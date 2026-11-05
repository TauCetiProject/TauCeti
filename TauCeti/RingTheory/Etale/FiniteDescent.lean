/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.RingHom.Finite

/-!
# Finite étale algebras under faithfully flat base change

For a pushout square of commutative rings `S' = R' ⊗[R] S` in which `R'` is faithfully flat over
`R`, the algebra `S` is finite étale over `R` if and only if `S'` is finite étale over `R'`. One
direction is stability of finite and étale ring maps under base change; the other is their
descent along faithfully flat ring maps, `RingHom.Finite.codescendsAlong_faithfullyFlat` and
`RingHom.Etale.codescendsAlong_faithfullyFlat`. Thus finite étaleness of an algebra may be checked
after a faithfully flat extension of the base, for instance after completing a Noetherian local
ring.

## Main results

* `CommRingCat.finite_and_etale_iff_of_isPushout_of_faithfullyFlat`: across a pushout square in
  `CommRingCat` whose base extension is faithfully flat, a ring map is finite étale if and only if
  its base change is.
-/

public section

universe u

namespace CommRingCat

open CategoryTheory

/-- For a pushout square of commutative rings whose base extension `g : R ⟶ R'` is faithfully flat,
the ring map `f : R ⟶ S` is finite étale if and only if its base change `inr : R' ⟶ S'` is. -/
theorem finite_and_etale_iff_of_isPushout_of_faithfullyFlat {R S R' S' : CommRingCat.{u}}
    {f : R ⟶ S} {g : R ⟶ R'} {inl : S ⟶ S'} {inr : R' ⟶ S'} (hsq : IsPushout f g inl inr)
    (hg : g.hom.FaithfullyFlat) :
    (f.hom.Finite ∧ f.hom.Etale) ↔ (inr.hom.Finite ∧ inr.hom.Etale) := by
  algebraize [f.hom, g.hom, inl.hom, inr.hom, inr.hom.comp g.hom]
  have : IsScalarTower R S S' := .of_algebraMap_eq fun x ↦ congr($(hsq.w).hom x).symm
  have : Algebra.IsPushout R S R' S' := CommRingCat.isPushout_iff_isPushout.mp hsq
  exact ⟨fun h ↦ ⟨RingHom.finite_isStableUnderBaseChange R S R' S' h.1,
      RingHom.Etale.isStableUnderBaseChange R S R' S' h.2⟩,
    fun h ↦ ⟨RingHom.Finite.codescendsAlong_faithfullyFlat hg h.1,
      RingHom.Etale.codescendsAlong_faithfullyFlat hg h.2⟩⟩

end CommRingCat
