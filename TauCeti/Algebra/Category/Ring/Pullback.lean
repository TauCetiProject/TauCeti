/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
public import TauCeti.RingTheory.Pullback

/-!
# Pullbacks in the category of rings

The fibre product `RingHom.pullback f g` of ring homomorphisms `f : A →+* C` and `g : B →+* C`,
the subring of pairs of `A × B` that agree in `C`, is the pullback of `f` and `g` in `RingCat`.
The rings need not be commutative. This compares the explicit fibre product, on which Milnor
squares are built, with the categorical pullback, so that limit arguments in `RingCat` apply
to it. Mathlib's `CommRingCat.pullbackConeIsLimit` is the commutative counterpart.

## Main definitions

* `RingCat.pullbackCone f g`: the pullback cone on `RingHom.pullback f.hom g.hom`, with the two
  projections.
* `RingCat.pullbackConeIsLimit f g`: this cone is a limit cone.
-/

public section

universe u

open CategoryTheory Limits

namespace RingCat

variable {A B C : RingCat.{u}} (f : A ⟶ C) (g : B ⟶ C)

/-- The pullback cone in `RingCat` on the fibre product `RingHom.pullback f.hom g.hom`, with the
projections `RingHom.pullbackFst` and `RingHom.pullbackSnd`.

The body is exposed because the statements of `pullbackCone_fst` and `pullbackCone_snd` compare
morphisms out of `(pullbackCone f g).pt` with morphisms out of `of (f.hom.pullback g.hom)`, and
these sources agree only after unfolding the cone. -/
@[expose]
def pullbackCone : PullbackCone f g :=
  PullbackCone.mk (ofHom (f.hom.pullbackFst g.hom)) (ofHom (f.hom.pullbackSnd g.hom))
    (hom_ext (f.hom.pullback_comm_sq g.hom))

@[simp]
theorem pullbackCone_pt : (pullbackCone f g).pt = of (f.hom.pullback g.hom) :=
  (rfl)

@[simp]
theorem pullbackCone_fst : (pullbackCone f g).fst = ofHom (f.hom.pullbackFst g.hom) :=
  (rfl)

@[simp]
theorem pullbackCone_snd : (pullbackCone f g).snd = ofHom (f.hom.pullbackSnd g.hom) :=
  (rfl)

/-- The fibre product of rings is the pullback in `RingCat`: the cone `RingCat.pullbackCone f g`
is a limit cone, with lift given by `RingHom.pullbackLift`. -/
def pullbackConeIsLimit : IsLimit (pullbackCone f g) :=
  PullbackCone.IsLimit.mk _
    (fun s ↦ ofHom (f.hom.pullbackLift g.hom s.fst.hom s.snd.hom congr(($s.condition).hom)))
    (fun _ ↦ hom_ext (RingHom.pullbackFst_comp_pullbackLift ..))
    (fun _ ↦ hom_ext (RingHom.pullbackSnd_comp_pullbackLift ..))
    (fun _ _ h₁ h₂ ↦ hom_ext (RingHom.eq_pullbackLift _ congr(($h₁).hom) congr(($h₂).hom)))

end RingCat
