/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.Banding.Descent
public import TauCeti.CategoryTheory.Sites.Descent.Stackification.IsStack
public import TauCeti.CategoryTheory.Sites.Descent.Stackification.Universal

/-!
# Abelian bandings on stackification

An abelian banding of a prestack extends uniquely along the stackification unit, by the general
construction `AbelianBanding.descend`. Compatibility with a morphism of coefficients is detected
on the original prestack. This supplies the band and compatibility criteria for change of band
in Olsson, *Stacks*, Theorem 31.7.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Definition 31.1 and Theorem 31.7
-/

public section

noncomputable section

universe w v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.AbelianBanding

universe t

open TauCeti.Stack

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{w}}
  {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{max t v', max (t + 1) u v v' u'}} [F.IsPrestack J]
  (b : F.AbelianBanding J A)

/-- The abelian banding of the stackification induced by a banding of the original prestack.
The fibre universes are the existing size hypotheses of the stackification unit. -/
def stackification :
    (TauCeti.Stack.stackification.{t} J F).AbelianBanding J A :=
  b.descend (toStackification.{t, v', u'} J F)
    (fun U ↦ Stackification.Obj.fullyFaithfulToObjFunctor.{t} J F U)

/-- The unit of stackification preserves the induced band. -/
instance bandPreserving_toStackification :
    BandPreserving b (stackification.{w, v, u, v', u', t} b)
      (toStackification.{t, v', u'} J F) :=
  b.bandPreserving_descend _ _

/-- At the image of an original object, the stackification band is the image of its original
band automorphism. -/
@[simp]
theorem stackification_mulEquiv_obj (U : C) (x : F.obj (.mk (op U)))
    (a : Multiplicative (A.obj.obj (op U))) :
    (stackification.{w, v, u, v', u', t} b).mulEquiv U (((toStackification.{t, v', u'} J F).app
      (.mk (op U))).toFunctor.obj x) a =
      ((toStackification.{t, v', u'} J F).app (.mk (op U))).toFunctor.mapAut x
        (b.mulEquiv U x a) :=
  b.descend_mulEquiv_obj _ _ U x a

open scoped StrongTrans

/-- Compatibility with a morphism of bands out of stackification is detected after composition
with its band-preserving unit. -/
theorem bandCompatible_stackification_iff {B : Sheaf J AddCommGrpCat.{w}}
    {H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{max t v', max (t + 1) u v v' u'}}
    (φ : A ⟶ B) (bH : H.AbelianBanding J B)
    (θ : TauCeti.Stack.stackification.{t} J F ⟶ H) :
    BandCompatible φ (stackification.{w, v, u, v', u', t} b) bH θ ↔
      BandCompatible φ b bH (toStackification.{t, v', u'} J F ≫ θ) := by
  constructor
  · intro h
    let := h
    simpa only [Category.id_comp] using
      (BandCompatible.comp (bF := b) (stackification.{w, v, u, v', u', t} b)
        (𝟙 A) φ (toStackification.{t, v', u'} J F) θ)
  · intro h
    let := h
    exact BandCompatible.of_comp (bF := b) (stackification.{w, v, u, v', u', t} b)
      φ (toStackification.{t, v', u'} J F) θ

/-- A transformation out of stackification into a banded pseudofunctor preserves the band exactly
when its composite with the unit does. -/
theorem bandPreserving_stackification_iff
    {H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{max t v', max (t + 1) u v v' u'}}
    (bH : H.AbelianBanding J A)
    (θ : TauCeti.Stack.stackification.{t} J F ⟶ H) :
    BandPreserving (stackification.{w, v, u, v', u', t} b) bH θ ↔
      BandPreserving b bH (toStackification.{t, v', u'} J F ≫ θ) := by
  simpa only [bandCompatible_id_iff] using
    bandCompatible_stackification_iff.{w, v, u, v', u', t} b (𝟙 A) bH θ

variable {B : Sheaf J AddCommGrpCat.{w}}
  {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{max t v', max (t + 1) u v v' u'}}
  (φ : A ⟶ B) (bG : G.AbelianBanding J B)

/-- The stackification of a transformation is compatible with a morphism of bands exactly when
the original transformation is compatible with it. -/
@[simp]
theorem bandCompatible_stackificationMap_iff [G.IsPrestack J] (ψ : F ⟶ G) :
    BandCompatible φ (stackification.{w, v, u, v', u', t} b)
      (stackification.{w, v, u, v', u', t} bG) (stackificationMap.{t} J ψ) ↔
      BandCompatible φ b bG ψ := by
  rw [bandCompatible_stackification_iff,
    bandCompatible_iff_of_iso (toStackificationCompStackificationMapIso.{t, v', u'} J ψ)]
  constructor
  · intro h
    let := h
    refine ⟨fun U x a ↦ ?_⟩
    apply (Stackification.Obj.fullyFaithfulToObjFunctor.{t} J G U).autMulEquivOfFullyFaithful
      ((ψ.app (.mk (op U))).toFunctor.obj x) |>.injective
    exact (Functor.comp_mapAut _ _ _ _).symm.trans
      ((BandCompatible.mapAut_mulEquiv (bF := b)
        (bG := stackification.{w, v, u, v', u', t} bG) (φ := φ)
        (η := ψ ≫ toStackification.{t, v', u'} J G) U x a).trans
        (BandPreserving.mapAut_mulEquiv (bF := bG)
          (bG := stackification.{w, v, u, v', u', t} bG)
          (η := toStackification.{t, v', u'} J G) U _ _).symm)
  · intro h
    let := h
    simpa only [Category.comp_id] using
      (BandCompatible.comp bG φ (𝟙 B) ψ (toStackification.{t, v', u'} J G))

/-- The universal extension into a stack is compatible with a morphism of bands exactly when
the original transformation is compatible with it. -/
@[simp]
theorem bandCompatible_stackificationLift_iff [G.IsStack J] (ψ : F ⟶ G) :
    BandCompatible φ (stackification.{w, v, u, v', u', t} b) bG
      (stackificationLift.{t, v', u'} J ψ) ↔ BandCompatible φ b bG ψ := by
  rw [bandCompatible_stackification_iff]
  exact bandCompatible_iff_of_iso (toStackificationCompStackificationLiftIso.{t, v', u'} J ψ)

end CategoryTheory.Pseudofunctor.AbelianBanding
