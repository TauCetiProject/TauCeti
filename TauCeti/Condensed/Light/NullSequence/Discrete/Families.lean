/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Condensed.Light.NullSequence.Discrete.Basic
public import Mathlib.Condensed.Light.Monoidal
public import TauCeti.Data.Finsupp.Difference

import TauCeti.Condensed.Light.InternalHom.Discrete
import TauCeti.CategoryTheory.Monoidal.Closed.Preadditive

/-!
# Discrete null-sequence families

Compactness makes a profinite family of null sequences with discrete coefficients uniformly
finitely supported. This module identifies the family with finitely supported sequences of
locally constant coefficients, compatibly with the null-sequence shift and difference.
-/

public section

universe u

open CategoryTheory Category MonoidalCategory LightCondensed Opposite
open TauCeti

namespace ModuleCat

variable {R : Type u} [CommRing R]

private noncomputable def nullSeqDiscreteHomEquiv (M : ModuleCat.{u} R)
    (S : LightProfinite.{u}) :
    (nullSeq R ⟶ ((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M)) ≃+
    (nullSeq R ⟶ (LightCondMod.LocallyConstant.functor R).obj
      (ModuleCat.of R (LocallyConstant S M))) :=
  (Linear.homCongr ℤ (Iso.refl _) (lightCondFreeInternalHomDiscreteIso M S)).toAddEquiv

private lemma nullSeqDiscreteHomEquiv_apply (M : ModuleCat.{u} R)
    (S : LightProfinite.{u})
    (g : nullSeq R ⟶ ((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M)) :
    nullSeqDiscreteHomEquiv M S g = g ≫ (lightCondFreeInternalHomDiscreteIso M S).hom := by
  rw [nullSeqDiscreteHomEquiv, LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply,
    Linear.homCongr_apply, Iso.refl_inv, Category.id_comp]

private lemma nullSeqDiscreteHomEquiv_shift (M : ModuleCat.{u} R)
    (S : LightProfinite.{u})
    (g : nullSeq R ⟶ ((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M)) :
    nullSeqDiscreteHomEquiv M S (nullShift R ≫ g) =
      nullShift R ≫ nullSeqDiscreteHomEquiv M S g := by
  simp only [nullSeqDiscreteHomEquiv_apply, Category.assoc]

/-- Profinite families of discrete null sequences are uniformly finitely supported. -/
noncomputable def nullSeqDiscreteTensorHomEquivFinsupp (M : ModuleCat.{u} R)
    (S : LightProfinite.{u}) :
    (nullSeq R ⊗ (LightCondensed.free R).obj S.toCondensed ⟶
      (LightCondMod.LocallyConstant.functor R).obj M) ≃+
        (ℕ →₀ LocallyConstant S M) :=
  (tensorSwapCurryEquiv (nullSeq R) ((LightCondensed.free R).obj S.toCondensed) _).trans
    ((nullSeqDiscreteHomEquiv M S).trans
      (ModuleCat.nullSeqHomEquivFinsupp (ModuleCat.of R (LocallyConstant S M))))

/-- The coefficient at n is evaluation of the represented product section at the nth point. -/
lemma nullSeqDiscreteTensorHomEquivFinsupp_apply (M : ModuleCat.{u} R)
    (S : LightProfinite.{u})
    (g : nullSeq R ⊗ (LightCondensed.free R).obj S.toCondensed ⟶
      (LightCondMod.LocallyConstant.functor R).obj M) (n : ℕ) (x : S) :
    nullSeqDiscreteTensorHomEquivFinsupp M S g n x =
      lightLocallyConstantSectionsEquiv M (S ⊗ liftedSequence.{u})
        ((S ⊗ liftedSequence.{u}).freeModuleHomEquiv
          ((Functor.Monoidal.μIso (lightProfiniteToLightCondSet ⋙ LightCondensed.free R)
              S liftedSequence.{u}).inv ≫
            (LightCondensed.free R).obj S.toCondensed ◁
              (toReducedLightFree R).app (Under.mk inftyPoint) ≫
            (β_ (nullSeq R) ((LightCondensed.free R).obj S.toCondensed)).inv ≫ g))
        (x, sequencePoint n) := by
  simp only [nullSeqDiscreteTensorHomEquivFinsupp, AddEquiv.trans_apply]
  rw [ModuleCat.nullSeqHomEquivFinsupp_apply, nullSeqDiscreteHomEquiv_apply,
    reducedLightFreeHomEquiv_postcomp_val]
  -- The reduced free section is indexed by the pointed test object's underlying space.
  erw [lightCondFreeInternalHomDiscreteIso_hom_app_apply M S liftedSequence]
  rw [lightCondFreeInternalHomSectionsEquiv_apply, lightCondFreeInternalHomProductEquiv_apply,
    reducedLightFreeHomEquiv_apply_val]
  -- Currying gives the section on the underlying space of the pointed test object.
  erw [AddEquiv.symm_apply_apply liftedSequence.freeModuleHomEquiv]
  rw [MonoidalClosed.uncurry_natural_left, tensorSwapCurryEquiv_apply,
    MonoidalClosed.uncurry_curry]
  -- Only the presentation of the composite free functor differs.
  rfl

/-- The family comparison sends the null-sequence difference to
`a ↦ (n ↦ a n − a (n + 1))` on finitely supported sequences of locally constant coefficients. -/
lemma nullSeqDiscreteTensorHomEquivFinsupp_difference (M : ModuleCat.{u} R)
    (S : LightProfinite.{u})
    (g : nullSeq R ⊗ (LightCondensed.free R).obj S.toCondensed ⟶
      (LightCondMod.LocallyConstant.functor R).obj M) :
    nullSeqDiscreteTensorHomEquivFinsupp M S (g - (nullShift R ▷ _) ≫ g) =
      Finsupp.oneSubShiftEquiv (nullSeqDiscreteTensorHomEquivFinsupp M S g) := by
  ext n x
  simp only [nullSeqDiscreteTensorHomEquivFinsupp, AddEquiv.trans_apply, map_sub,
    tensorSwapCurryEquiv_precomp, nullSeqDiscreteHomEquiv_shift,
    Finsupp.sub_apply,
    Finsupp.oneSubShiftEquiv_apply, Finsupp.oneSubShift_apply, LocallyConstant.sub_apply]
  exact congrArg (fun a : LocallyConstant S M ↦
    (ModuleCat.nullSeqHomEquivFinsupp (ModuleCat.of R (LocallyConstant S M))
      (nullSeqDiscreteHomEquiv M S (tensorSwapCurryEquiv (nullSeq R)
        ((LightCondensed.free R).obj S.toCondensed) _ g)) n) x - a x)
    (ModuleCat.nullSeqHomEquivFinsupp_nullShift
      (ModuleCat.of R (LocallyConstant S M)) _ n)

end ModuleCat
