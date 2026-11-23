/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Condensed.Light.NullSequence.Discrete
public import TauCeti.Condensed.Light.Solid.Basic

import TauCeti.Condensed.Light.DiscreteInternalHom
public import TauCeti.Data.Finsupp.Difference

import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Linear.Basic

/-!
# Discrete light condensed modules are solid

Compactness makes a family of null sequences with discrete coefficients uniformly finitely
supported. The inverse of one minus the shift is consequently the finite tail sum.
-/

public section

universe u

open CategoryTheory Category MonoidalCategory LightCondensed Opposite
open LightCondMod.LocallyConstant TauCeti

namespace ModuleCat

variable {R : Type u} [CommRing R]

private noncomputable def nullSeqDiscreteHomEquiv (M : ModuleCat.{u} R)
    (S : LightProfinite.{u}) :
    (nullSeq R ⟶ ((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M)) ≃+
    (nullSeq R ⟶ (LightCondMod.LocallyConstant.functor R).obj
      (ModuleCat.of R (LocallyConstant S M))) := by
  let N := ((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
    (LightCondMod.LocallyConstant.functor R).obj M)
  let D := (LightCondMod.LocallyConstant.functor R).obj
    (ModuleCat.of R (LocallyConstant S M))
  let E := internalHomSectionsEquiv M S
  have hn (s : N.obj.obj (op liftedSequence.{u})) :
      E _ (N.obj.map inftyPoint.op s) = D.obj.map inftyPoint.op (E _ s) := by
    exact internalHomSectionsEquiv_naturality M S inftyPoint s
  have hm (s : N.obj.obj (op liftedSequence.{u})) :
      s ∈ (N.obj.map inftyPoint.op).hom.toAddMonoidHom.ker ↔
      E _ s ∈ (D.obj.map inftyPoint.op).hom.toAddMonoidHom.ker := by
    -- Align the kernel-membership wrappers with the naturality equation for sections.
    change N.obj.map inftyPoint.op s = 0 ↔ D.obj.map inftyPoint.op (E _ s) = 0
    constructor
    · intro hs
      exact (hn s).symm.trans ((congrArg (E _) hs).trans (map_zero _))
    · intro hs
      apply (E _).injective
      exact (hn s).trans (hs.trans (map_zero _).symm)
  let e : (N.obj.map inftyPoint.op).hom.toAddMonoidHom.ker ≃+
      (D.obj.map inftyPoint.op).hom.toAddMonoidHom.ker :=
    { toEquiv := (E liftedSequence).toEquiv.subtypeEquiv hm
      map_add' := fun s t ↦ Subtype.ext ((E _).map_add s.val t.val) }
  exact (reducedLightFreeHomEquiv R (Under.mk inftyPoint) N).trans
    (e.trans (reducedLightFreeHomEquiv R (Under.mk inftyPoint) D).symm)

private lemma nullSeqDiscreteHomEquiv_val (M : ModuleCat.{u} R)
    (S : LightProfinite.{u})
    (g : nullSeq R ⟶ ((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M)) :
    (reducedLightFreeHomEquiv R (Under.mk inftyPoint) _
      (nullSeqDiscreteHomEquiv M S g)).val =
      internalHomSectionsEquiv M S liftedSequence
        (reducedLightFreeHomEquiv R (Under.mk inftyPoint) _ g).val := by
  simp only [nullSeqDiscreteHomEquiv, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rfl

private lemma nullSeqDiscreteHomEquiv_shift (M : ModuleCat.{u} R)
    (S : LightProfinite.{u})
    (g : nullSeq R ⟶ ((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M)) :
    nullSeqDiscreteHomEquiv M S (nullShift R ≫ g) =
      nullShift R ≫ nullSeqDiscreteHomEquiv M S g := by
  apply (reducedLightFreeHomEquiv R (Under.mk inftyPoint) _).injective
  apply Subtype.ext
  rw [nullSeqDiscreteHomEquiv_val, reducedLightFreeHomEquiv_nullShift_val,
    reducedLightFreeHomEquiv_nullShift_val, nullSeqDiscreteHomEquiv_val]
  exact internalHomSectionsEquiv_naturality M S natShift _

private noncomputable def tensorSwapCurryEquiv (M : ModuleCat.{u} R)
    (S : LightProfinite.{u}) :
    (nullSeq R ⊗ (LightCondensed.free R).obj S.toCondensed ⟶
      (LightCondMod.LocallyConstant.functor R).obj M) ≃+
    (nullSeq R ⟶ ((LightCondensed.free R).obj S.toCondensed ⟶[LightCondMod R]
      (LightCondMod.LocallyConstant.functor R).obj M)) := by
  letI : (tensorLeft ((LightCondensed.free R).obj S.toCondensed)).Additive :=
    preservesFiniteColimits_le_additiveFunctor _ _ _ ⟨inferInstance⟩
  exact ((Linear.homCongr ℤ (β_ (nullSeq R) ((LightCondensed.free R).obj S.toCondensed))
    (Iso.refl _)).toAddEquiv).trans
    ((ihom.adjunction _).homAddEquiv _ _)

private lemma tensorSwapCurryEquiv_apply (M : ModuleCat.{u} R)
    (S : LightProfinite.{u})
    (g : nullSeq R ⊗ (LightCondensed.free R).obj S.toCondensed ⟶
      (LightCondMod.LocallyConstant.functor R).obj M) :
    tensorSwapCurryEquiv M S g = MonoidalClosed.curry
      ((β_ (nullSeq R) ((LightCondensed.free R).obj S.toCondensed)).inv ≫ g) := by
  simp only [tensorSwapCurryEquiv, AddEquiv.trans_apply,
     AddEquiv.coe_mk, Equiv.coe_fn_mk ]
  rfl

private lemma tensorSwapCurryEquiv_shift (M : ModuleCat.{u} R)
    (S : LightProfinite.{u})
    (g : nullSeq R ⊗ (LightCondensed.free R).obj S.toCondensed ⟶
      (LightCondMod.LocallyConstant.functor R).obj M) :
    tensorSwapCurryEquiv M S ((nullShift R ▷ _) ≫ g) =
      nullShift R ≫ tensorSwapCurryEquiv M S g := by
  rw [tensorSwapCurryEquiv_apply, tensorSwapCurryEquiv_apply,
    ← MonoidalClosed.curry_natural_left]
  congr 1
  rw [← Category.assoc, ← BraidedCategory.braiding_inv_naturality_right,
    Category.assoc]

/-- Profinite families of discrete null sequences are uniformly finitely supported. -/
noncomputable def nullSeqDiscreteTensorHomEquivFinsupp (M : ModuleCat.{u} R)
    (S : LightProfinite.{u}) :
    (nullSeq R ⊗ (LightCondensed.free R).obj S.toCondensed ⟶
      (LightCondMod.LocallyConstant.functor R).obj M) ≃+
        (ℕ →₀ LocallyConstant S M) :=
  (tensorSwapCurryEquiv M S).trans ((nullSeqDiscreteHomEquiv M S).trans
    (ModuleCat.nullSeqHomEquivFinsupp (ModuleCat.of R (LocallyConstant S M))))

/-- The coefficient at n is evaluation of the represented product section at the nth point. -/
lemma nullSeqDiscreteTensorHomEquivFinsupp_apply (M : ModuleCat.{u} R)
    (S : LightProfinite.{u})
    (g : nullSeq R ⊗ (LightCondensed.free R).obj S.toCondensed ⟶
      (LightCondMod.LocallyConstant.functor R).obj M) (n : ℕ) (x : S) :
    nullSeqDiscreteTensorHomEquivFinsupp M S g n x =
      LightCondMod.LocallyConstant.sectionsEquiv M (S ⊗ liftedSequence.{u})
        ((S ⊗ liftedSequence.{u}).freeModuleHomEquiv
          ((Functor.Monoidal.μIso (lightProfiniteToLightCondSet ⋙ LightCondensed.free R)
              S liftedSequence.{u}).inv ≫
            (LightCondensed.free R).obj S.toCondensed ◁
              (toReducedLightFree R).app (Under.mk inftyPoint) ≫
            (β_ (nullSeq R) ((LightCondensed.free R).obj S.toCondensed)).inv ≫ g))
        (x, sequencePoint n) := by
  -- Align the composed equivalence with the named coefficient equation for discrete null sequences.
  change (ModuleCat.nullSeqHomEquivFinsupp (ModuleCat.of R (LocallyConstant S M))
    (nullSeqDiscreteHomEquiv M S (tensorSwapCurryEquiv M S g))) n x = _
  rw [ModuleCat.nullSeqHomEquivFinsupp_apply]
  rw [nullSeqDiscreteHomEquiv_val]
  have hsec := sectionsEquiv_apply (ModuleCat.of R (LocallyConstant S M))
    liftedSequence (internalHomSectionsEquiv M S liftedSequence
      (reducedLightFreeHomEquiv R (Under.mk inftyPoint) _
        (tensorSwapCurryEquiv M S g)).val)
  refine (congrArg (fun f : LocallyConstant liftedSequence (LocallyConstant S M) ↦
    f (sequencePoint n) x) hsec).trans ?_
  have hrep : liftedSequence.freeModuleHomEquiv.symm
      (reducedLightFreeHomEquiv R (Under.mk inftyPoint) _
        (tensorSwapCurryEquiv M S g)).val =
      (toReducedLightFree R).app (Under.mk inftyPoint) ≫ tensorSwapCurryEquiv M S g := by
    rw [reducedLightFreeHomEquiv_apply_val]
    exact AddEquiv.symm_apply_apply _ _
  rw [internalHomSectionsEquiv_apply, internalHomProductEquiv_apply, hrep,
    MonoidalClosed.uncurry_natural_left, tensorSwapCurryEquiv_apply,
    MonoidalClosed.uncurry_curry]
  rfl

/-- The family comparison sends the null-sequence difference to coefficientwise difference. -/
lemma nullSeqDiscreteTensorHomEquivFinsupp_difference (M : ModuleCat.{u} R)
    (S : LightProfinite.{u})
    (g : nullSeq R ⊗ (LightCondensed.free R).obj S.toCondensed ⟶
      (LightCondMod.LocallyConstant.functor R).obj M) :
    nullSeqDiscreteTensorHomEquivFinsupp M S (g - (nullShift R ▷ _) ≫ g) =
      Finsupp.oneSubShiftEquiv (nullSeqDiscreteTensorHomEquivFinsupp M S g) := by
  ext n x
  simp only [nullSeqDiscreteTensorHomEquivFinsupp, AddEquiv.trans_apply, map_sub,
    tensorSwapCurryEquiv_shift, nullSeqDiscreteHomEquiv_shift,
    Finsupp.sub_apply,
    Finsupp.oneSubShiftEquiv_apply, Finsupp.oneSubShift_apply, LocallyConstant.sub_apply]
  exact congrArg (fun a : LocallyConstant S M ↦
    (ModuleCat.nullSeqHomEquivFinsupp (ModuleCat.of R (LocallyConstant S M))
      (nullSeqDiscreteHomEquiv M S (tensorSwapCurryEquiv M S g)) n) x - a x)
    (ModuleCat.nullSeqHomEquivFinsupp_nullShift
      (ModuleCat.of R (LocallyConstant S M)) _ n)

/-- The locally constant realization of every discrete coefficient module is solid. -/
lemma isLightSolid_locallyConstant (M : ModuleCat.{u} R) :
    IsLightSolid ((LightCondMod.LocallyConstant.functor R).obj M) := by
  rw [isLightSolid_iff_bijective]
  intro S
  let E := nullSeqDiscreteTensorHomEquivFinsupp M S
  have h : E ∘ (fun g ↦ g - (nullShift R ▷ _) ≫ g) = Finsupp.oneSubShiftEquiv ∘ E := by
    funext g
    exact nullSeqDiscreteTensorHomEquivFinsupp_difference M S g
  have hb : Function.Bijective (E ∘ (fun g ↦ g - (nullShift R ▷ _) ≫ g)) := by
    rw [h]
    exact Finsupp.oneSubShiftEquiv.bijective.comp E.bijective
  exact (Function.Bijective.of_comp_iff' E.bijective _).mp hb

/-- Every discrete light condensed module is solid. -/
lemma isLightSolid_discrete (M : ModuleCat.{u} R) :
    IsLightSolid ((LightCondensed.discrete (ModuleCat R)).obj M) :=
  (isLightSolid_locallyConstant M).of_iso
    ((LightCondMod.LocallyConstant.functorIsoDiscrete R).app M)

end ModuleCat
