/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Action
public import TauCeti.AlgebraicGeometry.Pullback.Over
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Uniqueness
public import TauCeti.CategoryTheory.Comma.Over

/-!
# Orbit schemes under field extensions

Extending the ground field commutes with the locally closed scheme image of an
orbit morphism. The comparison respects the immersion into the ambient scheme,
the parametrization by the acting group, and the restricted algebraic action on
the orbit scheme. It preserves the entire scheme structure across any field
extension `K / k`, without algebraic closedness, reducedness or smoothness
assumptions on the ground fields, the group or the acted-on scheme.

The action after base change is the native action transported by the monoidal
pullback functor. Its orbit morphism is the pullback of the original one.
Surjectivity and schematic dominance of the orbit factorization survive this
flat base change; uniqueness of locally closed image factorizations then gives
the comparison, and monomorphicity of the pulled-back inclusion gives
equivariance.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f.
* The Stacks Project, Tag 01R5 (flat base change of scheme-theoretic images).
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace TauCeti.SchemeAction

universe u

variable {k K : Type u} [Field k] [Field K]
  (f : Spec (.of K) ⟶ Spec (.of k))
  (G : Over (Spec (.of k))) {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X]
  [LocallyOfFiniteType G.hom] [CompactSpace G.left]
  [LocallyOfFiniteType X.hom] [CompactSpace X.left]
  (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)

attribute [local instance] Functor.modObjObj

local instance : IsLocallyNoetherian ((Over.pullback f).obj X).left :=
  LocallyOfFiniteType.isLocallyNoetherian ((Over.pullback f).obj X).hom

private theorem isPullback_orbitProjection :
    IsPullback ((Over.pullback f).map (orbitProjection G x)).left
      (pullback.fst G.hom f) (pullback.fst (orbitToBase G x) f) (toOrbit G x) := by
  simpa only [orbitOver, Over.mk_hom, orbitProjection_left] using
    Over.isPullback_pullback_map_left f (orbitProjection G x)

local instance : Surjective ((Over.pullback f).map (orbitProjection G x)).left :=
  MorphismProperty.of_isPullback (isPullback_orbitProjection f G x).flip inferInstance

local instance : IsSchemeTheoreticallyDominant
    ((Over.pullback f).map (orbitProjection G x)).left :=
  IsSchemeTheoreticallyDominant.of_isPullback (isPullback_orbitProjection f G x).flip

local instance : IsImmersion ((Over.pullback f).map (orbitInclusion G x)).left := by
  have : IsImmersion (orbitInclusion G x).left := by
    rw [orbitInclusion_left]
    infer_instance
  exact MorphismProperty.of_isPullback
    (Over.isPullback_pullback_map_left f (orbitInclusion G x)).flip inferInstance

/-- Extending the ground field identifies the new orbit scheme with the pullback of
the original orbit scheme, including any nonreduced structure. -/
def orbitBaseChangeIso :
    orbitScheme ((Over.pullback f).obj G)
        (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map x) ≅
      ((Over.pullback f).obj (orbitOver G x)).left :=
  Scheme.Hom.locallyClosedImageIsoOfFactorization
    (orbitMap ((Over.pullback f).obj G)
      (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map x)).left _
      ((Over.pullback f).map (orbitProjection G x)).left
      ((Over.pullback f).map (orbitInclusion G x)).left (by
        rw [← Over.comp_left, ← Functor.map_comp, orbitProjection_inclusion,
          (Over.pullback f).map_orbitMap G X x])

/-- The field-extension comparison intertwines the orbit immersions. -/
-- The pullback map simplifies before this left side; use this equation with rw.
@[reassoc]
theorem orbitBaseChangeIso_hom_inclusion :
    (orbitBaseChangeIso f G x).hom ≫ ((Over.pullback f).map (orbitInclusion G x)).left =
      orbitι ((Over.pullback f).obj G)
        (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map x) := by
  rw [orbitBaseChangeIso, orbitι_def]
  apply Scheme.Hom.locallyClosedImageIsoOfFactorization_hom_ι

/-- The inverse comparison respects the same ambient immersion. -/
@[reassoc (attr := simp)]
theorem orbitBaseChangeIso_inv_inclusion :
    (orbitBaseChangeIso f G x).inv ≫
        orbitι ((Over.pullback f).obj G)
          (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map x) =
      ((Over.pullback f).map (orbitInclusion G x)).left := by
  rw [Iso.inv_comp_eq, orbitBaseChangeIso_hom_inclusion]

/-- The comparison also intertwines the maps from the base-changed acting group. -/
@[reassoc (attr := simp)]
theorem toOrbit_orbitBaseChangeIso_hom :
    toOrbit ((Over.pullback f).obj G)
        (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map x) ≫
        (orbitBaseChangeIso f G x).hom =
      ((Over.pullback f).map (orbitProjection G x)).left := by
  rw [orbitBaseChangeIso, toOrbit_def]
  apply Scheme.Hom.toLocallyClosedImage_isoOfFactorization_hom

/-- The orbit immersions commute with the projection to the original ground field model. -/
@[reassoc (attr := simp)]
theorem orbitBaseChangeIso_hom_fst_ι :
    (orbitBaseChangeIso f G x).hom ≫ pullback.fst (orbitToBase G x) f ≫ orbitι G x =
      orbitι ((Over.pullback f).obj G)
          (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map x) ≫
        pullback.fst X.hom f := by
  have H := congrArg (fun a ↦ a ≫ pullback.fst X.hom f)
    (orbitBaseChangeIso_hom_inclusion f G x)
  simpa only [Category.assoc, Over.pullback_map_left, pullback.lift_fst,
    orbitInclusion_left, orbitOver, Over.mk_hom] using H

/-- The comparison is an isomorphism over the extended ground field. -/
@[reassoc (attr := simp)]
theorem orbitBaseChangeIso_hom_snd :
    (orbitBaseChangeIso f G x).hom ≫ pullback.snd (orbitToBase G x) f =
      orbitToBase ((Over.pullback f).obj G)
        (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map x) := by
  have H : (orbitBaseChangeIso f G x).hom ≫
      ((Over.pullback f).obj (orbitOver G x)).hom =
        orbitToBase ((Over.pullback f).obj G)
          (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map x) := by
    rw [← Over.w ((Over.pullback f).map (orbitInclusion G x)), ← Category.assoc,
      orbitBaseChangeIso_hom_inclusion, orbitToBase_def]
  simpa only [Over.pullback_obj_hom, orbitOver, Over.mk_hom] using H

/-- The inverse field-extension comparison is also over the ground field. -/
@[reassoc (attr := simp)]
theorem orbitBaseChangeIso_inv_toBase :
    (orbitBaseChangeIso f G x).inv ≫
        orbitToBase ((Over.pullback f).obj G)
          (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map x) =
      pullback.snd (orbitToBase G x) f := by
  rw [Iso.inv_comp_eq, orbitBaseChangeIso_hom_snd]

/-- Extending the ground field identifies the orbit scheme over `K` with the pullback of the
original orbit scheme, as schemes over `Spec K`. -/
def orbitOverBaseChangeIso :
    letI := (Over.pullback f).modObjObj G X
    orbitOver ((Over.pullback f).obj G)
        (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map x) ≅
      (Over.pullback f).obj (orbitOver G x) :=
  Over.isoMk (orbitBaseChangeIso f G x) (orbitBaseChangeIso_hom_snd f G x)

/-- Forgetting the extended ground field recovers `orbitBaseChangeIso.hom`. -/
@[simp]
theorem orbitOverBaseChangeIso_hom_left :
    (orbitOverBaseChangeIso f G x).hom.left = (orbitBaseChangeIso f G x).hom := (rfl)

/-- Forgetting the extended ground field on the inverse recovers `orbitBaseChangeIso.inv`. -/
@[simp]
theorem orbitOverBaseChangeIso_inv_left :
    (orbitOverBaseChangeIso f G x).inv.left = (orbitBaseChangeIso f G x).inv := (rfl)

/-- The comparison over `Spec K` intertwines the orbit inclusions. -/
@[reassoc]
theorem orbitOverBaseChangeIso_hom_inclusion :
    (orbitOverBaseChangeIso f G x).hom ≫ (Over.pullback f).map (orbitInclusion G x) =
      orbitInclusion ((Over.pullback f).obj G)
        (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map x) := by
  ext
  simpa using orbitBaseChangeIso_hom_inclusion f G x

/-- The inverse comparison over `Spec K` intertwines the orbit inclusions. -/
@[reassoc (attr := simp)]
theorem orbitOverBaseChangeIso_inv_inclusion :
    (orbitOverBaseChangeIso f G x).inv ≫
        orbitInclusion ((Over.pullback f).obj G)
          (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map x) =
      (Over.pullback f).map (orbitInclusion G x) := by
  rw [Iso.inv_comp_eq, orbitOverBaseChangeIso_hom_inclusion]

/-- The comparison over `Spec K` intertwines the projections from the base-changed group. -/
@[reassoc (attr := simp)]
theorem orbitProjection_orbitOverBaseChangeIso_hom :
    orbitProjection ((Over.pullback f).obj G)
        (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map x) ≫
        (orbitOverBaseChangeIso f G x).hom =
      (Over.pullback f).map (orbitProjection G x) := by
  ext
  simp

/-- The base-change comparison of orbit schemes is equivariant for the restricted action of the
base-changed group. -/
theorem isModHom_orbitOverBaseChangeIso_hom :
    letI := (Over.pullback f).modObjObj G X
    letI := (Over.pullback f).modObjObj G (orbitOver G x)
    IsModHom ((Over.pullback f).obj G) (orbitOverBaseChangeIso f G x).hom := by
  let := (Over.pullback f).modObjObj G X
  let := (Over.pullback f).modObjObj G (orbitOver G x)
  have : IsModHom ((Over.pullback f).obj G) ((Over.pullback f).map (orbitInclusion G x)) :=
    (Over.pullback f).modObjObj_isModHom G (orbitInclusion G x)
  have : Mono ((Over.pullback f).map (orbitInclusion G x)) := Over.mono_of_mono_left _
  refine ⟨(cancel_mono ((Over.pullback f).map (orbitInclusion G x))).mp ?_⟩
  simp only [Category.assoc, IsModHom.smul_hom,
    MonoidalCategory.selfLeftAction_actionHomRight, orbitOverBaseChangeIso_hom_inclusion]
  rw [← whiskerLeft_comp_assoc, orbitOverBaseChangeIso_hom_inclusion]

/-- The inverse base-change comparison of orbit schemes is also equivariant for the restricted
action of the base-changed group. -/
theorem isModHom_orbitOverBaseChangeIso_inv :
    letI := (Over.pullback f).modObjObj G X
    letI := (Over.pullback f).modObjObj G (orbitOver G x)
    IsModHom ((Over.pullback f).obj G) (orbitOverBaseChangeIso f G x).inv := by
  let := (Over.pullback f).modObjObj G X
  let := (Over.pullback f).modObjObj G (orbitOver G x)
  let := isModHom_orbitOverBaseChangeIso_hom f G x
  infer_instance

/-- Extending the ground field gives a cartesian square relating the structure morphisms of the
base-changed and original orbit schemes. -/
theorem isPullback_orbitToBase_baseChange :
    IsPullback
      (orbitToBase ((Over.pullback f).obj G)
        (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map x))
      ((orbitBaseChangeIso f G x).hom ≫ pullback.fst (orbitToBase G x) f)
      f (orbitToBase G x) :=
  (IsPullback.of_hasPullback (orbitToBase G x) f).flip.of_iso
    (orbitBaseChangeIso f G x).symm (.refl _) (.refl _) (.refl _)
    (by simp) (by simp) (by simp) (by simp)

/-- Extending the ground field gives a cartesian square relating the projections from the
base-changed and original groups onto their orbit schemes. -/
theorem isPullback_toOrbit_baseChange :
    IsPullback
      (toOrbit ((Over.pullback f).obj G)
        (Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map x))
      (pullback.fst G.hom f)
      ((orbitBaseChangeIso f G x).hom ≫ pullback.fst (orbitToBase G x) f)
      (toOrbit G x) :=
  (isPullback_orbitProjection f G x).of_iso
    (.refl _) (orbitBaseChangeIso f G x).symm (.refl _) (.refl _)
    (by rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom, Iso.comp_inv_eq,
      toOrbit_orbitBaseChangeIso_hom])
    (by simp) (by simp) (by simp)

end TauCeti.SchemeAction
