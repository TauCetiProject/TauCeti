/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Action
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Uniqueness
public import TauCeti.CategoryTheory.Comma.Over

/-!
# Orbit schemes under extension of algebraically closed fields

Extending the ground field commutes with the locally closed scheme image of an
orbit morphism. The comparison respects the immersion into the ambient scheme
and the parametrization by the acting group. It preserves the entire scheme
structure, without reducedness or smoothness assumptions on the group or the
acted-on scheme.

The action after base change is the native action transported by the monoidal
pullback functor. Its orbit morphism is the pullback of the original one.
Surjectivity and schematic dominance of the orbit factorization survive this
flat base change; uniqueness of locally closed image factorizations then gives
the comparison.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.c–7.f.
* The Stacks Project, Tag 01R5 (flat base change of scheme-theoretic images).
-/

public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace TauCeti.SchemeAction

universe u

variable {k K : Type u} [Field k] [Field K] [IsAlgClosed k]
  (f : Spec (.of K) ⟶ Spec (.of k))
  (G : Over (Spec (.of k))) {X : Over (Spec (.of k))} [GrpObj G] [ModObj G X]
  [LocallyOfFiniteType G.hom] [CompactSpace G.left]
  [LocallyOfFiniteType X.hom] [CompactSpace X.left]
  (x : 𝟙_ (Over (Spec (.of k))) ⟶ X)

attribute [local instance] Functor.modObjObj

local instance (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType ((Over.pullback f).obj Y).hom := by
  dsimp only [Over.pullback, Over.mk_hom]
  infer_instance

local instance (Y : Over (Spec (.of k))) [CompactSpace Y.left] :
    CompactSpace ((Over.pullback f).obj Y).left := by
  dsimp only [Over.pullback, Over.mk_left]
  infer_instance

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

variable [IsAlgClosed K]

/-- Extending algebraically closed ground fields identifies the new orbit scheme with
the pullback of the original orbit scheme, including its nonreduced structure. -/
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

end TauCeti.SchemeAction
