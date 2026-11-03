/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Closed

/-!
# Kan fibrations of based mapping simplicial sets

The based mapping simplicial set preserves Kan fibrations in its target. In particular,
based maps into a Kan complex form a Kan complex, and simplicial loops preserve Kan complexes.
These are point-set lifting statements, independent of a stable model structure.

The proof uses the unpointed pullback-hom fibration for the inclusion of the basepoint.
Lifting against this map retains the prescribed basepoint, rather than merely lifting
in the unpointed mapping simplicial set.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Chapter I.
-/

public section

open CategoryTheory CategoryTheory.ConcreteCategory MonoidalCategory MonoidalClosed Limits
  HomotopicalAlgebra
open scoped Simplicial

universe u

namespace TauCeti.PointedSSet

open SSet.modelCategoryQuillen

variable {X E B : PointedSSet.{u}}

/-- Restriction of an unpointed mapping simplex to the chosen point of its source. -/
@[simp]
lemma pre_point_app (X E : PointedSSet.{u}) {n m : SimplexCategoryᵒᵖ}
    (φ : ((CategoryTheory.ihom X.right).obj E.right).obj n) (f : n ⟶ m)
    (z : (Δ[0] : SSet.{u}).obj m) :
    (((MonoidalClosed.pre X.hom).app E.right).app n φ).app m f z =
      φ.app m f (X.point m) := by
  have h := congrArg (fun k : (Δ[0] : SSet.{u}) ⊗
      (CategoryTheory.ihom X.right).obj E.right ⟶ E.right ↦
    k.app m (z, ((CategoryTheory.ihom X.right).obj E.right).map f φ))
      (id_tensor_pre_app_comp_ev X.hom E.right)
  -- Evaluation applies a mapping simplex at the identity; simplicial restriction by `f`
  -- turns that identity component into its `f` component.
  change (((MonoidalClosed.pre X.hom).app E.right).app m
    (((CategoryTheory.ihom X.right).obj E.right).map f φ)).app m (𝟙 m) z =
      (((CategoryTheory.ihom X.right).obj E.right).map f φ).app m (𝟙 m)
        (X.hom.app m z) at h
  have hn := congrArg (fun ψ : ((CategoryTheory.ihom (Δ[0] : SSet.{u})).obj
      E.right).obj m ↦ ψ.app m (𝟙 m) z)
    (NatTrans.naturality_apply ((MonoidalClosed.pre X.hom).app E.right) f φ)
  have result := hn.symm.trans h
  -- The simplicial operator on the native internal hom precomposes its simplex index.
  change (((MonoidalClosed.pre X.hom).app E.right).app n φ).app m (f ≫ 𝟙 m) z =
    φ.app m (f ≫ 𝟙 m) (X.hom.app m z) at result
  simpa only [Category.comp_id, hom_app] using result

/-- The constant family of maps from the zero-simplex to the chosen point of `E`. -/
def pointRestriction (E : PointedSSet.{u}) (K : SSet.{u}) :
    K ⟶ (CategoryTheory.ihom (Δ[0] : SSet.{u})).obj E.right where
  app _ := ↾fun _ ↦ Functor.HomObj.ofNatTrans E.hom

/-- Every component of the constant family is the chosen point. -/
@[simp]
lemma pointRestriction_app_app (E : PointedSSet.{u}) (K : SSet.{u})
    {n m : SimplexCategoryᵒᵖ} (x : K.obj n) (f : n ⟶ m) (z : (Δ[0] : SSet.{u}).obj m) :
    ((pointRestriction E K).app n x).app m f z = E.point m :=
  hom_app E m z

/-- Constant families at the basepoint are natural in their parameter. -/
@[reassoc (attr := simp)]
lemma comp_pointRestriction (E : PointedSSet.{u}) {K L : SSet.{u}} (f : K ⟶ L) :
    f ≫ pointRestriction E L = pointRestriction E K := (rfl)

/-- Based maps preserve the constant family at the basepoint. -/
@[reassoc (attr := simp)]
lemma pointRestriction_comp_ihom_map (p : E ⟶ B) (K : SSet.{u}) :
    pointRestriction E K ≫ (CategoryTheory.ihom (Δ[0] : SSet.{u})).map p.right =
      pointRestriction B K := by
  ext n : 1
  apply ConcreteCategory.hom_ext
  intro x
  apply Functor.functorHom_ext fun m f ↦ ?_
  ext z
  -- Postcomposition on the unpointed internal hom composes its component maps.
  change p.right.app m (E.hom.app m z) = B.hom.app m z
  simp only [hom_app, app_point]

/-- A family of unpointed maps is based exactly when restriction to the source basepoint
is the constant family at the target basepoint. -/
lemma range_le_basedMaps_iff (X E : PointedSSet.{u}) {K : SSet.{u}}
    (f : K ⟶ (CategoryTheory.ihom X.right).obj E.right) :
    SSet.Subcomplex.range f ≤ basedMaps X E ↔
      f ≫ (MonoidalClosed.pre X.hom).app E.right = pointRestriction E K := by
  constructor
  · intro hf
    ext n : 1
    apply ConcreteCategory.hom_ext
    intro x
    apply Functor.functorHom_ext fun m g ↦ ?_
    ext z
    exact (pre_point_app X E (f.app n x) g z).trans
      (((mem_basedMaps_iff _).1 (hf n ⟨x, rfl⟩) m g).trans
        (pointRestriction_app_app E K x g z).symm)
  · intro hf n φ hφ
    obtain ⟨x, rfl⟩ := hφ
    apply (mem_basedMaps_iff _).2
    intro m g
    have h := congrArg (fun k : K ⟶ (CategoryTheory.ihom (Δ[0] : SSet.{u})).obj E.right ↦
      (k.app n x).app m g (SSet.stdSimplex.const 0 0 m)) hf
    exact (pre_point_app X E (f.app n x) g _).symm.trans
      (h.trans (pointRestriction_app_app E K x g _))

/-- The inclusion of based maps restricts to the constant family at the basepoint. -/
@[reassoc (attr := simp)]
lemma basedMaps_ι_comp_pre (X E : PointedSSet.{u}) :
    (basedMaps X E).ι ≫ (MonoidalClosed.pre X.hom).app E.right =
      pointRestriction E (basedMaps X E).toSSet :=
  (range_le_basedMaps_iff X E _).1 (by rintro n _ ⟨φ, rfl⟩; exact φ.2)

/-- The based mapping simplicial set is the fibre of restriction to the source basepoint
at the target basepoint, expressed as a pullback over the zero-simplex. -/
theorem basedMaps_isPullback (X E : PointedSSet.{u}) :
    IsPullback (basedMaps X E).ι (SSet.stdSimplex.isTerminalObj₀.from _)
      ((MonoidalClosed.pre X.hom).app E.right) (pointRestriction E Δ[0]) := by
  have hw : (basedMaps X E).ι ≫ (MonoidalClosed.pre X.hom).app E.right =
      SSet.stdSimplex.isTerminalObj₀.from _ ≫ pointRestriction E Δ[0] := by simp
  let lift (s : PullbackCone ((MonoidalClosed.pre X.hom).app E.right)
      (pointRestriction E Δ[0])) : s.pt ⟶ (basedMaps X E).toSSet :=
    SSet.Subcomplex.lift s.fst ((range_le_basedMaps_iff X E _).2
      (s.condition.trans (comp_pointRestriction E s.snd)))
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw lift
    (fun _ ↦ SSet.Subcomplex.lift_ι _ _)
    (fun _ ↦ SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)
    (fun s m hm _ ↦ (cancel_mono (basedMaps X E).ι).1
      (hm.trans (SSet.Subcomplex.lift_ι _ _).symm)))

/-- Inclusion of based maps into unpointed maps commutes with postcomposition. -/
@[simp, reassoc]
lemma ihom_map_right_comp_ι (X : PointedSSet.{u}) (p : E ⟶ B) :
    ((PointedSSet.ihom X).map p).right ≫ (basedMaps X B).ι =
      (basedMaps X E).ι ≫ (CategoryTheory.ihom X.right).map p.right := by
  ext n : 1
  rfl

/-- The based mapping simplicial set preserves Kan fibrations in the target. -/
instance fibration_ihom_map (X : PointedSSet.{u}) (p : E ⟶ B) [Fibration p.right] :
    Fibration ((PointedSSet.ihom X).map p).right := by
  -- Expose the subcomplex carriers of the based mapping objects for the lifting square.
  dsimp only [PointedSSet.ihom]
  -- The unpointed corner map imposes both the target map and the fixed basepoint.
  have : Mono X.hom := SSet.stdSimplex.isTerminalObj₀.mono_from X.hom
  let Q := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom X.hom p.right
  -- Normalize the bifunctor presentation to its unpointed internal-hom objects.
  dsimp only [MonoidalClosed.internalHom] at Q
  have : Fibration Q.π := SSet.fibration_pullbackObjObjπ Q
  have hfst : Q.π ≫ Q.fst = (MonoidalClosed.pre X.hom).app E.right := Q.π_fst
  have hsnd : Q.π ≫ Q.snd = (CategoryTheory.ihom X.right).map p.right := Q.π_snd
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A D i hi
  have hQ : HasLiftingProperty i Q.π :=
    (SSet.modelCategoryQuillen.fibration_iff Q.π).1 inferInstance i hi
  constructor
  intro a b sq
  let b' : D ⟶ Q.pt := Q.isPullback.lift (pointRestriction E D)
    (b ≫ (basedMaps X B).ι) (by
      exact (pointRestriction_comp_ihom_map p D).trans
        ((b ≫= basedMaps_ι_comp_pre X B).trans (comp_pointRestriction B b)).symm)
  have sq' : CommSq (a ≫ (basedMaps X E).ι) i Q.π b' := by
    constructor
    apply Q.hom_ext
    · simpa only [Category.assoc, hfst, b', IsPullback.lift_fst] using
        ((a ≫= basedMaps_ι_comp_pre X E).trans (comp_pointRestriction E a)).trans
          (comp_pointRestriction E i).symm
    · simpa only [Category.assoc, hsnd, b', IsPullback.lift_snd] using
        (a ≫= (ihom_map_right_comp_ι X p).symm).trans
          (sq.w =≫ (basedMaps X B).ι)
  have : sq'.HasLift := hQ.sq_hasLift sq'
  -- The first corner equation says that the unpointed lift is still based.
  let l := sq'.lift
  have hl : SSet.Subcomplex.range l ≤ basedMaps X E := by
    rw [range_le_basedMaps_iff]
    have h := sq'.fac_right =≫ Q.fst
    simpa only [Category.assoc, hfst, l, b', IsPullback.lift_fst] using h
  refine ⟨⟨SSet.Subcomplex.lift l hl, ?_, ?_⟩⟩
  · apply (cancel_mono (basedMaps X E).ι).1
    simpa only [Category.assoc, SSet.Subcomplex.lift_ι] using sq'.fac_left
  · apply (cancel_mono (basedMaps X B).ι).1
    have h := sq'.fac_right =≫ Q.snd
    have hlp : l ≫ (CategoryTheory.ihom X.right).map p.right = b ≫ (basedMaps X B).ι := by
      simpa only [Category.assoc, hsnd, l, b', IsPullback.lift_snd] using h
    exact (Category.assoc _ _ _).trans
      ((SSet.Subcomplex.lift l hl ≫= ihom_map_right_comp_ι X p).trans
        ((Category.assoc _ _ _).symm.trans ((SSet.Subcomplex.lift_ι l hl =≫ _).trans hlp)))

/-- Based maps into a Kan complex form a Kan complex, with no hypothesis on the source. -/
instance kanComplex_ihom (X E : PointedSSet.{u}) [SSet.KanComplex E.right] :
    SSet.KanComplex ((PointedSSet.ihom X).obj E).right := by
  have : Mono X.hom := SSet.stdSimplex.isTerminalObj₀.mono_from X.hom
  have hf : Fibration (SSet.stdSimplex.isTerminalObj₀.from (basedMaps X E).toSSet) := by
    rw [SSet.modelCategoryQuillen.fibration_iff]
    exact MorphismProperty.of_isPullback (basedMaps_isPullback X E)
      ((SSet.modelCategoryQuillen.fibration_iff _).1 inferInstance)
  exact (isFibrant_iff_of_isTerminal _ SSet.stdSimplex.isTerminalObj₀).2 hf

end TauCeti.PointedSSet
