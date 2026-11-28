/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

import TauCeti.CategoryTheory.Comma.Over
import TauCeti.CategoryTheory.Yoneda.Diagonal
public import TauCeti.AlgebraicGeometry.IdealSheaf.Functor
import TauCeti.AlgebraicGeometry.IdealSheaf.IncidenceLocus
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import TauCeti.AlgebraicGeometry.Morphisms.Separated.Representable

/-!
# Closed diagonals for functors of finite locally free closed subschemes

A functor with a monic classification into the functor of ideal sheaves has closed diagonal
whenever each of its closed families is finite locally free over the parameter scheme. The closed
subscheme representing a
pullback of the diagonal is the equality locus of the two families. Consequently every scheme
representing such a subfunctor is separated over the base.

No representability hypothesis on the classified functor is needed for the diagonal statement.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe u v

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- An ideal family is finite locally free over its parameter scheme when its closed subscheme
is finite, flat and locally finitely presented over that scheme. -/
structure IsFiniteLocallyFreeFamily {X S : Scheme.{u}} (f : X ⟶ S) (T : Over S)
    (I : (pullback T.hom f).IdealSheafData) : Prop where
  /-- The family is finite over its parameter scheme. -/
  isFinite : IsFinite (I.subschemeι ≫ pullback.fst T.hom f)
  /-- The family is flat over its parameter scheme. -/
  flat : Flat (I.subschemeι ≫ pullback.fst T.hom f)
  /-- The family is locally finitely presented over its parameter scheme. -/
  locallyOfFinitePresentation : LocallyOfFinitePresentation (I.subschemeι ≫ pullback.fst T.hom f)

end AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)
  (F : (Over S)ᵒᵖ ⥤ Type u) (α : F ⟶ baseChangeIdealSheafFunctor f) [Mono α]
  (hP : ∀ (T : Over S) (I : F.obj (op T)),
    (α.app (op T) I).IsFiniteLocallyFreeFamily f T)

include hP

omit hP in
/-- Equality of two finite locally free closed families is cut out by an ideal sheaf of their
parameter scheme. The criterion holds after every morphism of test schemes. -/
theorem exists_idealSheafData_le_ker_iff_map_eq {T : Over S} (I J : F.obj (op T))
    (hI : (α.app (op T) I).IsFiniteLocallyFreeFamily f T)
    (hJ : (α.app (op T) J).IsFiniteLocallyFreeFamily f T) :
    ∃ K : T.left.IdealSheafData, ∀ {W : Over S} (a : W ⟶ T),
      K ≤ a.left.ker ↔ F.map a.op I = F.map a.op J := by
  obtain ⟨hIfin, hIflat, hIfp⟩ := hI
  obtain ⟨hJfin, hJflat, hJfp⟩ := hJ
  refine ⟨Scheme.IdealSheafData.equalityLocus (pullback.fst T.hom f)
    (α.app (op T) I) (α.app (op T) J),
    fun {W} a ↦ ?_⟩
  rw [Scheme.IdealSheafData.equalityLocus_le_ker_iff_of_isPullback (α.app (op T) I) (α.app (op T) J)
    (Over.isPullback_pullback_map_left f a)]
  have hα (L : F.obj (op T)) : α.app (op W) (F.map a.op L) =
      (α.app (op T) L).comap ((Over.pullback f).map a).left := by
    simpa only [baseChangeIdealSheafFunctor_map_apply, Quiver.Hom.unop_op] using
      α.naturality_apply a.op L
  rw [← hα I, ← hα J]
  exact (CategoryTheory.injective_of_mono (α.app (op W))).eq_iff

omit hP in
private def diagonalLift {T : Over S} (a : yoneda.obj T ⟶ F ⨯ F)
    (K : T.left.IdealSheafData)
    (hK : ∀ {W : Over S} (c : W ⟶ T), K ≤ c.left.ker ↔
      F.map c.op (yonedaEquiv (a ≫ prod.fst)) =
        F.map c.op (yonedaEquiv (a ≫ prod.snd)))
    (cone : PullbackCone (diag F) a) :
    cone.pt ⟶ yoneda.obj (Over.mk (K.subschemeι ≫ T.hom)) := by
  refine {
    app W := TypeCat.ofHom fun x ↦ ?_
    naturality W W' g := ?_ }
  · let c : W.unop ⟶ T := cone.snd.app W x
    have hc : K ≤ c.left.ker :=
      (hK c).mpr (cone.map_yonedaEquiv_prod_fst_eq_snd x)
    exact Over.homMk (IsClosedImmersion.lift K.subschemeι c.left
      (by simpa only [Scheme.IdealSheafData.ker_subschemeι] using hc))
      (by simp only [Over.mk_hom, IsClosedImmersion.lift_fac_assoc, Over.w])
  · ext x
    apply Over.OverMorphism.ext
    rw [← cancel_mono K.subschemeι]
    simpa only [TypeCat.Fun.toFun_apply, yoneda_obj_map, types_comp_apply,
      TypeCat.ofHom_apply, Over.comp_left, Category.assoc,
      Over.homMk_left, IsClosedImmersion.lift_fac, IsClosedImmersion.lift_fac_assoc]
      using congrArg CommaMorphism.left (congrArg (fun q ↦ q x) (cone.snd.naturality g))

omit hP in
private theorem diagonalLift_fac {T : Over S} (a : yoneda.obj T ⟶ F ⨯ F)
    (K : T.left.IdealSheafData)
    (hK : ∀ {W : Over S} (c : W ⟶ T), K ≤ c.left.ker ↔
      F.map c.op (yonedaEquiv (a ≫ prod.fst)) =
        F.map c.op (yonedaEquiv (a ≫ prod.snd)))
    (cone : PullbackCone (diag F) a) :
    diagonalLift F a K hK cone ≫ yoneda.map (Over.homMk K.subschemeι) = cone.snd := by
  ext W x
  apply Over.OverMorphism.ext
  exact IsClosedImmersion.lift_fac _ _ _

/-- The pullback of the diagonal of a functor of finite locally free closed subschemes along
any map from a scheme is represented by a closed subscheme of that scheme. -/
theorem exists_isClosedImmersion_isPullback_diagonal {T : Over S}
    (a : yoneda.obj T ⟶ F ⨯ F) :
    ∃ (Z : Over S) (ι : Z ⟶ T) (b : yoneda.obj Z ⟶ F),
      IsClosedImmersion ι.left ∧ IsPullback b (yoneda.map ι) (diag F) a := by
  let I := yonedaEquiv (a ≫ prod.fst)
  let J := yonedaEquiv (a ≫ prod.snd)
  obtain ⟨K, hK⟩ := exists_idealSheafData_le_ker_iff_map_eq f F α I J (hP T I) (hP T J)
  let Z : Over S := Over.mk (K.subschemeι ≫ T.hom)
  let ι : Z ⟶ T := Over.homMk K.subschemeι
  let b : yoneda.obj Z ⟶ F := yoneda.map ι ≫ a ≫ prod.fst
  have heq : yoneda.map ι ≫ a ≫ prod.fst = yoneda.map ι ≫ a ≫ prod.snd := by
    apply yonedaEquiv.injective
    simpa only [I, J, yonedaEquiv_naturality, Category.assoc] using
      (hK ι).mp (by simp [ι, Scheme.IdealSheafData.ker_subschemeι])
  have comm : b ≫ diag F = yoneda.map ι ≫ a := by
    apply prod.hom_ext <;> simp [b, heq]
  refine ⟨Z, ι, b, (by simpa only [ι, Over.homMk_left] using
    (inferInstance : IsClosedImmersion K.subschemeι)), IsPullback.of_isLimit' ⟨comm⟩ ?_⟩
  have : Mono ι := by dsimp [ι]; infer_instance
  refine PullbackCone.IsLimit.mk _ (diagonalLift F a K hK) ?_
    (diagonalLift_fac F a K hK) ?_
  · intro cone
    dsimp only [b]
    rw [← Category.assoc, ← Category.assoc, diagonalLift_fac]
    simpa only [Category.assoc, diag, prod.lift_fst, Category.comp_id] using
      (cone.condition =≫ prod.fst).symm
  · intro cone m _hm₁ hm₂
    apply (cancel_mono (yoneda.map ι)).1
    rw [diagonalLift_fac]
    exact hm₂

/-- The diagonal of a functor of finite locally free closed subschemes is representable by
closed immersions of schemes over the base. -/
theorem isClosedImmersion_diagonal_of_mono_baseChangeIdealSheafFunctor :
    MorphismProperty.relative yoneda
      (MorphismProperty.inverseImage (@IsClosedImmersion : MorphismProperty Scheme.{u})
        (Over.forget S)) (diag F) := by
  have : MorphismProperty.RespectsIso (@IsClosedImmersion : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      (@IsClosedImmersion : MorphismProperty Scheme.{u}) (Over.forget S)) :=
    MorphismProperty.RespectsIso.inverseImage _ _
  apply MorphismProperty.relative.of_exists
  intro T a
  obtain ⟨Z, ι, b, hι, h⟩ := exists_isClosedImmersion_isPullback_diagonal f F α hP a
  exact ⟨Z, b, ι, h, hι⟩

/-- Every scheme representing a functor of finite locally free closed subschemes is separated
over the base. -/
theorem isSeparated_of_representableBy_of_mono_baseChangeIdealSheafFunctor {H : Over S}
    (e : F.RepresentableBy H) : IsSeparated H.hom :=
  isSeparated_of_representableBy_of_relative_diag
    (isClosedImmersion_diagonal_of_mono_baseChangeIdealSheafFunctor f F α hP) e

end TauCeti.AlgebraicGeometry
