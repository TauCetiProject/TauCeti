/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Hilbert.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.IncidenceLocus
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Section
public import Mathlib.CategoryTheory.RepresentedBy

/-!
# Hilbert functors of closed subschemes

A closed immersion induces an injective map of Hilbert functors. A finite locally free
family of closed subschemes lies in its image exactly on the incidence locus of the
ambient defining ideal. Consequently, if the ambient Hilbert functor is representable,
the Hilbert functor of the closed subscheme is represented by a closed subscheme of it.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Opposite TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Hilbert

variable {X Y S : Scheme.{u}} (i : X ⟶ Y) (f : Y ⟶ S)

/-- The ambient morphism is a base change of `X ⟶ Y`. -/
lemma isPullback_ambientMap (T : Over S) :
    IsPullback (pullback.mapSnd T.hom f (i ≫ f) i rfl) (pullback.snd T.hom (i ≫ f))
      (pullback.snd T.hom f) i := by
  refine IsPullback.of_right ?_ (pullback.mapSnd_snd T.hom f (i ≫ f) i rfl)
    (IsPullback.of_hasPullback T.hom f)
  simpa only [pullback.mapSnd_fst, Category.assoc] using
    (IsPullback.of_hasPullback T.hom (i ≫ f))

/-- Changing the test scheme gives a cartesian square of ambient morphisms. -/
lemma isPullback_baseChange_ambientMap {T W : Over S} (a : W ⟶ T) :
    IsPullback ((Over.pullback (i ≫ f)).map a).left (pullback.mapSnd W.hom f (i ≫ f) i rfl)
      (pullback.mapSnd T.hom f (i ≫ f) i rfl) ((Over.pullback f).map a).left := by
  refine (IsPullback.of_bot ?_ ?_ (isPullback_ambientMap i f T)).flip
  · simpa only [Over.pullback_map_left, pullback.lift_snd] using isPullback_ambientMap i f W
  · apply pullback.hom_ext <;> simp [Over.pullback_map_left]

variable [IsClosedImmersion i]

instance (T : Over S) : IsClosedImmersion (pullback.mapSnd T.hom f (i ≫ f) i rfl) :=
  MorphismProperty.of_isPullback (isPullback_ambientMap i f T).flip inferInstance

end AlgebraicGeometry.Hilbert



namespace AlgebraicGeometry.Hilbert

variable {X Y S : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] (f : Y ⟶ S)

/-- A closed immersion induces the Hilbert-functor map given by the scheme-theoretic image
of each finite locally free closed family. -/
def closedImmersionι (d : ℕ) : hilbertFunctor (i ≫ f) d ⟶ hilbertFunctor f d where
  app T := TypeCat.ofHom fun J ↦ ⟨J.val.map (pullback.mapSnd T.unop.hom f (i ≫ f) i rfl),
    (mem_hilbertSubfunctor_obj_iff _ _).mpr (by
      apply Scheme.IdealSheafData.IsFiniteLocallyFreeOfDegree.map_of_isClosedImmersion
      simpa only [pullback.mapSnd_fst] using
        (mem_hilbertSubfunctor_obj_iff _ _).mp J.property)⟩
  naturality W W' a := by
    ext J : 3
    apply Subtype.ext
    exact (Scheme.IdealSheafData.ker_eq_comap_of_isPullback _
      ((J.val.isPullback_subschemeMap_comap (pullback.mapSnd W.unop.hom f (i ≫ f) i rfl)
        (isPullback_baseChange_ambientMap i f a.unop)).flip))

/-- The map of Hilbert functors pushes forward the defining ideal sheaf. -/
lemma closedImmersionι_app_val (d : ℕ) {T : Over S}
    (J : (hilbertFunctor (i ≫ f) d).obj (op T)) :
    Subtype.val (α := (pullback T.hom f).IdealSheafData)
      ((closedImmersionι i f d).app (op T) J) = J.val.map (pullback.mapSnd T.hom f (i ≫ f) i rfl) :=
  (rfl)

/-- Closed immersion of ambient schemes gives an injection on Hilbert families. -/
lemma closedImmersionι_app_injective (d : ℕ) (T : Over S) :
    Function.Injective ((closedImmersionι i f d).app (op T)) := by
  intro first second equality
  apply Subtype.ext
  have h := congrArg (fun point ↦ point.val.comap (pullback.mapSnd T.hom f (i ≫ f) i rfl)) equality
  simpa only [closedImmersionι_app_val,
    Scheme.IdealSheafData.comap_map_of_isClosedImmersion] using h

/-- A Hilbert family lies in the closed subscheme precisely when its ideal contains the
base-changed ambient defining ideal. -/
lemma exists_closedImmersionι_app_eq_iff (d : ℕ) {T : Over S}
    (I : (hilbertFunctor f d).obj (op T)) :
    (∃ J, (closedImmersionι i f d).app (op T) J = I) ↔
      (pullback.mapSnd T.hom f (i ≫ f) i rfl).ker ≤ I.val := by
  constructor
  · rintro ⟨J, rfl⟩
    rw [closedImmersionι_app_val, ← Scheme.IdealSheafData.map_bot]
    exact Scheme.IdealSheafData.map_mono _ bot_le
  · intro hI
    refine ⟨⟨I.val.comap (pullback.mapSnd T.hom f (i ≫ f) i rfl),
      (mem_hilbertSubfunctor_obj_iff _ _).mpr ?_⟩, Subtype.ext ?_⟩
    · have hdegree := Scheme.IdealSheafData.IsFiniteLocallyFreeOfDegree.comap_of_isClosedImmersion
        (pullback.mapSnd T.hom f (i ≫ f) i rfl) (pullback.fst T.hom f)
        ((mem_hilbertSubfunctor_obj_iff _ _).mp I.property) hI
      simpa only [pullback.mapSnd_fst] using hdegree
    · exact (Scheme.IdealSheafData.map_comap_of_isClosedImmersion I.val _).trans
        (sup_eq_left.mpr hI)

private lemma ker_ambientMap_eq_comap {T W : Over S} (a : W ⟶ T) :
    (pullback.mapSnd W.hom f (i ≫ f) i rfl).ker =
      (pullback.mapSnd T.hom f (i ≫ f) i rfl).ker.comap ((Over.pullback f).map a).left :=
  Scheme.IdealSheafData.ker_eq_comap_of_isPullback _
    (isPullback_baseChange_ambientMap i f a).flip

/-- For every finite locally free Hilbert family, containment in the closed ambient
subscheme is cut out by a single ideal sheaf on its parameter scheme. -/
theorem exists_idealSheafData_closedImmersionι_range (d : ℕ) (T : Over S)
    (point : (hilbertFunctor f d).obj (op T)) :
    ∃ K : T.left.IdealSheafData, ∀ (W : Over S) (a : W ⟶ T),
      (∃ family, (closedImmersionι i f d).app (op W) family =
        (hilbertFunctor f d).map a.op point) ↔ K ≤ a.left.ker := by
  have hdegree := (mem_hilbertSubfunctor_obj_iff _ _).mp point.property
  have := hdegree.isFinite
  have := hdegree.flat
  have := hdegree.locallyOfFinitePresentation
  refine ⟨Scheme.IdealSheafData.incidenceLocus (pullback.fst T.hom f)
    (pullback.mapSnd T.hom f (i ≫ f) i rfl).ker point.val, fun W a ↦ ?_⟩
  rw [exists_closedImmersionι_app_eq_iff, ker_ambientMap_eq_comap,
    hilbertFunctor_map_val]
  exact (Scheme.IdealSheafData.incidenceLocus_le_ker_iff_of_isPullback _ _
    (Over.isPullback_pullback_map_left f a)).symm

/-- A representation of the ambient Hilbert functor restricts to a representation by a
closed subscheme for the Hilbert functor of any closed ambient subscheme. -/
theorem exists_isClosedImmersion_representableBy {d : ℕ} {H : Over S}
    (representation : (hilbertFunctor f d).RepresentableBy H) :
    ∃ (Z : Over S) (j : Z ⟶ H), IsClosedImmersion j.left ∧
      ∃ smallerRepresentation : (hilbertFunctor (i ≫ f) d).RepresentableBy Z,
        ∀ {T : Over S} (a : T ⟶ Z),
          (closedImmersionι i f d).app (op T) (smallerRepresentation.homEquiv a) =
            representation.homEquiv (a ≫ j) := by
  let P := hilbertFunctor (i ≫ f) d
  let Φ := closedImmersionι i f d
  obtain ⟨K, hK⟩ := exists_idealSheafData_closedImmersionι_range i f d H
    (representation.homEquiv (𝟙 H))
  let Z : Over S := Over.mk (K.subschemeι ≫ H.hom)
  let j : Z ⟶ H := Over.homMk K.subschemeι
  have huniversal : ∃ point : P.obj (op Z),
      Φ.app (op Z) point = representation.homEquiv j := by
    rw [representation.homEquiv_eq]
    exact (hK Z j).mpr (by simp [j, Scheme.IdealSheafData.ker_subschemeι])
  obtain ⟨universal, huniversal⟩ := huniversal
  have hmap {T : Over S} (a : T ⟶ Z) :
      Φ.app (op T) (P.map a.op universal) = representation.homEquiv (a ≫ j) := by
    rw [representation.homEquiv_comp, ← huniversal, NatTrans.naturality_apply]
  have hinjective (T : Over S) :
      Function.Injective (fun a : T ⟶ Z ↦ P.map a.op universal) := by
    intro a b equality
    have hab : a ≫ j = b ≫ j := representation.homEquiv.injective
      ((hmap a).symm.trans ((congrArg (Φ.app (op T)) equality).trans (hmap b)))
    apply Over.OverMorphism.ext
    exact (cancel_mono K.subschemeι).mp (congrArg CommaMorphism.left hab)
  have hsurjective (T : Over S) :
      Function.Surjective (fun a : T ⟶ Z ↦ P.map a.op universal) := by
    intro point
    let a : T ⟶ H := representation.homEquiv.symm (Φ.app (op T) point)
    have hKa : K ≤ a.left.ker := (hK T a).mp ⟨point, by
      rw [← representation.homEquiv_eq, Equiv.apply_symm_apply]⟩
    let b : T ⟶ Z := Over.homMk (IsClosedImmersion.lift K.subschemeι a.left
      (by rwa [Scheme.IdealSheafData.ker_subschemeι])) (by
        simp only [Z, Over.mk_hom, IsClosedImmersion.lift_fac_assoc]
        exact Over.w a)
    have hb : b ≫ j = a := by
      apply Over.OverMorphism.ext
      exact IsClosedImmersion.lift_fac _ _ _
    refine ⟨b, closedImmersionι_app_injective i f d T ?_⟩
    rw [hmap, hb, Equiv.apply_symm_apply]
  have represented : P.IsRepresentedBy universal := ⟨fun {T} ↦ ⟨hinjective T, hsurjective T⟩⟩
  refine ⟨Z, j, inferInstanceAs (IsClosedImmersion K.subschemeι),
    represented.representableBy, ?_⟩
  intro T a
  simpa only [Functor.IsRepresentedBy.representableBy_homEquiv_apply] using hmap a

/-- Closed immersions of ambient schemes preserve representability of Hilbert functors. -/
theorem isRepresentable_hilbertFunctor_of_isClosedImmersion (d : ℕ)
    (h : (hilbertFunctor f d).IsRepresentable) :
    (hilbertFunctor (i ≫ f) d).IsRepresentable := by
  obtain ⟨H, ⟨representation⟩⟩ := h.has_representation
  obtain ⟨_, _, _, smallerRepresentation, _⟩ :=
    exists_isClosedImmersion_representableBy i f representation
  exact smallerRepresentation.isRepresentable

end AlgebraicGeometry.Hilbert
