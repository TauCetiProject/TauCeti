/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Spectra.MappingSpace
public import TauCeti.CategoryTheory.Monoidal.Mod.Free.Closed
import Mathlib.CategoryTheory.Adjunction.Whiskering
import TauCeti.CategoryTheory.Adjunction.Unique

/-!
# Cotensors of symmetric spectra

The cotensor `E^K` of a symmetric spectrum with a pointed simplicial set has levels
`Map_*(K, E_n)`. Its sphere action is the existing action on the internal function spectrum
`Hom_S(F₀ K, E)`, and it is right adjoint to smashing each level with `K`.

The level formula uses the free-module internal-hom comparison and the uniqueness of right
adjoints. Mathlib's `Adjunction.whiskerRight` gives the adjunction between pointwise smash and
pointwise mapping objects on symmetric sequences; the identity-shuffle isomorphism identifies
the first functor with Day convolution by the sequence concentrated in degree zero.

The same uniqueness of right adjoints, paired with the levelwise smash comparison
`levelSmashFreeIso : (F_n K) ∧ L ≅ F_n (K ∧ L)`, identifies the pointed mapping space
`Map(F_n K, E)` out of a free symmetric spectrum with `Map_*(K, E_n)` (`mappingSpaceFreeIso`),
and in particular `Map(F_n S⁰, E) ≅ E_n` (`mappingSpaceFreeZeroIso`).

These are point-set constructions. No model structure or derived adjunction is asserted.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Sections 1 and 2.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.SymmetricSequence

open scoped DayFunctor

/-- The symmetric sequence of pointed mapping objects `n ↦ Map_*(K, X_n)`, with permutations
acting by postcomposition. -/
noncomputable abbrev levelwiseIhom (K : PointedSSet.{0}) :
    SymmetricSequence.{0} ⥤ SymmetricSequence.{0} :=
  (DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor ⋙
    (Functor.whiskeringRight FiniteBijection PointedSSet.{0} PointedSSet.{0}).obj
      (CategoryTheory.ihom K) ⋙
    (DayFunctor.equiv FiniteBijection PointedSSet.{0}).inverse

private noncomputable abbrev pointwiseSmash (K : PointedSSet.{0}) :
    SymmetricSequence.{0} ⥤ SymmetricSequence.{0} :=
  (DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor ⋙
    (Functor.whiskeringRight FiniteBijection PointedSSet.{0} PointedSSet.{0}).obj
      (MonoidalCategory.tensorLeft K) ⋙
    (DayFunctor.equiv FiniteBijection PointedSSet.{0}).inverse

private lemma pointwiseSmash_obj_obj (K : PointedSSet.{0}) (X : SymmetricSequence.{0})
    (c : FiniteBijection) :
    ((pointwiseSmash K).obj X).functor.obj c = K ⊗ X.functor.obj c := rfl

private lemma pointwiseSmash_obj_map (K : PointedSSet.{0}) (X : SymmetricSequence.{0})
    {c d : FiniteBijection} (σ : c ⟶ d) :
    ((pointwiseSmash K).obj X).functor.map σ = K ◁ X.functor.map σ := rfl

private lemma pointwiseSmash_map_app (K : PointedSSet.{0})
    {X Y : SymmetricSequence.{0}} (f : X ⟶ Y) (c : FiniteBijection) :
    ((pointwiseSmash K).map f).natTrans.app c = K ◁ f.natTrans.app c := rfl

private noncomputable def pointwiseSmashAdjunction (K : PointedSSet.{0}) :
    pointwiseSmash K ⊣ levelwiseIhom K :=
  (DayFunctor.equiv FiniteBijection PointedSSet.{0}).toAdjunction |>.comp
    (((CategoryTheory.ihom.adjunction K).whiskerRight FiniteBijection).comp
      (DayFunctor.equiv FiniteBijection PointedSSet.{0}).symm.toAdjunction)

private noncomputable def pointwiseSmashι (K : PointedSSet.{0}) (X : SymmetricSequence.{0}) :
    (pointwiseSmash K).obj X ⟶ X ⊗ (free 0).obj K :=
  .mk
    { app c := (β_ K (X.functor.obj c)).hom ≫ tensorFreeZeroι X K c.len
      naturality := by
        rintro ⟨n⟩ ⟨m⟩ σ
        simp only [pointwiseSmash_obj_obj, pointwiseSmash_obj_map]
        rw [Category.assoc, ← map_whiskerRight_comp_tensorFreeZeroι,
          BraidedCategory.braiding_naturality_right_assoc] }

private lemma pointwiseSmashι_app (K : PointedSSet.{0}) (X : SymmetricSequence.{0})
    (c : FiniteBijection) :
    (pointwiseSmashι K X).natTrans.app c =
      (β_ K (X.functor.obj c)).hom ≫ tensorFreeZeroι X K c.len := rfl

private instance (K : PointedSSet.{0}) (X : SymmetricSequence.{0}) :
    IsIso (pointwiseSmashι K X) := by
  have : ∀ c : FiniteBijection,
      IsIso (((DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor.map
        (pointwiseSmashι K X)).app c) := by
    rintro ⟨n⟩
    exact IsIso.comp_isIso' (β_ K (X.functor.obj (FiniteBijection.mk n))).isIso_hom
      (isIso_tensorFreeZeroι X K n)
  have : IsIso ((DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor.map
      (pointwiseSmashι K X)) := NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso _ (DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor

private noncomputable def pointwiseSmashRightIso (K : PointedSSet.{0}) :
    pointwiseSmash K ≅ MonoidalCategory.tensorRight ((free 0).obj K) :=
  NatIso.ofComponents
    (fun X ↦ asIso (pointwiseSmashι K X))
    (by
      intro X Y f
      apply DayFunctor.hom_ext
      apply NatTrans.ext
      funext c
      rcases c with ⟨n⟩
      simp only [pointwiseSmash_obj_obj, DayFunctor.comp_natTrans, NatTrans.comp_app,
        pointwiseSmash_map_app,
        asIso_hom, pointwiseSmashι_app, Functor.flip_obj_map, curriedTensor_map_app]
      rw [Category.assoc, ← tensorFreeZeroι_naturality_left,
        BraidedCategory.braiding_naturality_right_assoc])

private lemma pointwiseSmashRightIso_hom_app (K : PointedSSet.{0})
    (X : SymmetricSequence.{0}) (c : FiniteBijection) :
    ((pointwiseSmashRightIso K).hom.app X).natTrans.app c =
      (β_ K (X.functor.obj c)).hom ≫ tensorFreeZeroι X K c.len := rfl

private noncomputable def pointwiseSmashIso (K : PointedSSet.{0}) :
    pointwiseSmash K ≅ MonoidalCategory.tensorLeft ((free 0).obj K) :=
  pointwiseSmashRightIso K ≪≫
    (BraidedCategory.tensorLeftIsoTensorRight ((free 0).obj K)).symm

private lemma pointwiseSmashIso_hom_app (K : PointedSSet.{0})
    (X : SymmetricSequence.{0}) (c : FiniteBijection) :
    ((pointwiseSmashIso K).hom.app X).natTrans.app c =
      (β_ K (X.functor.obj c)).hom ≫ tensorFreeZeroι X K c.len ≫
        ((β_ ((free 0).obj K) X).inv).natTrans.app c := by
  simp only [pointwiseSmash_obj_obj, pointwiseSmashIso, Iso.trans_hom,
    NatTrans.comp_app, Iso.symm_hom,
    BraidedCategory.tensorLeftIsoTensorRight_inv_app, DayFunctor.comp_natTrans,
    NatTrans.comp_app, pointwiseSmashRightIso_hom_app, Category.assoc]

private noncomputable def pointwiseSmashMap {K L : PointedSSet.{0}} (f : K ⟶ L) :
    pointwiseSmash K ⟶ pointwiseSmash L :=
  Functor.whiskerLeft (DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor
    (Functor.whiskerRight
      ((Functor.whiskeringRight FiniteBijection PointedSSet.{0} PointedSSet.{0}).map
        ((tensoringLeft PointedSSet.{0}).map f))
      (DayFunctor.equiv FiniteBijection PointedSSet.{0}).inverse)

private lemma pointwiseSmashMap_app {K L : PointedSSet.{0}} (f : K ⟶ L)
    (X : SymmetricSequence.{0}) (c : FiniteBijection) :
    ((pointwiseSmashMap f).app X).natTrans.app c = f ▷ X.functor.obj c := rfl

private lemma pointwiseSmashRightIso_naturality {K L : PointedSSet.{0}} (f : K ⟶ L) :
    pointwiseSmashMap f ≫ (pointwiseSmashRightIso L).hom =
      (pointwiseSmashRightIso K).hom ≫
        (tensoringRight SymmetricSequence.{0}).map ((free 0).map f) := by
  apply NatTrans.ext
  funext X
  apply DayFunctor.hom_ext
  apply NatTrans.ext
  funext c
  rcases c with ⟨n⟩
  simp only [pointwiseSmash_obj_obj, NatTrans.comp_app, DayFunctor.comp_natTrans,
    NatTrans.comp_app, pointwiseSmashMap_app, pointwiseSmashRightIso_hom_app,
    Functor.flip_map_app, curriedTensor_obj_map]
  rw [Category.assoc, ← tensorFreeZeroι_naturality_right,
    BraidedCategory.braiding_naturality_left_assoc]

private lemma pointwiseSmashIso_naturality {K L : PointedSSet.{0}} (f : K ⟶ L) :
    pointwiseSmashMap f ≫ (pointwiseSmashIso L).hom =
      (pointwiseSmashIso K).hom ≫
        (tensoringLeft SymmetricSequence.{0}).map ((free 0).map f) := by
  simp only [pointwiseSmashIso, Iso.trans_hom, Category.assoc]
  rw [← Category.assoc, pointwiseSmashRightIso_naturality, Category.assoc]
  congr 1
  apply NatTrans.ext
  funext X
  exact BraidedCategory.braiding_inv_naturality_right X ((free 0).map f)

/-- Mapping out of `G₀ K` in the closed Day convolution category is levelwise pointed mapping.
The comparison is the right-adjoint mate of the identity-shuffle level isomorphism. -/
noncomputable def freeZeroIhomIso (K : PointedSSet.{0}) :
    DayFunctor.internalHom ((free 0).obj K) ≅ levelwiseIhom K :=
  asIso (conjugateEquiv (DayFunctor.internalHomAdjunction ((free 0).obj K))
    (pointwiseSmashAdjunction K) (pointwiseSmashIso K).hom)

private lemma pointwiseSmashAdjunction_counit_app (K : PointedSSet.{0})
    (X : SymmetricSequence.{0}) (n : ℕ) :
    ((pointwiseSmashAdjunction K).counit.app X).natTrans.app
        (FiniteBijection.mk n) =
      (CategoryTheory.ihom.ev K).app (X.functor.obj (FiniteBijection.mk n)) := by
  simp [pointwiseSmashAdjunction, Adjunction.comp_counit_app,
    Equivalence.toAdjunction_counit, DayFunctor.equiv]

private noncomputable def pointwiseIhomPre {K L : PointedSSet.{0}} (f : K ⟶ L) :
    levelwiseIhom L ⟶ levelwiseIhom K :=
  conjugateEquiv (pointwiseSmashAdjunction L) (pointwiseSmashAdjunction K)
    (pointwiseSmashMap f)

private lemma pointwiseIhomPre_app_natTrans_app {K L : PointedSSet.{0}} (f : K ⟶ L)
    (X : SymmetricSequence.{0}) (n : ℕ) :
    ((pointwiseIhomPre f).app X).natTrans.app (FiniteBijection.mk n) =
      (MonoidalClosed.pre f).app (X.functor.obj (FiniteBijection.mk n)) := by
  have h := conjugateEquiv_counit (pointwiseSmashAdjunction L)
    (pointwiseSmashAdjunction K) (pointwiseSmashMap f) X
  have hc := congrArg (fun g ↦ g.natTrans.app (FiniteBijection.mk n)) h
  simp only [pointwiseSmash_obj_obj, DayFunctor.comp_natTrans, NatTrans.comp_app,
    pointwiseSmash_map_app,
    pointwiseSmashMap_app, pointwiseSmashAdjunction_counit_app] at hc
  exact MonoidalClosed.uncurry_injective
    (hc.trans (MonoidalClosed.uncurry_pre f _).symm)

/-- In each level, the Day internal hom out of `G₀ K` is the pointed mapping object out of `K`.
The symmetric action on the mapping object is induced by postcomposition. -/
noncomputable def freeZeroIhomLevelIso (K : PointedSSet.{0}) (X : SymmetricSequence.{0})
    (n : ℕ) :
    ((DayFunctor.internalHom ((free 0).obj K)).obj X).functor.obj
        (FiniteBijection.mk n) ≅
      (CategoryTheory.ihom K).obj (X.functor.obj (FiniteBijection.mk n)) :=
  ((DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor.mapIso
    ((freeZeroIhomIso K).app X)).app (FiniteBijection.mk n)

/-- Evaluation after the level comparison is evaluation in the closed Day category restricted
to the identity shuffle, with the two smash coordinates interchanged. This characterizes the
comparison without unfolding either mapping object. -/
@[reassoc]
lemma whiskerLeft_freeZeroIhomLevelIso_hom_comp_ev (K : PointedSSet.{0})
    (X : SymmetricSequence.{0}) (n : ℕ) :
    K ◁ (freeZeroIhomLevelIso K X n).hom ≫
        (CategoryTheory.ihom.ev K).app (X.functor.obj (FiniteBijection.mk n)) =
      (β_ K _).hom ≫
        tensorFreeZeroι ((DayFunctor.internalHom ((free 0).obj K)).obj X) K n ≫
        ((β_ ((free 0).obj K) _).inv).natTrans.app (FiniteBijection.mk n) ≫
        (DayFunctor.ev ((free 0).obj K) X).natTrans.app (FiniteBijection.mk n) := by
  have h := conjugateEquiv_counit
    (DayFunctor.internalHomAdjunction ((free 0).obj K))
    (pointwiseSmashAdjunction K) (pointwiseSmashIso K).hom X
  have hday : (DayFunctor.internalHomAdjunction ((free 0).obj K)).counit.app X =
      DayFunctor.ev ((free 0).obj K) X :=
    DayFunctor.ihom_ev_app ((free 0).obj K) X
  rw [hday] at h
  have hc := congrArg (fun g ↦ g.natTrans.app (FiniteBijection.mk n)) h
  simp only [pointwiseSmash_obj_obj, DayFunctor.comp_natTrans, NatTrans.comp_app,
    pointwiseSmash_map_app, pointwiseSmashAdjunction_counit_app,
    pointwiseSmashIso_hom_app, Category.assoc] at hc
  exact hc

/-- The level comparison is natural in the target symmetric sequence. -/
@[simp↓, reassoc (attr := simp↓)]
lemma freeZeroIhomLevelIso_hom_naturality (K : PointedSSet.{0})
    {X Y : SymmetricSequence.{0}} (f : X ⟶ Y) (n : ℕ) :
    ((DayFunctor.internalHom ((free 0).obj K)).map f).natTrans.app
        (FiniteBijection.mk n) ≫ (freeZeroIhomLevelIso K Y n).hom =
      (freeZeroIhomLevelIso K X n).hom ≫
        (CategoryTheory.ihom K).map (f.natTrans.app (FiniteBijection.mk n)) :=
  congrArg (fun g ↦ g.natTrans.app (FiniteBijection.mk n))
    ((freeZeroIhomIso K).hom.naturality f)

/-- The level comparison is equivariant for every finite bijection. -/
@[simp↓, reassoc (attr := simp↓)]
lemma map_comp_freeZeroIhomLevelIso_hom (K : PointedSSet.{0})
    (X : SymmetricSequence.{0}) {n m : ℕ}
    (σ : FiniteBijection.mk n ⟶ FiniteBijection.mk m) :
    ((DayFunctor.internalHom ((free 0).obj K)).obj X).functor.map σ ≫
        (freeZeroIhomLevelIso K X m).hom =
      (freeZeroIhomLevelIso K X n).hom ≫
        (CategoryTheory.ihom K).map (X.functor.map σ) :=
  ((freeZeroIhomIso K).hom.app X).natTrans.naturality σ

/-- Precomposition of mapping objects in `K` agrees with precomposition of the levelwise pointed
mapping objects under the level formula. -/
@[reassoc]
lemma freeZeroIhomLevelIso_hom_naturality_left {K L : PointedSSet.{0}} (f : K ⟶ L)
    (X : SymmetricSequence.{0}) (n : ℕ) :
    ((MonoidalClosed.pre ((free 0).map f)).app X).natTrans.app
        (FiniteBijection.mk n) ≫ (freeZeroIhomLevelIso K X n).hom =
      (freeZeroIhomLevelIso L X n).hom ≫
        (MonoidalClosed.pre f).app (X.functor.obj (FiniteBijection.mk n)) := by
  have h : MonoidalClosed.pre ((free 0).map f) ≫ (freeZeroIhomIso K).hom =
      (freeZeroIhomIso L).hom ≫ pointwiseIhomPre f := by
    -- The native closed structure on Day functors selects precisely this adjunction.
    change conjugateEquiv (DayFunctor.internalHomAdjunction ((free 0).obj L))
        (DayFunctor.internalHomAdjunction ((free 0).obj K))
        ((tensoringLeft SymmetricSequence.{0}).map ((free 0).map f)) ≫
        conjugateEquiv (DayFunctor.internalHomAdjunction ((free 0).obj K))
          (pointwiseSmashAdjunction K) (pointwiseSmashIso K).hom =
      conjugateEquiv (DayFunctor.internalHomAdjunction ((free 0).obj L))
        (pointwiseSmashAdjunction L) (pointwiseSmashIso L).hom ≫
        conjugateEquiv (pointwiseSmashAdjunction L) (pointwiseSmashAdjunction K)
          (pointwiseSmashMap f)
    rw [conjugateEquiv_comp, conjugateEquiv_comp, pointwiseSmashIso_naturality]
  have hc := congrArg (fun g ↦ (g.app X).natTrans.app (FiniteBijection.mk n)) h
  simp only [NatTrans.comp_app, DayFunctor.comp_natTrans, NatTrans.comp_app,
    pointwiseIhomPre_app_natTrans_app] at hc
  exact hc

end TauCeti.SymmetricSequence

namespace TauCeti.SymmetricSpectrum

open scoped DayFunctor

/-- Smashing every level with a fixed pointed simplicial set, with the sphere acting on the
spectrum coordinate. On objects this is the existing `levelSmash` construction. -/
noncomputable abbrev levelSmashRight (K : PointedSSet.{0}) :
    SymmetricSpectrum ⥤ SymmetricSpectrum :=
  Mod.tensorRight ((SymmetricSequence.free 0).obj K)

/-- The point-set cotensor `E^K`: the internal function spectrum from the free spectrum `F₀ K`.
Its levels are the pointed mapping objects `Map_*(K, E_n)` (`cotensorLevelIso`). -/
noncomputable abbrev cotensor (K : PointedSSet.{0}) :
    SymmetricSpectrum ⥤ SymmetricSpectrum :=
  Mod.internalHom ((free 0).obj K)

/-- Levelwise smash with `K` is left adjoint to the cotensor by `K`. -/
noncomputable def levelSmashCotensorAdjunction (K : PointedSSet.{0}) :
    levelSmashRight K ⊣ cotensor K :=
  (Mod.internalHomAdjunction ((free 0).obj K)).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight ((free 0).obj K) ≪≫
      Mod.tensorRightFreeIso ((SymmetricSequence.free 0).obj K))

/-- Smashing symmetric spectra with a fixed pointed simplicial set `K` is a left adjoint, hence
preserves colimits of all sizes. -/
instance (K : PointedSSet.{0}) : (levelSmashRight K).IsLeftAdjoint :=
  (levelSmashCotensorAdjunction K).isLeftAdjoint

/-- Cotensoring symmetric spectra by a fixed pointed simplicial set `K` is a right adjoint, hence
preserves limits of all sizes. -/
instance (K : PointedSSet.{0}) : (cotensor K).IsRightAdjoint :=
  (levelSmashCotensorAdjunction K).isRightAdjoint

/-- The cotensor adjunction curries a map after identifying levelwise smash with balanced smash
by the free spectrum and exchanging the two factors. -/
lemma levelSmashCotensorAdjunction_homEquiv_apply (K : PointedSSet.{0})
    {E F : SymmetricSpectrum} (f : (levelSmashRight K).obj E ⟶ F) :
    (levelSmashCotensorAdjunction K).homEquiv E F f =
      Mod.tensorHomEquiv ((free 0).obj K) E F
        ((β_ ((free 0).obj K) E).hom ≫
          (Mod.tensorFreeIso E).hom.app ((SymmetricSequence.free 0).obj K) ≫ f) := by
  rw [levelSmashCotensorAdjunction, Adjunction.homEquiv_ofNatIsoLeft_apply,
    Mod.internalHomAdjunction_homEquiv]
  congr 1
  simp only [Iso.trans_hom, NatTrans.comp_app,
    BraidedCategory.tensorLeftIsoTensorRight_hom_app, Mod.tensorRightFreeIso_hom_app,
    Category.assoc]

/-- The inverse cotensor adjunction identifies levelwise smash with balanced smash by the free
spectrum, exchanges the factors, and applies the uncurried map. -/
lemma levelSmashCotensorAdjunction_homEquiv_symm_apply (K : PointedSSet.{0})
    {E F : SymmetricSpectrum} (f : E ⟶ (cotensor K).obj F) :
    ((levelSmashCotensorAdjunction K).homEquiv E F).symm f =
      (Mod.tensorFreeIso E).inv.app ((SymmetricSequence.free 0).obj K) ≫
        (β_ ((free 0).obj K) E).inv ≫
        (Mod.tensorHomEquiv ((free 0).obj K) E F).symm f := by
  rw [levelSmashCotensorAdjunction, Adjunction.homEquiv_ofNatIsoLeft_symm_apply,
    Mod.internalHomAdjunction_homEquiv]
  simp only [Iso.trans_inv, NatTrans.comp_app,
    BraidedCategory.tensorLeftIsoTensorRight_inv_app, Mod.tensorRightFreeIso_inv_app,
    Category.assoc]

/-- Forgetting the sphere action on a cotensor gives the levelwise pointed mapping sequence. -/
noncomputable def cotensorUnderlyingIso (K : PointedSSet.{0}) :
    cotensor K ⋙ Mod.forget SymmetricSequence.sphere ≅
      Mod.forget SymmetricSequence.sphere ⋙ SymmetricSequence.levelwiseIhom K :=
  Mod.ihomFreeIso ((SymmetricSequence.free 0).obj K) ≪≫
    Functor.isoWhiskerLeft (Mod.forget SymmetricSequence.sphere)
      (SymmetricSequence.freeZeroIhomIso K)

/-- The level formula `(E^K)_n ≅ Map_*(K, E_n)` of the point-set cotensor. -/
noncomputable def cotensorLevelIso (K : PointedSSet.{0}) (E : SymmetricSpectrum) (n : ℕ) :
    (evaluation n).obj ((cotensor K).obj E) ≅
      (CategoryTheory.ihom K).obj ((evaluation n).obj E) :=
  ((DayFunctor.equiv FiniteBijection PointedSSet.{0}).functor.mapIso
    ((cotensorUnderlyingIso K).app E)).app (FiniteBijection.mk n)

/-- The level formula restricts a sphere-linear map to the free generators, then applies the
identity-shuffle comparison for Day convolution. -/
lemma cotensorLevelIso_hom (K : PointedSSet.{0}) (E : SymmetricSpectrum) (n : ℕ) :
    (cotensorLevelIso K E n).hom =
      ((Mod.ihomFreeIso ((SymmetricSequence.free 0).obj K)).hom.app E).natTrans.app
        (FiniteBijection.mk n) ≫
      (SymmetricSequence.freeZeroIhomLevelIso K E.X n).hom := by rfl

/-- The cotensor level formula is natural in the spectrum. -/
@[simp↓, reassoc (attr := simp↓)]
lemma cotensorLevelIso_hom_naturality (K : PointedSSet.{0})
    {E F : SymmetricSpectrum} (f : E ⟶ F) (n : ℕ) :
    (evaluation n).map ((cotensor K).map f) ≫ (cotensorLevelIso K F n).hom =
      (cotensorLevelIso K E n).hom ≫ (CategoryTheory.ihom K).map ((evaluation n).map f) :=
  congrArg (fun g ↦ g.natTrans.app (FiniteBijection.mk n))
    ((cotensorUnderlyingIso K).hom.naturality f)

/-- The symmetric action on the cotensor is postcomposition by the symmetric action on the
target spectrum. -/
@[simp↓, reassoc (attr := simp↓)]
lemma map_comp_cotensorLevelIso_hom (K : PointedSSet.{0}) (E : SymmetricSpectrum)
    {n m : ℕ} (σ : FiniteBijection.mk n ⟶ FiniteBijection.mk m) :
    ((cotensor K).obj E).X.functor.map σ ≫ (cotensorLevelIso K E m).hom =
      (cotensorLevelIso K E n).hom ≫ (CategoryTheory.ihom K).map (E.X.functor.map σ) :=
  ((cotensorUnderlyingIso K).hom.app E).natTrans.naturality σ

/-- Precomposition by `K ⟶ L` gives a spectrum map `E^L ⟶ E^K`; the cotensor level formula
identifies its levels with ordinary pointed precomposition. -/
@[reassoc]
lemma cotensorLevelIso_hom_naturality_left {K L : PointedSSet.{0}} (f : K ⟶ L)
    (E : SymmetricSpectrum) (n : ℕ) :
    (evaluation n).map ((MonoidalClosed.pre ((free 0).map f)).app E) ≫
        (cotensorLevelIso K E n).hom =
      (cotensorLevelIso L E n).hom ≫
        (MonoidalClosed.pre f).app ((evaluation n).obj E) := by
  have h := congrArg (fun g ↦ g.natTrans.app (FiniteBijection.mk n))
    (Mod.ihomFreeIso_hom_naturality_left ((SymmetricSequence.free 0).map f) E)
  have h' := congrArg
    (fun g ↦ g ≫ (SymmetricSequence.freeZeroIhomLevelIso K E.X n).hom) h
  have hday := congrArg
    (fun g ↦ ((Mod.ihomFreeIso ((SymmetricSequence.free 0).obj L)).hom.app E).natTrans.app
      (FiniteBijection.mk n) ≫ g)
    (SymmetricSequence.freeZeroIhomLevelIso_hom_naturality_left f E.X n)
  simp only at h'
  rw [cotensorLevelIso_hom, cotensorLevelIso_hom]
  exact h'.trans hday

/-! ### Free smash comparisons and mapping spaces out of free spectra -/

/-- Smashing a free symmetric spectrum `F_n K` on the right with `L` is naturally isomorphic in
`L` to `F_n (K ∧ L)`. -/
noncomputable def levelSmashFreeIso (n : ℕ) (K : PointedSSet.{0}) :
    levelSmash ((free n).obj K) ≅ MonoidalCategory.tensorLeft K ⋙ free n :=
  Functor.isoWhiskerLeft (SymmetricSequence.free 0)
      (Mod.tensorLeftFreeIso (A := SymmetricSequence.sphere) ((SymmetricSequence.free n).obj K)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerRight (SymmetricSequence.freeTensorFreeZeroIso n K)
      (freeMod SymmetricSequence.sphere) ≪≫
    Functor.associator _ _ _

/-- On the generating level `n`, `(levelSmashFreeIso n K).inv.app L` sends the generator
`K ∧ L` into `(F_n K)_n ∧ L ≅ (F_n K ∧ L)_n`. -/
@[reassoc (attr := simp)]
lemma freeι_comp_evaluation_map_levelSmashFreeIso_inv_app (n : ℕ) (K L : PointedSSet.{0}) :
    freeι n (K ⊗ L) ≫ (evaluation n).map ((levelSmashFreeIso n K).inv.app L) =
      freeι n K ▷ L ≫ SymmetricSequence.tensorFreeZeroι ((free n).obj K).X L n := by
  have hcomp : ((levelSmashFreeIso n K).inv.app L).hom =
      ((freeMod SymmetricSequence.sphere).map
        ((SymmetricSequence.freeTensorFreeZeroIso n K).inv.app L)).hom ≫
      ((Mod.tensorLeftFreeIso (A := SymmetricSequence.sphere)
        ((SymmetricSequence.free n).obj K)).inv.app ((SymmetricSequence.free 0).obj L)).hom := by
    simp [levelSmashFreeIso]
  -- Expose `(evaluation n).map` on `SymmetricSpectrum` as
  -- `.hom.natTrans.app (FiniteBijection.mk n)`.
  change freeι n (K ⊗ L) ≫ (((levelSmashFreeIso n K).inv.app L).hom).natTrans.app
      (FiniteBijection.mk n) = _
  rw [hcomp, freeι_eq, DayFunctor.comp_natTrans, NatTrans.comp_app, Category.assoc,
    Mod.tensorLeftFreeIso_inv_app_hom]
  have hmod : (freeModι SymmetricSequence.sphere ((SymmetricSequence.free n).obj (K ⊗ L))) ≫
      ((freeMod SymmetricSequence.sphere).map
        ((SymmetricSequence.freeTensorFreeZeroIso n K).inv.app L)).hom ≫
      (α_ SymmetricSequence.sphere ((SymmetricSequence.free n).obj K)
        ((SymmetricSequence.free 0).obj L)).inv =
      ((SymmetricSequence.freeTensorFreeZeroIso n K).inv.app L) ≫
        (freeModι SymmetricSequence.sphere ((SymmetricSequence.free n).obj K) ▷
          (SymmetricSequence.free 0).obj L) := by
    rw [← freeModι_naturality_assoc]
    dsimp only [Functor.comp_obj, MonoidalCategory.curriedTensor_obj_obj]
    rw [freeModι_tensor]
  have hmodApp := congrArg (fun g : (SymmetricSequence.free n).obj (K ⊗ L) ⟶ _ ↦
    g.natTrans.app (FiniteBijection.mk n)) hmod
  simp only [DayFunctor.comp_natTrans, NatTrans.comp_app] at hmodApp
  rw [hmodApp, SymmetricSequence.freeι_comp_freeTensorFreeZeroIso_inv_app_assoc,
    ← SymmetricSequence.tensorFreeZeroι_naturality_left, ← comp_whiskerRight_assoc,
    ← freeι_eq]
  -- `((free n).obj K).X` is `SymmetricSequence.sphere ⊗ (SymmetricSequence.free n).obj K`.
  dsimp only [free, Functor.comp_obj]

/-- Smashing `F_n S⁰` with `L` is naturally isomorphic in `L` to `F_n L`. -/
noncomputable def levelSmashFreeZeroIso (n : ℕ) :
    levelSmash ((free n).obj (𝟙_ _)) ≅ free n :=
  levelSmashFreeIso n (𝟙_ _) ≪≫
    Functor.isoWhiskerRight (leftUnitorNatIso PointedSSet.{0}) (free n) ≪≫
    Functor.leftUnitor (free n)

/-- On the generating level `n`, `(levelSmashFreeZeroIso n).inv.app L` sends the generator
`L` through `(λ_ L).inv` into `(F_n S⁰)_n ∧ L ≅ (F_n S⁰ ∧ L)_n`. -/
@[reassoc (attr := simp)]
lemma freeι_comp_evaluation_map_levelSmashFreeZeroIso_inv_app (n : ℕ) (L : PointedSSet.{0}) :
    freeι n L ≫ (evaluation n).map ((levelSmashFreeZeroIso n).inv.app L) =
      (λ_ L).inv ≫ freeι n (𝟙_ _) ▷ L ≫
        SymmetricSequence.tensorFreeZeroι ((free n).obj (𝟙_ _)).X L n := by
  have hinv : (levelSmashFreeZeroIso n).inv.app L =
      (free n).map (λ_ L).inv ≫ (levelSmashFreeIso n (𝟙_ _)).inv.app L := by
    simp [levelSmashFreeZeroIso]
  rw [hinv, Functor.map_comp, ← Category.assoc, ← freeι_naturality, Category.assoc,
    freeι_comp_evaluation_map_levelSmashFreeIso_inv_app]

/-- Mapping out of the free symmetric spectrum `F_n K` into `E` is naturally isomorphic to the
pointed mapping space `Map_*(K, E_n)`. -/
noncomputable def mappingSpaceFreeIso (n : ℕ) (K : PointedSSet.{0}) :
    mappingSpace ((free n).obj K) ≅ evaluation n ⋙ CategoryTheory.ihom K :=
  (levelSmashMappingSpaceAdjunction ((free n).obj K)).rightAdjointUniq
    (((CategoryTheory.ihom.adjunction K).comp (freeEvaluationAdjunction n)).ofNatIsoLeft
      (levelSmashFreeIso n K).symm)

/-- Under `mappingSpaceFreeIso n K`, the adjunction bijection `F_n K ∧ L ⟶ E` corresponds to the
curried restriction of `K ∧ L ⟶ E_n` along the generator and `tensorFreeZeroι`. -/
@[reassoc]
lemma homEquiv_comp_mappingSpaceFreeIso_hom_app (n : ℕ) (K L : PointedSSet.{0})
    (E : SymmetricSpectrum) (f : (levelSmash ((free n).obj K)).obj L ⟶ E) :
    (levelSmashMappingSpaceAdjunction ((free n).obj K)).homEquiv L E f ≫
        (mappingSpaceFreeIso n K).hom.app E =
      MonoidalClosed.curry (freeι n K ▷ L ≫
        SymmetricSequence.tensorFreeZeroι ((free n).obj K).X L n ≫ (evaluation n).map f) := by
  let adj2 := ((CategoryTheory.ihom.adjunction K).comp (freeEvaluationAdjunction n)).ofNatIsoLeft
    (levelSmashFreeIso n K).symm
  rw [mappingSpaceFreeIso, Adjunction.homEquiv_comp_rightAdjointUniq_hom_app _ adj2]
  dsimp only [adj2]
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply, Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply, Iso.symm_hom]
  dsimp only [MonoidalCategory.curriedTensor_obj_obj]
  rw [Adjunction.homEquiv_unit (freeEvaluationAdjunction n), freeEvaluationAdjunction_unit_app,
    Functor.map_comp, freeι_comp_evaluation_map_levelSmashFreeIso_inv_app_assoc,
    MonoidalClosed.homEquiv_apply_eq]
  -- Normalize the `free`/`evaluation` abbreviations on both sides.
  dsimp only [free, SymmetricSequence.free, Functor.comp_obj, evaluation]

/-- Uncurrying `(mappingSpaceFreeIso n K).hom.app E` yields restriction of the counit evaluation
along the generator `freeι n K` and `tensorFreeZeroι`. -/
@[reassoc]
lemma uncurry_mappingSpaceFreeIso_hom_app (n : ℕ) (K : PointedSSet.{0}) (E : SymmetricSpectrum) :
    MonoidalClosed.uncurry ((mappingSpaceFreeIso n K).hom.app E) =
      freeι n K ▷ (mappingSpace ((free n).obj K)).obj E ≫
        SymmetricSequence.tensorFreeZeroι ((free n).obj K).X
          ((mappingSpace ((free n).obj K)).obj E) n ≫
        (evaluation n).map ((levelSmashMappingSpaceAdjunction ((free n).obj K)).counit.app E) := by
  rw [← Category.id_comp ((mappingSpaceFreeIso n K).hom.app E),
    ← Adjunction.right_triangle_components (levelSmashMappingSpaceAdjunction ((free n).obj K)),
    ← Adjunction.homEquiv_unit, homEquiv_comp_mappingSpaceFreeIso_hom_app,
    MonoidalClosed.uncurry_curry]

/-- Mapping out of `F_n S⁰` into `E` is naturally isomorphic to level `E_n`. -/
noncomputable def mappingSpaceFreeZeroIso (n : ℕ) :
    mappingSpace ((free n).obj (𝟙_ _)) ≅ evaluation n :=
  mappingSpaceFreeIso n (𝟙_ _) ≪≫
    Functor.isoWhiskerLeft (evaluation n) MonoidalClosed.unitNatIso.symm

/-- On components, `(mappingSpaceFreeZeroIso n).hom.app E` factors through
`mappingSpaceFreeIso n S⁰` and `MonoidalClosed.unitNatIso.inv`. -/
@[reassoc]
lemma mappingSpaceFreeZeroIso_hom_app (n : ℕ) (E : SymmetricSpectrum) :
    (mappingSpaceFreeZeroIso n).hom.app E =
      (mappingSpaceFreeIso n (𝟙_ _)).hom.app E ≫
        MonoidalClosed.unitNatIso.inv.app ((evaluation n).obj E) := by
  simp [mappingSpaceFreeZeroIso]

/-- Under `mappingSpaceFreeZeroIso n`, the adjunction bijection `F_n S⁰ ∧ L ⟶ E` corresponds to
restriction along the generator and `tensorFreeZeroι`, precomposed with `(λ_ L).inv`. -/
@[reassoc]
lemma homEquiv_comp_mappingSpaceFreeZeroIso_hom_app (n : ℕ) (L : PointedSSet.{0})
    (E : SymmetricSpectrum) (f : (levelSmash ((free n).obj (𝟙_ _))).obj L ⟶ E) :
    (levelSmashMappingSpaceAdjunction ((free n).obj (𝟙_ _))).homEquiv L E f ≫
        (mappingSpaceFreeZeroIso n).hom.app E =
      (λ_ L).inv ≫ freeι n (𝟙_ _) ▷ L ≫
        SymmetricSequence.tensorFreeZeroι ((free n).obj (𝟙_ _)).X L n ≫
        (evaluation n).map f := by
  have hunitInv : MonoidalClosed.unitNatIso.inv.app ((evaluation n).obj E) =
      (λ_ _).inv ≫ (CategoryTheory.ihom.ev (𝟙_ PointedSSet.{0})).app ((evaluation n).obj E) := by
    simp [MonoidalClosed.unitNatIso]
  rw [mappingSpaceFreeZeroIso_hom_app, ← Category.assoc,
    homEquiv_comp_mappingSpaceFreeIso_hom_app, hunitInv,
    ← Category.assoc (MonoidalClosed.curry _), leftUnitor_inv_naturality, Category.assoc,
    ← MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_curry]

end TauCeti.SymmetricSpectrum
