/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Augment
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import TauCeti.Algebra.Homology.Single.Kernel

/-!
# Injective resolutions: exact functors, comparison maps and short exact extensions

An additive functor `F : C ⥤ D` which preserves homology and injective objects sends an injective
resolution `I` of `Z` to an injective resolution `F.mapInjectiveResolution I` of `F.obj Z`, whose
complex is `F` applied to the complex of `I`. This is the dual of Mathlib's
`CategoryTheory.Functor.mapProjectiveResolution`.

Consequently, choosing injective resolutions commutes with `F` up to homotopy: the functor
`injectiveResolutions C ⋙ F.mapHomotopyCategory _` is naturally isomorphic to
`F ⋙ injectiveResolutions D` (`CategoryTheory.Functor.injectiveResolutionsCompIso`). This is what
makes right derived functors commute with such functors. Without the hypothesis on injective
objects, an exact functor `G` still sends `I` to a resolution of `G.obj Z`
(`CategoryTheory.InjectiveResolution.exact₀_map` and
`CategoryTheory.InjectiveResolution.exactAt_succ_map`), whose terms need not be injective.

A morphism `f : Z ⟶ Y` lifts to a morphism of complexes from any resolution `ι : Z[0] ⟶ K` of `Z`
to an injective resolution `I` of `Y` (`CategoryTheory.InjectiveResolution.descOfQuasiIso`), and
two such lifts agreeing on `Z` are homotopic
(`CategoryTheory.InjectiveResolution.homotopyOfQuasiIso`). The terms of `K` need not be injective.
The constructions follow Mathlib's `CategoryTheory.InjectiveResolution.desc` and
`CategoryTheory.InjectiveResolution.descHomotopy`, whose source is required to be an injective
resolution.

The augmentation of an injective resolution `I` of `Z` is also available as
`CategoryTheory.InjectiveResolution.ι₀ I : Z ⟶ I⁰`, whose source is `Z` itself rather than the
degree `0` object of the single complex on `Z`, so that it composes with morphisms out of `Z`
without unfolding the single complex. For a short exact sequence `0 ⟶ X ⟶ I ⟶ Q ⟶ 0` with `I`
injective, an injective resolution `R` of `Q` extends to the injective resolution
`X ⟶ I ⟶ R⁰ ⟶ R¹ ⟶ ⋯` of `X` (`CategoryTheory.InjectiveResolution.ofShortExact`).
-/

public section

open CategoryTheory Limits

universe v v' u u'

namespace CategoryTheory.Functor

section

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [Preadditive D] [CategoryWithHomology D]

/-- An additive functor `F` which preserves homology and sends injective objects to injective
objects sends an injective resolution of `Z` to an injective resolution of `F.obj Z`.

The body is exposed so that the complex of the image is definitionally `F` applied to the complex
of `I`, as `injectiveResolutionsCompIso` requires. -/
@[expose, simps cocomplex]
noncomputable def mapInjectiveResolution (F : C ⥤ D) [F.Additive]
    [F.PreservesInjectiveObjects] [F.PreservesHomology] {Z : C} (I : InjectiveResolution Z) :
    InjectiveResolution (F.obj Z) where
  cocomplex := (F.mapHomologicalComplex _).obj I.cocomplex
  injective n := PreservesInjectiveObjects.injective_obj (I.injective n)
  ι := (HomologicalComplex.singleMapHomologicalComplex F _ _).inv.app _ ≫
    (F.mapHomologicalComplex _).map I.ι
  quasiIso := inferInstance

/-- In degree zero, the coaugmentation of `F.mapInjectiveResolution I` is `F` applied to that
of `I`. -/
@[simp]
lemma mapInjectiveResolution_ι_f_zero (F : C ⥤ D) [F.Additive]
    [F.PreservesInjectiveObjects] [F.PreservesHomology] {Z : C} (I : InjectiveResolution Z) :
    (F.mapInjectiveResolution I).ι.f 0 = F.map (I.ι.f 0) := by
  simp [mapInjectiveResolution]

end

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasInjectiveResolutions D]
  (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects] [F.PreservesHomology]

/-- Choosing injective resolutions commutes, up to homotopy, with an additive functor preserving
homology and injective objects: `F` applied to the chosen resolution of `X` is homotopy
equivalent to the chosen resolution of `F.obj X`, naturally in `X`. -/
noncomputable def injectiveResolutionsCompIso :
    injectiveResolutions C ⋙ F.mapHomotopyCategory _ ≅ F ⋙ injectiveResolutions D :=
  NatIso.ofComponents
    -- `F.mapHomotopyCategory` sends the class of a complex to the class of its image under `F`
    (fun X ↦ (F.mapInjectiveResolution (injectiveResolution X)).iso.symm)
    (fun {X Y} f ↦ by
      -- `(injectiveResolutions C).map f` is the class of `desc f`, and `F.mapHomotopyCategory`
      -- sends it to the class of `F` applied to `desc f`, a lift of `F.map f`
      exact (InjectiveResolution.iso_inv_naturality (F.map f)
        (F.mapInjectiveResolution (injectiveResolution X))
        (F.mapInjectiveResolution (injectiveResolution Y))
        ((F.mapHomologicalComplex _).map (InjectiveResolution.desc f _ _))
        (by
          rw [mapInjectiveResolution_ι_f_zero, mapInjectiveResolution_ι_f_zero,
            mapHomologicalComplex_map_f]
          -- `F.map_comp` is applied by unification: the source of `I.ι.f 0` is `X` only up to
          -- unfolding `CochainComplex.single₀`
          exact (F.map_comp _ _).symm.trans
            ((congrArg F.map (InjectiveResolution.desc_commutes_zero f _ _)).trans
              (F.map_comp _ _)))).symm)

/-- The comparison `injectiveResolutionsCompIso` at `X` is the homotopy equivalence between `F`
applied to the chosen resolution of `X` and the chosen resolution of `F.obj X`. -/
@[simp]
lemma injectiveResolutionsCompIso_hom_app (X : C) :
    (F.injectiveResolutionsCompIso).hom.app X =
      (F.mapInjectiveResolution (injectiveResolution X)).iso.inv :=
  (rfl)

end CategoryTheory.Functor

noncomputable section

namespace CategoryTheory.InjectiveResolution

open CochainComplex HomologicalComplex

section Augmentation

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
  {Z : C} (I : InjectiveResolution Z)

/-- The augmentation `Z ⟶ I⁰` of an injective resolution, with source `Z` itself rather than the
degree `0` object of the single complex on `Z`, as for `I.ι.f 0`. -/
def ι₀ : Z ⟶ I.cocomplex.X 0 :=
  (fromSingle₀Equiv _ _ I.ι).1

/-- The augmentation `Z ⟶ I⁰` composed with the differential `I⁰ ⟶ I¹` vanishes. -/
@[reassoc (attr := simp)]
lemma ι₀_comp_d : I.ι₀ ≫ I.cocomplex.d 0 1 = 0 :=
  (fromSingle₀Equiv _ _ I.ι).2

/-- `I.ι₀` is the morphism `Z ⟶ I⁰` corresponding to the augmentation `I.ι` of `I`. -/
@[simp]
lemma fromSingle₀Equiv_ι : fromSingle₀Equiv _ _ I.ι = ⟨I.ι₀, I.ι₀_comp_d⟩ :=
  (rfl)

/-- The augmentation `Z ⟶ I⁰` of an injective resolution is a monomorphism. -/
-- `I.ι₀` is `I.ι.f 0` by unfolding `fromSingle₀Equiv`, and the source `((single₀ C).obj Z).X 0`
-- of `I.ι.f 0` is `Z` by unfolding `single₀`, so Mathlib's instance for `I.ι.f 0` applies
instance : Mono I.ι₀ := inferInstanceAs (Mono (I.ι.f 0))

end Augmentation

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An injective resolution `Z ⟶ I⁰ ⟶ I¹` is exact at `I⁰`. -/
-- Mathlib's `exact₀` is stated for `I.ι.f 0`, whose source `((single₀ C).obj Z).X 0` is `Z` by
-- unfolding `single₀`; `I.ι₀` is `I.ι.f 0` by unfolding `fromSingle₀Equiv`
lemma exact_ι₀ {Z : C} (I : InjectiveResolution Z) :
    (ShortComplex.mk _ _ I.ι₀_comp_d).Exact :=
  I.exact₀

section ShortExact

variable {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₂]
  (R : InjectiveResolution S.X₃)

/-- For a short exact sequence `0 ⟶ X ⟶ I ⟶ Q ⟶ 0` with `I` injective, the injective resolution
`X ⟶ I ⟶ R⁰ ⟶ R¹ ⟶ ⋯` of `X` obtained from an injective resolution `R` of `Q`.

The body is exposed so that the degree `0` object of the complex is definitionally `I`, as the
statement of `ofShortExact_ι₀` requires. -/
@[expose]
def ofShortExact : InjectiveResolution S.X₁ where
  cocomplex := R.cocomplex.augment (S.g ≫ R.ι₀) (by simp)
  injective n := by cases n <;> dsimp <;> infer_instance
  ι := (CochainComplex.fromSingle₀Equiv _ _).symm ⟨S.f, (S.zero_assoc _).trans zero_comp⟩
  quasiIso := ⟨fun n => by
    rcases n with _ | _ | n
    · rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
      · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
          ⟨(ShortComplex.exact_iff_of_epi_of_isIso_of_mono
            ({ τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := R.ι₀ } :
              S ⟶ ShortComplex.mk S.f (S.g ≫ R.ι₀) (by simp))).1 hS.exact, hS.mono_f⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by
            dsimp
            simp only [Category.id_comp]
            -- `S.X₂` is the degree `0` object of the augmented complex only up to unfolding
            -- `augment`, so `simp` can neither cancel `𝟙 S.X₂` nor rewrite the component
            exact ((Category.comp_id _).trans (CochainComplex.fromSingle₀Equiv_symm_apply_f_zero
              (C := R.cocomplex.augment (S.g ≫ R.ι₀) (by simp)) S.f _)).symm)
          (by simp)
      -- the differentials into and out of degree `0` vanish, between objects which are those of
      -- the short complexes only up to unfolding `single₀` and `augment`
      all_goals rfl
    · rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _),
        HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)]
      have : Epi S.g := hS.epi_g
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
        ({ τ₁ := S.g, τ₂ := 𝟙 _, τ₃ := 𝟙 _ } :
          ShortComplex.mk (S.g ≫ R.ι₀) (R.cocomplex.d 0 1) (by simp) ⟶
            ShortComplex.mk R.ι₀ (R.cocomplex.d 0 1) R.ι₀_comp_d)).2 R.exact_ι₀
    · rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _),
        HomologicalComplex.exactAt_iff' _ (n + 1) (n + 2) (n + 3) (by simp) (by simp)]
      exact R.exact_succ n⟩

/-- The complex of `R.ofShortExact hS` is that of `R`, augmented by `S.g ≫ R.ι₀ : I ⟶ R⁰`. -/
@[simp]
lemma ofShortExact_cocomplex :
    (R.ofShortExact hS).cocomplex = R.cocomplex.augment (S.g ≫ R.ι₀) (by simp) :=
  (rfl)

/-- The augmentation `X ⟶ I` of `R.ofShortExact hS` is `S.f`. -/
@[simp]
lemma ofShortExact_ι₀ : (R.ofShortExact hS).ι₀ = S.f :=
  congrArg Subtype.val ((fromSingle₀Equiv _ _).apply_symm_apply _)

end ShortExact

section Desc

variable {Y Z : C} {K : CochainComplex C ℕ} (f : Z ⟶ Y) (I : InjectiveResolution Y)
  (ι : (single₀ C).obj Z ⟶ K) [QuasiIso ι]

/-- The degree `0` component of `descOfQuasiIso`. -/
private def descOfQuasiIsoFZero : K.X 0 ⟶ I.cocomplex.X 0 :=
  Injective.factorThru (((single₀ C).map f).f 0 ≫ I.ι.f 0) (ι.f 0)

private lemma ι_f_zero_descOfQuasiIsoFZero :
    ι.f 0 ≫ descOfQuasiIsoFZero f I ι = ((single₀ C).map f).f 0 ≫ I.ι.f 0 :=
  Injective.comp_factorThru _ _

/-- The degree `1` component of `descOfQuasiIso`. -/
private def descOfQuasiIsoFOne : K.X 1 ⟶ I.cocomplex.X 1 :=
  (exact_f_zero_of_quasiIsoAt ι).descToInjective
    (descOfQuasiIsoFZero f I ι ≫ I.cocomplex.d 0 1)
    (by rw [reassoc_of% (ι_f_zero_descOfQuasiIsoFZero f I ι), I.ι_f_zero_comp_complex_d,
      comp_zero])

private lemma d_descOfQuasiIsoFOne :
    K.d 0 1 ≫ descOfQuasiIsoFOne f I ι = descOfQuasiIsoFZero f I ι ≫ I.cocomplex.d 0 1 :=
  (exact_f_zero_of_quasiIsoAt ι).comp_descToInjective _ _

/-- **Lifting to an injective resolution.** A morphism `f : Z ⟶ Y` lifts to a morphism of
complexes from any resolution `ι : Z[0] ⟶ K` of `Z` to an injective resolution `I` of `Y`
(`CategoryTheory.InjectiveResolution.ι_comp_descOfQuasiIso`). The terms of `K` need not be
injective. -/
def descOfQuasiIso : K ⟶ I.cocomplex :=
  mkHom _ _ (descOfQuasiIsoFZero f I ι) (descOfQuasiIsoFOne f I ι)
    (d_descOfQuasiIsoFOne f I ι).symm fun n ⟨_, g', w⟩ ↦
      ⟨(exact_succ_of_quasiIsoAt ι n).descToInjective (g' ≫ I.cocomplex.d (n + 1) (n + 2))
          (by simp [← reassoc_of% w]),
        ((exact_succ_of_quasiIsoAt ι n).comp_descToInjective _ _).symm⟩

/-- The lift `descOfQuasiIso f I ι` is compatible with `f` and the two resolutions. -/
@[reassoc (attr := simp)]
lemma ι_comp_descOfQuasiIso : ι ≫ descOfQuasiIso f I ι = (single₀ C).map f ≫ I.ι := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  rcases n with _ | n
  · simpa [descOfQuasiIso] using ι_f_zero_descOfQuasiIsoFZero f I ι
  · exact (isZero_single_obj_X _ _ _ _ (by simp)).eq_of_src _ _

end Desc

section Homotopy

variable {Y : C} {K : CochainComplex C ℕ} {I : InjectiveResolution Y} {Z : C}
  (ι : (single₀ C).obj Z ⟶ K) [QuasiIso ι]

/-- The degree `0` component of `homotopyZeroOfQuasiIso`. -/
private def homotopyZeroOfQuasiIsoZero (g : K ⟶ I.cocomplex) (hg : ι ≫ g = 0) :
    K.X 1 ⟶ I.cocomplex.X 0 :=
  (exact_f_zero_of_quasiIsoAt ι).descToInjective (g.f 0) congr($(hg).f 0)

private lemma d_homotopyZeroOfQuasiIsoZero (g : K ⟶ I.cocomplex) (hg : ι ≫ g = 0) :
    K.d 0 1 ≫ homotopyZeroOfQuasiIsoZero ι g hg = g.f 0 :=
  (exact_f_zero_of_quasiIsoAt ι).comp_descToInjective _ _

/-- A morphism from a resolution of `Z` to an injective resolution, which vanishes on `Z`, is
homotopic to zero. -/
private def homotopyZeroOfQuasiIso (g : K ⟶ I.cocomplex) (hg : ι ≫ g = 0) : Homotopy g 0 :=
  Homotopy.mkCoinductive _ (homotopyZeroOfQuasiIsoZero ι g hg)
    (d_homotopyZeroOfQuasiIsoZero ι g hg).symm
    ((exact_succ_of_quasiIsoAt ι 0).descToInjective
      (g.f 1 - homotopyZeroOfQuasiIsoZero ι g hg ≫ I.cocomplex.d 0 1)
      (by simp [← reassoc_of% d_homotopyZeroOfQuasiIsoZero ι g hg, ← g.comm]))
    (by
      rw [(exact_succ_of_quasiIsoAt ι 0).comp_descToInjective]
      abel)
    fun n ⟨h, h', w⟩ ↦
      ⟨(exact_succ_of_quasiIsoAt ι (n + 1)).descToInjective
          (g.f (n + 2) - h' ≫ I.cocomplex.d (n + 1) (n + 2))
          (by simp [← g.comm, w]),
        by
          rw [(exact_succ_of_quasiIsoAt ι (n + 1)).comp_descToInjective]
          abel⟩

/-- **Lifts to an injective resolution are unique up to homotopy.** Two morphisms from a
resolution `ι : Z[0] ⟶ K` of `Z` to an injective resolution which agree on `Z` are homotopic. -/
def homotopyOfQuasiIso (g h : K ⟶ I.cocomplex) (hgh : ι ≫ g = ι ≫ h) : Homotopy g h :=
  Homotopy.equivSubZero.symm
    (homotopyZeroOfQuasiIso ι (g - h) (by rw [Preadditive.comp_sub, hgh, sub_self]))

end Homotopy

section Map

variable {D : Type u'} [Category.{v'} D] [Abelian D] {Z : C} (I : InjectiveResolution Z)
  (G : C ⥤ D) [G.PreservesZeroMorphisms] [G.PreservesHomology]

omit [G.PreservesHomology] in
/-- Applying a functor `G` preserving zero morphisms to an injective resolution
`Z ⟶ I⁰ ⟶ I¹` gives a complex. -/
lemma map_ι_f_zero_comp_d :
    G.map (I.ι.f 0) ≫ ((G.mapHomologicalComplex _).obj I.cocomplex).d 0 1 = 0 := by
  rw [Functor.mapHomologicalComplex_obj_d, ← G.map_comp, I.ι_f_zero_comp_complex_d, G.map_zero]

/-- An exact functor `G` keeps `0 ⟶ G(Z) ⟶ G(I⁰) ⟶ G(I¹)` exact, for an injective resolution
`I` of `Z`: the image of `I` under `G` is a resolution of `G(Z)`, whose terms need no longer be
injective. -/
lemma exact₀_map : (ShortComplex.mk _ _ (I.map_ι_f_zero_comp_d G)).Exact :=
  I.exact₀.map G

/-- An exact functor `G` keeps the complex of an injective resolution exact in positive
degrees. -/
lemma exactAt_succ_map (n : ℕ) :
    ((G.mapHomologicalComplex _).obj I.cocomplex).ExactAt (n + 1) :=
  (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)).2
    ((I.exact_succ n).map G)

end Map

end CategoryTheory.InjectiveResolution

end
