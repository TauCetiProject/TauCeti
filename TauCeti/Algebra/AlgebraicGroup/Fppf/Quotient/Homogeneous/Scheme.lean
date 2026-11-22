/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import TauCeti.Algebra.AlgebraicGroup.Fppf.SchemePoints
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.RationalPoints
public import TauCeti.Algebra.AlgebraicGroup.Hopf.LeftTranslation
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.SchemeMap
import Mathlib.CategoryTheory.Comma.Over.Pullback
import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Torsor

/-!
# Universal property and functoriality of represented homogeneous quotients

Let `G = Spec H` be an affine group scheme over a commutative ring `R`, and let `N` be the closed
subgroup scheme cut out by a Hopf ideal `I` of `H`. Suppose the fppf homogeneous quotient `G/N` is
represented by `X : Over (Spec R)` via `e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X`.
By full faithfulness of `CommAlgCat.pointsSheafFunctor`, `fppfHomogeneousQuotientHomEquiv` descends
to schemes over `Spec R`:

* The quotient projection `G ⟶ G/N` descends to `representedQuotientProjection H I e : Spec H ⟶ X`,
  which is epimorphic in `Over (Spec R)` and on underlying schemes, surjective on underlying
  schemes, and has left cosets of `N(A)` as its fibres on all `A`-valued points
  (`mapMulEquiv_comp_representedQuotientProjection_eq_iff`).
* Precomposition with `representedQuotientProjection H I e` identifies `X ⟶ Y` with right
  `N`-invariant `R`-scheme morphisms `Spec H ⟶ Y` (`representedQuotientHomEquiv`), and any locally
  surjective right `N`-invariant morphism `Spec H ⟶ Y` with left-coset point fibres exhibits `Y` as
  representing `G/N` (`fppfHomogeneousQuotientIsoPointsSheaf`, `isIso_representedQuotientDesc`).
* The surjective morphisms `fppfHomogeneousQuotientSchemeMap H hJI eI eJ` induced by subgroup
  inclusions `P ⊆ Q` (`J ≤ I`) commute with the projections from `Spec H`, give canonical
  comparison isomorphisms `representedQuotientIso`, and intertwine left translations
  (`representedQuotientTranslation`).
* Over an algebraically closed field `k`, `k`-rational points of `X` correspond to `G(k)/N(k)`
  compatibly with quotient maps and translations (`representedQuotientRationalPointsEquiv`).

No smoothness, reducedness, finite-type, or normality hypothesis is imposed on `R`, `G`, or `N`.

## Main declarations

* `CommHopfAlgCat.representedQuotientProjection`,
  `CommHopfAlgCat.mapMulEquiv_comp_representedQuotientProjection_eq_iff`: the canonical projection
  `Spec H ⟶ X` and its left-coset point-fibre characterization.
* `CommHopfAlgCat.representedQuotientHomEquiv`, `CommHopfAlgCat.representedQuotientDesc`: universal
  property and descent for `N`-invariant `R`-scheme morphisms out of `Spec H`.
* `CommHopfAlgCat.fppfHomogeneousQuotientDesc`,
  `CommHopfAlgCat.isIso_fppfHomogeneousQuotientDesc`: sheaf-level descent and recognition of
  schemes representing `G/N`.
* `CommHopfAlgCat.fppfHomogeneousQuotientIsoPointsSheaf`,
  `CommHopfAlgCat.isIso_representedQuotientDesc`: recognition of schemes representing `G/N`.
* `CommHopfAlgCat.eq_fppfHomogeneousQuotientSchemeMap_iff_comp`: the subgroup-induced morphism
  `CommHopfAlgCat.fppfHomogeneousQuotientSchemeMap` is the unique morphism compatible with the
  projections from `Spec H`.
* `CommHopfAlgCat.representedQuotientIso`: canonical comparison isomorphisms.
* `CommHopfAlgCat.universallyClosed_overHom_iff_of_fppfHomogeneousQuotient_iso`,
  `CommHopfAlgCat.isProper_overHom_iff_of_fppfHomogeneousQuotient_iso`: invariance of
  universal closedness and properness over `Spec R`.
* `CommHopfAlgCat.representedQuotientTranslation`: left-translation `R`-scheme automorphisms.
* `CommHopfAlgCat.representedQuotientRationalPointsEquiv`: `G(k)/N(k)` equivalence over
  algebraically closed `k`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 5.22 and §§5.c, 7.e.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §14.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

noncomputable section

section CommRing

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R)

section QuotientUniversalProperty

variable (I : HopfIdeal R H) {X : Over (Spec (CommRingCat.of R))}
  (e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)

/-- **The canonical quotient projection `Spec H ⟶ X` onto a representing scheme.** When `e`
identifies `G/N` with `pointsSheaf X`, `G ⟶ G/N` descends to a morphism in `Over (Spec R)`. -/
def representedQuotientProjection :
    (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ X :=
  (specPointsHomEquiv H X).symm (fppfHomogeneousQuotientProjection H I ≫ e.hom.hom)

/-- Evaluating `representedQuotientProjection` on an `A`-valued group point `g` computes the image
of `g` under the quotient projection and the representing isomorphism `e`. -/
@[reassoc] theorem mapMulEquiv_comp_representedQuotientProjection
    {A : CommAlgCat.{u} R} (g : HopfAlgebra.points (R := R) (H := H) A) :
    Spec.mapMulEquiv g ≫ representedQuotientProjection H I e =
      (e.hom.hom.app (op (op A))
        ((fppfHomogeneousQuotientProjection H I).app (op (op A)) (ULift.up g))).down :=
  comp_specPointsHomEquiv_symm H _ g

/-- On fppf point presheaves, `representedQuotientProjection` corresponds to
`fppfHomogeneousQuotientProjection H I ≫ e.hom.hom`. -/
@[simp] theorem specPointsHomEquiv_representedQuotientProjection :
    specPointsHomEquiv H X (representedQuotientProjection H I e) =
      fppfHomogeneousQuotientProjection H I ≫ e.hom.hom :=
  (specPointsHomEquiv H X).apply_symm_apply _

/-- On fppf sheaves of points, `representedQuotientProjection` is locally surjective. -/
instance isLocallySurjective_pointsSheafFunctor_map_representedQuotientProjection :
    Sheaf.IsLocallySurjective
      ((CommAlgCat.pointsSheafFunctor R).map (representedQuotientProjection H I e)) := by
  have hfac : (pointsPresheafUliftIsoPointsSheaf H).hom ≫
      ((CommAlgCat.pointsSheafFunctor R).map (representedQuotientProjection H I e)).hom =
      fppfHomogeneousQuotientProjection H I ≫ e.hom.hom := by
    rw [← specPointsHomEquiv_eq_comp, specPointsHomEquiv_representedQuotientProjection]
  have : IsIso e.hom.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map e.hom))
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac (CommAlgCat.fppfTopology R) hfac

/-- **The canonical projection `Spec H ⟶ X` is surjective on underlying schemes.** -/
instance instSurjectiveRepresentedQuotientProjectionLeft :
    Surjective (representedQuotientProjection H I e).left :=
  CommAlgCat.surjective_of_isLocallySurjective_pointsSheafFunctor_map
    (representedQuotientProjection H I e)

/-- The canonical projection `Spec H ⟶ X` is invariant under right multiplication by `N` on all
algebra-valued points. -/
theorem mapMulEquiv_mul_comp_representedQuotientProjection
    {A : CommAlgCat.{u} R} (g : HopfAlgebra.points (R := R) (H := H) A)
    (n : quotientPointsSubgroup H I A) :
    Spec.mapMulEquiv (g * n.val) ≫ representedQuotientProjection H I e =
      Spec.mapMulEquiv g ≫ representedQuotientProjection H I e := by
  have hinv := (fppfHomogeneousQuotientHomEquiv H I _ e.hom).property (op (op A)) g n
  rw [fppfHomogeneousQuotientHomEquiv_apply] at hinv
  rw [mapMulEquiv_comp_representedQuotientProjection,
    mapMulEquiv_comp_representedQuotientProjection]; exact congrArg ULift.down hinv

/-- **Fibres of `representedQuotientProjection` on `A`-valued points.** Two `A`-valued points of `G`
have the same image in `X` if and only if they lie in the same left coset of `N(A)`. -/
theorem mapMulEquiv_comp_representedQuotientProjection_eq_iff
    {A : CommAlgCat.{u} R} (g g' : HopfAlgebra.points (R := R) (H := H) A) :
    Spec.mapMulEquiv g ≫ representedQuotientProjection H I e =
        Spec.mapMulEquiv g' ≫ representedQuotientProjection H I e ↔
      g⁻¹ * g' ∈ quotientPointsSubgroup H I A := by
  rw [mapMulEquiv_comp_representedQuotientProjection,
    mapMulEquiv_comp_representedQuotientProjection]
  have : IsIso (e.hom.hom.app (op (op A))) :=
    inferInstanceAs (IsIso ((((sheafToPresheaf _ _).mapIso e).app (op (op A))).hom))
  exact (ULift.ext_iff.symm.trans
    (ConcreteCategory.bijective_of_isIso (e.hom.hom.app (op (op A)))).injective.eq_iff).trans
    (fppfHomogeneousQuotientProjection_eq_iff H I (op (op A)) g g')

/-- **Universal property of a represented homogeneous quotient (Milne, Proposition 5.22).**
Morphisms `X ⟶ Y` over `Spec R` correspond bijectively, via precomposition with
`representedQuotientProjection H I e`, to right `N`-invariant `R`-scheme morphisms `Spec H ⟶ Y`. -/
def representedQuotientHomEquiv (Y : Over (Spec (CommRingCat.of R))) :
    (X ⟶ Y) ≃
      {q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y //
        ∀ (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A)
          (n : quotientPointsSubgroup H I A),
          Spec.mapMulEquiv (g * n.val) ≫ q = Spec.mapMulEquiv g ≫ q} :=
  ((CommAlgCat.fullyFaithfulPointsSheafFunctor R).homEquiv).trans <|
    (Iso.homCongr e (Iso.refl (CommAlgCat.pointsSheaf Y))).symm.trans <|
      (fppfHomogeneousQuotientHomEquiv H I (CommAlgCat.pointsSheaf Y)).trans
        { toFun f := ⟨(specPointsHomEquiv H Y).symm f.val, fun A g n ↦ by
            rw [comp_specPointsHomEquiv_symm, comp_specPointsHomEquiv_symm]
            exact congrArg ULift.down (f.property (op (op A)) g n)⟩
          invFun q := ⟨specPointsHomEquiv H Y q.val, fun A g n ↦ by
            rw [specPointsHomEquiv_apply_app_apply, specPointsHomEquiv_apply_app_apply,
              q.property A.unop.unop g n]⟩
          left_inv f := Subtype.ext ((specPointsHomEquiv H Y).apply_symm_apply f.val)
          right_inv q := Subtype.ext ((specPointsHomEquiv H Y).symm_apply_apply q.val) }

/-- Forward evaluation of `representedQuotientHomEquiv` precomposes with
`representedQuotientProjection`. -/
@[simp] theorem representedQuotientHomEquiv_apply {Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    (representedQuotientHomEquiv H I e Y f).val = representedQuotientProjection H I e ≫ f := by
  apply (specPointsHomEquiv H Y).injective
  rw [specPointsHomEquiv_comp, specPointsHomEquiv_representedQuotientProjection]
  unfold representedQuotientHomEquiv
  simp only [Equiv.trans_apply, Equiv.coe_fn_mk, (specPointsHomEquiv H Y).apply_symm_apply,
    Functor.FullyFaithful.homEquiv_apply, Iso.homCongr_symm, Iso.homCongr_apply, Iso.symm_inv,
    Iso.refl_symm, Iso.refl_hom, Category.comp_id, fppfHomogeneousQuotientHomEquiv_apply,
    ObjectProperty.FullSubcategory.comp_hom, Category.assoc]

/-- Morphisms out of a scheme representing `G/N` are determined by their composites with
`representedQuotientProjection`. -/
theorem representedQuotient_hom_ext {Y : Over (Spec (CommRingCat.of R))} {f₁ f₂ : X ⟶ Y}
    (h : representedQuotientProjection H I e ≫ f₁ = representedQuotientProjection H I e ≫ f₂) :
    f₁ = f₂ :=
  (representedQuotientHomEquiv H I e Y).injective <| Subtype.ext <| by simpa using h

/-- The canonical projection `Spec H ⟶ X` onto a representing scheme is an epimorphism in
`Over (Spec R)`. -/
instance epi_representedQuotientProjection : Epi (representedQuotientProjection H I e) :=
  ⟨fun _ _ h ↦ representedQuotient_hom_ext H I e h⟩

/-- The canonical projection `Spec H ⟶ X` onto a representing scheme is an epimorphism of
underlying schemes. -/
instance epi_representedQuotientProjection_left : Epi (representedQuotientProjection H I e).left :=
  inferInstanceAs (Epi ((Over.forget _).map (representedQuotientProjection H I e)))

section SheafDesc

variable {Y : Over (Spec (CommRingCat.of R))}
  (q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y)
  (hq : ∀ (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A)
    (n : quotientPointsSubgroup H I A),
    Spec.mapMulEquiv (g * n.val) ≫ q = Spec.mapMulEquiv g ≫ q)

/-- **Sheaf-level descent of an `N`-invariant scheme morphism to `G/N`.** Every `R`-scheme
morphism `q : Spec H ⟶ Y` invariant under right multiplication by `N` descends to a morphism of
fppf sheaves `fppfHomogeneousQuotient H I ⟶ CommAlgCat.pointsSheaf Y`. -/
def fppfHomogeneousQuotientDesc :
    fppfHomogeneousQuotient H I ⟶ CommAlgCat.pointsSheaf Y :=
  (fppfHomogeneousQuotientHomEquiv H I (CommAlgCat.pointsSheaf Y)).symm
    ⟨specPointsHomEquiv H Y q, fun A g n ↦ by
      rw [specPointsHomEquiv_apply_app_apply, specPointsHomEquiv_apply_app_apply,
        hq A.unop.unop g n]⟩

/-- Restricting `fppfHomogeneousQuotientDesc` along the quotient projection recovers `q` on
convolution points. -/
@[reassoc (attr := simp)] theorem fppfHomogeneousQuotientProjection_comp_desc :
    fppfHomogeneousQuotientProjection H I ≫ (fppfHomogeneousQuotientDesc H I q hq).hom =
      specPointsHomEquiv H Y q :=
  fppfHomogeneousQuotientHomEquiv_symm_apply H I (CommAlgCat.pointsSheaf Y) _ _

/-- **Sheaf-level quotient recognition.** If `q : Spec H ⟶ Y` is right `N`-invariant, locally
surjective on fppf point sheaves, and has left cosets of `N` as its point-level fibres, then
`fppfHomogeneousQuotientDesc H I q hq` is an isomorphism of fppf sheaves. -/
theorem isIso_fppfHomogeneousQuotientDesc
    [Sheaf.IsLocallySurjective ((CommAlgCat.pointsSheafFunctor R).map q)]
    (hcoset : ∀ (A : CommAlgCat.{u} R) (g g' : HopfAlgebra.points (R := R) (H := H) A),
      Spec.mapMulEquiv g ≫ q = Spec.mapMulEquiv g' ≫ q → g⁻¹ * g' ∈ quotientPointsSubgroup H I A) :
    IsIso (fppfHomogeneousQuotientDesc H I q hq) := by
  have : Presheaf.IsLocallySurjective (CommAlgCat.fppfTopology R) (specPointsHomEquiv H Y q) := by
    rw [specPointsHomEquiv_eq_comp]; infer_instance
  exact isIso_fppfHomogeneousQuotientHomEquiv_symm H I (CommAlgCat.pointsSheaf Y)
    (specPointsHomEquiv H Y q) _ fun A g g' hgg' ↦ hcoset A.unop.unop g g' <|
      ULift.up_inj.mp <| (specPointsHomEquiv_apply_app_apply H q A g).symm.trans
        (hgg'.trans (specPointsHomEquiv_apply_app_apply H q A g'))

end SheafDesc

section Desc

variable {Y : Over (Spec (CommRingCat.of R))}
  (q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y)
  (hq : ∀ (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A)
    (n : quotientPointsSubgroup H I A),
    Spec.mapMulEquiv (g * n.val) ≫ q = Spec.mapMulEquiv g ≫ q)

/-- **Descent of an `N`-invariant scheme morphism to `G/N`.** Every `R`-scheme morphism
`q : Spec H ⟶ Y` invariant under right multiplication by `N` factors through
`representedQuotientProjection H I e` by a morphism `X ⟶ Y` over `Spec R`. -/
def representedQuotientDesc : X ⟶ Y :=
  (representedQuotientHomEquiv H I e Y).symm ⟨q, hq⟩

/-- On fppf sheaves of points, `representedQuotientDesc` induces the sheaf-level quotient descent
of `specPointsHomEquiv H Y q` precomposed with `e.inv`. -/
@[simp] theorem pointsSheafFunctor_map_representedQuotientDesc :
    (CommAlgCat.pointsSheafFunctor R).map (representedQuotientDesc H I e q hq) =
      e.inv ≫ fppfHomogeneousQuotientDesc H I q hq := by
  unfold fppfHomogeneousQuotientDesc representedQuotientDesc representedQuotientHomEquiv; simp

/-- Composing `representedQuotientProjection` with `representedQuotientDesc` recovers `q`. -/
@[reassoc (attr := simp)] theorem representedQuotientProjection_comp_desc :
    representedQuotientProjection H I e ≫ representedQuotientDesc H I e q hq = q :=
  (representedQuotientHomEquiv_apply H I e (representedQuotientDesc H I e q hq)).symm.trans
    (congrArg Subtype.val ((representedQuotientHomEquiv H I e Y).apply_symm_apply ⟨q, hq⟩))

/-- Postcomposing `representedQuotientDesc` with `f : Y ⟶ Z` descends `q ≫ f`. -/
@[reassoc] theorem representedQuotientDesc_comp {Z : Over (Spec (CommRingCat.of R))} (f : Y ⟶ Z) :
    representedQuotientDesc H I e q hq ≫ f =
      representedQuotientDesc H I e (q ≫ f)
        (fun A g n ↦ by rw [← Category.assoc, hq A g n, Category.assoc]) :=
  representedQuotient_hom_ext H I e <| by simp

/-- A morphism `f : X ⟶ Y` equals `representedQuotientDesc H I e q hq` if and only if its
composite with `representedQuotientProjection H I e` is `q`. -/
theorem eq_representedQuotientDesc_iff (f : X ⟶ Y) :
    f = representedQuotientDesc H I e q hq ↔ representedQuotientProjection H I e ≫ f = q :=
  ⟨by rintro rfl; exact representedQuotientProjection_comp_desc H I e q hq,
   fun h ↦ representedQuotient_hom_ext H I e
    (h.trans (representedQuotientProjection_comp_desc H I e q hq).symm)⟩

end Desc

/-- Inverse evaluation of `representedQuotientHomEquiv` is `representedQuotientDesc`. -/
@[simp] theorem representedQuotientHomEquiv_symm_apply {Y : Over (Spec (CommRingCat.of R))}
    (q : {q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y //
      ∀ (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A)
        (n : quotientPointsSubgroup H I A),
        Spec.mapMulEquiv (g * n.val) ≫ q = Spec.mapMulEquiv g ≫ q}) :
    (representedQuotientHomEquiv H I e Y).symm q =
      representedQuotientDesc H I e q.val q.property := (rfl)

/-- Descending `representedQuotientProjection` recovers the identity morphism on `X`. -/
@[simp] theorem representedQuotientDesc_projection
    (hq : ∀ (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A)
      (n : quotientPointsSubgroup H I A),
      Spec.mapMulEquiv (g * n.val) ≫ representedQuotientProjection H I e =
        Spec.mapMulEquiv g ≫ representedQuotientProjection H I e) :
    representedQuotientDesc H I e (representedQuotientProjection H I e) hq = 𝟙 X :=
  representedQuotient_hom_ext H I e <| by simp

end QuotientUniversalProperty

section QuotientRecognition

variable (I : HopfIdeal R H) {Y : Over (Spec (CommRingCat.of R))}
  (q : (Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R)) ⟶ Y)
  (hq : ∀ (A : CommAlgCat.{u} R) (g : HopfAlgebra.points (R := R) (H := H) A)
    (n : quotientPointsSubgroup H I A),
    Spec.mapMulEquiv (g * n.val) ≫ q = Spec.mapMulEquiv g ≫ q)

section Iso

variable [Sheaf.IsLocallySurjective ((CommAlgCat.pointsSheafFunctor R).map q)]
  (hcoset : ∀ (A : CommAlgCat.{u} R) (g g' : HopfAlgebra.points (R := R) (H := H) A),
    Spec.mapMulEquiv g ≫ q = Spec.mapMulEquiv g' ≫ q → g⁻¹ * g' ∈ quotientPointsSubgroup H I A)

/-- **Recognising a scheme representing `G/N`.** An `R`-scheme morphism `q : Spec H ⟶ Y` that is
invariant under right multiplication by `N`, locally surjective on fppf point sheaves, and whose
fibres on `A`-valued points are the left cosets of `N(A)` exhibits `Y` as representing
`fppfHomogeneousQuotient H I`. -/
def fppfHomogeneousQuotientIsoPointsSheaf :
    fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf Y :=
  @asIso _ _ _ _ (fppfHomogeneousQuotientDesc H I q hq)
    (isIso_fppfHomogeneousQuotientDesc H I q hq hcoset)

/-- The forward morphism of `fppfHomogeneousQuotientIsoPointsSheaf` is
`fppfHomogeneousQuotientDesc`. -/
@[simp] theorem fppfHomogeneousQuotientIsoPointsSheaf_hom :
    (fppfHomogeneousQuotientIsoPointsSheaf H I q hq hcoset).hom =
      fppfHomogeneousQuotientDesc H I q hq := (rfl)

/-- Under `fppfHomogeneousQuotientIsoPointsSheaf`, `representedQuotientProjection` is `q`. -/
@[simp] theorem representedQuotientProjection_fppfHomogeneousQuotientIsoPointsSheaf :
    representedQuotientProjection H I (fppfHomogeneousQuotientIsoPointsSheaf H I q hq hcoset) =
      q := by
  apply (specPointsHomEquiv H Y).injective
  rw [specPointsHomEquiv_representedQuotientProjection,
    fppfHomogeneousQuotientIsoPointsSheaf_hom, fppfHomogeneousQuotientProjection_comp_desc]

end Iso

/-- **Scheme-level quotient recognition.** If `q : Spec H ⟶ Y` is right `N`-invariant, locally
surjective on fppf point sheaves, and has left cosets of `N` as its point-level fibres, then
`representedQuotientDesc H I e q hq : X ⟶ Y` is an isomorphism over `Spec R`. -/
theorem isIso_representedQuotientDesc {X : Over (Spec (CommRingCat.of R))}
    (e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
    [Sheaf.IsLocallySurjective ((CommAlgCat.pointsSheafFunctor R).map q)]
    (hcoset : ∀ (A : CommAlgCat.{u} R) (g g' : HopfAlgebra.points (R := R) (H := H) A),
      Spec.mapMulEquiv g ≫ q = Spec.mapMulEquiv g' ≫ q → g⁻¹ * g' ∈ quotientPointsSubgroup H I A) :
    IsIso (representedQuotientDesc H I e q hq) := by
  have : IsIso ((CommAlgCat.pointsSheafFunctor R).map (representedQuotientDesc H I e q hq)) := by
    rw [pointsSheafFunctor_map_representedQuotientDesc,
      ← fppfHomogeneousQuotientIsoPointsSheaf_hom H I q hq hcoset]; infer_instance
  exact isIso_of_fully_faithful (CommAlgCat.pointsSheafFunctor R) _

end QuotientRecognition

section SubgroupMap

variable {I J K : HopfIdeal R H}
  {X Y Z : Over (Spec (CommRingCat.of R))}

section MapLemmas

variable (hJI : J ≤ I)
  (eI : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
  (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)

/-- `fppfHomogeneousQuotientSchemeMap` commutes with `representedQuotientProjection` from
`Spec H`. -/
@[reassoc (attr := simp)]
theorem representedQuotientProjection_comp_fppfHomogeneousQuotientSchemeMap :
    representedQuotientProjection H I eI ≫ fppfHomogeneousQuotientSchemeMap H hJI eI eJ =
      representedQuotientProjection H J eJ := (specPointsHomEquiv H Y).injective <| by simp

/-- `fppfHomogeneousQuotientSchemeMap` is the unique `R`-scheme morphism `X ⟶ Y` compatible with
the canonical projections from `Spec H`. -/
theorem eq_fppfHomogeneousQuotientSchemeMap_iff_comp (f : X ⟶ Y) :
    f = fppfHomogeneousQuotientSchemeMap H hJI eI eJ ↔
      representedQuotientProjection H I eI ≫ f = representedQuotientProjection H J eJ :=
  ⟨by rintro rfl
      exact representedQuotientProjection_comp_fppfHomogeneousQuotientSchemeMap H hJI eI eJ,
   fun h ↦ representedQuotient_hom_ext H I eI <| h.trans
    (representedQuotientProjection_comp_fppfHomogeneousQuotientSchemeMap H hJI eI eJ).symm⟩

/-- `fppfHomogeneousQuotientSchemeMap` agrees with descending
`representedQuotientProjection H J eJ` along `representedQuotientProjection H I eI`. -/
theorem fppfHomogeneousQuotientSchemeMap_eq_desc :
    fppfHomogeneousQuotientSchemeMap H hJI eI eJ =
      representedQuotientDesc H I eI (representedQuotientProjection H J eJ)
        (fun A g n ↦ mapMulEquiv_mul_comp_representedQuotientProjection H J eJ g
          ⟨n.val, quotientPointsSubgroup_le_of_le H hJI A n.property⟩) :=
  (eq_representedQuotientDesc_iff H I eI _ _ _).mpr
    (representedQuotientProjection_comp_fppfHomogeneousQuotientSchemeMap H hJI eI eJ)

end MapLemmas

section IsoLemmas

variable (I) (e₁ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)
  (e₂ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf Y)

/-- **Canonical isomorphism between schemes representing the same homogeneous quotient.** Any two
`R`-schemes representing `fppfHomogeneousQuotient H I` are canonically isomorphic over `Spec R`. -/
def representedQuotientIso : X ≅ Y :=
  (CommAlgCat.fullyFaithfulPointsSheafFunctor R).preimageIso (e₁.symm ≪≫ e₂)

/-- The forward morphism of `representedQuotientIso` is
`fppfHomogeneousQuotientSchemeMap H (le_refl I)`. -/
@[simp] theorem representedQuotientIso_hom :
    (representedQuotientIso H I e₁ e₂).hom = fppfHomogeneousQuotientSchemeMap H (le_refl I) e₁ e₂ :=
  (CommAlgCat.pointsSheafFunctor R).map_injective <| by simp [representedQuotientIso]

/-- The inverse morphism of `representedQuotientIso` is
`fppfHomogeneousQuotientSchemeMap H (le_refl I)` in the opposite direction. -/
@[simp] theorem representedQuotientIso_inv :
    (representedQuotientIso H I e₁ e₂).inv = fppfHomogeneousQuotientSchemeMap H (le_refl I) e₂ e₁ :=
  (CommAlgCat.pointsSheafFunctor R).map_injective <| by simp [representedQuotientIso]

/-- Swapping the two representing schemes inverts `representedQuotientIso`. -/
@[simp] theorem representedQuotientIso_symm :
    (representedQuotientIso H I e₁ e₂).symm = representedQuotientIso H I e₂ e₁ := Iso.ext <| by simp

/-- Canonical comparison isomorphisms between representing schemes compose transitively. -/
@[simp] theorem representedQuotientIso_trans
    (e₃ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf Z) :
    representedQuotientIso H I e₁ e₂ ≪≫ representedQuotientIso H I e₂ e₃ =
      representedQuotientIso H I e₁ e₃ := Iso.ext <| by simp

include H I e₁ e₂ in
/-- Universal closedness over `Spec R` is invariant across schemes representing the same
`fppfHomogeneousQuotient H I`. -/
theorem universallyClosed_overHom_iff_of_fppfHomogeneousQuotient_iso :
    UniversallyClosed X.hom ↔ UniversallyClosed Y.hom :=
  ⟨fun _ ↦ universallyClosed_hom_of_le H (le_refl I) e₁ e₂,
   fun _ ↦ universallyClosed_hom_of_le H (le_refl I) e₂ e₁⟩

include H I e₁ e₂ in
/-- **Properness over `Spec R` is an intrinsic property of a represented homogeneous quotient.** -/
theorem isProper_overHom_iff_of_fppfHomogeneousQuotient_iso :
    IsProper X.hom ↔ IsProper Y.hom := by
  have : IsIso (representedQuotientIso H I e₁ e₂).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (representedQuotientIso H I e₁ e₂).hom))
  rw [← Over.w (representedQuotientIso H I e₁ e₂).hom]
  exact MorphismProperty.cancel_left_of_respectsIso @IsProper _ _

end IsoLemmas

/-- Comparing a representing scheme with itself gives the identity isomorphism. -/
@[simp] theorem representedQuotientIso_refl
    (e₁ : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X) :
    representedQuotientIso H I e₁ e₁ = Iso.refl X := Iso.ext <| by simp

end SubgroupMap

section Translation

variable (I : HopfIdeal R H) {X : Over (Spec (CommRingCat.of R))}
  (e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)

section PointTranslation

variable (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))

/-- **Left translation on a representing scheme.** Every `R`-valued group point `g ∈ G(R)` acts by
an `R`-scheme automorphism on any scheme `X` representing `fppfHomogeneousQuotient H I`. -/
def representedQuotientTranslation : X ≅ X :=
  (CommAlgCat.fullyFaithfulPointsSheafFunctor R).preimageIso
    (e.symm ≪≫ fppfHomogeneousQuotientTranslation H I g ≪≫ e)

/-- Translation by `1 ∈ G(R)` is the identity automorphism of `X`. -/
@[simp] theorem representedQuotientTranslation_one :
    representedQuotientTranslation H I e 1 = Iso.refl X :=
  Iso.ext <| (CommAlgCat.pointsSheafFunctor R).map_injective <| by
    simp [representedQuotientTranslation]

/-- On fppf sheaves of points, `representedQuotientTranslation` induces
`fppfHomogeneousQuotientTranslation` conjugated by `e`. -/
@[simp] theorem pointsSheafFunctor_mapIso_representedQuotientTranslation :
    (CommAlgCat.pointsSheafFunctor R).mapIso (representedQuotientTranslation H I e g) =
      e.symm ≪≫ fppfHomogeneousQuotientTranslation H I g ≪≫ e :=
  Iso.ext ((CommAlgCat.fullyFaithfulPointsSheafFunctor R).map_preimage _)

/-- On morphisms of fppf sheaves of points, `(representedQuotientTranslation H I e g).hom` induces
`(fppfHomogeneousQuotientTranslation H I g).hom` conjugated by `e`. -/
@[simp] theorem pointsSheafFunctor_map_representedQuotientTranslation_hom :
    (CommAlgCat.pointsSheafFunctor R).map (representedQuotientTranslation H I e g).hom =
      e.inv ≫ (fppfHomogeneousQuotientTranslation H I g).hom ≫ e.hom := by
  simpa only [Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom] using
    congrArg Iso.hom (pointsSheafFunctor_mapIso_representedQuotientTranslation H I e g)

/-- On morphisms of fppf sheaves of points, `(representedQuotientTranslation H I e g).inv` induces
`(fppfHomogeneousQuotientTranslation H I g).inv` conjugated by `e`. -/
@[simp] theorem pointsSheafFunctor_map_representedQuotientTranslation_inv :
    (CommAlgCat.pointsSheafFunctor R).map (representedQuotientTranslation H I e g).inv =
      e.inv ≫ (fppfHomogeneousQuotientTranslation H I g).inv ≫ e.hom := by
  simpa only [Functor.mapIso_inv, Iso.trans_inv, Iso.symm_inv, Category.assoc] using
    congrArg Iso.inv (pointsSheafFunctor_mapIso_representedQuotientTranslation H I e g)

/-- Left translations on `X` compose in action order. -/
@[simp] theorem representedQuotientTranslation_mul
    (h : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    representedQuotientTranslation H I e (g * h) =
      representedQuotientTranslation H I e h ≪≫ representedQuotientTranslation H I e g := by
  ext : 1; apply (CommAlgCat.pointsSheafFunctor R).map_injective
  have hmul := congrArg Iso.hom (fppfHomogeneousQuotientTranslation_mul H I g h)
  simp only [Iso.trans_hom, pointsSheafFunctor_map_representedQuotientTranslation_hom,
    Functor.map_comp, hmul, Category.assoc, Iso.hom_inv_id_assoc]

/-- Translation by `g⁻¹` is the inverse automorphism of translation by `g`. -/
@[simp] theorem representedQuotientTranslation_inv :
    representedQuotientTranslation H I e g⁻¹ = (representedQuotientTranslation H I e g).symm := by
  ext : 1
  have h := congrArg Iso.hom (representedQuotientTranslation_mul H I e g g⁻¹)
  rw [mul_inv_cancel, representedQuotientTranslation_one, Iso.refl_hom, Iso.trans_hom] at h
  rw [Iso.symm_hom, ← Category.id_comp (representedQuotientTranslation H I e g).inv, h,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- On projected `A`-valued points of `G`, `representedQuotientTranslation` acts by left
multiplication by the base-changed point `extendPoint H A g`. -/
@[reassoc] theorem mapMulEquiv_representedQuotientProjection_comp_translation_hom
    {A : CommAlgCat.{u} R} (x : HopfAlgebra.points (R := R) (H := H) A) :
    Spec.mapMulEquiv x ≫ representedQuotientProjection H I e ≫
        (representedQuotientTranslation H I e g).hom =
      Spec.mapMulEquiv (HopfAlgebra.extendPoint H A g * x) ≫
        representedQuotientProjection H I e := by
  have hcomp : specPointsHomEquiv H X
      (representedQuotientProjection H I e ≫ (representedQuotientTranslation H I e g).hom) =
      fppfHomogeneousQuotientProjection H I ≫
        (fppfHomogeneousQuotientTranslation H I g).hom.hom ≫ e.hom.hom := by simp
  have happ := congrArg (fun α ↦ (α.app (op (op A)) (ULift.up x)).down) hcomp
  rw [specPointsHomEquiv_apply_app_apply] at happ
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at happ
  rw [fppfHomogeneousQuotientTranslation_hom_app_projection] at happ
  exact happ.trans (mapMulEquiv_comp_representedQuotientProjection H I e _).symm

/-- On projected `A`-valued points of `G`, `(representedQuotientTranslation H I e g).inv` acts by
left multiplication by the base-changed inverse point `extendPoint H A g⁻¹`. -/
@[reassoc] theorem mapMulEquiv_representedQuotientProjection_comp_translation_inv
    {A : CommAlgCat.{u} R} (x : HopfAlgebra.points (R := R) (H := H) A) :
    Spec.mapMulEquiv x ≫ representedQuotientProjection H I e ≫
        (representedQuotientTranslation H I e g).inv =
      Spec.mapMulEquiv (HopfAlgebra.extendPoint H A g⁻¹ * x) ≫
        representedQuotientProjection H I e := by
  rw [← Iso.symm_hom, ← representedQuotientTranslation_inv]
  exact mapMulEquiv_representedQuotientProjection_comp_translation_hom H I e g⁻¹ x

/-- `representedQuotientProjection` intertwines left translation on `Spec H` by `g ∈ G(R)` with
`representedQuotientTranslation` on `X`. -/
@[reassoc] theorem representedQuotientProjection_comp_translation_hom :
    representedQuotientProjection H I e ≫ (representedQuotientTranslation H I e g).hom =
      Spec.mapMulEquiv (WithConv.toConv (HopfAlgebra.leftTranslationAlgEquiv g).toAlgHom) ≫
        representedQuotientProjection H I e := by
  have hid : Spec.mapMulEquiv (WithConv.toConv (AlgHom.id R H)) =
      𝟙 ((Spec (CommRingCat.of H)).asOver (Spec (CommRingCat.of R))) :=
    Over.OverMorphism.ext <| (TauCeti.CommHopfAlgCat.mapMulEquiv_left _).trans (Spec.map_id _)
  have h := mapMulEquiv_representedQuotientProjection_comp_translation_hom H I e g
    (A := CommAlgCat.of R H) (WithConv.toConv (AlgHom.id R H))
  rwa [hid, Category.id_comp, HopfAlgebra.extendPoint_apply, ← AlgHom.mapValue_apply,
    ← HopfAlgebra.toConv_leftTranslationAlgEquiv] at h

/-- `representedQuotientProjection` intertwines left translation on `Spec H` by `g⁻¹ ∈ G(R)` with
`(representedQuotientTranslation H I e g).inv` on `X`. -/
@[reassoc] theorem representedQuotientProjection_comp_translation_inv :
    representedQuotientProjection H I e ≫ (representedQuotientTranslation H I e g).inv =
      Spec.mapMulEquiv (WithConv.toConv (HopfAlgebra.leftTranslationAlgEquiv g⁻¹).toAlgHom) ≫
        representedQuotientProjection H I e := by
  rw [← Iso.symm_hom, ← representedQuotientTranslation_inv]
  exact representedQuotientProjection_comp_translation_hom H I e g⁻¹

end PointTranslation

section TranslationMap

variable {J : HopfIdeal R H} (hJI : J ≤ I) {Y : Over (Spec (CommRingCat.of R))}
  (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
  (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))

/-- **Equivariance of subgroup-induced quotient morphisms.** For `J ≤ I` (`P ⊆ Q`), the morphism
`fppfHomogeneousQuotientSchemeMap H hJI e eJ` intertwines left translation by every `g ∈ G(R)`. -/
@[reassoc] theorem representedQuotientTranslation_hom_comp_map :
    (representedQuotientTranslation H I e g).hom ≫ fppfHomogeneousQuotientSchemeMap H hJI e eJ =
      fppfHomogeneousQuotientSchemeMap H hJI e eJ ≫
        (representedQuotientTranslation H J eJ g).hom := by
  apply (CommAlgCat.pointsSheafFunctor R).map_injective
  simp only [Functor.map_comp, pointsSheafFunctor_map_representedQuotientTranslation_hom,
    pointsSheafFunctor_map_fppfHomogeneousQuotientSchemeMap, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (fppfHomogeneousQuotientTranslation H I g).hom,
    fppfHomogeneousQuotientTranslation_hom_comp_map H I hJI g, Category.assoc]

/-- For `J ≤ I` (`P ⊆ Q`), `fppfHomogeneousQuotientSchemeMap H hJI e eJ` also intertwines inverse
left translation by every `g ∈ G(R)`. -/
@[reassoc] theorem representedQuotientTranslation_inv_comp_map :
    (representedQuotientTranslation H I e g).inv ≫ fppfHomogeneousQuotientSchemeMap H hJI e eJ =
      fppfHomogeneousQuotientSchemeMap H hJI e eJ ≫
        (representedQuotientTranslation H J eJ g).inv := by
  rw [← Iso.symm_hom, ← representedQuotientTranslation_inv,
    ← Iso.symm_hom, ← representedQuotientTranslation_inv]
  exact representedQuotientTranslation_hom_comp_map H I e hJI eJ g⁻¹

end TranslationMap

end Translation

end CommRing

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k] (H : _root_.CommHopfAlgCat.{u} k)
  (I : HopfIdeal k H) {X : Over (Spec (CommRingCat.of k))}
  (e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf X)

/-- **Rational points of a scheme representing `G/N`.** Over an algebraically closed field `k`,
the left cosets `G(k)/N(k)` are in canonical bijection with `k`-rational points of `X`. -/
def representedQuotientRationalPointsEquiv :
    HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) ⧸
        quotientPointsSubgroup H I (CommAlgCat.of k k) ≃
      ((Spec (CommRingCat.of k)).asOver (Spec (CommRingCat.of k)) ⟶ X) :=
  (fppfHomogeneousQuotientRationalPointsEquiv H I).trans <|
    (Iso.toEquiv (((sheafToPresheaf (CommAlgCat.fppfTopology k) (Type (u + 1))).mapIso e).app
      (op (op (CommAlgCat.of k k))))).trans Equiv.ulift

section RationalPoints

variable (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))

/-- `representedQuotientRationalPointsEquiv` sends the coset of `g ∈ G(k)` to the image of `g`
under `representedQuotientProjection`. -/
@[simp] theorem representedQuotientRationalPointsEquiv_mk :
    representedQuotientRationalPointsEquiv H I e (QuotientGroup.mk g) =
      Spec.mapMulEquiv g ≫ representedQuotientProjection H I e := by
  unfold representedQuotientRationalPointsEquiv
  exact (congrArg (fun s ↦ (e.hom.hom.app (op (op (CommAlgCat.of k k))) s).down)
    (fppfHomogeneousQuotientRationalPointsEquiv_mk H I g)).trans
      (mapMulEquiv_comp_representedQuotientProjection H I e g).symm

/-- Inverse evaluation of `representedQuotientRationalPointsEquiv` sends the projected point of
`g ∈ G(k)` to its left coset `QuotientGroup.mk g`. -/
@[simp] theorem
    representedQuotientRationalPointsEquiv_symm_mapMulEquiv_comp_representedQuotientProjection :
    (representedQuotientRationalPointsEquiv H I e).symm
        (Spec.mapMulEquiv g ≫ representedQuotientProjection H I e) = QuotientGroup.mk g :=
  (representedQuotientRationalPointsEquiv H I e).symm_apply_eq.mpr
    (representedQuotientRationalPointsEquiv_mk H I e g).symm

end RationalPoints

/-- Every `k`-rational point of a scheme representing `G/N` over an algebraically closed field `k`
lifts to a `k`-rational point of `G`. -/
theorem exists_mapMulEquiv_comp_representedQuotientProjection_eq
    (x : (Spec (CommRingCat.of k)).asOver (Spec (CommRingCat.of k)) ⟶ X) :
    ∃ g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k),
      Spec.mapMulEquiv g ≫ representedQuotientProjection H I e = x := by
  obtain ⟨q, rfl⟩ := (representedQuotientRationalPointsEquiv H I e).surjective x
  induction q using QuotientGroup.induction_on with
  | H g => exact ⟨g, (representedQuotientRationalPointsEquiv_mk H I e g).symm⟩

/-- **Compatibility of `fppfHomogeneousQuotientSchemeMap` with rational cosets.** For `J ≤ I`
(`P ⊆ Q`), composing a `k`-point of `X` with `fppfHomogeneousQuotientSchemeMap H hJI e eJ` applies
the canonical coset projection `G(k)/P(k) → G(k)/Q(k)`. -/
@[reassoc] theorem representedQuotientRationalPointsEquiv_comp_map {J : HopfIdeal k H} (hJI : J ≤ I)
    {Y : Over (Spec (CommRingCat.of k))}
    (eJ : fppfHomogeneousQuotient H J ≅ CommAlgCat.pointsSheaf Y)
    (q : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) ⧸
      quotientPointsSubgroup H I (CommAlgCat.of k k)) :
    representedQuotientRationalPointsEquiv H I e q ≫ fppfHomogeneousQuotientSchemeMap H hJI e eJ =
      representedQuotientRationalPointsEquiv H J eJ
        (Subgroup.quotientMapOfLE (quotientPointsSubgroup_le_of_le H hJI _) q) := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [Subgroup.quotientMapOfLE_apply_mk, representedQuotientRationalPointsEquiv_mk,
      representedQuotientRationalPointsEquiv_mk, Category.assoc,
      representedQuotientProjection_comp_fppfHomogeneousQuotientSchemeMap]

section RationalTranslation

variable (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
  (q : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k) ⧸
    quotientPointsSubgroup H I (CommAlgCat.of k k))

/-- **Compatibility of `representedQuotientTranslation` with rational cosets.** Composing a
`k`-point of `X` with `(representedQuotientTranslation H I e g).hom` acts on `G(k)/N(k)` by left
multiplication by `g`. -/
@[reassoc] theorem representedQuotientRationalPointsEquiv_comp_translation_hom :
    representedQuotientRationalPointsEquiv H I e q ≫
        (representedQuotientTranslation H I e g).hom =
      representedQuotientRationalPointsEquiv H I e (g • q) := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [representedQuotientRationalPointsEquiv_mk, MulAction.Quotient.smul_mk, smul_eq_mul,
      representedQuotientRationalPointsEquiv_mk, Category.assoc,
      mapMulEquiv_representedQuotientProjection_comp_translation_hom, HopfAlgebra.extendPoint_self]

/-- Composing a `k`-point of `X` with `(representedQuotientTranslation H I e g).inv` acts on
`G(k)/N(k)` by left multiplication by `g⁻¹`. -/
@[reassoc] theorem representedQuotientRationalPointsEquiv_comp_translation_inv :
    representedQuotientRationalPointsEquiv H I e q ≫
        (representedQuotientTranslation H I e g).inv =
      representedQuotientRationalPointsEquiv H I e (g⁻¹ • q) := by
  rw [← Iso.symm_hom, ← representedQuotientTranslation_inv]
  exact representedQuotientRationalPointsEquiv_comp_translation_hom H I e g⁻¹ q

end RationalTranslation

end AlgClosed

end

end CommHopfAlgCat
