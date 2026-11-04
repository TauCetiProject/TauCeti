/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Frobenius.Perfect
public import TauCeti.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import TauCeti.AlgebraicGeometry.RelativeSpec.Basic
public import TauCeti.RingTheory.Perfect.Colimit

/-!
# Perfection of schemes

Let `p` be a prime. The *perfection* of a scheme `X` over `𝔽_p` is the universal perfect scheme
over `X`: a perfect scheme `X^perf` with a morphism `X^perf ⟶ X` through which every morphism from
a perfect scheme to `X` factors uniquely. Over an affine open `Spec A` of `X` it is the spectrum
of the colimit perfection of `A`, and the map `X^perf ⟶ X` is a universal homeomorphism, so passing
to the perfection does not change the underlying topology, even after base change.

The file first treats a `p`-radical ring map `φ : A ⟶ B` (Mathlib's `IsPRadical`), of which the
map from `A` to its colimit perfection `A → A^{1/p} → A^{1/p²} → ⋯` is the main example:

* `Spec.map φ : Spec B ⟶ Spec A` is a universal homeomorphism;
* every morphism from a perfect scheme `Y` to `Spec A` factors uniquely through `Spec.map φ`. When
  `B` is perfect, the scheme `Spec B` is itself perfect, so `Spec.map φ` is a coreflection of
  `Spec A` into perfect schemes.

For a general scheme `X` over `𝔽_p`, the perfection is glued with Mathlib's relative gluing on the
small affine Zariski site from the spectra `Spec (ColimitPerfection Γ(X, U))` over the affine opens
`U` of `X`. The colimit perfection `TauCeti.ColimitPerfection` is used rather than Mathlib's
`PerfectClosure`, which needs `CharP Γ(X, U) p` and so excludes the zero ring of sections over the
empty open; the two agree for rings of characteristic `p`
(`TauCeti.ColimitPerfection.ringEquivPerfectClosure`). The gluing applies because the colimit
perfection commutes with localization; it follows the construction of Mathlib's relative
normalization `AlgebraicGeometry.Scheme.Hom.normalization`. The universal property then follows
from the affine case by gluing lifts over the preimages of the affine opens of `X`.

## Main definitions

* `AlgebraicGeometry.Scheme.perfection X p hX`: the perfection `X^perf` of a scheme `X` with
  `hX : (p : Γ(X, ⊤)) = 0`.
* `AlgebraicGeometry.Scheme.fromPerfection X p hX`: its structure morphism `X^perf ⟶ X`.
* `AlgebraicGeometry.Scheme.perfectionCover X p hX`: the open cover of `X^perf` by the spectra
  `Spec (ColimitPerfection Γ(X, U))` over the affine opens `U` of `X`.
* `AlgebraicGeometry.Scheme.homPerfectionEquiv`: for a perfect scheme `T`, the bijection
  `(T ⟶ X^perf) ≃ (T ⟶ X)`.

## Main results

* `TauCeti.AlgebraicGeometry.IsUniversalHomeomorphism.SpecMap_of_isPRadical`: if `φ` is
  `p`-radical and `p = 0` in its target, then `Spec.map φ` is a universal homeomorphism.
* `TauCeti.AlgebraicGeometry.IsUniversalHomeomorphism.SpecMap_perfectClosureOf` and
  `TauCeti.AlgebraicGeometry.IsUniversalHomeomorphism.SpecMap_colimitPerfectionOf`: the instances
  that `Spec (PerfectClosure A p) ⟶ Spec A` and `Spec (ColimitPerfection A p hA) ⟶ Spec A` are
  universal homeomorphisms.
* `AlgebraicGeometry.Scheme.IsPerfect.bijective_comp_SpecMap`: for a perfect scheme `Y` and a
  `p`-radical `φ : A ⟶ B` with `p = 0` in `A`, composition with `Spec.map φ` is a bijection
  `(Y ⟶ Spec B) → (Y ⟶ Spec A)`.
* `AlgebraicGeometry.Scheme.IsPerfect.homSpecEquiv`: the corresponding equivalence of hom-sets.
* `AlgebraicGeometry.Scheme.isPullback_perfectionCover`: over an affine open `U` of `X`, the
  perfection of `X` is `Spec (ColimitPerfection Γ(X, U))`.
* `AlgebraicGeometry.Scheme.isUniversalHomeomorphism_fromPerfection`: `X^perf ⟶ X` is a universal
  homeomorphism.
* `AlgebraicGeometry.Scheme.isPerfect_perfection`: the perfection is a perfect scheme.
* `AlgebraicGeometry.Scheme.bijective_comp_fromPerfection`: the universal property, that
  composition with `X^perf ⟶ X` is a bijection `(T ⟶ X^perf) → (T ⟶ X)` for every perfect `T`.
* `AlgebraicGeometry.Scheme.isIso_fromPerfection`: a perfect scheme is its own perfection.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*, Invent. Math.
  209 (2017), Definition 3.1, Lemma 3.4 and Proposition 3.13.
* The Stacks Project, [Tag 04DF](https://stacks.math.columbia.edu/tag/04DF), the integral
  characterization of universal homeomorphisms.
* The Stacks Project, [Tag 01LL](https://stacks.math.columbia.edu/tag/01LL), gluing relative
  spectra over the affine opens of a scheme.
-/

public section

open CategoryTheory Opposite Polynomial

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {A B : CommRingCat.{u}} (φ : A ⟶ B) (p : ℕ) [Fact p.Prime]

/-- **The spectrum of a `p`-radical ring map is a universal homeomorphism.** If `φ : A ⟶ B` is
`p`-radical and `p = 0` in `B`, then `Spec.map φ : Spec B ⟶ Spec A` is integral, universally
injective and surjective. -/
theorem IsUniversalHomeomorphism.SpecMap_of_isPRadical [IsPRadical φ.hom p] (hB : (p : B) = 0) :
    IsUniversalHomeomorphism (Spec.map φ) := by
  refine (IsUniversalHomeomorphism.SpecMap_iff φ).2
    ⟨IsPRadical.isIntegral φ.hom p, fun K _ g₁ g₂ hg ↦ ?_,
      (IsPRadical.isHomeomorph_comap φ.hom p).surjective⟩
  -- A field receiving a map from `B` has characteristic `p`, and is reduced, so two maps into it
  -- agreeing on `A` agree.
  have : CharP K p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (by rw [← map_natCast g₁.hom, hB, map_zero])
  ext1
  exact IsPRadical.injective_comp K φ.hom p (congrArg CommRingCat.Hom.hom hg)

/-- **The perfection of an affine scheme is a universal homeomorphism**: for a ring `A` of
characteristic `p`, the map `Spec (PerfectClosure A p) ⟶ Spec A` is a universal homeomorphism. -/
instance IsUniversalHomeomorphism.SpecMap_perfectClosureOf (A : Type u) [CommRing A] [CharP A p] :
    IsUniversalHomeomorphism (Spec.map (CommRingCat.ofHom (PerfectClosure.of A p))) :=
  have : IsPRadical (CommRingCat.ofHom (PerfectClosure.of A p)).hom p :=
    PerfectClosure.isPRadical A p
  SpecMap_of_isPRadical _ p (CharP.cast_eq_zero _ p)

/-- The spectrum of the map from a ring in which `p` vanishes to its colimit perfection is a
universal homeomorphism. -/
instance IsUniversalHomeomorphism.SpecMap_colimitPerfectionOf (A : Type u) [CommRing A]
    (hA : (p : A) = 0) :
    IsUniversalHomeomorphism (Spec.map (CommRingCat.ofHom (ColimitPerfection.of A p hA))) :=
  have : IsPRadical (CommRingCat.ofHom (ColimitPerfection.of A p hA)).hom p :=
    ColimitPerfection.isPRadical A p hA
  SpecMap_of_isPRadical _ p ColimitPerfection.natCast_eq_zero

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IsPerfect

variable {A B : CommRingCat.{u}} (φ : A ⟶ B) {p : ℕ} [Fact p.Prime] (Y : Scheme.{u})
  [IsPerfect Y p]

/-- **Morphisms from a perfect scheme lift uniquely along the spectrum of a `p`-radical map.** If
`Y` is perfect and `φ : A ⟶ B` is `p`-radical with `p = 0` in `A`, then composition with
`Spec.map φ` is a bijection from morphisms `Y ⟶ Spec B` to morphisms `Y ⟶ Spec A`. -/
theorem bijective_comp_SpecMap [IsPRadical φ.hom p] (hA : (p : A) = 0) :
    Function.Bijective fun f : Y ⟶ Spec B ↦ f ≫ Spec.map φ := by
  -- Under the Γ–Spec adjunction, a morphism `Y ⟶ Spec R` is a ring map `R ⟶ Γ(Y, ⊤)`, and composing
  -- with `Spec.map φ` corresponds to precomposing that ring map with `φ`.
  let e (R : CommRingCat.{u}) : (R ⟶ Γ(Y, ⊤)) ≃ (Y ⟶ Spec R) :=
    (opEquiv _ _).symm.trans (ΓSpec.adjunction.homEquiv Y (op R))
  have he (g : B ⟶ Γ(Y, ⊤)) : e B g ≫ Spec.map φ = e A (φ ≫ g) :=
    (ΓSpec.adjunction.homEquiv_naturality_right _ φ.op).symm
  have h : Function.Bijective fun g : B ⟶ Γ(Y, ⊤) ↦ φ ≫ g :=
    (ConcreteCategory.homEquiv (X := A) (Y := Γ(Y, ⊤))).symm.bijective.comp <|
      (IsPRadical.bijective_comp φ.hom p hA).comp
        (ConcreteCategory.homEquiv (X := B) (Y := Γ(Y, ⊤))).bijective
  convert (e A).bijective.comp (h.comp (e B).symm.bijective) using 1
  ext1 f
  simp [← he]

/-- For a perfect scheme `Y` and a `p`-radical `φ : A ⟶ B` with `p = 0` in `A`, the bijection
`(Y ⟶ Spec B) ≃ (Y ⟶ Spec A)` given by composition with `Spec.map φ`. Its inverse lifts a morphism
`Y ⟶ Spec A` to `Spec B`. -/
noncomputable def homSpecEquiv [IsPRadical φ.hom p] (hA : (p : A) = 0) :
    (Y ⟶ Spec B) ≃ (Y ⟶ Spec A) :=
  .ofBijective _ (bijective_comp_SpecMap φ Y hA)

@[simp]
theorem homSpecEquiv_apply [IsPRadical φ.hom p] (hA : (p : A) = 0) (f : Y ⟶ Spec B) :
    homSpecEquiv φ Y hA f = f ≫ Spec.map φ :=
  (rfl)

/-- The lift of a morphism `g : Y ⟶ Spec A` along `Spec.map φ` composes with `Spec.map φ` to
`g`. -/
@[reassoc (attr := simp)]
theorem homSpecEquiv_symm_comp [IsPRadical φ.hom p] (hA : (p : A) = 0) (g : Y ⟶ Spec A) :
    (homSpecEquiv φ Y hA).symm g ≫ Spec.map φ = g :=
  (homSpecEquiv φ Y hA).apply_symm_apply g

end AlgebraicGeometry.Scheme.IsPerfect

/-! ### The perfection of a scheme -/

namespace AlgebraicGeometry.Scheme

open TauCeti TauCeti.AlgebraicGeometry AffineZariskiSite

noncomputable section

section ColimitPerfection

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]

/-- The spectrum of the colimit perfection of a ring in which `p` vanishes is perfect. -/
instance isPerfect_Spec_colimitPerfection (hA : (p : A) = 0) :
    IsPerfect (Spec (.of (ColimitPerfection A p hA))) p :=
  (isPerfect_Spec_iff _).2 ⟨ColimitPerfection.natCast_eq_zero, inferInstance⟩

end ColimitPerfection

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : (p : Γ(X, ⊤)) = 0)

/-- The presheaf of colimit perfections of the rings of sections of a scheme `X` over `𝔽_p`,
`U ↦ ColimitPerfection Γ(X, U)`. -/
@[expose]
def perfectionPresheaf : X.Opensᵒᵖ ⥤ CommRingCat.{u} where
  obj U := .of (ColimitPerfection Γ(X, U.unop) p (natCast_app_eq_zero hX U.unop))
  map i := CommRingCat.ofHom (ColimitPerfection.map _ _ (X.presheaf.map i).hom)
  map_id U := by
    ext1
    rw [X.presheaf.map_id, CommRingCat.hom_id, ColimitPerfection.map_id, CommRingCat.hom_ofHom,
      CommRingCat.hom_id]
  map_comp i j := by
    ext1
    rw [X.presheaf.map_comp, CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
      CommRingCat.hom_ofHom, CommRingCat.hom_ofHom,
      ColimitPerfection.map_comp _ (natCast_app_eq_zero hX _)]

@[simp]
theorem perfectionPresheaf_obj (U : X.Opensᵒᵖ) :
    (X.perfectionPresheaf p hX).obj U =
      .of (ColimitPerfection Γ(X, U.unop) p (natCast_app_eq_zero hX U.unop)) :=
  (rfl)

@[simp]
theorem perfectionPresheaf_map {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    (X.perfectionPresheaf p hX).map i =
      CommRingCat.ofHom (ColimitPerfection.map _ _ (X.presheaf.map i).hom) :=
  (rfl)

/-- The structure morphism from the structure presheaf of `X` to its presheaf of colimit
perfections. -/
@[expose]
def toPerfectionPresheaf : X.presheaf ⟶ X.perfectionPresheaf p hX where
  app U := CommRingCat.ofHom (ColimitPerfection.of _ p _)
  naturality _ _ i := by
    ext1
    exact (ColimitPerfection.map_comp_of _ (X.presheaf.map i).hom).symm

@[simp]
theorem toPerfectionPresheaf_app (U : X.Opensᵒᵖ) :
    (X.toPerfectionPresheaf p hX).app U =
      CommRingCat.ofHom (ColimitPerfection.of _ p (natCast_app_eq_zero hX U.unop)) :=
  (rfl)

/-- On the affine opens of `X`, the presheaf of colimit perfections is coequifibered over the
structure presheaf: over a basic open `D(f)` of an affine open `U`, it is the localization away
from `f` of the colimit perfection of `Γ(X, U)`. -/
theorem coequifibered_toPerfectionPresheaf :
    ((toOpensFunctor X).op.whiskerLeft (X.toPerfectionPresheaf p hX)).Coequifibered :=
  coequifibered_iff_forall_isLocalizationAway.mpr fun U f ↦
    have := U.2.isLocalization_basicOpen f
    ColimitPerfection.isLocalization_away (A' := Γ(X, X.basicOpen f))
      (hA := natCast_app_eq_zero hX U.1) f (natCast_app_eq_zero hX _)

/-- The relative gluing datum of the perfection of `X`: the affine schemes
`Spec (ColimitPerfection Γ(X, U))` over the affine opens `U` of `X`. -/
@[expose]
def perfectionGluingData : (directedCover X).RelativeGluingData :=
  relativeGluingData (X.coequifibered_toPerfectionPresheaf p hX)

/-- The *perfection* `X^perf` of a scheme `X` over `𝔽_p`, glued from the spectra of the colimit
perfections `Spec (ColimitPerfection Γ(X, U))` over the affine opens `U` of `X`. It is perfect
(`AlgebraicGeometry.Scheme.isPerfect_perfection`) and universal among perfect schemes over `X`
(`AlgebraicGeometry.Scheme.bijective_comp_fromPerfection`). -/
@[expose]
def perfection : Scheme.{u} :=
  (X.perfectionGluingData p hX).glued

/-- The structure morphism `X^perf ⟶ X` of the perfection. -/
@[expose]
def fromPerfection : X.perfection p hX ⟶ X :=
  (X.perfectionGluingData p hX).toBase

/-- The open cover of the perfection of `X` by the spectra of the colimit perfections of the rings
of sections of `X` over its affine opens. -/
@[expose]
def perfectionCover : (X.perfection p hX).OpenCover :=
  (X.perfectionGluingData p hX).cover

instance isOpenImmersion_perfectionCover_f (U : X.AffineZariskiSite) :
    IsOpenImmersion ((X.perfectionCover p hX).f U) :=
  isOpenImmersion_relativeGluingData_cover_f (X.coequifibered_toPerfectionPresheaf p hX) U

theorem perfectionCover_X (U : X.AffineZariskiSite) :
    (X.perfectionCover p hX).X U =
      Spec (.of (ColimitPerfection Γ(X, U.1) p (natCast_app_eq_zero hX U.1))) :=
  (rfl)

/-- Over an affine open `U` of `X`, the structure morphism of the perfection is `Spec` of the map
from `Γ(X, U)` to its colimit perfection. -/
@[reassoc (attr := simp)]
theorem perfectionCover_f_fromPerfection (U : X.AffineZariskiSite) :
    (X.perfectionCover p hX).f U ≫ X.fromPerfection p hX =
      Spec.map ((X.toPerfectionPresheaf p hX).app (op U.1)) ≫ U.2.fromSpec :=
  relativeGluingData_cover_f_toBase (X.coequifibered_toPerfectionPresheaf p hX) U

/-- The map from the ring of sections of `X` over an open to its colimit perfection is
`p`-radical. -/
instance isPRadical_toPerfectionPresheaf_app (U : X.Opensᵒᵖ) :
    IsPRadical ((X.toPerfectionPresheaf p hX).app U).hom p :=
  ColimitPerfection.isPRadical _ p _

/-- The preimage of an affine open `U` of `X` in the perfection is the chart over `U`. -/
theorem fromPerfection_preimage (U : X.AffineZariskiSite) :
    X.fromPerfection p hX ⁻¹ᵁ U.1 = ((X.perfectionCover p hX).f U).opensRange :=
  relativeGluingData_toBase_preimage (X.coequifibered_toPerfectionPresheaf p hX) U

/-- **The perfection is affine-locally the colimit perfection**: over an affine open `U` of `X`,
the perfection of `X` is `Spec (ColimitPerfection Γ(X, U))`. -/
theorem isPullback_perfectionCover (U : X.AffineZariskiSite) :
    IsPullback (Spec.map ((X.toPerfectionPresheaf p hX).app (op U.1)) ≫ U.2.isoSpec.inv)
      ((X.perfectionCover p hX).f U) U.1.ι (X.fromPerfection p hX) :=
  isPullback_relativeGluingData_cover (X.coequifibered_toPerfectionPresheaf p hX) U

/-- The structure morphism of the perfection is affine. -/
instance isAffineHom_fromPerfection : IsAffineHom (X.fromPerfection p hX) :=
  isAffineHom_relativeGluingData_toBase (X.coequifibered_toPerfectionPresheaf p hX)

/-- A morphism property which is local on the target holds for the structure morphism of the
perfection of `X` exactly when it holds for `Spec` of the maps from the rings of sections of `X`
over its affine opens to their colimit perfections. -/
theorem fromPerfection_iff (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P] :
    P (X.fromPerfection p hX) ↔ ∀ U : X.affineOpens,
      P (Spec.map (CommRingCat.ofHom (ColimitPerfection.of _ p (natCast_app_eq_zero hX U.1)))) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top X)]
  refine forall_congr' fun U ↦ ?_
  -- Over `U`, the restriction of the structure morphism is the chart of the perfection over `U`.
  have h := X.isPullback_perfectionCover p hX ⟨U.1, U.2⟩
  have h' := isPullback_morphismRestrict (X.fromPerfection p hX) U.1
  rw [← P.cancel_left_of_respectsIso (h.isoIsPullback _ _ h').hom,
    h.isoIsPullback_hom_fst _ _ h', P.cancel_right_of_respectsIso, toPerfectionPresheaf_app]
  rfl

/-- **The perfection of a scheme is a universal homeomorphism onto it.** -/
instance isUniversalHomeomorphism_fromPerfection :
    IsUniversalHomeomorphism (X.fromPerfection p hX) :=
  (X.fromPerfection_iff p hX _).2 fun _ ↦ inferInstance

/-- The prime `p` vanishes on the perfection of `X`. -/
theorem natCast_perfection_eq_zero : (p : Γ(X.perfection p hX, ⊤)) = 0 :=
  natCast_eq_zero_of_hom (X.fromPerfection p hX) hX

/-- **The perfection of a scheme is perfect**: it is covered by the spectra of colimit
perfections, which are perfect. -/
instance isPerfect_perfection : IsPerfect (X.perfection p hX) p :=
  IsPerfect.of_openCover (X.perfectionCover p hX)
    (fun U ↦ isPerfect_Spec_colimitPerfection (natCast_app_eq_zero hX U.1))
    (X.natCast_perfection_eq_zero p hX)

/-- **A perfect scheme is its own perfection**: the structure morphism of the perfection of a
perfect scheme is an isomorphism. -/
instance isIso_fromPerfection [IsPerfect X p] : IsIso (X.fromPerfection p hX) := by
  refine (MorphismProperty.isomorphisms.iff _).1
    ((X.fromPerfection_iff p hX (MorphismProperty.isomorphisms Scheme)).2 fun U ↦ ?_)
  have : IsIso (CommRingCat.ofHom (ColimitPerfection.of Γ(X, U.1) p
      (natCast_app_eq_zero hX U.1))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (ColimitPerfection.bijective_of _ p _)
  exact (MorphismProperty.isomorphisms.iff _).2 inferInstance

/-! ### The universal property of the perfection -/

section UniversalProperty

variable {X p hX} {T : Scheme.{u}} [IsPerfect T p]

/-- The affine opens of `X` cover `X`, indexed by the small affine Zariski site. -/
private theorem isOpenCover_affineZariskiSite :
    TopologicalSpace.IsOpenCover fun U : X.AffineZariskiSite ↦ U.toOpens := by
  refine .mk (top_le_iff.1 fun x _ ↦ ?_)
  obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.1
    ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U.1, U.2⟩, hxU⟩

omit [IsPerfect T p] in
/-- A morphism to the perfection of `X` maps the preimage of an affine open `U` of `X` into the
chart of the perfection over `U`. -/
private theorem range_comp_subset_range_perfectionCover_f (c : T ⟶ X.perfection p hX)
    (U : X.AffineZariskiSite) {W : T.Opens} (hW : W ≤ (c ≫ X.fromPerfection p hX) ⁻¹ᵁ U.1) :
    Set.range (W.ι ≫ c) ⊆ Set.range ((X.perfectionCover p hX).f U) := by
  rintro _ ⟨x, rfl⟩
  have hx : c (W.ι x) ∈ X.fromPerfection p hX ⁻¹ᵁ U.1 := hW x.2
  rw [fromPerfection_preimage] at hx
  exact hx

/-- **Morphisms from a perfect scheme to the perfection are determined over `X`**: two morphisms
`T ⟶ X^perf` from a perfect scheme `T` agree once they agree after composing to `X`. -/
theorem perfection_hom_ext {a b : T ⟶ X.perfection p hX}
    (h : a ≫ X.fromPerfection p hX = b ≫ X.fromPerfection p hX) : a = b := by
  refine (T.openCoverOfIsOpenCover _
    (isOpenCover_affineZariskiSite.comap (a ≫ X.fromPerfection p hX).base.1)).hom_ext _ _
    fun (U : X.AffineZariskiSite) ↦ ?_
  -- Over the preimage `W` of the affine open `U`, both morphisms land in the chart over `U`, which
  -- is the spectrum of a `p`-radical extension of `Γ(X, U)`.
  let W := (a ≫ X.fromPerfection p hX) ⁻¹ᵁ U.1
  let ι := (X.perfectionCover p hX).f U
  have : IsOpenImmersion ι := X.isOpenImmersion_perfectionCover_f p hX U
  let φ := (X.toPerfectionPresheaf p hX).app (op U.1)
  -- After composing to `X`, a lift `l` of `W.ι ≫ c` to the chart is `W.ι ≫ c ≫ fromPerfection`.
  have key (c : T ⟶ X.perfection p hX) (l : (W : Scheme) ⟶ (X.perfectionCover p hX).X U)
      (hl : l ≫ ι = W.ι ≫ c) :
      (l ≫ Spec.map φ) ≫ U.2.fromSpec = W.ι ≫ c ≫ X.fromPerfection p hX := by
    have h₁ := X.perfectionCover_f_fromPerfection p hX U
    calc (l ≫ Spec.map φ) ≫ U.2.fromSpec = l ≫ ι ≫ X.fromPerfection p hX := by
          simp only [ι, h₁, φ]
          exact Category.assoc _ _ _
      _ = W.ι ≫ c ≫ X.fromPerfection p hX := by simp only [reassoc_of% hl]
  have ha := IsOpenImmersion.lift_fac ι (W.ι ≫ a)
    (range_comp_subset_range_perfectionCover_f a U le_rfl)
  have hb := IsOpenImmersion.lift_fac ι (W.ι ≫ b)
    (range_comp_subset_range_perfectionCover_f b U (h ▸ le_rfl))
  have hl := (IsPerfect.bijective_comp_SpecMap φ W (natCast_app_eq_zero hX U.1)).1
    ((cancel_mono U.2.fromSpec).1 ((key a _ ha).trans
      ((congrArg (W.ι ≫ ·) h).trans (key b _ hb).symm)))
  exact ha.symm.trans ((congrArg (· ≫ ι) hl).trans hb)

/-- The lift of a morphism `T ⟶ X` from a perfect scheme `T` to the chart of the perfection of
`X` over an affine open `U`, defined on the preimage of `U`. -/
private def liftPerfectionCover (g : T ⟶ X) (U : X.AffineZariskiSite) :
    (g ⁻¹ᵁ U.1 : Scheme) ⟶ X.perfection p hX :=
  (IsPerfect.homSpecEquiv ((X.toPerfectionPresheaf p hX).app (op U.1)) (g ⁻¹ᵁ U.1)
      (natCast_app_eq_zero hX U.1)).symm ((g ∣_ U.1) ≫ U.2.isoSpec.hom) ≫
    (X.perfectionCover p hX).f U

private theorem liftPerfectionCover_fromPerfection (g : T ⟶ X) (U : X.AffineZariskiSite) :
    liftPerfectionCover (hX := hX) g U ≫ X.fromPerfection p hX = (g ⁻¹ᵁ U.1).ι ≫ g := by
  -- The rewrites are spelled out as a chain of equalities: the small affine Zariski site is not
  -- reducibly a subtype, so `rw` cannot abstract its elements.
  rw [liftPerfectionCover]
  refine (Category.assoc _ _ _).trans ?_
  refine (_ ≫= X.perfectionCover_f_fromPerfection p hX U).trans ?_
  refine (IsPerfect.homSpecEquiv_symm_comp_assoc _ _ _ _ _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact (_ ≫= U.2.isoSpec_hom_fromSpec).trans (morphismRestrict_ι g U.1)

/-- **The universal property of the perfection.** For a perfect scheme `T`, composition with the
structure morphism `X^perf ⟶ X` is a bijection from morphisms `T ⟶ X^perf` to morphisms
`T ⟶ X`. Thus the perfection is a coreflection of `X` into perfect schemes. -/
theorem bijective_comp_fromPerfection :
    Function.Bijective fun g : T ⟶ X.perfection p hX ↦ g ≫ X.fromPerfection p hX := by
  refine ⟨fun a b h ↦ perfection_hom_ext h, fun g ↦ ?_⟩
  let 𝒱 := T.openCoverOfIsOpenCover _ (isOpenCover_affineZariskiSite.comap g.base.1)
  -- Glue the lifts over the preimages of the affine opens of `X`; they agree on overlaps by
  -- uniqueness of lifts from perfect schemes.
  have (U : X.AffineZariskiSite) : IsPerfect (𝒱.X U) p := IsPerfect.opens _
  refine ⟨𝒱.glueMorphisms (fun (U : X.AffineZariskiSite) ↦ liftPerfectionCover g U)
    fun (U V : X.AffineZariskiSite) ↦ perfection_hom_ext ?_, ?_⟩
  · refine (Category.assoc _ _ _).trans ((_ ≫= liftPerfectionCover_fromPerfection g U).trans ?_)
    exact (Limits.pullback.condition_assoc g).trans
      ((_ ≫= liftPerfectionCover_fromPerfection g V).symm.trans (Category.assoc _ _ _).symm)
  · refine 𝒱.hom_ext _ _ fun (U : X.AffineZariskiSite) ↦ ?_
    exact (Cover.ι_glueMorphisms_assoc _ _ _ _ _).trans (liftPerfectionCover_fromPerfection g U)

variable (X p hX T)

/-- For a perfect scheme `T`, the bijection `(T ⟶ X^perf) ≃ (T ⟶ X)` given by composition with the
structure morphism of the perfection. Its inverse lifts a morphism `T ⟶ X` to the perfection. -/
def homPerfectionEquiv : (T ⟶ X.perfection p hX) ≃ (T ⟶ X) :=
  .ofBijective _ bijective_comp_fromPerfection

variable {X p hX T}

@[simp]
theorem homPerfectionEquiv_apply (g : T ⟶ X.perfection p hX) :
    X.homPerfectionEquiv p hX T g = g ≫ X.fromPerfection p hX :=
  (rfl)

/-- The lift of a morphism `g : T ⟶ X` to the perfection composes with `X^perf ⟶ X` to `g`. -/
@[reassoc (attr := simp)]
theorem homPerfectionEquiv_symm_comp (g : T ⟶ X) :
    (X.homPerfectionEquiv p hX T).symm g ≫ X.fromPerfection p hX = g :=
  (X.homPerfectionEquiv p hX T).apply_symm_apply g

end UniversalProperty

end

end AlgebraicGeometry.Scheme

/-! ### Checks -/

namespace AlgebraicGeometry.Scheme

open TauCeti.AlgebraicGeometry

variable {p : ℕ} [Fact p.Prime]

/-- The perfection `Spec 𝔽_p[t^{1/p^∞}] ⟶ 𝔸¹_{𝔽_p}` of the affine line is a universal
homeomorphism. -/
example : IsUniversalHomeomorphism
    (Spec.map (CommRingCat.ofHom (PerfectClosure.of (ZMod p)[X] p))) :=
  inferInstance

/-- The perfection of the affine line is not an isomorphism, since `𝔸¹_{𝔽_p}` is not perfect. -/
example : ¬ IsIso (Spec.map (CommRingCat.ofHom (PerfectClosure.of (ZMod p)[X] p))) := fun _ ↦
  not_isPerfect_Spec_polynomial (p := p) (ZMod p)
    (IsPerfect.of_etale (inv (Spec.map (CommRingCat.ofHom (PerfectClosure.of (ZMod p)[X] p)))))

/-- Every morphism from a perfect scheme to the affine line `𝔸¹_{𝔽_p}` lifts uniquely to its
perfection. -/
example (Y : Scheme.{0}) [IsPerfect Y p] :
    Function.Bijective fun f : Y ⟶ Spec (.of (PerfectClosure (ZMod p)[X] p)) ↦
      f ≫ Spec.map (CommRingCat.ofHom (PerfectClosure.of (ZMod p)[X] p)) :=
  have : IsPRadical (CommRingCat.ofHom (PerfectClosure.of (ZMod p)[X] p)).hom p :=
    PerfectClosure.isPRadical _ p
  IsPerfect.bijective_comp_SpecMap _ Y (CharP.cast_eq_zero _ p)

/-- The perfection of the affine line `𝔸¹_{𝔽_p}` is not an isomorphism onto it, since the perfection
is perfect and `𝔸¹_{𝔽_p}` is not. -/
example : ¬ IsIso ((Spec (.of (ZMod p)[X])).fromPerfection p
    (by rw [← map_natCast (ΓSpecIso (.of (ZMod p)[X])).inv.hom, CharP.cast_eq_zero, map_zero])) :=
  fun _ ↦ not_isPerfect_Spec_polynomial (p := p) (ZMod p)
    (IsPerfect.of_etale (inv ((Spec (.of (ZMod p)[X])).fromPerfection p _)))

end AlgebraicGeometry.Scheme
