/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import TauCeti.AlgebraicGeometry.Scheme.Opens
import TauCeti.RingTheory.Localization.Module

/-!
# Restricting local properties of scheme morphisms

For a morphism of schemes `f : X ⟶ Y` and an open `U` of `Y`, Mathlib's `f ∣_ U` is the
restriction `f ⁻¹ᵁ U ⟶ U`. A property local on the target passes from this restriction to
every smaller open. A property local on the source holds for a morphism that has it on an open
neighbourhood of every point of its source, and for a morphism out of a binary coproduct that has
it on both summands. An open immersion restricts to an isomorphism over
opens in its range.
Restricting the source to an open equal to the full preimage gives a pullback square, which
transfers properties stable under base change to `Scheme.Hom.resLE`. Between affine opens, a
property attached to a ring-hom property holds for `Scheme.Hom.resLE` iff the ring-hom property
holds for `Scheme.Hom.appLE`. Dually, in a pullback square of the inclusion of an open `U` along
`f`, pullback of functions along the top morphism identifies the functions on `f ⁻¹ᵁ U` with the
global functions of the base change.

## Main results

* `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict_of_le`: a property local on the target
  passes from `f ∣_ U` to `f ∣_ V` when `V ≤ U`.
* `AlgebraicGeometry.IsZariskiLocalAtSource.of_forall_exists_ι_comp`: a property local on the
  source holds for `f` if every point of `X` has an open neighbourhood `U` with `P (U.ι ≫ f)`.
* `AlgebraicGeometry.IsZariskiLocalAtSource.coprodDesc`: a property local on the source holds for
  `coprod.desc f g` when it holds for `f` and for `g`.
* `AlgebraicGeometry.Scheme.Hom.isIso_morphismRestrict_of_le_opensRange`: an open immersion
  restricts to an isomorphism over every open contained in its range.
* `AlgebraicGeometry.Scheme.Hom.isIso_appLE_of_isIso_morphismRestrict`: if `f ∣_ U` is an
  isomorphism and `V = f ⁻¹ᵁ U`, then `f.appLE U V h.le` is an isomorphism.
* `AlgebraicGeometry.Scheme.Hom.bijective_localizedModuleMap_of_isIso_morphismRestrict`: on qcqs
  schemes, if `f` restricts to an isomorphism over `Y.basicOpen (algebraMap R Γ(Y, ⊤) s)`, the
  induced `R`-algebra map on global sections becomes bijective after inverting `s`;
  `AlgebraicGeometry.Scheme.Hom.bijective_localizedModuleMap_of_basicOpen_le_opensRange` specializes
  this to open immersions containing that basic open in their range.
* `AlgebraicGeometry.Scheme.Hom.isPullback_resLE_of_eq`: the restriction of `f` to an open `U`
  of the target and an open `V` of the source equal to `f ⁻¹ᵁ U` is a pullback of `f`.
* `AlgebraicGeometry.Scheme.Hom.isIso_morphismRestrict_of_isIso_comp`: if an open immersion `ι`
  contains `f ⁻¹ᵁ V` in its range and `(ι ≫ f) ∣_ V` is an isomorphism, so is `f ∣_ V`.
* `AlgebraicGeometry.Scheme.Hom.isIso_pullbackFst_morphismRestrict`: being an isomorphism over an
  open is preserved by base change.
* `AlgebraicGeometry.Scheme.Hom.isIso_pullbackFst_of_preimage_eq_top`: if `f⁻¹(U)` is all of `X`
  and `φ` is an isomorphism over `U`, the base change `X ×_Y S' ⟶ X` is an isomorphism.
* `AlgebraicGeometry.Scheme.Hom.existsUnique_apply_eq_of_isIso_morphismRestrict`: if `f` restricts
  to an isomorphism over `U`, every point of `U` has a unique preimage under `f`.
* `AlgebraicGeometry.HasRingHomProperty.resLE_iff`: for affine opens `V ⊆ f ⁻¹ᵁ U`, a property
  attached to a ring-hom property `Q` holds for `f.resLE U V` iff `Q` holds for `f.appLE U V`.
* `CategoryTheory.CommSq.appLE_app_topIso_hom`: in a commutative square over the inclusion of an
  open `U`, the two ways of pulling a function on `U` back to the source of the square agree.
* `CategoryTheory.IsPullback.isIso_appLE`: in a pullback square of the inclusion of an open `U`
  along `f`, pullback along the top morphism identifies the functions on `f ⁻¹ᵁ U` with the
  global functions of the base change.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A property local on the target passes from the restriction over `U` to the restriction
over every open `V ≤ U`. -/
theorem IsZariskiLocalAtTarget.restrict_of_le (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] {f : X ⟶ Y} {U V : Y.Opens} (h : P (f ∣_ U)) (hVU : V ≤ U) :
    P (f ∣_ V) := by
  have himage : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hVU
  exact (P.arrow_mk_iso_iff
    (morphismRestrictRestrict f _ _ ≪≫ morphismRestrictEq f himage)).mp
    (IsZariskiLocalAtTarget.restrict h _)

/-- A property local on the source holds for a morphism if every point of its source has an
open neighbourhood on which it holds. -/
theorem IsZariskiLocalAtSource.of_forall_exists_ι_comp {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtSource P] {f : X ⟶ Y} (H : ∀ x, ∃ U : X.Opens, x ∈ U ∧ P (U.ι ≫ f)) :
    P f := by
  choose U hxU hU using H
  exact of_iSup_eq_top U
    (eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩) hU

/-- A property local on the source holds for a morphism out of a binary coproduct when it holds
for its restrictions to both summands. -/
theorem IsZariskiLocalAtSource.coprodDesc {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtSource P] {A B : Scheme.{u}} {f : A ⟶ Y} {g : B ⟶ Y} (hf : P f) (hg : P g) :
    P (Limits.coprod.desc f g) :=
  of_openCover (coprodOpenCover.{u, u} A B) fun i ↦ by
    rcases i with ⟨⟩ | ⟨⟩ <;> simpa [coprodOpenCover]

/-- An open immersion `f` restricts to an isomorphism over every open `V` contained in its
range. -/
theorem Scheme.Hom.isIso_morphismRestrict_of_le_opensRange [IsOpenImmersion f] {V : Y.Opens}
    (hV : V ≤ f.opensRange) : IsIso (f ∣_ V) := by
  refine (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, ⟨fun y ↦ ?_⟩⟩
  obtain ⟨z, hz⟩ := hV y.property
  exact ⟨⟨z, (Scheme.Hom.mem_preimage _).mpr (hz ▸ y.property)⟩,
    Subtype.ext ((morphismRestrict_base_coe _ _ _).trans hz)⟩

/-- If `f ∣_ U` is an isomorphism over an open `U` of `Y` and `V = f ⁻¹ᵁ U`, then
`f.appLE U V h.le : Γ(Y, U) ⟶ Γ(X, V)` is an isomorphism. -/
theorem Scheme.Hom.isIso_appLE_of_isIso_morphismRestrict {U : Y.Opens} {V : X.Opens}
    (h : V = f ⁻¹ᵁ U) [IsIso (f ∣_ U)] : IsIso (f.appLE U V h.le) := by
  have h1 : IsIso ((f ∣_ U).app ⊤) := inferInstance
  rw [morphismRestrict_app'] at h1
  exact (f.appLE_congr _ U.ι_image_top ((f ⁻¹ᵁ U).ι_image_top.trans h.symm)
    fun φ ↦ IsIso φ).mp h1

/-- On quasi-compact quasi-separated schemes `X` and `Y` with `R`-algebra structures on their
global sections, if `f : X ⟶ Y` induces `g : Γ(Y, ⊤) →ₐ[R] Γ(X, ⊤)` and restricts to an
isomorphism over `Y.basicOpen (algebraMap R Γ(Y, ⊤) s)`, then `g` becomes bijective after
inverting `s`. -/
theorem Scheme.Hom.bijective_localizedModuleMap_of_isIso_morphismRestrict {R : Type*}
    [CommSemiring R] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] [Algebra R Γ(Y, ⊤)] [Algebra R Γ(X, ⊤)]
    (g : Γ(Y, ⊤) →ₐ[R] Γ(X, ⊤)) (hg : g.toRingHom = f.appTop.hom) (s : R)
    [IsIso (f ∣_ Y.basicOpen (algebraMap R Γ(Y, ⊤) s))] :
    Function.Bijective (LocalizedModule.map (.powers s) g.toLinearMap) := by
  have hgx (y : Γ(Y, ⊤)) : f.appTop y = g y := congr($hg.symm y)
  let UY := Y.basicOpen (algebraMap R Γ(Y, ⊤) s)
  let UX := X.basicOpen (algebraMap R Γ(X, ⊤) s)
  have hUX : UX = f ⁻¹ᵁ UY := by
    dsimp only [UX, UY]
    rw [← g.commutes s, ← hgx]
    exact (Scheme.preimage_basicOpen_top f _).symm
  -- Sections over `UY` and `UX` are principal localizations of global sections.
  let resY : Γ(Y, ⊤) ⟶ Γ(Y, UY) := Y.presheaf.map (homOfLE le_top).op
  let resX : Γ(X, ⊤) ⟶ Γ(X, UX) := X.presheaf.map (homOfLE le_top).op
  have : IsLocalization.Away (algebraMap R Γ(Y, ⊤) s) Γ(Y, UY) :=
    isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ _
  have : IsLocalization.Away (algebraMap R Γ(X, ⊤) s) Γ(X, UX) :=
    isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ _
  -- Identify the localized map with the isomorphism `f.appLE UY UX hUX.le`.
  have hfLE_iso : IsIso (f.appLE UY UX hUX.le) := f.isIso_appLE_of_isIso_morphismRestrict hUX
  refine (g.bijective_localizedModuleMap_powers_iff s (f.appLE UY UX hUX.le).hom fun y ↦ ?_).mpr
    ((ConcreteCategory.isIso_iff_bijective _).mp hfLE_iso)
  -- `f.appLE_eq_app` identifies `f.appLE ⊤ ⊤ le_top` with `f.appTop` (since `f ⁻¹ᵁ ⊤ = ⊤`
  -- definitionally).
  have happ : f.appLE ⊤ ⊤ le_top = f.appTop := f.appLE_eq_app
  have hcomm : resY ≫ f.appLE UY UX hUX.le = f.appTop ≫ resX := by
    dsimp only [resY, resX]
    rw [Scheme.Hom.map_appLE, ← f.appLE_map (le_top : ⊤ ≤ f ⁻¹ᵁ ⊤) (homOfLE le_top).op, happ]
  simpa only [RingHom.algebraMap_toAlgebra, CommRingCat.comp_apply, hgx] using congr($hcomm y)

/-- On quasi-compact quasi-separated schemes `X` and `Y` with `R`-algebra structures on their
global sections, if `f : X ⟶ Y` is an open immersion inducing `g : Γ(Y, ⊤) →ₐ[R] Γ(X, ⊤)` and
containing `Y.basicOpen (algebraMap R Γ(Y, ⊤) s)` in its range, then `g` becomes bijective after
inverting `s`. -/
theorem Scheme.Hom.bijective_localizedModuleMap_of_basicOpen_le_opensRange {R : Type*}
    [CommSemiring R] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] [IsOpenImmersion f] [Algebra R Γ(Y, ⊤)] [Algebra R Γ(X, ⊤)]
    (g : Γ(Y, ⊤) →ₐ[R] Γ(X, ⊤)) (hg : g.toRingHom = f.appTop.hom) (s : R)
    (hs : Y.basicOpen (algebraMap R Γ(Y, ⊤) s) ≤ f.opensRange) :
    Function.Bijective (LocalizedModule.map (.powers s) g.toLinearMap) := by
  have := f.isIso_morphismRestrict_of_le_opensRange hs
  exact f.bijective_localizedModuleMap_of_isIso_morphismRestrict g hg s

/-- Restricting `f` over an open `U` of the target, with source the open `V = f ⁻¹ᵁ U` (up to a
propositional equality), gives a pullback of `f` along the inclusion of `U`. -/
theorem Scheme.Hom.isPullback_resLE_of_eq (U : Y.Opens) {V : X.Opens} (h : V = f ⁻¹ᵁ U) :
    IsPullback (f.resLE U V h.le) V.ι U.ι f := by
  subst h
  simpa [Scheme.Hom.resLE_eq_morphismRestrict] using isPullback_morphismRestrict f U

/-- If the range of an open immersion `ι` contains `f ⁻¹ᵁ V` and `(ι ≫ f) ∣_ V` is an
isomorphism, then so is `f ∣_ V`: over `V`, the morphism `f` is `ι ≫ f` up to an isomorphism. -/
theorem Scheme.Hom.isIso_morphismRestrict_of_isIso_comp {Z : Scheme.{u}} (ι : Z ⟶ X)
    [IsOpenImmersion ι] {V : Y.Opens} (hV : f ⁻¹ᵁ V ≤ ι.opensRange)
    (h : IsIso ((ι ≫ f) ∣_ V)) : IsIso (f ∣_ V) := by
  have : IsIso (ι ∣_ f ⁻¹ᵁ V) := ι.isIso_morphismRestrict_of_le_opensRange hV
  rw [morphismRestrict_comp] at h
  -- `h` is passed explicitly: the source of the composite in its type is written
  -- `(ι ≫ f) ⁻¹ᵁ V` rather than `ι ⁻¹ᵁ f ⁻¹ᵁ V`, which instance search does not unfold.
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ (ι ∣_ f ⁻¹ᵁ V) (f ∣_ V) _ h

/-- If `φ : S' ⟶ Y` is an isomorphism over `U`, then the projection `X ×_Y S' ⟶ X` is an
isomorphism over `f⁻¹(U)`: it is the base change of `φ⁻¹(U) ≅ U` along `f⁻¹(U) ⟶ U`. -/
theorem Scheme.Hom.isIso_pullbackFst_morphismRestrict {S' : Scheme.{u}} (φ : S' ⟶ Y)
    {U : Y.Opens} (hU : IsIso (φ ∣_ U)) : IsIso (Limits.pullback.fst f φ ∣_ (f ⁻¹ᵁ U)) := by
  have s := (isPullback_morphismRestrict (Limits.pullback.fst f φ) (f ⁻¹ᵁ U)).flip.paste_horiz
    (IsPullback.of_hasPullback f φ).flip
  rw [← morphismRestrict_ι] at s
  exact (s.of_right' (isPullback_morphismRestrict φ U).flip).isIso_snd_of_isIso

/-- If `f⁻¹(U)` is all of `X` and `φ : S' ⟶ Y` is an isomorphism over `U`, then the projection
`X ×_Y S' ⟶ X` is an isomorphism. -/
theorem Scheme.Hom.isIso_pullbackFst_of_preimage_eq_top {S' : Scheme.{u}} (φ : S' ⟶ Y)
    {U : Y.Opens} (h : f ⁻¹ᵁ U = ⊤) (hU : IsIso (φ ∣_ U)) : IsIso (Limits.pullback.fst f φ) := by
  have := f.isIso_pullbackFst_morphismRestrict φ hU
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun _ : Unit ↦ f ⁻¹ᵁ U) (by simp [h]) fun _ ↦ this

/-- If the restriction of `f` over `U` is an isomorphism, every point in `U` has a
unique preimage in the whole source of `f`. -/
theorem Scheme.Hom.existsUnique_apply_eq_of_isIso_morphismRestrict (U : Y.Opens)
    [IsIso (f ∣_ U)] {x : Y} (hx : x ∈ U) : ∃! y : X, f y = x := by
  have hf : Function.Bijective (f ∣_ U) := by
    simpa only [Scheme.coe_homeoOfIso, asIso_hom] using
      (Scheme.homeoOfIso (asIso (f ∣_ U))).bijective
  obtain ⟨y, hy, huniq⟩ := hf.existsUnique ⟨x, hx⟩
  refine ⟨y.val, (morphismRestrict_base_coe f U y).symm.trans (congrArg Subtype.val hy),
    fun z hz ↦ ?_⟩
  have hzU : z ∈ f ⁻¹ᵁ U := (Scheme.Hom.mem_preimage f).mpr (hz.symm ▸ hx)
  have hz' : (f ∣_ U) ⟨z, hzU⟩ = ⟨x, hx⟩ :=
    Subtype.ext ((morphismRestrict_base_coe f U ⟨z, hzU⟩).trans hz)
  exact congrArg Subtype.val (huniq ⟨z, hzU⟩ hz')

/-- Let `V ⊆ f⁻¹ U` with `U` and `V` affine, and let `P` be a morphism property attached to the
ring-hom property `Q`. Then `P` holds for the restriction `V ⟶ U` of `f` iff `Q` holds for
`f.appLE U V : Γ(Y, U) ⟶ Γ(X, V)`. -/
theorem HasRingHomProperty.resLE_iff (P : MorphismProperty Scheme.{u})
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop} [HasRingHomProperty P Q]
    {f : X ⟶ Y} {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) : P (f.resLE U V hVU) ↔ Q (f.appLE U V hVU).hom := by
  have : IsAffine U := hU
  have : IsAffine V := hV
  rw [HasRingHomProperty.iff_of_isAffine (P := P)]
  exact (HasRingHomProperty.isLocal_ringHomProperty P).respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f U V hVU)

/-- A square of open immersions identifying the source with the full inverse image
of the target open identifies its top arrow with the restriction of the bottom arrow. -/
noncomputable def Scheme.Hom.morphismRestrictArrowIso {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) {i : U ⟶ X} {j : V ⟶ Y} (g : U ⟶ V)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (h : i ≫ f = g ≫ j) (he : f ⁻¹ᵁ j.opensRange = i.opensRange) :
    Arrow.mk (f ∣_ j.opensRange) ≅ Arrow.mk g := by
  have hi : Set.range (f ⁻¹ᵁ j.opensRange).ι = Set.range i := by
    rw [Scheme.Opens.range_ι, he]
    rfl
  have hj : Set.range j.opensRange.ι = Set.range j := by
    rw [Scheme.Opens.range_ι]
    rfl
  refine Arrow.isoMk' (f ∣_ j.opensRange) g
    (IsOpenImmersion.isoOfRangeEq (f ⁻¹ᵁ j.opensRange).ι i hi)
    (IsOpenImmersion.isoOfRangeEq j.opensRange.ι j hj) ?_
  rw [← cancel_mono j, Category.assoc, Category.assoc, ← h,
    IsOpenImmersion.isoOfRangeEq_hom_fac_assoc,
    IsOpenImmersion.isoOfRangeEq_hom_fac, morphismRestrict_ι]


/-- The source isomorphism identifying a restriction with an open square respects its inclusion. -/
@[reassoc (attr := simp)]
theorem Scheme.Hom.morphismRestrictArrowIso_hom_left_comp {U V : Scheme.{u}}
    {i : U ⟶ X} {j : V ⟶ Y} (g : U ⟶ V) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : i ≫ f = g ≫ j) (he : f ⁻¹ᵁ j.opensRange = i.opensRange) :
    (f.morphismRestrictArrowIso g h he).hom.left ≫ i = (f ⁻¹ᵁ j.opensRange).ι := by
  simp [morphismRestrictArrowIso, Arrow.isoMk']

/-- The target isomorphism identifying a restriction with an open square respects its inclusion. -/
@[reassoc (attr := simp)]
theorem Scheme.Hom.morphismRestrictArrowIso_hom_right_comp {U V : Scheme.{u}}
    {i : U ⟶ X} {j : V ⟶ Y} (g : U ⟶ V) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : i ≫ f = g ≫ j) (he : f ⁻¹ᵁ j.opensRange = i.opensRange) :
    (f.morphismRestrictArrowIso g h he).hom.right ≫ j = j.opensRange.ι := by
  simp [morphismRestrictArrowIso, Arrow.isoMk']

end AlgebraicGeometry

namespace CategoryTheory

open AlgebraicGeometry

variable {Z Y T : Scheme.{u}} {U : T.Opens} {j : Z ⟶ Y} {g : Z ⟶ U} {f : Y ⟶ T}

/-- In a commutative square over the inclusion of an open `U`, the top morphism `j` maps all of
its source into `f ⁻¹ᵁ U`. -/
theorem CommSq.top_le_preimage_preimage (h : CommSq j g f U.ι) : ⊤ ≤ j ⁻¹ᵁ f ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, h.w, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]
  exact (Scheme.Hom.preimage_top g).ge

/-- In a commutative square over the inclusion of an open `U`, pulling a function on `U` back to
the source along `g` is pulling it back along `f` to `f ⁻¹ᵁ U` and then along `j`. -/
theorem CommSq.appLE_app_topIso_hom (h : CommSq j g f U.ι) (r : Γ(U, ⊤)) :
    j.appLE (f ⁻¹ᵁ U) ⊤ h.top_le_preimage_preimage (f.app U (U.topIso.hom r)) = g.appTop r := by
  have hι : U.ι.appLE U ⊤ U.ι_preimage_self.ge (U.topIso.hom r) = r := by
    rw [← CommRingCat.comp_apply]
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_hom]
    exact congr($((T.presheaf.map_comp _ _).symm.trans (T.presheaf.map_id _)) r)
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.congr_appLE _ h.w _ _ _
      (by rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]; exact le_rfl),
    ← Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ U.ι_preimage_self.ge (Scheme.Hom.preimage_top _).ge,
    CommRingCat.comp_apply, hι]
  exact congr($((Scheme.Hom.app_eq_appLE _).symm) r)

/-- In a pullback square of the inclusion of an open `U` along `f`, pullback of functions along
the top morphism `j` is an isomorphism `Γ(Y, f ⁻¹ᵁ U) ≅ Γ(Z, ⊤)`. -/
theorem IsPullback.isIso_appLE (h : IsPullback j g f U.ι) :
    IsIso (j.appLE (f ⁻¹ᵁ U) ⊤ h.toCommSq.top_le_preimage_preimage) := by
  -- Through the pullback square of `f ∣_ U`, `j` is an isomorphism onto `f ⁻¹ᵁ U` followed by
  -- the inclusion of this open, on whose sections over `f ⁻¹ᵁ U` pullback is an isomorphism.
  let e := h.isoIsPullback _ _ (isPullback_morphismRestrict f U).flip
  have he : e.hom ≫ (f ⁻¹ᵁ U).ι = j := h.isoIsPullback_hom_fst _ _ _
  have h2 := Scheme.Hom.appLE_comp_appLE e.hom (f ⁻¹ᵁ U).ι (f ⁻¹ᵁ U) ⊤ ⊤
    (f ⁻¹ᵁ U).ι_preimage_self.ge le_top
  simp only [he] at h2
  rw [← h2]
  have : IsIso (e.hom.appLE ⊤ ⊤ le_top) :=
    (Scheme.Hom.appLE_congr _ le_rfl rfl e.hom.preimage_top fun φ ↦ IsIso φ).mp
      (by rw [Scheme.Hom.appLE_eq_app]; infer_instance)
  infer_instance

end CategoryTheory
