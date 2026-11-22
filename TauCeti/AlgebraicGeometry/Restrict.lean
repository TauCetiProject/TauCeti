/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Restricting local properties of scheme morphisms

For a morphism of schemes `f : X ⟶ Y` and an open `U` of `Y`, Mathlib's `f ∣_ U` is the
restriction `f ⁻¹ᵁ U ⟶ U`. A property local on the target passes from this restriction to
every smaller open. A property local on the source holds for a morphism that has it on an open
neighbourhood of every point of its source. An open immersion restricts to an isomorphism over
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
* `AlgebraicGeometry.Scheme.Hom.isIso_morphismRestrict_of_le_opensRange`: an open immersion
  restricts to an isomorphism over every open contained in its range.
* `AlgebraicGeometry.Scheme.Hom.isPullback_resLE_of_eq`: the restriction of `f` to an open `U`
  of the target and an open `V` of the source equal to `f ⁻¹ᵁ U` is a pullback of `f`.
* `AlgebraicGeometry.Scheme.Hom.isIso_morphismRestrict_of_isIso_comp`: if an open immersion `ι`
  contains `f ⁻¹ᵁ V` in its range and `(ι ≫ f) ∣_ V` is an isomorphism, so is `f ∣_ V`.
* `AlgebraicGeometry.HasRingHomProperty.resLE_iff`: for affine opens `V ⊆ f ⁻¹ᵁ U`, a property
  attached to a ring-hom property `Q` holds for `f.resLE U V` iff `Q` holds for `f.appLE U V`.
* `AlgebraicGeometry.Scheme.Hom.congr_appLE`: equal morphisms induce the same maps
  `Γ(Y, U) ⟶ Γ(X, V)`, whatever the proofs of `V ≤ f ⁻¹ᵁ U`.
* `CategoryTheory.CommSq.appLE_app_topIso_hom`: in a commutative square over the inclusion of an
  open `U`, the two ways of pulling a function on `U` back to the source of the square agree.
* `CategoryTheory.IsPullback.isIso_appLE`: in a pullback square of the inclusion of an open `U`
  along `f`, pullback along the top morphism identifies the functions on `f ⁻¹ᵁ U` with the
  global functions of the base change.
* `AlgebraicGeometry.Scheme.opensRange_homOfLE_sup`: the inclusions of `U` and `W` cover `U ⊔ W`.
* `TauCeti.AlgebraicGeometry.pullbackMapOpenIso`: pulling back an `Over U`-object pushed forward
  to `S` commutes with restricting `f` to `U`.
* `TauCeti.AlgebraicGeometry.infImageOpenIso`: canonical isomorphism between `U ⊓ (W₁.ι ''ᵁ V)`
  and `V.ι ⁻¹ᵁ (W₁.ι ⁻¹ᵁ U)`.
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

/-- An open immersion `f` restricts to an isomorphism over every open `V` contained in its
range. -/
theorem Scheme.Hom.isIso_morphismRestrict_of_le_opensRange [IsOpenImmersion f] {V : Y.Opens}
    (hV : V ≤ f.opensRange) : IsIso (f ∣_ V) := by
  refine (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, ⟨fun y ↦ ?_⟩⟩
  obtain ⟨z, hz⟩ := hV y.property
  exact ⟨⟨z, (Scheme.Hom.mem_preimage _).mpr (hz ▸ y.property)⟩,
    Subtype.ext ((morphismRestrict_base_coe _ _ _).trans hz)⟩

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

/-- Equal morphisms induce the same maps on sections `Γ(Y, U) ⟶ Γ(X, V)`. Unlike rewriting along
`f = g`, this applies when the proofs of `V ≤ f ⁻¹ᵁ U` and of `V ≤ g ⁻¹ᵁ U` are unrelated. -/
theorem Scheme.Hom.congr_appLE {g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens) (hf hg) :
    f.appLE U V hf = g.appLE U V hg := by
  subst e
  rfl

/-- The inclusions of `U` and `W` into `U ⊔ W` cover `U ⊔ W`. -/
lemma Scheme.opensRange_homOfLE_sup (S : Scheme.{u}) (U W : S.Opens) :
    (S.homOfLE (le_sup_left : U ≤ U ⊔ W)).opensRange ⊔
      (S.homOfLE (le_sup_right : W ≤ U ⊔ W)).opensRange = ⊤ := by
  rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE, ← Scheme.Hom.preimage_sup]
  simpa only [Scheme.Opens.opensRange_ι] using Scheme.Hom.preimage_opensRange (U ⊔ W).ι

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

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry Limits

/-- Pulling back a scheme over an open subscheme `U ⊆ S` pushed forward to `S` along `f : T ⟶ S`
is naturally isomorphic to pulling back along `f ∣_ U` and pushing forward along `(f ⁻¹ᵁ U).ι`. -/
noncomputable def pullbackMapOpenIso {S T : Scheme.{u}} (f : T ⟶ S) (U : S.Opens) :
    Over.map U.ι ⋙ Over.pullback f ≅ Over.pullback (f ∣_ U) ⋙ Over.map (f ⁻¹ᵁ U).ι :=
  NatIso.ofComponents
    (fun A ↦
      let h := (IsPullback.of_hasPullback A.hom (f ∣_ U)).paste_vert
        (isPullback_morphismRestrict f U)
      Over.isoMk h.isoPullback.symm (by
        simp only [Iso.symm_hom, Functor.comp_obj, Over.map_obj_hom, Over.pullback_obj_hom,
          Iso.inv_comp_eq, h.isoPullback_hom_snd]))
    fun {A B} g ↦ by
      ext1
      simp only [Functor.comp_map, Over.comp_left, Over.isoMk_hom_left, Iso.symm_hom]
      rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
      apply pullback.hom_ext
      · simp only [Category.assoc, Over.map_obj_hom, IsPullback.isoPullback_hom_fst,
          IsPullback.isoPullback_hom_fst_assoc, Over.pullback_map_left, Over.map_map_left,
          pullback.lift_fst]
      · simp only [Category.assoc, Over.map_obj_hom, IsPullback.isoPullback_hom_snd,
          Over.map_map_left, Over.pullback_map_left, pullback.lift_snd_assoc, pullback.lift_snd]

/-- For opens `U, W₁ ⊆ S` and `V ⊆ W₁`, canonical isomorphism between `U ⊓ (W₁.ι ''ᵁ V)` and
`V.ι ⁻¹ᵁ (W₁.ι ⁻¹ᵁ U)`. -/
noncomputable def infImageOpenIso {S : Scheme.{u}} (U W₁ : S.Opens) (V : W₁.toScheme.Opens) :
    (U ⊓ (W₁.ι ''ᵁ V)).toScheme ≅ (V.ι ⁻¹ᵁ (W₁.ι ⁻¹ᵁ U)).toScheme :=
  have heq : U ⊓ (W₁.ι ''ᵁ V) = (V.ι ≫ W₁.ι) ''ᵁ ((V.ι ≫ W₁.ι) ⁻¹ᵁ U) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_comp,
      Scheme.Opens.opensRange_ι, inf_comm]
  S.isoOfEq heq ≪≫ ((V.ι ≫ W₁.ι).isoImage ((V.ι ≫ W₁.ι) ⁻¹ᵁ U)).symm ≪≫
    V.toScheme.isoOfEq (Scheme.Hom.comp_preimage V.ι W₁.ι U)

/-- `infImageOpenIso` identifies the restriction of `V.ι ∣_ (W₁.ι ⁻¹ᵁ U) ≫ W₁.ι ∣_ U` with the
inclusion `U ⊓ (W₁.ι ''ᵁ V) ≤ U`. -/
@[reassoc]
theorem infImageOpenIso_hom_comp_left {S : Scheme.{u}} (U W₁ : S.Opens) (V : W₁.toScheme.Opens) :
    (infImageOpenIso U W₁ V).hom ≫ (V.ι ∣_ (W₁.ι ⁻¹ᵁ U)) ≫ (W₁.ι ∣_ U) =
      S.homOfLE (inf_le_left : U ⊓ (W₁.ι ''ᵁ V) ≤ U) := by
  rw [← cancel_mono U.ι]
  simp only [infImageOpenIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, morphismRestrict_ι,
    morphismRestrict_ι_assoc, Scheme.isoOfEq_hom_ι_assoc, Scheme.Hom.isoImage_inv_ι,
    Scheme.isoOfEq_hom_ι, Scheme.homOfLE_ι]

/-- `infImageOpenIso` identifies `(V.ι ∣_ (W₁.ι ⁻¹ᵁ U)) ≫ (W₁.ι ⁻¹ᵁ U).ι` with the inclusion
`U ⊓ (W₁.ι ''ᵁ V) ≤ W₁.ι ''ᵁ V ≤ W₁`. -/
@[reassoc]
theorem infImageOpenIso_hom_comp_right {S : Scheme.{u}} (U W₁ : S.Opens) (V : W₁.toScheme.Opens) :
    (infImageOpenIso U W₁ V).hom ≫ (V.ι ∣_ (W₁.ι ⁻¹ᵁ U)) ≫ (W₁.ι ⁻¹ᵁ U).ι =
      S.homOfLE (inf_le_right : U ⊓ (W₁.ι ''ᵁ V) ≤ W₁.ι ''ᵁ V) ≫
        S.homOfLE (W₁.ι_image_le V) := by
  rw [← cancel_mono W₁.ι]
  simp only [infImageOpenIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    morphismRestrict_ι_assoc, Scheme.isoOfEq_hom_ι_assoc, Scheme.Hom.isoImage_inv_ι,
    Scheme.isoOfEq_hom_ι, Scheme.homOfLE_ι]

end TauCeti.AlgebraicGeometry
