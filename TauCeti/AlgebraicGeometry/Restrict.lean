/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Restricting local properties of scheme morphisms

For a morphism of schemes `f : X ⟶ Y` and an open `U` of `Y`, Mathlib's `f ∣_ U` is the
restriction `f ⁻¹ᵁ U ⟶ U`. A property local on the target passes from this restriction to
every smaller open. An open immersion restricts to an isomorphism over opens in its range.
Restricting the source to an open equal to the full preimage gives a pullback square, which
transfers properties stable under base change to `Scheme.Hom.resLE`. Dually, in a pullback square
of the inclusion of an open `U` along `f`, pullback of functions along the top morphism identifies
the functions on `f ⁻¹ᵁ U` with the global functions of the base change.

## Main results

* `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict_of_le`: a property local on the target
  passes from `f ∣_ U` to `f ∣_ V` when `V ≤ U`.
* `AlgebraicGeometry.Scheme.Hom.isIso_morphismRestrict_of_le_opensRange`: an open immersion
  restricts to an isomorphism over every open contained in its range.
* `AlgebraicGeometry.Scheme.Hom.isPullback_resLE_of_eq`: the restriction of `f` to an open `U`
  of the target and an open `V` of the source equal to `f ⁻¹ᵁ U` is a pullback of `f`.
* `AlgebraicGeometry.Scheme.Hom.isIso_morphismRestrict_of_isIso_comp`: if an open immersion `ι`
  contains `f ⁻¹ᵁ V` in its range and `(ι ≫ f) ∣_ V` is an isomorphism, so is `f ∣_ V`.
* `AlgebraicGeometry.Scheme.Hom.congr_appLE`: equal morphisms induce the same maps
  `Γ(Y, U) ⟶ Γ(X, V)`, whatever the proofs of `V ≤ f ⁻¹ᵁ U`.
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

/-- An open immersion `f` restricts to an isomorphism over every open `V` contained in its
range. -/
theorem Scheme.Hom.isIso_morphismRestrict_of_le_opensRange [IsOpenImmersion f] {V : Y.Opens}
    (hV : V ≤ f.opensRange) : IsIso (f ∣_ V) := by
  refine (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, ⟨fun y ↦ ?_⟩⟩
  obtain ⟨z, hz⟩ := hV y.2
  exact ⟨⟨z, (Scheme.Hom.mem_preimage _).mpr (hz ▸ y.2)⟩,
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

/-- Equal morphisms induce the same maps on sections `Γ(Y, U) ⟶ Γ(X, V)`. Unlike rewriting along
`f = g`, this applies when the proofs of `V ≤ f ⁻¹ᵁ U` and of `V ≤ g ⁻¹ᵁ U` are unrelated. -/
theorem Scheme.Hom.congr_appLE {g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens) (hf hg) :
    f.appLE U V hf = g.appLE U V hg := by
  subst e
  rfl

end AlgebraicGeometry

namespace CategoryTheory

open AlgebraicGeometry

variable {Z Y T : Scheme.{u}} {U : T.Opens} {j : Z ⟶ Y} {g : Z ⟶ U} {f : Y ⟶ T}

/-- In a commutative square over the inclusion of an open `U`, the top morphism `j` maps all of
its source into `f ⁻¹ᵁ U`. -/
theorem CommSq.top_le_preimage_preimage (h : CommSq j g f U.ι) : ⊤ ≤ j ⁻¹ᵁ f ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, h.w, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]
  rfl

/-- In a commutative square over the inclusion of an open `U`, pulling a function on `U` back to
the source along `g` is pulling it back along `f` to `f ⁻¹ᵁ U` and then along `j`. -/
theorem CommSq.appLE_app_topIso_hom (h : CommSq j g f U.ι) (r : Γ(U, ⊤)) :
    j.appLE (f ⁻¹ᵁ U) ⊤ h.top_le_preimage_preimage (f.app U (U.topIso.hom r)) = g.appTop r := by
  have hι : U.topIso.hom ≫ U.ι.appLE U ⊤ U.ι_preimage_self.ge = 𝟙 _ := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_hom]
    exact (T.presheaf.map_comp _ _).symm.trans (T.presheaf.map_id _)
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.congr_appLE _ h.w _ _ _
      (by rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]; exact le_rfl),
    ← Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ U.ι_preimage_self.ge (Scheme.Hom.preimage_top _).ge,
    CommRingCat.comp_apply,
    show U.ι.appLE U ⊤ U.ι_preimage_self.ge (U.topIso.hom r) = r from congr($hι r)]
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
  have : IsIso (e.hom.appLE ⊤ ⊤ le_top) := by
    rw [show e.hom.appLE ⊤ ⊤ le_top = e.hom.appTop from (Scheme.Hom.app_eq_appLE _).symm]
    exact inferInstanceAs (IsIso (e.hom.app ⊤))
  infer_instance

end CategoryTheory
