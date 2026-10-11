/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Pullbacks
public import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.SplitEpi

/-!
# Base change of ideal sheaves

This file identifies the closed subscheme of an ideal sheaf pulled back along a fibre-product
projection with the corresponding base change. It also records the resulting preservation of
flatness and fibre rank for the closed subscheme, and the affine-local form of that flatness: over
affine opens `W ⊆ S` and `U ⊆ f⁻¹ W`, the quotient `Γ(X, U) ⧸ I(U)` is flat over `Γ(S, W)`
(`flat_appLE_comp_ofHom_quotient_mk`). Conversely, flatness of that quotient is exactly flatness of
the restricted subscheme morphism (`TauCeti.flat_resLE_subschemeι_iff`).

The ideal sheaf of a closed immersion pulled back along any pullback square is the inverse image
of its ideal sheaf (`AlgebraicGeometry.Scheme.IdealSheafData.ker_eq_comap_of_isPullback`). In
particular, for a section `s` of `f : X ⟶ S` which is a closed immersion, the ideal sheaf of its
base change `T ⟶ X ×_S T` along `g : T ⟶ S` is the inverse image of the ideal sheaf of `s`
(`CategoryTheory.SplitEpi.ker_pullback_section`), and the same holds for the product of the
ideal sheaves of finitely many sections
(`AlgebraicGeometry.Scheme.IdealSheafData.prod_ker_pullback_section`). Taking the ideal sheaf of
a section, or of a finite family of sections, therefore commutes with arbitrary base change.

The closed subscheme of the inverse image `I.comap g` along `g : X' ⟶ X` is the base change of the
closed subscheme of `I` along `g`. Hence, if the closed subscheme of `I` is finite and flat over a
base `S` and `g` is finite and flat of constant rank `n`, the rank over `S` of the closed subscheme
of `I.comap g` is `n` times that of `I`
(`AlgebraicGeometry.Scheme.IdealSheafData.finrank_comap_subschemeι_comp`). For relative effective
Cartier divisors on relative curves, whose degree is this rank, this is the statement that inverse
images under finite flat morphisms of constant degree multiply degrees.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {S T X : Scheme.{u}}

/-- The closed subscheme cut out by the pullback of an ideal sheaf along a fibre-product
projection is the base change of its original closed subscheme. -/
noncomputable def comapPullbackFstIso (I : X.IdealSheafData) (f : X ⟶ S)
    (g : T ⟶ S) :
    (I.comap (pullback.fst f g)).subscheme ≅ pullback (I.subschemeι ≫ f) g :=
  I.comapIso (pullback.fst f g) ≪≫
    pullbackSymmetry (pullback.fst f g) I.subschemeι ≪≫
      pullbackRightPullbackFstIso f g I.subschemeι

/-- The base-change comparison preserves the projection to the original closed subscheme. -/
@[reassoc (attr := simp)]
theorem comapPullbackFstIso_hom_fst (I : X.IdealSheafData) (f : X ⟶ S)
    (g : T ⟶ S) :
    (I.comapPullbackFstIso f g).hom ≫ pullback.fst (I.subschemeι ≫ f) g =
      subschemeMap _ _ (pullback.fst f g) (I.le_map_comap _) := by
  simp [comapPullbackFstIso, Category.assoc]

/-- The inverse base-change comparison preserves the projection to the original closed
subscheme. -/
@[reassoc (attr := simp)]
theorem comapPullbackFstIso_inv_fst (I : X.IdealSheafData) (f : X ⟶ S)
    (g : T ⟶ S) :
    (I.comapPullbackFstIso f g).inv ≫
        subschemeMap _ _ (pullback.fst f g) (I.le_map_comap _) =
      pullback.fst (I.subschemeι ≫ f) g := by
  rw [← comapPullbackFstIso_hom_fst, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp]

/-- The base-change comparison preserves the projection to the new base. -/
@[reassoc (attr := simp)]
theorem comapPullbackFstIso_hom_snd (I : X.IdealSheafData) (f : X ⟶ S)
    (g : T ⟶ S) :
    (I.comapPullbackFstIso f g).hom ≫ pullback.snd (I.subschemeι ≫ f) g =
      (I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g := by
  simp [comapPullbackFstIso, Category.assoc]

/-- Flatness of the closed subscheme over the base is preserved by arbitrary base change. -/
theorem flat_comap_subschemeι_comp_snd (I : X.IdealSheafData) (f : X ⟶ S)
    (g : T ⟶ S) [Flat (I.subschemeι ≫ f)] :
    Flat ((I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g) := by
  rw [← comapPullbackFstIso_hom_snd]
  infer_instance

/-- **Ideal sheaves of closed immersions are stable under base change.** If `i' : P ⟶ X` is the
base change of a closed immersion `i : Z ⟶ Y` along `f : X ⟶ Y`, then the ideal sheaf of `i'` is
the inverse image of the ideal sheaf of `i`. -/
theorem ker_eq_comap_of_isPullback {P Y Z : Scheme.{u}} {i' : P ⟶ X} {g : P ⟶ Z} {f : X ⟶ Y}
    (i : Z ⟶ Y) [IsClosedImmersion i] (h : IsPullback i' g f i) : i'.ker = i.ker.comap f := by
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso, ker_fst_of_isClosedImmersion]

/-- The degree of a finite flat closed subscheme is preserved by base change. More precisely, if
`X' ⟶ X` is the base change of `X ⟶ S` along `S' ⟶ S`, then the closed subscheme cut out by
the inverse-image ideal sheaf has rank at `s'` equal to the original closed subscheme's rank at
its image in `S`.

The hypothesis that the original closed subscheme is finite and flat is exactly what is needed
for the two rank functions. -/
theorem finrank_comap_of_isPullback {X' S' : Scheme.{u}} (I : X.IdealSheafData) (f : X ⟶ S)
    (g : X' ⟶ X) (f' : X' ⟶ S') (h : S' ⟶ S)
    (H : IsPullback g f' f h) [Flat (I.subschemeι ≫ f)] [IsFinite (I.subschemeι ≫ f)]
    (s : S') :
    ((I.comap g).subschemeι ≫ f').finrank s = (I.subschemeι ≫ f).finrank (h s) := by
  let α := subschemeMap (I.comap g) I g (I.le_map_comap g)
  have hI : IsPullback (I.comap g).subschemeι α g I.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ (by simp [α]) (by simp)
  have h' : IsPullback α ((I.comap g).subschemeι ≫ f') (I.subschemeι ≫ f) h := by
    simpa [Category.assoc] using (hI.paste_horiz H.flip).flip
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _ h' s

/-- **The ideal sheaf of a section commutes with base change.** For a section `h.section_` of
`f : X ⟶ S` which is a closed immersion, as it is when `f` is separated, the ideal sheaf of its
base change `(h.pullback g).section_ : T ⟶ X ×_S T` along `g : T ⟶ S` is the inverse image of
the ideal sheaf of `h.section_` along the projection `X ×_S T ⟶ X`. -/
theorem _root_.CategoryTheory.SplitEpi.ker_pullback_section {f : X ⟶ S} (h : SplitEpi f)
    [IsClosedImmersion h.section_] (g : T ⟶ S) :
    (h.pullback g).section_.ker = h.section_.ker.comap (pullback.fst f g) :=
  ker_eq_comap_of_isPullback _ (h.isPullback_pullback_section g)

/-- The ideal sheaves of finitely many sections of `f : X ⟶ S`, each a closed immersion, commute
with base change along `g : T ⟶ S`: the product of the ideal sheaves of the base-changed
sections `T ⟶ X ×_S T` is the inverse image of the product of the original ideal sheaves. For
sections through the smooth locus of a relative curve, this is the statement that the divisor
`s₁ + ⋯ + sₙ` commutes with base change. -/
theorem prod_ker_pullback_section {ι : Type*} (t : Finset ι) {f : X ⟶ S}
    (h : ι → SplitEpi f) [∀ i, IsClosedImmersion (h i).section_] (g : T ⟶ S) :
    ∏ i ∈ t, ((h i).pullback g).section_.ker =
      (∏ i ∈ t, (h i).section_.ker).comap (pullback.fst f g) := by
  simp only [comap_prod, SplitEpi.ker_pullback_section]

/-- If the closed subscheme of `I` is flat over `S`, then over an affine open `W` of `S`, the
quotient `Γ(X, U) ⧸ I(U)` is flat over `Γ(S, W)` for every affine open `U ⊆ f⁻¹ W`. -/
theorem flat_appLE_comp_ofHom_quotient_mk (I : X.IdealSheafData) (f : X ⟶ S)
    [Flat (I.subschemeι ≫ f)] {W : S.Opens} (hW : IsAffineOpen W) (U : X.affineOpens)
    (hUW : U.1 ≤ f ⁻¹ᵁ W) :
    (f.appLE W U hUW ≫ CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))).hom.Flat := by
  have h := (I.subschemeι ≫ f).flat_appLE hW (U.2.preimage I.subschemeι)
    ((Scheme.Hom.preimage_mono _ hUW).trans_eq rfl)
  rw [← Scheme.Hom.appLE_comp_appLE I.subschemeι f W U.1 _ hUW le_rfl,
    ← Scheme.Hom.app_eq_appLE, subschemeι_app, ← Category.assoc] at h
  exact (RingHom.Flat.respectsIso.cancel_right_isIso _ _).mp h

/-- **Inverse images multiply ranks.** Suppose the closed subscheme of `I` is finite and flat over
`S` through `f : X ⟶ S`, and `g : X' ⟶ X` is finite and flat of constant rank `n`. Then the
rank over `S` of the closed subscheme of the inverse image `I.comap g` is `n` times the rank of
the closed subscheme of `I`.

For a relative effective Cartier divisor `D` on `X` over `S` that is finite over `S`, the inverse
image `g⁻¹ D` is again a relative effective Cartier divisor
(`AlgebraicGeometry.Scheme.IdealSheafData.IsRelativeEffectiveCartier.comap_of_flat`), and this
says `deg (g⁻¹ D) = n * deg D`. -/
theorem finrank_comap_subschemeι_comp (I : X.IdealSheafData) (f : X ⟶ S)
    [Flat (I.subschemeι ≫ f)] [IsFinite (I.subschemeι ≫ f)] {X' : Scheme.{u}} (g : X' ⟶ X)
    [Flat g] [IsFinite g] {n : ℕ} (hg : ∀ x, g.finrank x = n) (s : S) :
    ((I.comap g).subschemeι ≫ g ≫ f).finrank s = n * (I.subschemeι ≫ f).finrank s := by
  -- The closed subscheme of `I.comap g` is `X' ×_X I.subscheme`, finite flat of rank `n` over
  -- `I.subscheme`.
  rw [← comapIso_hom_fst, Category.assoc, pullback.condition_assoc,
    Scheme.Hom.finrank_comp_left_of_isIso]
  exact Scheme.Hom.finrank_comp _ _ (fun x ↦ by rw [Scheme.Hom.finrank_pullback_snd, hg]) s

end AlgebraicGeometry.Scheme.IdealSheafData

namespace TauCeti

open AlgebraicGeometry AlgebraicGeometry.Scheme.IdealSheafData

variable {S X : Scheme.{u}}

/-- Flatness of the closed subscheme cut out by `I` over a pair of affine opens is equivalent
to flatness of its quotient algebra of sections over the base. -/
theorem flat_resLE_subschemeι_iff {I : X.IdealSheafData} {f : X ⟶ S}
    {W : S.Opens} (hW : IsAffineOpen W) (U : X.affineOpens)
    (hUW : U.1 ≤ f ⁻¹ᵁ W) :
    Flat ((I.subschemeι ≫ f).resLE W (I.subschemeι ⁻¹ᵁ U.1)
      ((Scheme.Hom.preimage_mono I.subschemeι hUW).trans_eq rfl)) ↔
      (f.appLE W U hUW ≫ CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))).hom.Flat := by
  have : IsAffine W.toScheme := hW
  have : IsAffine (I.subschemeι ⁻¹ᵁ U.1).toScheme := U.2.preimage I.subschemeι
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat),
    RingHom.Flat.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso _ _ _ _),
    ← Scheme.Hom.appLE_comp_appLE I.subschemeι f W U.1 _ hUW le_rfl,
    ← Scheme.Hom.app_eq_appLE, subschemeι_app, ← Category.assoc]
  exact RingHom.Flat.respectsIso.cancel_right_isIso _ _

end TauCeti
