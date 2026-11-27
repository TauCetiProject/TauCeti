/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import TauCeti.AlgebraicGeometry.Morphisms.FormallySmooth.Lift.Torsor
import Mathlib.AlgebraicGeometry.Gluing
import TauCeti.AlgebraicGeometry.Restrict

/-!
# The sheaf of lifts along a first-order thickening

Let `f : X ⟶ S` be a morphism of schemes, `i : T ⟶ T'` a morphism with `T` and `T'` over `S`
through `a : T ⟶ X` and `h : T' ⟶ S`. Over an open `U` of `T'`, the lifts of `a` along `i` are the
morphisms `U ⟶ X` over `S` restricting to `a` on `i⁻¹(U)`
(`TauCeti.AlgebraicGeometry.ThickeningLift (i ∣_ U) ((i ⁻¹ᵁ U).ι ≫ a) f (U.ι ≫ h)`). Restricting
lifts to smaller opens makes them a presheaf of sets on `T'`
(`TauCeti.AlgebraicGeometry.liftPresheaf i a f h`), and since morphisms of schemes glue along open
covers it is a sheaf (`TauCeti.AlgebraicGeometry.isSheaf_liftPresheaf`,
`TauCeti.AlgebraicGeometry.liftSheaf`). For `f` smooth and `i` a
first-order thickening, the sheaf of lifts has a section near every point of `T'`
(`TauCeti.AlgebraicGeometry.exists_thickeningLift_restrict`, whose lifts are exactly the
sections `(liftPresheaf i a f h).obj (op U)`), and by
`TauCeti.AlgebraicGeometry.ThickeningLift.instAddTorsor` its nonempty sets of sections are torsors
under derivations. This is the sheaf of lifts of Stacks, Lemma 37.9.5 (04FJ).

## Main definitions

* `TauCeti.AlgebraicGeometry.ThickeningLift.restrictLE`: restricting a lift over `U` to `V ≤ U`.
* `TauCeti.AlgebraicGeometry.liftPresheaf i a f h`: the presheaf of lifts on `T'`.
* `TauCeti.AlgebraicGeometry.liftSheaf i a f h`: the sheaf of lifts on `T'`.

## Main results

* `TauCeti.AlgebraicGeometry.isSheaf_liftPresheaf`: the presheaf of lifts is a sheaf.

## References

* [Stacks Project, Lemma 37.9.5](https://stacks.math.columbia.edu/tag/04FJ): the sheaf of lifts
  is a torsor.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

variable {X S T T' : Scheme.{u}} {i : T ⟶ T'} {a : T ⟶ X} {f : X ⟶ S} {h : T' ⟶ S}

namespace ThickeningLift

/-- Restricting a lift over an open `U` of `T'` to an open `V ≤ U`. -/
noncomputable def restrictLE {U V : T'.Opens} (hVU : V ≤ U)
    (b : ThickeningLift (i ∣_ U) ((i ⁻¹ᵁ U).ι ≫ a) f (U.ι ≫ h)) :
    ThickeningLift (i ∣_ V) ((i ⁻¹ᵁ V).ι ≫ a) f (V.ι ≫ h) where
  hom := T'.homOfLE hVU ≫ b.hom
  comp_hom := by
    rw [morphismRestrict_homOfLE_assoc i V U hVU, b.comp_hom, Scheme.homOfLE_ι_assoc]
  hom_comp := by rw [Category.assoc, b.hom_comp, Scheme.homOfLE_ι_assoc]

/-- The restriction of a lift is its composite with the inclusion of opens. -/
@[simp]
theorem restrictLE_hom {U V : T'.Opens} (hVU : V ≤ U)
    (b : ThickeningLift (i ∣_ U) ((i ⁻¹ᵁ U).ι ≫ a) f (U.ι ≫ h)) :
    (restrictLE hVU b).hom = T'.homOfLE hVU ≫ b.hom := by
  rw [restrictLE]

/-- Restricting a lift to the same open does nothing. -/
@[simp]
theorem restrictLE_rfl {U : T'.Opens}
    (b : ThickeningLift (i ∣_ U) ((i ⁻¹ᵁ U).ι ≫ a) f (U.ι ≫ h)) :
    restrictLE le_rfl b = b := by
  ext1
  simp

/-- Restricting a lift twice is restricting it once. -/
@[simp]
theorem restrictLE_restrictLE {U V W : T'.Opens} (hVU : V ≤ U) (hWV : W ≤ V)
    (b : ThickeningLift (i ∣_ U) ((i ⁻¹ᵁ U).ι ≫ a) f (U.ι ≫ h)) :
    restrictLE hWV (restrictLE hVU b) = restrictLE (hWV.trans hVU) b := by
  ext1
  simp

/-- Restricting a global lift to `U` and then to `V ≤ U` is restricting it to `V`. -/
@[simp]
theorem restrictLE_restrict {U V : T'.Opens} (hVU : V ≤ U) (b : ThickeningLift i a f h) :
    restrictLE hVU (b.restrict U) = b.restrict V := by
  ext1
  simp

end ThickeningLift

variable (i a f h) in
/-- The **presheaf of lifts** on `T'`: over an open `U`, the lifts of `a` restricted to `i⁻¹(U)`
along `i ∣_ U`, over `h` restricted to `U`, with restriction of lifts to smaller opens. -/
noncomputable abbrev liftPresheaf : TopCat.Presheaf (Type u) T'.carrier where
  obj U := ThickeningLift (i ∣_ U.unop) ((i ⁻¹ᵁ U.unop).ι ≫ a) f (Scheme.Opens.ι U.unop ≫ h)
  map g := ↾ThickeningLift.restrictLE g.unop.le
  map_id U := by
    ext b
    exact congrArg ThickeningLift.hom (ThickeningLift.restrictLE_rfl b)
  map_comp g g' := by
    ext b
    exact congrArg ThickeningLift.hom
      (ThickeningLift.restrictLE_restrictLE g.unop.le g'.unop.le b).symm

/-- The restriction maps of the presheaf of lifts precompose with the inclusion of opens. -/
theorem liftPresheaf_map_hom {U V : T'.Opensᵒᵖ} (g : U ⟶ V) (b : (liftPresheaf i a f h).obj U) :
    ((liftPresheaf i a f h).map g b).hom = T'.homOfLE g.unop.le ≫ b.hom :=
  ThickeningLift.restrictLE_hom _ b

variable (i a f h) in
/-- **The presheaf of lifts is a sheaf**: lifts over the members of an open cover that agree on
the overlaps glue uniquely, since morphisms of schemes glue along open covers. -/
theorem isSheaf_liftPresheaf : (liftPresheaf i a f h).IsSheaf := by
  refine TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types _ fun ι U sf hsf ↦ ?_
  let 𝒰 := Scheme.Opens.iSupOpenCover U
  have compat : ∀ k l, pullback.fst (𝒰.f k) (𝒰.f l) ≫ (sf k).hom =
      pullback.snd (𝒰.f k) (𝒰.f l) ≫ (sf l).hom := fun (k l : ι) ↦ by
    have hP := isPullback_opens_inf_le (le_iSup U k) (le_iSup U l)
    have e := congrArg ThickeningLift.hom (hsf k l)
    rw [liftPresheaf_map_hom, liftPresheaf_map_hom] at e
    dsimp only [𝒰, Scheme.Opens.iSupOpenCover]
    simp only [← hP.isoPullback_inv_fst, ← hP.isoPullback_inv_snd, Category.assoc, e]
  -- Gluing the lifts on the members of the cover gives a lift on `⨆ U`.
  let g := 𝒰.glueMorphisms (fun k ↦ (sf k).hom) compat
  have hg : ∀ k, T'.homOfLE (le_iSup U k) ≫ g = (sf k).hom := 𝒰.ι_glueMorphisms _ compat
  have comp_hom : i ∣_ (⨆ k, U k) ≫ g = (i ⁻¹ᵁ ⨆ k, U k).ι ≫ a := by
    have H (k : ι) : pullback.fst (i ∣_ ⨆ k, U k) (T'.homOfLE (le_iSup U k)) ≫ i ∣_ (⨆ k, U k) ≫ g =
        pullback.fst (i ∣_ ⨆ k, U k) (T'.homOfLE (le_iSup U k)) ≫ (i ⁻¹ᵁ ⨆ k, U k).ι ≫ a := by
      -- `i⁻¹(U k)` is the pullback of `i ∣_ ⨆ U` along `U k ⟶ ⨆ U`.
      have hP := i.isPullback_morphismRestrict_homOfLE (le_iSup U k)
      simp only [← hP.isoPullback_inv_fst, Category.assoc, reassoc_of% hP.w, hg, (sf k).comp_hom,
        Scheme.homOfLE_ι_assoc]
    -- The cover maps of `𝒰.pullback₁ (i ∣_ ⨆ U)` are the projections `pullback.fst` of `H` by
    -- definition. The `simps` lemmas of `pullback₁` cannot rewrite them, since the index type of
    -- the pulled-back cover is not reducibly `ι`.
    exact Scheme.Cover.hom_ext (𝒰.pullback₁ (i ∣_ (⨆ k, U k))) _ _ H
  have hom_comp : g ≫ f = Scheme.Opens.ι (⨆ k, U k) ≫ h :=
    𝒰.hom_ext _ _ fun (k : ι) ↦ by
      dsimp only [𝒰, Scheme.Opens.iSupOpenCover]
      rw [reassoc_of% hg, (sf k).hom_comp, Scheme.homOfLE_ι_assoc]
  refine ⟨⟨g, comp_hom, hom_comp⟩, fun k ↦ ThickeningLift.ext (hg k), fun s hs ↦ ?_⟩
  refine ThickeningLift.ext (𝒰.hom_ext _ _ fun (k : ι) ↦ ?_)
  dsimp only [𝒰, Scheme.Opens.iSupOpenCover]
  rw [hg]
  exact congrArg ThickeningLift.hom (hs k)

variable (i a f h) in
/-- The **sheaf of lifts** on `T'`: the presheaf of lifts `liftPresheaf i a f h`, which is a sheaf
by `isSheaf_liftPresheaf`. -/
noncomputable def liftSheaf : TopCat.Sheaf (Type u) T'.carrier :=
  ⟨liftPresheaf i a f h, isSheaf_liftPresheaf i a f h⟩

/-- The underlying presheaf of the sheaf of lifts is the presheaf of lifts. -/
@[simp]
theorem liftSheaf_obj : (liftSheaf i a f h).obj = liftPresheaf i a f h := by
  rw [liftSheaf]

end TauCeti.AlgebraicGeometry
