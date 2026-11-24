/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Category

/-!
# Base change for the linear Temperley–Lieb category

Given a ring homomorphism `φ : R →+* S` between commutative rings sending `δ : R` to `δ' : S`,
this file constructs the additive base-change functor
`TauCeti.TLCat.mapRingHom φ hδ : TLCat R δ ⥤ TLCat S δ'` acting by `φ` on planar-matching
coefficients, together with its compatibility with `diagBasis`, `linearize`, `cup`, and `cap` and
its functoriality natural isomorphisms `TauCeti.TLCat.mapRingHomIdIso` and
`TauCeti.TLCat.mapRingHomCompIso`.

## Main definitions

* `TauCeti.TLCat.mapRingHom`: the additive base-change functor `TLCat R δ ⥤ TLCat S δ'` along a
  ring homomorphism `φ : R →+* S` with `φ δ = δ'`.
* `TauCeti.TLCat.mapRingHomIdIso`: natural isomorphism from base change along `RingHom.id R` to
  the identity functor.
* `TauCeti.TLCat.mapRingHomCompIso`: natural isomorphism from composing two base-change functors
  to base change along the composite ring homomorphism.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845, §2.
-/

public section

open CategoryTheory

namespace TauCeti.TLCat

universe u v

variable {R : Type u} [CommRing R] {δ : R}
variable {S : Type v} [CommRing S] {δ' : S}

/-- **Base change of the Temperley–Lieb category** along a ring homomorphism `φ : R →+* S` sending
`δ` to `δ'`: preserves objects and applies `φ` to every planar-matching coefficient.

Marked `@[expose, implicit_reducible]` so `((mapRingHom φ hδ).obj X)` reduces in dependent morphism
types `(mapRingHom φ hδ).obj X ⟶ (mapRingHom φ hδ).obj Y` without `eqToHom`. -/
@[expose, implicit_reducible]
noncomputable def mapRingHom (φ : R →+* S) (hδ : φ δ = δ') : TLCat R δ ⥤ TLCat S δ' where
  obj X := of X.as
  map f := Hom.ofCoeff (Finsupp.mapRange φ φ.map_zero f.coeff)
  map_id X := hom_ext <| by simp
  map_comp f g := hom_ext <| by
    simp only [coeff_comp]
    induction f.coeff using Finsupp.induction_linear with
    | zero => simp
    | add u₁ u₂ ih₁ ih₂ => simp [Finsupp.mapRange_add, ih₁, ih₂]
    | single x a =>
      induction g.coeff using Finsupp.induction_linear with
      | zero => simp
      | add v₁ v₂ ih₁ ih₂ => simp [Finsupp.mapRange_add, ih₁, ih₂]
      | single y b =>
        simp [compCoeff_single_single, hδ]

@[simp]
theorem mapRingHom_obj_as (φ : R →+* S) (hδ : φ δ = δ') (X : TLCat R δ) :
    ((mapRingHom φ hδ).obj X).as = X.as := (rfl)

@[simp]
theorem mapRingHom_obj_of (φ : R →+* S) (hδ : φ δ = δ') (n : ℕ) :
    (mapRingHom φ hδ).obj (of n) = of n := (rfl)

@[simp]
theorem coeff_mapRingHom_map (φ : R →+* S) (hδ : φ δ = δ') {X Y : TLCat R δ} (f : X ⟶ Y) :
    ((mapRingHom φ hδ).map f).coeff = Finsupp.mapRange φ φ.map_zero f.coeff := (rfl)

instance (φ : R →+* S) (hδ : φ δ = δ') : (mapRingHom φ hδ).Additive where
  map_add {_ _} f g := hom_ext (Finsupp.ext fun x => by simp)

@[simp]
theorem mapRingHom_map_diagBasis (φ : R →+* S) (hδ : φ δ = δ')
    {X Y : TLCat R δ} (x : PlanarMatching (X.as + Y.as)) :
    (mapRingHom φ hδ).map (diagBasis X Y x) =
      diagBasis ((mapRingHom φ hδ).obj X) ((mapRingHom φ hδ).obj Y) x :=
  hom_ext <| by simp

@[simp]
theorem mapRingHom_map_smul (φ : R →+* S) (hδ : φ δ = δ') {X Y : TLCat R δ}
    (r : R) (f : X ⟶ Y) :
    (mapRingHom φ hδ).map (r • f) = φ r • (mapRingHom φ hδ).map f :=
  hom_ext (Finsupp.ext fun x => by simp)

@[simp]
theorem mapRingHom_map_linearize_map (φ : R →+* S) (hδ : φ δ = δ')
    {X Y : TLDiagCat} (f : X ⟶ Y) :
    (mapRingHom φ hδ).map ((linearize R δ).map f) = (linearize S δ').map f :=
  hom_ext <| by
    simp [linearize_map, coeff_diagBasis (X := of X.as) (Y := of Y.as), hδ, Finsupp.smul_single]

@[simp]
theorem mapRingHom_map_cup (φ : R →+* S) (hδ : φ δ = δ') :
    (mapRingHom φ hδ).map (cup : (of 0 : TLCat R δ) ⟶ of 2) = cup := by
  rw [cup_eq_diagBasis, cup_eq_diagBasis]
  exact mapRingHom_map_diagBasis φ hδ (X := of 0) (Y := of 2) TLDiagram.cup.matching

@[simp]
theorem mapRingHom_map_cap (φ : R →+* S) (hδ : φ δ = δ') :
    (mapRingHom φ hδ).map (cap : (of 2 : TLCat R δ) ⟶ of 0) = cap := by
  rw [cap_eq_diagBasis, cap_eq_diagBasis]
  exact mapRingHom_map_diagBasis φ hδ (X := of 2) (Y := of 0) TLDiagram.cap.matching

/-- Base change along `RingHom.id R` is naturally isomorphic to the identity functor. -/
noncomputable def mapRingHomIdIso :
    mapRingHom (RingHom.id R) (rfl : RingHom.id R δ = δ) ≅ 𝟭 (TLCat R δ) :=
  NatIso.ofComponents (fun X => Iso.refl X) fun {X Y} f => by
    cases X; cases Y
    dsimp only [Functor.id_obj, Functor.id_map, Iso.refl_hom, mapRingHom]
    rw [Category.comp_id, Category.id_comp]
    exact hom_ext (Finsupp.ext fun _ => by simp)

@[simp]
theorem mapRingHomIdIso_hom_app (X : TLCat R δ) :
    (mapRingHomIdIso (R := R) (δ := δ)).hom.app X = 𝟙 X := (rfl)

@[simp]
theorem mapRingHomIdIso_inv_app (X : TLCat R δ) :
    (mapRingHomIdIso (R := R) (δ := δ)).inv.app X = 𝟙 X := (rfl)

/-- Composing two base-change functors is naturally isomorphic to base change along the composite
ring homomorphism. -/
noncomputable def mapRingHomCompIso {T : Type*} [CommRing T] {δ'' : T}
    (φ : R →+* S) (hδ : φ δ = δ') (ψ : S →+* T) (hδ' : ψ δ' = δ'') :
    mapRingHom φ hδ ⋙ mapRingHom ψ hδ' ≅
      mapRingHom (ψ.comp φ) (by rw [RingHom.comp_apply, hδ, hδ']) :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun f => by
    dsimp only [Functor.comp_obj, Functor.comp_map, Iso.refl_hom]
    rw [Category.comp_id, Category.id_comp]
    exact hom_ext (Finsupp.ext fun _ => by simp)

@[simp]
theorem mapRingHomCompIso_hom_app {T : Type*} [CommRing T] {δ'' : T}
    (φ : R →+* S) (hδ : φ δ = δ') (ψ : S →+* T) (hδ' : ψ δ' = δ'') (X : TLCat R δ) :
    (mapRingHomCompIso φ hδ ψ hδ').hom.app X = 𝟙 (of X.as) := (rfl)

@[simp]
theorem mapRingHomCompIso_inv_app {T : Type*} [CommRing T] {δ'' : T}
    (φ : R →+* S) (hδ : φ δ = δ') (ψ : S →+* T) (hδ' : ψ δ' = δ'') (X : TLCat R δ) :
    (mapRingHomCompIso φ hδ ψ hδ').inv.app X = 𝟙 (of X.as) := (rfl)

end TauCeti.TLCat
