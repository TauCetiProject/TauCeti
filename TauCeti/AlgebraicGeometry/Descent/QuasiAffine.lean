/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import TauCeti.AlgebraicGeometry.AffineScheme.Basic
public import TauCeti.AlgebraicGeometry.Descent.Affine
public import TauCeti.AlgebraicGeometry.Descent.Gluing
public import TauCeti.AlgebraicGeometry.Descent.Open
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.StructureSheaf

/-!
# Effective descent for quasi-affine schemes

Let `p : S' ⟶ S` be a morphism of schemes with `S'` affine, and `D` a descent datum relative to
`p`, in the sense of `TauCeti.DescentDatum p X`, on a scheme `X ⟶ S'`. Since `S'` is affine, the
affinization `X ⟶ Spec Γ(X, ⊤)` lies over `S'`. This file shows that when `p` is flat and `X` is
quasi-compact and quasi-separated, `D` induces a descent datum `D.affinization` on
`Spec Γ(X, ⊤)` for which the affinization is a morphism of descent data
(`TauCeti.DescentDatum.toAffinization`), and that it is the only such descent datum
(`TauCeti.DescentDatum.eq_affinization`).

The construction rests on flat base change for global functions. The map
`S' ×_S X ⟶ S' ×_S Spec Γ(X, ⊤)` between the action spaces is the base change of
`X ⟶ Spec Γ(X, ⊤)` along the flat projection `S' ×_S Spec Γ(X, ⊤) ⟶ Spec Γ(X, ⊤)`, so it induces
an isomorphism on global functions
(`TauCeti.AlgebraicGeometry.isIso_appTop_of_isPullback_of_flat`). Hence the composite of the
action of `D` with the affinization extends uniquely to a morphism
`S' ×_S Spec Γ(X, ⊤) ⟶ Spec Γ(X, ⊤)` (`AlgebraicGeometry.Scheme.Hom.precompEquivOfIsIsoAppTop`),
which is the action of `D.affinization`. Its axioms, equalities of morphisms into affine schemes,
are checked after restriction to the action spaces of `D`, where they are the axioms of `D`.

For quasi-affine `X` the affinization is an open immersion. If moreover `S` is affine and `p` is
surjective, `D.affinization` is effective by descent for affine schemes
(`TauCeti.DescentDatum.exists_isAffine_baseChange_hom_isIso`), so `X` is an open of the base
change of an affine scheme `Y₀` over `S`, stable under its canonical descent datum. Stable opens
of a base change descend
(`TauCeti.DescentDatum.Hom.exists_baseChange_hom_isIso_of_isOpenImmersion`), and therefore so
does `X`, to a quasi-compact open of `Y₀`
(`TauCeti.DescentDatum.exists_isQuasiAffine_baseChange_hom_isIso`).

Gluing these descents along a cover of `X` by stable opens
(`TauCeti.DescentDatum.exists_baseChange_hom_isIso_of_iSup_eq_top`), a descent datum on a scheme
covered by stable quasi-affine opens is effective
(`TauCeti.DescentDatum.exists_baseChange_hom_isIso_of_iSup_eq_top_of_isQuasiAffine`). This is the
local step of descent for schemes with a relatively ample line bundle: if `D` is compatible with an
ample line bundle `L` on `X`, the nonvanishing loci `X_s` of the sections `s` of the powers of `L`
which are invariant under `D` are stable quasi-affine opens of `X`, to which the result applies
once they cover `X`.

## Main definitions

* `TauCeti.DescentDatum.affinization D`: the descent datum on `Spec Γ(X, ⊤)` induced by `D`, with
  action characterized by `TauCeti.DescentDatum.affinizationActionMap_comp_affinization_act`.
* `TauCeti.DescentDatum.toAffinization D`: the affinization `X ⟶ Spec Γ(X, ⊤)`, as a morphism of
  descent data from `D` to `D.affinization`.

## Main results

* `TauCeti.DescentDatum.eq_affinization`: `D.affinization` is the unique descent datum on
  `Spec Γ(X, ⊤)` for which the affinization is a morphism of descent data.
* `TauCeti.DescentDatum.exists_isQuasiAffine_baseChange_hom_isIso`: **effective descent for
  quasi-affine schemes** along a flat surjective morphism of affine schemes.
* `TauCeti.DescentDatum.exists_baseChange_hom_isIso_of_iSup_eq_top_of_isQuasiAffine`: effective
  descent for schemes covered by stable quasi-affine opens, along such a morphism.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII.
* The Stacks Project, Chapter *Descent*, Section *Descent data for schemes over schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.DescentDatum

open TauCeti.AlgebraicGeometry

variable {S S' : Scheme.{u}} {p : S' ⟶ S} {X : Over S'}

section Affinization

variable [IsAffine S']

variable (p X) in
/-- The base change `S' ×_S X ⟶ S' ×_S Spec Γ(X, ⊤)` of the affinization of `X` to the action
spaces. It is an abbreviation, so that it is reducibly the morphism
`pullback.map` through which morphisms of descent data intertwine actions (`Hom.map_act`). -/
noncomputable abbrev affinizationActionMap :
    pullback p (X.hom ≫ p) ⟶ pullback p ((Spec.map X.hom.appTop ≫ S'.isoSpec.inv) ≫ p) :=
  pullback.map _ _ _ _ (𝟙 S') X.left.toSpecΓ (𝟙 S) (by simp) (by simp)

/-- The map between action spaces is the base change of the affinization of `X` along
`S' ×_S Spec Γ(X, ⊤) ⟶ Spec Γ(X, ⊤)`. -/
theorem isPullback_affinizationActionMap :
    IsPullback (pullback.snd p (X.hom ≫ p)) (affinizationActionMap p X) X.left.toSpecΓ
      (pullback.snd p ((Spec.map X.hom.appTop ≫ S'.isoSpec.inv) ≫ p)) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback _ _).flip
  simpa using (IsPullback.of_hasPullback p (X.hom ≫ p)).flip

variable (p X) in
/-- The base change of the affinization of `X` to the iterated action spaces. -/
private noncomputable abbrev affinizationActionMap₂ :
    pullback p (pullback.fst p (X.hom ≫ p) ≫ p) ⟶
      pullback p (pullback.fst p ((Spec.map X.hom.appTop ≫ S'.isoSpec.inv) ≫ p) ≫ p) :=
  pullback.map _ _ _ _ (𝟙 S') (affinizationActionMap p X) (𝟙 S) (by simp) (by simp)

private theorem isPullback_affinizationActionMap₂ :
    IsPullback (pullback.snd p (pullback.fst p (X.hom ≫ p) ≫ p) ≫ pullback.snd p (X.hom ≫ p))
      (affinizationActionMap₂ p X) X.left.toSpecΓ
      (pullback.snd p (pullback.fst p ((Spec.map X.hom.appTop ≫ S'.isoSpec.inv) ≫ p) ≫ p) ≫
        pullback.snd p ((Spec.map X.hom.appTop ≫ S'.isoSpec.inv) ≫ p)) := by
  refine IsPullback.paste_horiz ?_ isPullback_affinizationActionMap
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback _ _).flip
  simpa using (IsPullback.of_hasPullback p (pullback.fst p (X.hom ≫ p) ≫ p)).flip

/-- The affinization of `X`, as a scheme over `S'`, is affine. -/
instance isAffine_affinization_left :
    IsAffine (Over.mk (Spec.map X.hom.appTop ≫ S'.isoSpec.inv)).left :=
  inferInstanceAs (IsAffine (Spec Γ(X.left, ⊤)))

variable [Flat p] [CompactSpace X.left] [QuasiSeparatedSpace X.left]

/-- For `p` flat and `X` quasi-compact and quasi-separated, the base change of the affinization
of `X` to the action spaces induces an isomorphism on global sections. Its target need not be
affine, so this map need not be the absolute affinization of the action space. -/
instance isIso_appTop_affinizationActionMap : IsIso (affinizationActionMap p X).appTop :=
  isIso_appTop_of_isPullback_of_flat isPullback_affinizationActionMap

private instance isIso_appTop_affinizationActionMap₂ : IsIso (affinizationActionMap₂ p X).appTop :=
  isIso_appTop_of_isPullback_of_flat isPullback_affinizationActionMap₂

omit [IsAffine S'] [Flat p] [CompactSpace X.left] [QuasiSeparatedSpace X.left] in
/-- Let `t : X ⟶ Y` be a morphism over `S'` to an affine scheme whose base change to
`S' ×_S (S' ×_S X)` induces an isomorphism on global sections. A morphism `S' ×_S Y ⟶ Y` over the
first projection which extends the composite of the action of `D` with `t` satisfies the cocycle
condition. -/
private theorem act_assoc_of_comp_eq (D : DescentDatum p X) {Y : Over S'} [IsAffine Y.left]
    (t : X ⟶ Y) (ht : IsIso (pullback.map p (pullback.fst p (X.hom ≫ p) ≫ p) p
      (pullback.fst p (Y.hom ≫ p) ≫ p) (𝟙 S')
      (pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') t.left (𝟙 S) (by simp) (by simp))
      (𝟙 S) (by simp) (by simp)).appTop)
    (A : pullback p (Y.hom ≫ p) ⟶ Y.left) (hA : A ≫ Y.hom = pullback.fst p (Y.hom ≫ p))
    (hjA : pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') t.left (𝟙 S) (by simp) (by simp) ≫ A =
      D.act ≫ t.left) :
    pullback.lift (pullback.fst p (pullback.fst p (Y.hom ≫ p) ≫ p))
        (pullback.snd p (pullback.fst p (Y.hom ≫ p) ≫ p) ≫ A)
        (by rw [Category.assoc, reassoc_of% hA]; exact pullback.condition) ≫ A =
      pullback.lift (pullback.fst p (pullback.fst p (Y.hom ≫ p) ≫ p))
        (pullback.snd p (pullback.fst p (Y.hom ≫ p) ≫ p) ≫ pullback.snd p (Y.hom ≫ p))
        (by
          rw [Category.assoc, ← pullback.condition (f := p) (g := Y.hom ≫ p)]
          exact pullback.condition) ≫ A := by
  refine Scheme.Hom.eq_of_comp_eq_of_mono_appTop (pullback.map p (pullback.fst p (X.hom ≫ p) ≫ p) p
      (pullback.fst p (Y.hom ≫ p) ≫ p) (𝟙 S')
      (pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') t.left (𝟙 S) _ _) (𝟙 S) _ _) ?_
  -- Both sides restrict to the two sides of the cocycle condition of `D`, followed by `t`.
  have h₁ : pullback.map p (pullback.fst p (X.hom ≫ p) ≫ p) p (pullback.fst p (Y.hom ≫ p) ≫ p)
      (𝟙 S') (pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') t.left (𝟙 S) (by simp) (by simp))
      (𝟙 S) (by simp) (by simp) ≫ pullback.lift (pullback.fst p (pullback.fst p (Y.hom ≫ p) ≫ p))
        (pullback.snd p (pullback.fst p (Y.hom ≫ p) ≫ p) ≫ A)
        (by rw [Category.assoc, reassoc_of% hA]; exact pullback.condition) =
      pullback.lift (pullback.fst p (pullback.fst p (X.hom ≫ p) ≫ p))
        (pullback.snd p (pullback.fst p (X.hom ≫ p) ≫ p) ≫ D.act)
        (by rw [Category.assoc, D.act_hom_assoc]; exact pullback.condition) ≫
        pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') t.left (𝟙 S) (by simp) (by simp) :=
    pullback.hom_ext (by simp) (by simp [hjA])
  have h₂ : pullback.map p (pullback.fst p (X.hom ≫ p) ≫ p) p (pullback.fst p (Y.hom ≫ p) ≫ p)
      (𝟙 S') (pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') t.left (𝟙 S) (by simp) (by simp))
      (𝟙 S) (by simp) (by simp) ≫ pullback.lift (pullback.fst p (pullback.fst p (Y.hom ≫ p) ≫ p))
        (pullback.snd p (pullback.fst p (Y.hom ≫ p) ≫ p) ≫ pullback.snd p (Y.hom ≫ p))
        (by
          rw [Category.assoc, ← pullback.condition (f := p) (g := Y.hom ≫ p)]
          exact pullback.condition) =
      pullback.lift (pullback.fst p (pullback.fst p (X.hom ≫ p) ≫ p))
        (pullback.snd p (pullback.fst p (X.hom ≫ p) ≫ p) ≫ pullback.snd p (X.hom ≫ p))
        (by
          rw [Category.assoc, ← pullback.condition (f := p) (g := X.hom ≫ p)]
          exact pullback.condition) ≫
        pullback.map p (X.hom ≫ p) p (Y.hom ≫ p) (𝟙 S') t.left (𝟙 S) (by simp) (by simp) :=
    pullback.hom_ext (by simp) (by simp)
  rw [reassoc_of% h₁, reassoc_of% h₂, hjA, reassoc_of% D.act_assoc]

/-- The descent datum on the affinization `Spec Γ(X, ⊤)` induced by a descent datum `D` on `X`:
its action is the unique morphism `S' ×_S Spec Γ(X, ⊤) ⟶ Spec Γ(X, ⊤)` extending the composite of
the action of `D` with the affinization of `X`. -/
noncomputable def affinization (D : DescentDatum p X) :
    DescentDatum p (Over.mk (Spec.map X.hom.appTop ≫ S'.isoSpec.inv)) where
  act := ((affinizationActionMap p X).precompEquivOfIsIsoAppTop _).symm (D.act ≫ X.left.toSpecΓ)
  act_hom := (affinizationActionMap p X).eq_of_comp_eq_of_mono_appTop (by simp)
  lift_act := X.left.toSpecΓ.eq_of_comp_eq_of_mono_appTop (by
    have : X.left.toSpecΓ ≫ pullback.lift (Spec.map X.hom.appTop ≫ S'.isoSpec.inv)
        (𝟙 (Spec Γ(X.left, ⊤))) (by simp) =
        pullback.lift X.hom (𝟙 X.left) (by simp) ≫ affinizationActionMap p X :=
      pullback.hom_ext (by simp) (by simp)
    simp [reassoc_of% this])
  act_assoc := act_assoc_of_comp_eq D (Y := Over.mk (Spec.map X.hom.appTop ≫ S'.isoSpec.inv))
      (Over.homMk X.left.toSpecΓ (by simp)) (isIso_appTop_affinizationActionMap₂ (p := p)) _
      ((affinizationActionMap p X).eq_of_comp_eq_of_mono_appTop (by simp)) (by simp)

/-- The action of the descent datum on the affinization extends the action of `D`. -/
@[reassoc (attr := simp)]
theorem affinizationActionMap_comp_affinization_act (D : DescentDatum p X) :
    affinizationActionMap p X ≫ D.affinization.act = D.act ≫ X.left.toSpecΓ :=
  Scheme.Hom.comp_precompEquivOfIsIsoAppTop_symm_apply _ _ _

/-- The affinization `X ⟶ Spec Γ(X, ⊤)` is a morphism of descent data from `D` to
`D.affinization`. -/
noncomputable def toAffinization (D : DescentDatum p X) : Hom D D.affinization where
  hom := Over.homMk X.left.toSpecΓ (by simp)
  map_act := affinizationActionMap_comp_affinization_act D

@[simp]
theorem toAffinization_hom_left (D : DescentDatum p X) :
    D.toAffinization.hom.left = X.left.toSpecΓ :=
  (rfl)

/-- `D.affinization` is the only descent datum on `Spec Γ(X, ⊤)` for which the affinization
`X ⟶ Spec Γ(X, ⊤)` is a morphism of descent data. -/
theorem eq_affinization (D : DescentDatum p X)
    (E : DescentDatum p (Over.mk (Spec.map X.hom.appTop ≫ S'.isoSpec.inv))) (f : Hom D E)
    (hf : f.hom.left = X.left.toSpecΓ) : E = D.affinization := by
  refine DescentDatum.ext ((affinizationActionMap p X).eq_of_comp_eq_of_mono_appTop ?_)
  rw [affinizationActionMap_comp_affinization_act, ← hf, ← f.map_act]
  congr 1
  exact pullback.hom_ext (by simp) (by simp [hf])

end Affinization

/-- **Effective descent for quasi-affine schemes.** Let `p : S' ⟶ S` be a flat surjective
morphism of affine schemes and `D` a descent datum relative to `p` on a quasi-affine scheme `X`
over `S'`. Then `D` is effective: it is isomorphic to the canonical descent datum on the base
change of a quasi-affine scheme over `S`. -/
theorem exists_isQuasiAffine_baseChange_hom_isIso [IsAffine S] [IsAffine S'] [Flat p]
    [Surjective p] [X.left.IsQuasiAffine] (D : DescentDatum p X) :
    ∃ X₀ : Over S, X₀.left.IsQuasiAffine ∧ ∃ f : Hom (baseChange p X₀) D, IsIso f.hom := by
  -- The descent datum on the affinization is effective, by descent for affine schemes.
  obtain ⟨Y₀, hY₀, g, hg⟩ := D.affinization.exists_isAffine_baseChange_hom_isIso
  -- So `X` is an open of the base change of `Y₀`, stable under the canonical descent datum.
  let f := g.inv.comp D.toAffinization
  have : IsOpenImmersion f.hom.left := by
    rw [Hom.comp_hom, Over.comp_left, toAffinization_hom_left, Hom.inv_hom]
    infer_instance
  obtain ⟨U₀, h, hh, -⟩ := f.exists_baseChange_hom_isIso_of_isOpenImmersion
  refine ⟨_, ?_, h, hh⟩
  -- The open `U₀` is quasi-compact, being the image of `X` under a surjection.
  have : CompactSpace (pullback (U₀.ι ≫ Y₀.hom) p : Scheme.{u}) :=
    (Scheme.homeoOfIso (asIso h.hom.left)).symm.compactSpace
  have : CompactSpace U₀ :=
    (Scheme.Hom.surjective (pullback.fst (U₀.ι ≫ Y₀.hom) p)).compactSpace
      (pullback.fst (U₀.ι ≫ Y₀.hom) p).continuous
  exact Scheme.IsQuasiAffine.of_isImmersion (X := U₀.toScheme) U₀.ι

/-- **Effective descent for schemes covered by stable quasi-affine opens.** Let `p : S' ⟶ S` be
a flat surjective morphism of affine schemes and `D` a descent datum relative to `p` on a scheme
`X` over `S'`. If `X` is covered by opens `U i` which are stable under `D` and quasi-affine, then
`D` is effective: it is isomorphic to the canonical descent datum on the base change of a scheme
over `S`. -/
theorem exists_baseChange_hom_isIso_of_iSup_eq_top_of_isQuasiAffine [IsAffine S] [IsAffine S']
    [Flat p] [Surjective p] (D : DescentDatum p X) {ι : Sort*} (U : ι → X.left.Opens)
    (hU : ⨆ i, U i = ⊤) (hs : ∀ i, D.IsStable (U i)) [∀ i, (U i).toScheme.IsQuasiAffine] :
    ∃ (Y : Over S) (g : Hom (baseChange p Y) D), IsIso g.hom := by
  refine exists_baseChange_hom_isIso_of_iSup_eq_top U hU hs fun i ↦ ?_
  -- The restriction of `D` to `U i` lives on `U i`, regarded as a scheme over `S'`.
  have : (Over.mk ((U i).ι ≫ X.hom)).left.IsQuasiAffine :=
    inferInstanceAs (U i).toScheme.IsQuasiAffine
  obtain ⟨Y, -, g, hg⟩ := (D.restrict (U i) (hs i)).exists_isQuasiAffine_baseChange_hom_isIso
  exact ⟨Y, g, hg⟩

end TauCeti.DescentDatum
