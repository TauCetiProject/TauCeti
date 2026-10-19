/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ProjModel
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.VariableChange.Basic
import TauCeti.AlgebraicGeometry.Scheme.Opens

/-!
# Pointed isomorphisms of projective Weierstrass models over a scheme

Let `S` be a scheme and `W` a Weierstrass curve over the ring of global sections `Γ(S, ⊤)`. A
projective Weierstrass model of `W` over `S` is a scheme `X` over `S` together with a morphism
`f : X ⟶ projModel W` which makes `X` the base change of `projModel W` along
`S.toSpecΓ : S ⟶ Spec Γ(S, ⊤)`; its zero section is the section `z` of `X ⟶ S` lying over the zero
section of `projModel W`. No hypothesis is made on `S`: it need not be affine, quasi-compact or
reduced.

This file shows that, over such a base, every isomorphism of projective Weierstrass models over `S`
which carries the zero section to the zero section is induced by a unique change of variables with
coefficients in `Γ(S, ⊤)`
(`WeierstrassCurve.existsUnique_hom_comp_eq_comp_projModelVariableChangeIso_hom`). Over an affine
base this is
`WeierstrassCurve.existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom`, which this file
extends to an arbitrary base.

The proof restricts the isomorphism `e` to the projective models over the affine opens `U` of `S`:
over `U`, the model of `W` is the projective model of the restriction of `W` to `Γ(S, U)`, and the
affine classification provides a unique change of variables `C_U` over `Γ(S, U)` inducing `e`. By
uniqueness, these changes of variables are compatible with restriction to smaller affine opens, so
their four coefficients `u`, `r`, `s`, `t`, and the inverse of `u`, glue to global sections
(`AlgebraicGeometry.Scheme.existsUnique_gluing_affineOpens`). The resulting change of variables
induces `e`, as both agree over every affine open.

## Main results

* `WeierstrassCurve.existsUnique_hom_comp_eq_comp_projModelVariableChangeIso_hom`: a pointed
  isomorphism over `S` of projective Weierstrass models of `W` and `W'` over `S` is induced by a
  unique change of variables `C` over `Γ(S, ⊤)` with `C • W' = W`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.2.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite

universe u

namespace WeierstrassCurve

/-! ### Changes of variables and base change -/

-- A change of variables inducing a morphism `j ≫ m = C ≫ j'` out of projective models over `A`
-- induces the corresponding morphism out of the projective models over `B`, for `ψ : A →+* B`.
private theorem map_of_eq_comp {A B : Type u} [CommRing A] [CommRing B] {V V' : WeierstrassCurve A}
    {Y Y' : Scheme.{u}} {j : V.projModel ⟶ Y} {j' : V'.projModel ⟶ Y'} {m : Y ⟶ Y'}
    {C : VariableChange A} (h : C • V' = V)
    (hC : j ≫ m = eqToHom (congrArg projModel h.symm) ≫ (V'.projModelVariableChangeIso C).hom ≫ j')
    (ψ : A →+* B) :
    ∃ h' : C.map ψ • V'.map ψ = V.map ψ, (V.projModelBaseChange ψ ≫ j) ≫ m =
      eqToHom (congrArg projModel h'.symm) ≫
        ((V'.map ψ).projModelVariableChangeIso (C.map ψ)).hom ≫ V'.projModelBaseChange ψ ≫ j' := by
  subst h
  refine ⟨map_variableChange V' C ψ, ?_⟩
  rw [Category.assoc, hC, eqToHom_refl, Category.id_comp,
    projModelVariableChangeIso_hom_projModelBaseChange_assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]

-- Transport of an equation `j ≫ m = C ≫ j'` along equalities of Weierstrass curves.
private theorem exists_eq_comp_of_eq {A : Type u} [CommRing A] {V₁ V₂ V₁' V₂' : WeierstrassCurve A}
    {Y Y' : Scheme.{u}} {j₁ : V₁.projModel ⟶ Y} {j₂ : V₂.projModel ⟶ Y} {j₁' : V₁'.projModel ⟶ Y'}
    {j₂' : V₂'.projModel ⟶ Y'} {m : Y ⟶ Y'} {C : VariableChange A} (hV : V₁ = V₂)
    (hV' : V₁' = V₂') (hj : eqToHom (congrArg projModel hV.symm) ≫ j₁ = j₂)
    (hj' : eqToHom (congrArg projModel hV'.symm) ≫ j₁' = j₂')
    (H : ∃ h : C • V₁' = V₁, j₁ ≫ m =
      eqToHom (congrArg projModel h.symm) ≫ (V₁'.projModelVariableChangeIso C).hom ≫ j₁') :
    ∃ h : C • V₂' = V₂, j₂ ≫ m =
      eqToHom (congrArg projModel h.symm) ≫ (V₂'.projModelVariableChangeIso C).hom ≫ j₂' := by
  subst hV hV' hj hj'
  simpa using H

/-! ### The projective models over the points `Spec A ⟶ S` -/

section Local

variable {S X : Scheme.{u}} {W : WeierstrassCurve Γ(S, ⊤)} {p : X ⟶ S} {f : X ⟶ W.projModel}
  (hX : IsPullback f p W.projModelOver S.toSpecΓ) {A : Type u} [CommRing A]
  {φ : Γ(S, ⊤) →+* A} {g : Spec (.of A) ⟶ S} (hg : g ≫ S.toSpecΓ = Spec.map (CommRingCat.ofHom φ))

-- Over a point `g : Spec A ⟶ S`, lying over `Spec φ`, the projective model of `W.map φ` is the
-- base change of `X` along `g`, through this morphism.
private noncomputable def localι : (W.map φ).projModel ⟶ X :=
  hX.lift (W.projModelBaseChange φ) ((W.map φ).projModelOver ≫ g) (by
    rw [Category.assoc, hg, projModelBaseChange_projModelOver])

@[reassoc (attr := simp)]
private theorem localι_fst : localι hX hg ≫ f = W.projModelBaseChange φ :=
  hX.lift_fst _ _ _

@[reassoc (attr := simp)]
private theorem localι_snd : localι hX hg ≫ p = (W.map φ).projModelOver ≫ g :=
  hX.lift_snd _ _ _

private theorem isPullback_localι : IsPullback (localι hX hg) (W.map φ).projModelOver p g :=
  .of_right (by simpa [hg] using W.isPullback_projModelBaseChange φ) (localι_snd hX hg) hX

@[reassoc]
private theorem projModelZero_localι {z : S ⟶ X} (hzp : z ≫ p = 𝟙 S)
    (hzf : z ≫ f = S.toSpecΓ ≫ W.projModelZero) :
    (W.map φ).projModelZero ≫ localι hX hg = g ≫ z :=
  hX.hom_ext (by simp [projModelZero_projModelBaseChange, reassoc_of% hg, hzf]) (by simp [hzp])

-- The morphism over `Spec B ⟶ Spec A ⟶ S` factors through the morphism over `Spec A ⟶ S`.
private theorem projModelBaseChange_localι {B : Type u} [CommRing B] (ψ : A →+* B)
    (hg' : (Spec.map (CommRingCat.ofHom ψ) ≫ g) ≫ S.toSpecΓ =
      Spec.map (CommRingCat.ofHom (ψ.comp φ))) :
    eqToHom (congrArg projModel (W.map_map φ ψ).symm) ≫ (W.map φ).projModelBaseChange ψ ≫
      localι hX hg = localι hX hg' :=
  hX.hom_ext (by simp [projModelBaseChange_comp])
    (by simp [eqToHom_projModelOver_assoc (W.map_map φ ψ).symm])

-- The morphisms over equal points `Spec A ⟶ S` agree, through the identification of the models.
private theorem eqToHom_localι {φ₁ φ₂ : Γ(S, ⊤) →+* A} (hφ : φ₁ = φ₂) {g₁ g₂ : Spec (.of A) ⟶ S}
    (hg : g₁ = g₂) (h₁ : g₁ ≫ S.toSpecΓ = Spec.map (CommRingCat.ofHom φ₁))
    (h₂ : g₂ ≫ S.toSpecΓ = Spec.map (CommRingCat.ofHom φ₂)) :
    eqToHom (congrArg (fun φ ↦ (W.map φ).projModel) hφ.symm) ≫ localι hX h₁ = localι hX h₂ := by
  subst hφ hg
  simp

variable {X' : Scheme.{u}} {W' : WeierstrassCurve Γ(S, ⊤)} {p' : X' ⟶ S} {f' : X' ⟶ W'.projModel}
  (hX' : IsPullback f' p' W'.projModelOver S.toSpecΓ)

-- Over `g`, a morphism `m : X ⟶ X'` is induced by at most one change of variables.
private theorem local_unique (m : X ⟶ X') {C C' : VariableChange A} (h : C • W'.map φ = W.map φ)
    (h' : C' • W'.map φ = W.map φ)
    (hC : localι hX hg ≫ m = eqToHom (congrArg projModel h.symm) ≫
      ((W'.map φ).projModelVariableChangeIso C).hom ≫ localι hX' hg)
    (hC' : localι hX hg ≫ m = eqToHom (congrArg projModel h'.symm) ≫
      ((W'.map φ).projModelVariableChangeIso C').hom ≫ localι hX' hg) : C = C' :=
  (eqToHom_comp_projModelVariableChangeIso_hom_inj h h').mp <|
    (isPullback_localι hX' hg).hom_ext (by simp only [Category.assoc, ← hC, ← hC'])
      (by simp only [Category.assoc, projModelVariableChangeIso_hom_projModelOver]
          rw [eqToHom_projModelOver h.symm, eqToHom_projModelOver h'.symm])

-- Over `g`, a pointed isomorphism `e : X ≅ X'` over `S` is induced by a change of variables.
private theorem local_exists (e : X ≅ X') (he : e.hom ≫ p' = p) {z : S ⟶ X} (hzp : z ≫ p = 𝟙 S)
    (hzf : z ≫ f = S.toSpecΓ ≫ W.projModelZero)
    (hzf' : z ≫ e.hom ≫ f' = S.toSpecΓ ≫ W'.projModelZero) :
    ∃ C : VariableChange A, ∃ h : C • W'.map φ = W.map φ,
      localι hX hg ≫ e.hom = eqToHom (congrArg projModel h.symm) ≫
        ((W'.map φ).projModelVariableChangeIso C).hom ≫ localι hX' hg := by
  -- the base change `eU` of `e` along `g` is a pointed isomorphism of projective models over
  -- `Spec A`
  have hP : IsPullback (localι hX hg ≫ e.hom) (W.map φ).projModelOver p' g :=
    (isPullback_localι hX hg).of_iso (.refl _) e (.refl _) (.refl _) (by simp) (by simp)
      (by simp [he]) (by simp)
  let eU := hP.isoIsPullback _ _ (isPullback_localι hX' hg)
  have hfst : eU.hom ≫ localι hX' hg = localι hX hg ≫ e.hom := hP.isoIsPullback_hom_fst _ _ _
  have hsnd : eU.hom ≫ (W'.map φ).projModelOver = (W.map φ).projModelOver :=
    hP.isoIsPullback_hom_snd _ _ _
  have h0U : (W.map φ).projModelZero ≫ eU.hom = (W'.map φ).projModelZero :=
    (isPullback_localι hX' hg).hom_ext
      (by rw [Category.assoc, hfst, projModelZero_localι_assoc hX hg hzp hzf,
        projModelZero_localι hX' hg (z := z ≫ e.hom) (by simp [he, hzp]) (by simpa using hzf')])
      (by simp [hsnd])
  obtain ⟨C, ⟨h, hC⟩, -⟩ := existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom eU hsnd h0U
  exact ⟨C, h, by rw [← hfst, hC, Category.assoc]⟩

end Local

/-! ### Gluing over the affine opens -/

section Global

variable {S X X' : Scheme.{u}} {W W' : WeierstrassCurve Γ(S, ⊤)} {p : X ⟶ S}
  {f : X ⟶ W.projModel} (hX : IsPullback f p W.projModelOver S.toSpecΓ) {p' : X' ⟶ S}
  {f' : X' ⟶ W'.projModel} (hX' : IsPullback f' p' W'.projModelOver S.toSpecΓ)

-- Restriction of global sections to an affine open `U`.
private noncomputable def resAffine (U : S.affineOpens) : Γ(S, ⊤) →+* Γ(S, U.1) :=
  (S.presheaf.map (homOfLE le_top).op).hom

private theorem fromSpec_toSpecΓ_eq (U : S.affineOpens) :
    U.2.fromSpec ≫ S.toSpecΓ = Spec.map (CommRingCat.ofHom (resAffine U)) := by
  rw [resAffine, CommRingCat.ofHom_hom]
  exact U.2.fromSpec_toSpecΓ

-- A morphism out of `X` is determined by its restrictions to the projective models over the affine
-- opens of `S`.
private theorem hom_ext_localι {Y : Scheme.{u}} {m₁ m₂ : X ⟶ Y}
    (h : ∀ U : S.affineOpens, localι hX (fromSpec_toSpecΓ_eq U) ≫ m₁ =
      localι hX (fromSpec_toSpecΓ_eq U) ≫ m₂) : m₁ = m₂ := by
  refine Scheme.hom_ext_of_forall _ _ fun x ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (p x)) isOpen_univ
  let V : S.affineOpens := ⟨U, hU⟩
  -- the inclusion of `p⁻¹(V)` factors through the projective model over `V`
  have hfac := (isPullback_localι hX (fromSpec_toSpecΓ_eq V)).lift_fst (p ⁻¹ᵁ V.1).ι
    (p ∣_ V.1 ≫ V.2.isoSpec.hom)
    (by rw [Category.assoc, V.2.isoSpec_hom_fromSpec, morphismRestrict_ι])
  refine ⟨p ⁻¹ᵁ V.1, hxU, ?_⟩
  rw [← hfac]
  simp only [Category.assoc, h V]

-- A change of variables inducing an isomorphism over `S` induces its base change along `φ`.
private theorem projModelBaseChange_comp_variableChange {A : Type u} [CommRing A]
    {C : VariableChange Γ(S, ⊤)} (h : C • W' = W) (φ : Γ(S, ⊤) →+* A)
    (h' : C.map φ • W'.map φ = W.map φ) :
    W.projModelBaseChange φ ≫ eqToHom (congrArg projModel h.symm) ≫
        (W'.projModelVariableChangeIso C).hom =
      eqToHom (congrArg projModel h'.symm) ≫
        ((W'.map φ).projModelVariableChangeIso (C.map φ)).hom ≫ W'.projModelBaseChange φ := by
  subst h
  simp [projModelVariableChangeIso_hom_projModelBaseChange]

-- Over every point `g : Spec A ⟶ S`, a change of variables inducing `m` over `S` induces `m`.
private theorem localι_comp_of_eq {A : Type u} [CommRing A] {φ : Γ(S, ⊤) →+* A}
    {g : Spec (.of A) ⟶ S} (hg : g ≫ S.toSpecΓ = Spec.map (CommRingCat.ofHom φ)) (m : X ⟶ X')
    (hm : m ≫ p' = p) {C : VariableChange Γ(S, ⊤)} (h : C • W' = W)
    (hC : m ≫ f' =
      f ≫ eqToHom (congrArg projModel h.symm) ≫ (W'.projModelVariableChangeIso C).hom) :
    ∃ h' : C.map φ • W'.map φ = W.map φ, localι hX hg ≫ m =
      eqToHom (congrArg projModel h'.symm) ≫
        ((W'.map φ).projModelVariableChangeIso (C.map φ)).hom ≫ localι hX' hg := by
  subst h
  refine ⟨map_variableChange W' C φ, hX'.hom_ext ?_ ?_⟩
  · simp [hC, projModelVariableChangeIso_hom_projModelBaseChange]
  · simp [hm, eqToHom_projModelOver_assoc (map_variableChange W' C φ).symm]

include hX hX' in
/-- **Pointed isomorphisms of projective Weierstrass models over a scheme are changes of
variables.** Let `S` be a scheme, let `W` and `W'` be Weierstrass curves over `Γ(S, ⊤)`, and let
`X` and `X'` be projective Weierstrass models of `W` and `W'` over `S`: base changes of
`projModel W` and `projModel W'` along `S.toSpecΓ`, and let `z` be the zero section of `X`. Then
every isomorphism `e : X ≅ X'` over `S` carrying `z` to the zero section of `X'`, that is, to a
section lying over the zero section of `projModel W'`, is induced by a unique change of variables
`C` over `Γ(S, ⊤)` with `C • W' = W`: under `f` and `f'`, `e` is the isomorphism
`projModel W = projModel (C • W') ≅ projModel W'` induced by `C`. No hypothesis on `S` is needed. -/
theorem existsUnique_hom_comp_eq_comp_projModelVariableChangeIso_hom (e : X ≅ X')
    (he : e.hom ≫ p' = p) {z : S ⟶ X} (hzp : z ≫ p = 𝟙 S)
    (hzf : z ≫ f = S.toSpecΓ ≫ W.projModelZero)
    (hzf' : z ≫ e.hom ≫ f' = S.toSpecΓ ≫ W'.projModelZero) :
    ∃! C : VariableChange Γ(S, ⊤), ∃ h : C • W' = W,
      e.hom ≫ f' =
        f ≫ eqToHom (congrArg projModel h.symm) ≫ (W'.projModelVariableChangeIso C).hom := by
  -- over each affine open `U`, `e` is induced by a unique change of variables `Cs U`
  choose Cs hCs using fun U : S.affineOpens ↦
    local_exists hX (fromSpec_toSpecΓ_eq U) hX' e he hzp hzf hzf'
  have uniq (U : S.affineOpens) {C : VariableChange Γ(S, U.1)}
      (hC : ∃ h : C • W'.map (resAffine U) = W.map (resAffine U),
        localι hX (fromSpec_toSpecΓ_eq U) ≫ e.hom = eqToHom (congrArg projModel h.symm) ≫
          ((W'.map (resAffine U)).projModelVariableChangeIso C).hom ≫
            localι hX' (fromSpec_toSpecΓ_eq U)) : C = Cs U :=
    hC.elim fun h hC ↦ (hCs U).elim fun h' hC' ↦ local_unique hX _ hX' e.hom h h' hC hC'
  -- restriction from an affine open `U` to an affine open `V ⊆ U`
  have hρ (U V : S.affineOpens) (hVU : V.1 ≤ U.1) :
      (S.presheaf.map (homOfLE hVU).op).hom.comp (resAffine U) = resAffine V := by
    rw [resAffine, resAffine, ← CommRingCat.hom_comp, ← Functor.map_comp]
    rfl
  -- the local changes of variables are compatible with restriction
  have compat (U V : S.affineOpens) (hVU : V.1 ≤ U.1) :
      (Cs U).map (S.presheaf.map (homOfLE hVU).op).hom = Cs V := by
    set ψ := (S.presheaf.map (homOfLE hVU).op).hom
    have hg : Spec.map (CommRingCat.ofHom ψ) ≫ U.2.fromSpec = V.2.fromSpec := by
      rw [CommRingCat.ofHom_hom]
      exact U.2.map_fromSpec V.2 _
    have hg' : (Spec.map (CommRingCat.ofHom ψ) ≫ U.2.fromSpec) ≫ S.toSpecΓ =
        Spec.map (CommRingCat.ofHom (ψ.comp (resAffine U))) := by
      rw [Category.assoc, fromSpec_toSpecΓ_eq, ← Spec.map_comp]
      rfl
    obtain ⟨h, hC⟩ := hCs U
    refine uniq V (exists_eq_comp_of_eq (by rw [map_map, hρ U V hVU])
      (by rw [map_map, hρ U V hVU]) ?_ ?_ (map_of_eq_comp h hC ψ))
    · rw [← eqToHom_localι hX (hρ U V hVU) hg hg' (fromSpec_toSpecΓ_eq V),
        ← projModelBaseChange_localι hX (fromSpec_toSpecΓ_eq U) ψ hg', eqToHom_trans_assoc]
    · rw [← eqToHom_localι hX' (hρ U V hVU) hg hg' (fromSpec_toSpecΓ_eq V),
        ← projModelBaseChange_localι hX' (fromSpec_toSpecΓ_eq U) ψ hg', eqToHom_trans_assoc]
  -- global sections are glued from, and determined by, their restrictions to the affine opens
  have glue (a : ∀ U : S.affineOpens, Γ(S, U.1))
      (ha : ∀ U V hVU, (S.presheaf.map (homOfLE hVU).op).hom.comp (resAffine U) = resAffine V →
        (S.presheaf.map (homOfLE hVU).op).hom (a U) = a V) :
      ∃ x : Γ(S, ⊤), ∀ U, resAffine U x = a U :=
    (S.existsUnique_gluing_affineOpens a fun U V hVU ↦ ha U V hVU (hρ U V hVU)).exists
  have ext (x y : Γ(S, ⊤)) (h : ∀ U, resAffine U x = resAffine U y) : x = y :=
    (S.existsUnique_gluing_affineOpens (fun U ↦ resAffine U y) fun U V hVU ↦
      congrArg (· y) (congrArg DFunLike.coe (hρ U V hVU))).unique h fun _ ↦ rfl
  have hext (C₁ C₂ : VariableChange Γ(S, ⊤))
      (h : ∀ U, C₁.map (resAffine U) = C₂.map (resAffine U)) : C₁ = C₂ := by
    ext
    · exact ext _ _ fun U ↦ congrArg (fun C ↦ (C.u : Γ(S, U.1))) (h U)
    · exact ext _ _ fun U ↦ congrArg VariableChange.r (h U)
    · exact ext _ _ fun U ↦ congrArg VariableChange.s (h U)
    · exact ext _ _ fun U ↦ congrArg VariableChange.t (h U)
  -- glue the four coefficients of the local changes of variables, and the inverse of `u`
  obtain ⟨u, hu⟩ := glue (fun U ↦ ((Cs U).u : Γ(S, U.1))) fun U V hVU _ ↦
    congrArg (fun C ↦ (C.u : Γ(S, V.1))) (compat U V hVU)
  obtain ⟨v, hv⟩ := glue (fun U ↦ (↑(Cs U).u⁻¹ : Γ(S, U.1))) fun U V hVU _ ↦ by
    simpa [VariableChange.map] using
      congrArg (fun C : VariableChange Γ(S, V.1) ↦ ((C.u⁻¹ : Γ(S, V.1)ˣ) : Γ(S, V.1)))
        (compat U V hVU)
  obtain ⟨r, hr⟩ := glue (fun U ↦ (Cs U).r) fun U V hVU _ ↦
    congrArg VariableChange.r (compat U V hVU)
  obtain ⟨s, hs⟩ := glue (fun U ↦ (Cs U).s) fun U V hVU _ ↦
    congrArg VariableChange.s (compat U V hVU)
  obtain ⟨t, ht⟩ := glue (fun U ↦ (Cs U).t) fun U V hVU _ ↦
    congrArg VariableChange.t (compat U V hVU)
  let C : VariableChange Γ(S, ⊤) :=
    ⟨⟨u, v, ext _ _ fun U ↦ by simp [hu, hv], ext _ _ fun U ↦ by simp [hu, hv]⟩, r, s, t⟩
  have hCU (U : S.affineOpens) : C.map (resAffine U) = Cs U :=
    VariableChange.ext (Units.ext (hu U)) (hr U) (hs U) (ht U)
  -- `C` carries `W'` to `W`, since it does so over every affine open
  have hW : C • W' = W := by
    have h (U : S.affineOpens) : (C • W').map (resAffine U) = W.map (resAffine U) := by
      rw [← map_variableChange, hCU]
      exact (hCs U).fst
    ext
    · exact ext _ _ fun U ↦ congrArg WeierstrassCurve.a₁ (h U)
    · exact ext _ _ fun U ↦ congrArg WeierstrassCurve.a₂ (h U)
    · exact ext _ _ fun U ↦ congrArg WeierstrassCurve.a₃ (h U)
    · exact ext _ _ fun U ↦ congrArg WeierstrassCurve.a₄ (h U)
    · exact ext _ _ fun U ↦ congrArg WeierstrassCurve.a₆ (h U)
  refine ⟨C, ⟨hW, hom_ext_localι hX fun U ↦ ?_⟩, fun C' ⟨h', hC'⟩ ↦ hext _ _ fun U ↦
    (uniq U (localι_comp_of_eq hX hX' _ e.hom he h' hC')).trans (hCU U).symm⟩
  -- over every affine open, both sides are induced by the restriction of `C`
  have H := hCs U
  rw [← hCU U] at H
  obtain ⟨h₁, h₂⟩ := H
  rw [← Category.assoc, h₂, Category.assoc, Category.assoc, localι_fst, localι_fst_assoc,
    projModelBaseChange_comp_variableChange hW (resAffine U) h₁]

end Global

end WeierstrassCurve
