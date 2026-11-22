/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Gluing
public import TauCeti.AlgebraicGeometry.Limits.Finite.Presentation
public import TauCeti.Algebra.Category.CommAlgCat.Localization
public import TauCeti.AlgebraicGeometry.FiniteEtale.PuncturedSpectrum
import TauCeti.Topology.Sober
import TauCeti.Algebra.Category.CommAlgCat.FilteredColimits
import TauCeti.AlgebraicGeometry.Pullback.SpecMap
import TauCeti.RingTheory.Etale.NoetherianDescent
import Mathlib.Algebra.Category.Ring.FinitePresentation

/-!
# Spreading out finite étale covers, and extension across points where purity holds

Let `W` be a retrocompact open of a scheme `X` and `x` a point of `X`. A finite étale cover of `W`
and a finite étale cover of the local scheme `Spec 𝒪_{X,x}` that agree over
`W ×_X Spec 𝒪_{X,x}` glue to a finite étale cover of an open neighbourhood of `x` containing `W`
(`TauCeti.FiniteEtaleScheme.exists_pullback_iso_of_isPullback_fromSpecStalk`; Stacks, Lemma
32.20.3 (0BQ5), existence, for finite étale covers).

The proof presents `Spec 𝒪_{X,x}` as the cofiltered limit of the spectra of the principal
localizations `Γ(A)[1/f]`, `f(x) ≠ 0`, of an affine open neighbourhood `A` of `x`, since
`𝒪_{X,x}` is the filtered colimit of these rings (`Submonoid.localizationAwayCoconeIsColimit`). A
finite étale cover of `Spec 𝒪_{X,x}` descends to one of these principal opens `D(f)`, as finite
étale algebras descend through filtered colimits of rings
(`TauCeti.Algebra.exists_etale_finite_algEquiv_tensorProduct_of_factorization`). Isomorphisms of
finite étale covers of a quasi-compact open descend along such limits
(`TauCeti.FiniteEtaleScheme.exists_nonempty_iso_pullback_fst_of_isLimit`, from the descent of
morphisms and isomorphisms of finitely presented schemes, Stacks 01ZM and 081E). So the two covers
agree over `W ∩ D(f')` for a smaller principal open `D(f')` of `x`, and they glue along it
(`TauCeti.FiniteEtaleScheme.exists_pullback_iso_of_isPullback`).

With purity, this extends finite étale covers across points of a Noetherian scheme
(`TauCeti.FiniteEtaleScheme.essSurj_pullback_ι_of_purityHolds`; Stacks, Lemma 58.21.6 (0EY7)).
Among the opens containing `U` to which a cover of `U` extends, choose a maximal one `W`. If
`W ≠ X`, the generic point `x` of an irreducible component of `X ∖ W` has all its proper
generizations in `W`, so the preimage of `W` in `Spec 𝒪_{X,x}` is the punctured spectrum. Purity
for `𝒪_{X,x}` extends the cover over `Spec 𝒪_{X,x}`, and spreading out extends it to an open
strictly larger than `W`, a contradiction.

## Main results

* `TauCeti.FiniteEtaleScheme.exists_nonempty_iso_pullback_fst_of_isLimit`: finite étale covers
  that are isomorphic over a cofiltered limit of qcqs schemes with affine transition maps are
  isomorphic at a finite stage.
* `TauCeti.FiniteEtaleScheme.exists_pullback_iso_of_isPullback_fromSpecStalk`: spreading out a
  finite étale cover from `Spec 𝒪_{X,x}` to an open neighbourhood of `x`.
* `TauCeti.FiniteEtaleScheme.essSurj_pullback_ι_of_purityHolds`: on a Noetherian scheme, if purity
  holds for the local rings at all points outside an open `U`, every finite étale cover of `U`
  extends to `X`.

## References

* [The Stacks Project, Lemma 32.20.3](https://stacks.math.columbia.edu/tag/0BQ5) and
  [Lemma 32.20.4](https://stacks.math.columbia.edu/tag/0EY3), spreading out from a local scheme.
* [The Stacks Project, Lemma 58.21.6](https://stacks.math.columbia.edu/tag/0EY7), extension of
  finite étale covers across points where purity holds.
* [The Stacks Project, Lemma 32.10.1](https://stacks.math.columbia.edu/tag/01ZM) and
  [Lemma 32.8.11](https://stacks.math.columbia.edu/tag/081E), descent of morphisms and
  isomorphisms along limits.
-/
public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

section Limit

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}}

/-- The scheme underlying the base change of `E` along `pullback.fst t z`, written as the
pullback of `E ⟶ T ⟶ Dᵢ` along `z`. -/
private def pullbackFstIso {i : I} {T Z : Scheme.{u}} (t : T ⟶ D.obj i) (z : Z ⟶ D.obj i)
    (E : FiniteEtaleScheme T) :
    Limits.pullback z (E.obj.hom ≫ t) ≅ Limits.pullback E.obj.hom (Limits.pullback.fst t z) :=
  pullbackSymmetry _ _ ≪≫ (pullbackRightPullbackFstIso t z E.obj.hom).symm

@[reassoc (attr := simp)]
private lemma pullbackFstIso_hom_fst {i : I} {T Z : Scheme.{u}} (t : T ⟶ D.obj i)
    (z : Z ⟶ D.obj i) (E : FiniteEtaleScheme T) :
    (pullbackFstIso t z E).hom ≫ Limits.pullback.fst _ _ = Limits.pullback.snd _ _ := by
  simp [pullbackFstIso]

@[reassoc (attr := simp)]
private lemma pullbackFstIso_hom_snd_snd {i : I} {T Z : Scheme.{u}} (t : T ⟶ D.obj i)
    (z : Z ⟶ D.obj i) (E : FiniteEtaleScheme T) :
    (pullbackFstIso t z E).hom ≫ Limits.pullback.snd _ _ ≫ Limits.pullback.snd _ _ =
      Limits.pullback.fst _ _ := by
  simp [pullbackFstIso]

@[reassoc (attr := simp)]
private lemma pullbackFstIso_inv_fst {i : I} {T Z : Scheme.{u}} (t : T ⟶ D.obj i)
    (z : Z ⟶ D.obj i) (E : FiniteEtaleScheme T) :
    (pullbackFstIso t z E).inv ≫ Limits.pullback.fst _ _ =
      Limits.pullback.snd _ _ ≫ Limits.pullback.snd _ _ := by
  simp [pullbackFstIso]

@[reassoc (attr := simp)]
private lemma pullbackFstIso_inv_snd {i : I} {T Z : Scheme.{u}} (t : T ⟶ D.obj i)
    (z : Z ⟶ D.obj i) (E : FiniteEtaleScheme T) :
    (pullbackFstIso t z E).inv ≫ Limits.pullback.snd _ _ = Limits.pullback.fst _ _ := by
  simp [pullbackFstIso]

/-- Pasting: the pullback of `fst : Dⱼ ×_{Dᵢ} X ⟶ Dⱼ` along `z` is the pullback along
`z ≫ D.map a`, after rewriting the latter as `w`. -/
private def pasteIso {i j : I} (a : j ⟶ i) {X Z : Scheme.{u}} (p : X ⟶ D.obj i)
    (z : Z ⟶ D.obj j) (w : Z ⟶ D.obj i) (hw : z ≫ D.map a = w) :
    Limits.pullback z (Limits.pullback.fst (D.map a) p) ≅ Limits.pullback w p :=
  pullbackRightPullbackFstIso (D.map a) p z ≪≫ pullback.congrHom hw rfl

@[reassoc (attr := simp)]
private lemma pasteIso_hom_fst {i j : I} (a : j ⟶ i) {X Z : Scheme.{u}} (p : X ⟶ D.obj i)
    (z : Z ⟶ D.obj j) (w : Z ⟶ D.obj i) (hw : z ≫ D.map a = w) :
    (pasteIso a p z w hw).hom ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _ := by
  simp [pasteIso]

@[reassoc (attr := simp)]
private lemma pasteIso_hom_snd {i j : I} (a : j ⟶ i) {X Z : Scheme.{u}} (p : X ⟶ D.obj i)
    (z : Z ⟶ D.obj j) (w : Z ⟶ D.obj i) (hw : z ≫ D.map a = w) :
    (pasteIso a p z w hw).hom ≫ Limits.pullback.snd _ _ =
      Limits.pullback.snd _ _ ≫ Limits.pullback.snd _ _ := by
  simp [pasteIso]

@[reassoc (attr := simp)]
private lemma pasteIso_inv_fst {i j : I} (a : j ⟶ i) {X Z : Scheme.{u}} (p : X ⟶ D.obj i)
    (z : Z ⟶ D.obj j) (w : Z ⟶ D.obj i) (hw : z ≫ D.map a = w) :
    (pasteIso a p z w hw).inv ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _ := by
  rw [Iso.inv_comp_eq, pasteIso_hom_fst]

/-- At a stage `k ⟶ j ⟶ i`, an isomorphism
`Dₖ ×_{Dⱼ} (Dⱼ ×_{Dᵢ} E) ≅ Dₖ ×_{Dⱼ} (Dⱼ ×_{Dᵢ} F)` over `Dₖ` is an isomorphism of the base
changes of `E` and `F` to `T ×_{Dᵢ} Dₖ`. -/
private lemma nonempty_iso_of_isIso_pullbackMap {i j k : I} (hji : j ⟶ i) (hkj : k ⟶ j)
    {T : Scheme.{u}} (t : T ⟶ D.obj i) [Mono t] {E F : FiniteEtaleScheme T}
    (b : Limits.pullback (D.map hji) (E.obj.hom ≫ t) ⟶
      Limits.pullback (D.map hji) (F.obj.hom ≫ t))
    (hb : b ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _)
    [IsIso (pullback.map (D.map hkj) (Limits.pullback.fst (D.map hji) (E.obj.hom ≫ t))
      (D.map hkj) (Limits.pullback.fst (D.map hji) (F.obj.hom ≫ t)) (𝟙 _) b (𝟙 _)
      (by simp) (by simp [hb]))] :
    Nonempty ((pullback (Limits.pullback.fst t (D.map (hkj ≫ hji)))).obj E ≅
      (pullback (Limits.pullback.fst t (D.map (hkj ≫ hji)))).obj F) := by
  have hk' : D.map hkj ≫ D.map hji = D.map (hkj ≫ hji) := (D.map_comp _ _).symm
  let Φ : Limits.pullback E.obj.hom (Limits.pullback.fst t (D.map (hkj ≫ hji))) ≅
      Limits.pullback F.obj.hom (Limits.pullback.fst t (D.map (hkj ≫ hji))) :=
    (pullbackFstIso t _ E).symm ≪≫ (pasteIso hji (E.obj.hom ≫ t) _ _ hk').symm ≪≫
      asIso (pullback.map (D.map hkj) (Limits.pullback.fst (D.map hji) (E.obj.hom ≫ t))
        (D.map hkj) (Limits.pullback.fst (D.map hji) (F.obj.hom ≫ t)) (𝟙 _) b (𝟙 _)
        _ _) ≪≫
      pasteIso hji (F.obj.hom ≫ t) _ _ hk' ≪≫ pullbackFstIso t _ F
  -- `Φ` lies over `T ×_{Dᵢ} Dₖ`: both sides lie over `Dₖ`, and `T ×_{Dᵢ} Dₖ ⟶ Dₖ` is monic.
  have hΦ : Φ.hom ≫ Limits.pullback.snd F.obj.hom _ = Limits.pullback.snd E.obj.hom
      (Limits.pullback.fst t (D.map (hkj ≫ hji))) := by
    rw [← cancel_mono (Limits.pullback.snd t (D.map (hkj ≫ hji)))]
    simp [Φ]
  exact ⟨ObjectProperty.isoMk _ (Over.isoMk Φ hΦ)⟩

/-- If `b` over `Dⱼ` is compatible with an isomorphism `e'` over the limit `S`, then the base
change of `b` to `S` is an isomorphism. -/
private lemma isIso_pullbackMap_π {c : Cone D} {i j : I} (hji : j ⟶ i) {X Y : Scheme.{u}}
    (p : X ⟶ D.obj i) (q : Y ⟶ D.obj i)
    (e' : Limits.pullback (c.π.app i) p ≅ Limits.pullback (c.π.app i) q)
    (he' : e'.hom ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _)
    (b : Limits.pullback (D.map hji) p ⟶ Limits.pullback (D.map hji) q)
    (hb : b ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _)
    (hcomm : pullback.map (c.π.app i) p (D.map hji) p (c.π.app j) (𝟙 X) (𝟙 _) (by simp)
      (by simp) ≫ b = e'.hom ≫ pullback.map (c.π.app i) q (D.map hji) q (c.π.app j) (𝟙 Y)
        (𝟙 _) (by simp) (by simp)) :
    IsIso (pullback.map (c.π.app j) (Limits.pullback.fst (D.map hji) p) (c.π.app j)
      (Limits.pullback.fst (D.map hji) q) (𝟙 _) b (𝟙 _) (by simp) (by simp [hb])) := by
  -- Through the pasting isomorphisms `S ×_{Dⱼ} (Dⱼ ×_{Dᵢ} -) ≅ S ×_{Dᵢ} -`, it is `e'`.
  have hlim : pullback.map (c.π.app j) (Limits.pullback.fst (D.map hji) p) (c.π.app j)
      (Limits.pullback.fst (D.map hji) q) (𝟙 _) b (𝟙 _) (by simp) (by simp [hb]) ≫
        (pasteIso hji q _ _ (c.w hji)).hom =
      (pasteIso hji p _ _ (c.w hji)).hom ≫ e'.hom := by
    apply pullback.hom_ext
    · simp [he']
    · have hX : (pasteIso hji p _ _ (c.w hji)).hom ≫ pullback.map (c.π.app i) p (D.map hji) p
          (c.π.app j) (𝟙 _) (𝟙 _) (by simp) (by simp) = Limits.pullback.snd _ _ := by
        apply pullback.hom_ext
        · simp [pullback.condition]
        · simp
      have := congr($hcomm ≫ Limits.pullback.snd _ _)
      simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
        Category.comp_id] at this
      simp only [Category.assoc, pasteIso_hom_snd, limit.lift_π_assoc, PullbackCone.mk_pt,
        PullbackCone.mk_π_app]
      rw [← reassoc_of% hX, this]
  rw [← Iso.eq_comp_inv] at hlim
  rw [hlim]
  infer_instance

/-- **Isomorphisms of finite étale covers descend along cofiltered limits.** Let `S = lim Dⱼ` be
a cofiltered limit of quasi-compact quasi-separated schemes with affine transition maps, and let
`t : T ⟶ Dᵢ` be a quasi-compact monomorphism locally of finite presentation, for instance the
inclusion of a quasi-compact open. If two finite étale covers `E` and `F` of `T` become isomorphic
after base change to `T ×_{Dᵢ} S`, they are already isomorphic after base change to
`T ×_{Dᵢ} Dⱼ` for some `j ⟶ i`. -/
theorem exists_nonempty_iso_pullback_fst_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D} (hc : IsLimit c) {i : I} {T : Scheme.{u}}
    (t : T ⟶ D.obj i) [Mono t] [LocallyOfFinitePresentation t] [QuasiCompact t]
    {E F : FiniteEtaleScheme T}
    (e : (pullback (Limits.pullback.fst t (c.π.app i))).obj E ≅
      (pullback (Limits.pullback.fst t (c.π.app i))).obj F) :
    ∃ (j : I) (a : j ⟶ i), Nonempty ((pullback (Limits.pullback.fst t (D.map a))).obj E ≅
      (pullback (Limits.pullback.fst t (D.map a))).obj F) := by
  -- The isomorphism `e` over the limit, as a morphism `S ×_{Dᵢ} E ⟶ S ×_{Dᵢ} F` over `S`.
  let eL : Limits.pullback E.obj.hom (Limits.pullback.fst t (c.π.app i)) ≅
      Limits.pullback F.obj.hom (Limits.pullback.fst t (c.π.app i)) :=
    (Over.forget _).mapIso ((ObjectProperty.ι _).mapIso e)
  have heL : eL.hom ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _ := Over.w e.hom.hom
  let e' : Limits.pullback (c.π.app i) (E.obj.hom ≫ t) ≅
      Limits.pullback (c.π.app i) (F.obj.hom ≫ t) :=
    pullbackFstIso t _ E ≪≫ eL ≪≫ (pullbackFstIso t _ F).symm
  have he' : e'.hom ≫ Limits.pullback.fst _ (F.obj.hom ≫ t) = Limits.pullback.fst _ _ := by
    simp [e', reassoc_of% heL]
  -- It is the base change of a morphism `b` over some `Dⱼ`, which is an isomorphism over `S`.
  obtain ⟨j, hji, b, hb, hcomm⟩ := hc.exists_pullbackMap_comp_eq e'.hom he'
  have := QuasiCompact.compactSpace_of_compactSpace
    (Limits.pullback.fst (D.map hji) (E.obj.hom ≫ t))
  have := QuasiCompact.compactSpace_of_compactSpace
    (Limits.pullback.fst (D.map hji) (F.obj.hom ≫ t))
  have := quasiSeparatedSpace_of_quasiSeparated
    (Limits.pullback.fst (D.map hji) (F.obj.hom ≫ t))
  have : LocallyOfFinitePresentation b := by
    have : LocallyOfFinitePresentation
        (b ≫ Limits.pullback.fst (D.map hji) (F.obj.hom ≫ t)) := by
      rw [hb]; infer_instance
    exact locallyOfFinitePresentation_of_comp b
      (Limits.pullback.fst (D.map hji) (F.obj.hom ≫ t))
  have := isIso_pullbackMap_π hji _ _ e' he' b hb hcomm
  -- Hence `b` is an isomorphism over some later stage `Dₖ`.
  obtain ⟨k, hkj, hk⟩ := hc.exists_isIso_pullbackMap b hb
  exact ⟨k, hkj ≫ hji, nonempty_iso_of_isIso_pullbackMap hji hkj t b hb⟩

end Limit

section Localization

variable {R : Type u} [CommRing R] (M : Submonoid R)

/-- The spectra of the principal localizations `R[1/∏ s]`, for finite sets `s` of elements of
`M`, with the maps induced by inverting more elements. -/
private abbrev awaySpecDiagram : (Finset M)ᵒᵖ ⥤ Scheme.{u} :=
  (M.localizationAwayDiagram ⋙ forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).op ⋙ Scheme.Spec

private instance (s : (Finset M)ᵒᵖ) : IsAffine ((awaySpecDiagram M).obj s) := by
  dsimp only [awaySpecDiagram, Functor.comp_obj, Functor.op_obj, Scheme.Spec_obj]
  infer_instance

/-- The open immersion `Spec R[1/∏ s] ⟶ Spec R`. -/
private abbrev awaySpecToSpec (s : (Finset M)ᵒᵖ) : (awaySpecDiagram M).obj s ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (M.localizationAwayDiagram.obj s.unop)))

private lemma awaySpecDiagram_map_awaySpecToSpec {s s' : (Finset M)ᵒᵖ} (f : s ⟶ s') :
    (awaySpecDiagram M).map f ≫ awaySpecToSpec M s' = awaySpecToSpec M s := by
  dsimp only [awaySpecDiagram, awaySpecToSpec, Functor.comp_map, Functor.op_map,
    Scheme.Spec_map]
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact (M.localizationAwayDiagram.map f.unop).hom.commutes x

private instance (s : (Finset M)ᵒᵖ) : IsOpenImmersion (awaySpecToSpec M s) := by
  -- The stage is `Localization.Away (∏ x ∈ s, x)` up to the identification of its object.
  have h : CommRingCat.ofHom (algebraMap R (M.localizationAwayDiagram.obj s.unop)) =
      CommRingCat.ofHom (algebraMap R (Localization.Away (∏ x ∈ s.unop, (x : R)))) ≫
        (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).map
          (eqToHom (M.localizationAwayDiagram_obj s.unop).symm) := by
    ext x
    exact ((eqToHom (M.localizationAwayDiagram_obj s.unop).symm).hom.commutes x).symm
  rw [awaySpecToSpec, h, Spec.map_comp]
  infer_instance

private instance {s s' : (Finset M)ᵒᵖ} (f : s ⟶ s') :
    IsOpenImmersion ((awaySpecDiagram M).map f) :=
  have : IsOpenImmersion ((awaySpecDiagram M).map f ≫ awaySpecToSpec M s') := by
    rw [awaySpecDiagram_map_awaySpecToSpec]; infer_instance
  .of_comp _ (awaySpecToSpec M s')

variable (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]

/-- The principal localizations `R[1/∏ s]` as commutative rings, with the canonical maps to
`M⁻¹R`; its apex is `M⁻¹R` itself. -/
private abbrev awayCocone : Cocone (M.localizationAwayDiagram ⋙
    forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) :=
  (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).mapCocone
    ((M.localizationAwayCocone S).extend (eqToHom (M.localizationAwayCocone_pt S)))

/-- `M⁻¹R` is the filtered colimit of the principal localizations `R[1/∏ s]`. -/
private def awayCoconeIsColimit : IsColimit (awayCocone M S) := by
  let U := forget₂ (CommAlgCat.{u} R) CommRingCat.{u}
  -- Forgetting the algebra structure preserves this filtered colimit: the forgetful functor
  -- to types preserves it, and the forgetful functor from rings to types reflects it.
  have : PreservesColimitsOfShape (Finset M) (U ⋙ forget CommRingCat) :=
    preservesColimitsOfShape_of_natIso (eqToIso HasForget₂.forget_comp).symm
  have : ReflectsColimit (M.localizationAwayDiagram ⋙ U) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  have : PreservesColimit M.localizationAwayDiagram U :=
    preservesColimit_of_reflects_of_preserves U (forget CommRingCat)
  exact isColimitOfPreserves U (IsColimit.extendIso _ (M.localizationAwayCoconeIsColimit S))

/-- The cone exhibiting `Spec (M⁻¹R)` as the limit of the spectra of principal localizations. -/
private abbrev awaySpecCone : Cone (awaySpecDiagram M) :=
  Scheme.Spec.mapCone (awayCocone M S).op

/-- The spectrum of a localization is the cofiltered limit of the spectra of the principal
localizations, as `Spec` turns the filtered colimit `M⁻¹R = colim R[1/∏ s]` into a limit. -/
private def awaySpecConeIsLimit : IsLimit (awaySpecCone M S) :=
  isLimitOfPreserves Scheme.Spec (awayCoconeIsColimit M S).op

private lemma awaySpecCone_π_awaySpecToSpec (s : (Finset M)ᵒᵖ) :
    (awaySpecCone M S).π.app s ≫ awaySpecToSpec M s =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  dsimp only [awaySpecCone, awaySpecToSpec, Functor.mapCone_π_app, Cocone.op_π,
    Scheme.Spec_map, NatTrans.op_app]
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact (((M.localizationAwayCocone S).extend
    (eqToHom (M.localizationAwayCocone_pt S))).ι.app s.unop).hom.commutes x

/-- Every finite étale scheme over `Spec (M⁻¹R)` is the base change of a finite étale scheme
over the spectrum of a principal localization `R[1/∏ s]`. -/
private lemma exists_pullback_awaySpecCone_iso (Y : FiniteEtaleScheme (Spec (.of S))) :
    ∃ (s : (Finset M)ᵒᵖ) (Y₀ : FiniteEtaleScheme ((awaySpecDiagram M).obj s)),
      Nonempty ((pullback ((awaySpecCone M S).π.app s)).obj Y₀ ≅ Y) := by
  let F := M.localizationAwayDiagram ⋙ forget₂ (CommAlgCat.{u} R) CommRingCat.{u}
  let ψ (s : Finset M) : F.obj s →+* S := ((awayCocone M S).ι.app s).hom
  -- Maps from rings of finite presentation over `ℤ` to `M⁻¹R` factor through a stage. The stages
  -- are indexed by finite subsets of `M`, as in the limit presentation of `Spec (M⁻¹R)`, rather
  -- than by single elements of `M` as in
  -- `TauCeti.Algebra.exists_etale_finite_algEquiv_tensorProduct_localizationAway`.
  have hfactor (P : Type u) [CommRing P] [Algebra.FinitePresentation ℤ P] (g : P →+* S) :
      ∃ s, ∃ φ : P →+* F.obj s, (ψ s).comp φ = g := by
    let α : (Functor.const (Finset M)).obj (CommRingCat.of (ULift.{u} ℤ)) ⟶ F :=
      { app _ := CommRingCat.isInitial.to _
        naturality _ _ _ := CommRingCat.isInitial.hom_ext _ _ }
    -- The map out of the initial object `ULift ℤ` is the cast `ULift ℤ ≃+* ℤ → P`.
    have hfp : (CommRingCat.isInitial.to (CommRingCat.of P)).hom.FinitePresentation :=
      (RingHom.finitePresentation_algebraMap.mpr inferInstance).comp
        (RingHom.FinitePresentation.of_bijective ULift.ringEquiv.bijective)
    obtain ⟨s, φ, -, hφ⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit _ F α _
      (awayCocone M S) (awayCoconeIsColimit M S) hfp (CommRingCat.ofHom g)
      fun _ ↦ CommRingCat.isInitial.hom_ext _ _
    exact ⟨s, φ.hom, congrArg CommRingCat.Hom.hom hφ.symm⟩
  -- `Y` is the spectrum of a finite étale `M⁻¹R`-algebra `B`, which descends to a stage.
  have := essSurj_spec (.of S)
  obtain ⟨B, ⟨eB⟩⟩ := Functor.EssSurj.mem_essImage (spec (.of S)) Y
  obtain ⟨s, B₀, _, _, _, _, ⟨e⟩⟩ :=
    TauCeti.Algebra.exists_etale_finite_algEquiv_tensorProduct_of_factorization
      (fun s ↦ F.obj s) ψ hfactor B.unop.obj
  let := (ψ s).toAlgebra
  refine ⟨Opposite.op s, (spec (F.obj s)).obj (Opposite.op (CommAlgCat.FiniteEtale.of _ B₀)),
    ⟨?_ ≪≫ eB⟩⟩
  apply ObjectProperty.isoMk
  -- `Over.pullback` bundles `pullback.snd` and `algSpec` bundles `Spec.algebraMap`, so the objects
  -- are those of `pullbackSpecIsoOfAlgEquiv`, as in `essSurj_pullback_of_essSurj_baseChange`.
  rw [pullback_obj_obj, spec_obj_obj, spec_obj_obj]
  exact TauCeti.AlgebraicGeometry.pullbackSpecIsoOfAlgEquiv (F.obj s) B₀ S B.unop.obj e.symm

end Localization

section Glue

/-- Finite étale covers of an open `W` of `X` and of an open subscheme `G : Z ⟶ X` which agree
over their intersection glue to a finite étale cover of `W ∪ G(Z)`. -/
private lemma exists_glue {X Z P : Scheme.{u}} {W : X.Opens} (G : Z ⟶ X) [IsOpenImmersion G]
    {i₁ : P ⟶ W} {i₂ : P ⟶ Z} (h : IsPullback i₁ i₂ W.ι G) (V : FiniteEtaleScheme W)
    (Y : FiniteEtaleScheme Z) (e : (pullback i₁).obj V ≅ (pullback i₂).obj Y) :
    ∃ V' : FiniteEtaleScheme (W ⊔ G.opensRange : X.Opens),
      Nonempty ((pullback (X.homOfLE le_sup_left)).obj V' ≅ V) ∧
      ∀ j : Z ⟶ (W ⊔ G.opensRange : X.Opens), j ≫ Scheme.Opens.ι _ = G →
        Nonempty ((pullback j).obj V' ≅ Y) := by
  set W' : X.Opens := W ⊔ G.opensRange
  have hrange : Set.range G ⊆ Set.range W'.ι := by
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange]
    exact (le_sup_right : G.opensRange ≤ W')
  let j₂ : Z ⟶ W' := IsOpenImmersion.lift W'.ι G hrange
  have hj₂ : j₂ ≫ W'.ι = G := IsOpenImmersion.lift_fac _ _ _
  -- The overlap square, which is cartesian over `X`, stays cartesian over the open `W'`.
  have hsq : IsPullback i₁ i₂ (X.homOfLE le_sup_left) j₂ := by
    replace h :
        IsPullback i₁ i₂ (X.homOfLE (le_sup_left : W ≤ W') ≫ W'.ι) (j₂ ≫ W'.ι) := by
      rw [Scheme.homOfLE_ι, hj₂]; exact h
    refine IsPullback.of_isLimit' ⟨by rw [← cancel_mono W'.ι]; simpa using h.w⟩
      (PullbackCone.IsLimit.mk _
        (fun s ↦ h.lift s.fst s.snd (by simp [reassoc_of% s.condition]))
        (fun s ↦ h.lift_fst _ _ _) (fun s ↦ h.lift_snd _ _ _) fun s l h₁ h₂ ↦ ?_)
    exact h.hom_ext (by simpa using h₁) (by simpa using h₂)
  have hcover : (X.homOfLE (le_sup_left : W ≤ W')).opensRange ⊔ j₂.opensRange = ⊤ := by
    have hG : (j₂ ≫ W'.ι).opensRange = G.opensRange :=
      TopologicalSpace.Opens.ext (by simp only [Scheme.Hom.coe_opensRange, hj₂])
    rw [Scheme.opensRange_homOfLE, ← W'.ι.preimage_image_eq j₂.opensRange,
      ← Scheme.Hom.opensRange_comp, hG, ← Scheme.Hom.preimage_sup,
      Scheme.Opens.ι_preimage_self]
  have : IsOpenImmersion i₁ :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip inferInstance
  have : IsOpenImmersion i₂ :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) h inferInstance
  obtain ⟨V', e₁, e₂, -⟩ := exists_pullback_iso_of_isPullback hsq hcover e
  refine ⟨V', ⟨e₁⟩, fun j hj ↦ ?_⟩
  obtain rfl : j = j₂ := by rw [← cancel_mono W'.ι, hj, hj₂]
  exact ⟨e₂⟩

/-- Let `S = lim Dⱼ` be a cofiltered limit as in `exists_nonempty_iso_pullback_fst_of_isLimit`,
with a morphism `g : Dᵢ ⟶ X`. If a finite étale cover `V` of a retrocompact open `W` of `X` and a
finite étale cover `Y₀` of `Dᵢ` agree over `W ×_X S`, they already agree over
`(W ×_X Dᵢ) ×_{Dᵢ} Dₖ` for some `k ⟶ i`. -/
private lemma exists_iso_stage {I : Type u} [Category.{u} I] [IsCofiltered I]
    {D : I ⥤ Scheme.{u}} [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] {c : Cone D}
    (hc : IsLimit c) {X : Scheme.{u}} {W : X.Opens} [QuasiCompact W.ι] {i : I}
    (g : D.obj i ⟶ X) {T : Scheme.{u}} {a : T ⟶ W} {b : T ⟶ c.pt}
    (h : IsPullback a b W.ι (c.π.app i ≫ g)) (V : FiniteEtaleScheme W)
    (Y₀ : FiniteEtaleScheme (D.obj i))
    (e : (pullback b).obj ((pullback (c.π.app i)).obj Y₀) ≅ (pullback a).obj V) :
    ∃ (k : I) (hk : k ⟶ i), Nonempty ((pullback
      (Limits.pullback.fst (Limits.pullback.snd W.ι g) (D.map hk) ≫
        Limits.pullback.fst W.ι g)).obj V ≅
      (pullback (Limits.pullback.snd (Limits.pullback.snd W.ι g) (D.map hk))).obj
        ((pullback (D.map hk)).obj Y₀)) := by
  let t := Limits.pullback.snd W.ι g
  let P := Limits.pullback.fst t (c.π.app i)
  -- Over `(W ×_X Dᵢ) ×_{Dᵢ} S`, which maps to `T = W ×_X S`, the two covers agree.
  let κ : Limits.pullback t (c.π.app i) ⟶ T :=
    h.lift (P ≫ Limits.pullback.fst W.ι g) (Limits.pullback.snd t (c.π.app i)) (by
      rw [Category.assoc, Limits.pullback.condition, reassoc_of% Limits.pullback.condition])
  have hκa : κ ≫ a = P ≫ Limits.pullback.fst W.ι g := h.lift_fst _ _ _
  have hκb : κ ≫ b = Limits.pullback.snd t (c.π.app i) := h.lift_snd _ _ _
  let eLim : (pullback P).obj ((pullback (Limits.pullback.fst W.ι g)).obj V) ≅
      (pullback P).obj ((pullback t).obj Y₀) :=
    (pullbackComp _ _).symm.app V ≪≫ eqToIso (by rw [hκa]) ≪≫ (pullbackComp κ a).app V ≪≫
      (pullback κ).mapIso e.symm ≪≫ (pullbackComp κ b).symm.app _ ≪≫
      eqToIso (by rw [hκb, Functor.comp_obj]) ≪≫
      (pullbackComp (Limits.pullback.snd t (c.π.app i)) (c.π.app i)).symm.app Y₀ ≪≫
      eqToIso (by rw [Limits.pullback.condition]) ≪≫ (pullbackComp P t).app Y₀
  -- The isomorphism descends to a stage `Dₖ`.
  obtain ⟨k, hk, ⟨eA⟩⟩ := exists_nonempty_iso_pullback_fst_of_isLimit hc t eLim
  exact ⟨k, hk, ⟨(pullbackComp _ _).app V ≪≫ eA ≪≫ (pullbackComp _ _).symm.app Y₀ ≪≫
    eqToIso (by rw [Limits.pullback.condition]) ≪≫ (pullbackComp _ _).app Y₀⟩⟩

end Glue

/-- **Spreading out a finite étale cover from the local scheme at a point.** Let `W` be a
retrocompact open of a scheme `X`, `x` a point of `X`, and `T = W ×_X Spec 𝒪_{X,x}`. If a finite
étale cover `V` of `W` and a finite étale cover `Y` of `Spec 𝒪_{X,x}` agree over `T`, they glue
to a finite étale cover `V'` of an open `W' ⊇ W` containing `x`: the restriction of `V'` to `W`
is `V`, and its pullback to `Spec 𝒪_{X,x}` is `Y`.

This is the existence part of Stacks, Lemma 32.20.3 (0BQ5), for finite étale covers; that the
glued scheme is again finite étale is the corresponding case of Lemma 32.20.4 (0EY3). -/
@[stacks 0BQ5 "Existence of the glued scheme, for finite étale covers."]
theorem exists_pullback_iso_of_isPullback_fromSpecStalk {X : Scheme.{u}} {W : X.Opens}
    [QuasiCompact W.ι] {x : X} {T : Scheme.{u}} {a : T ⟶ W}
    {b : T ⟶ Spec (X.presheaf.stalk x)} (h : IsPullback a b W.ι (X.fromSpecStalk x))
    (V : FiniteEtaleScheme W) (Y : FiniteEtaleScheme (Spec (X.presheaf.stalk x)))
    (e : (pullback b).obj Y ≅ (pullback a).obj V) :
    ∃ (W' : X.Opens) (hW : W ≤ W') (hx : x ∈ W') (V' : FiniteEtaleScheme W'),
      Nonempty ((pullback (X.homOfLE hW)).obj V' ≅ V) ∧
      Nonempty ((pullback (W'.fromSpecStalkOfMem x hx)).obj V' ≅ Y) := by
  -- Present `Spec 𝒪_{X,x}` as the limit of the principal open neighbourhoods `D(f)` of `x` in
  -- an affine open `A`, and descend `Y` to one of them.
  obtain ⟨A, hA, hxA, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ (⊤ : X.Opens) from trivial)
  have hA : IsAffineOpen A := hA
  let M := (hA.primeIdealOf ⟨x, hxA⟩).asIdeal.primeCompl
  let alg : Algebra Γ(X, A) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxA⟩
  have loc : IsLocalization M (X.presheaf.stalk x) := hA.isLocalization_stalk ⟨x, hxA⟩
  -- The algebra structure of the stalk over `Γ(X, A)` is given by the germ map.
  have halg : CommRingCat.ofHom (algebraMap Γ(X, A) (X.presheaf.stalk x)) =
      X.presheaf.germ A x hxA := (rfl)
  let D := awaySpecDiagram M
  let c := awaySpecCone M (X.presheaf.stalk x)
  have hc : IsLimit c := awaySpecConeIsLimit M (X.presheaf.stalk x)
  let g (s : (Finset M)ᵒᵖ) : D.obj s ⟶ X := awaySpecToSpec M s ≫ hA.fromSpec
  have hDg {s s' : (Finset M)ᵒᵖ} (f : s ⟶ s') : D.map f ≫ g s' = g s := by
    simp only [g, D, ← Category.assoc, awaySpecDiagram_map_awaySpecToSpec]
  have hcg (s : (Finset M)ᵒᵖ) : c.π.app s ≫ g s = X.fromSpecStalk x := by
    rw [← Category.assoc, awaySpecCone_π_awaySpecToSpec,
      ← hA.fromSpecStalk_eq_fromSpecStalk hxA, IsAffineOpen.fromSpecStalk, halg]
  obtain ⟨s₀, Y₀, ⟨ε⟩⟩ := @exists_pullback_awaySpecCone_iso _ _ M (X.presheaf.stalk x) _ alg loc Y
  -- `V` and `Y₀` agree over a principal neighbourhood `D(f)` of `x`, where they glue.
  rw [← hcg s₀] at h
  obtain ⟨k, hk, ⟨eglue⟩⟩ := exists_iso_stage hc (g s₀) h V Y₀ ((pullback b).mapIso ε ≪≫ e)
  have hsq : IsPullback (Limits.pullback.fst (Limits.pullback.snd W.ι (g s₀)) (D.map hk) ≫
      Limits.pullback.fst W.ι (g s₀))
      (Limits.pullback.snd (Limits.pullback.snd W.ι (g s₀)) (D.map hk)) W.ι (g k) := by
    rw [← hDg hk]
    exact (IsPullback.of_hasPullback _ (D.map hk)).paste_horiz
      (IsPullback.of_hasPullback W.ι (g s₀))
  obtain ⟨V', ⟨e₁⟩, hV'⟩ := exists_glue (g k) hsq V _ eglue
  have hx : x ∈ W ⊔ (g k).opensRange := by
    have h₁ : (c.π.app k ≫ g k) (IsLocalRing.closedPoint (X.presheaf.stalk x)) = x := by
      rw [hcg k]; exact Scheme.fromSpecStalk_closedPoint
    exact Or.inr ⟨_, h₁⟩
  refine ⟨_, le_sup_left, hx, V', ⟨e₁⟩, ?_⟩
  -- The pullback of the glued cover to `Spec 𝒪_{X,x}` factors through `D(f')`.
  have hrange : Set.range (g k) ⊆ Set.range (W ⊔ (g k).opensRange).ι := by
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange]
    exact (le_sup_right : (g k).opensRange ≤ _)
  let j := IsOpenImmersion.lift (W ⊔ (g k).opensRange).ι (g k) hrange
  have hj : j ≫ (W ⊔ (g k).opensRange).ι = g k := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨e₂⟩ := hV' j hj
  have hfac : (W ⊔ (g k).opensRange).fromSpecStalkOfMem x hx = c.π.app k ≫ j := by
    rw [← cancel_mono (W ⊔ (g k).opensRange).ι, Scheme.Opens.fromSpecStalkOfMem_ι,
      Category.assoc, hj, hcg]
  exact ⟨eqToIso (by rw [hfac]) ≪≫ (pullbackComp _ _).app V' ≪≫ (pullback _).mapIso e₂ ≪≫
    (pullbackComp _ _).symm.app Y₀ ≪≫ eqToIso (by rw [c.w hk]) ≪≫ ε⟩

section Purity

/-- If an open `W` is not everything, some point `x ∉ W` has all its proper generizations in
`W`: the generic point of an irreducible component of the complement. -/
private lemma exists_not_mem_forall_specializes {X : Scheme.{u}} {W : X.Opens} (hW : W ≠ ⊤) :
    ∃ x : X, x ∉ W ∧ ∀ y : X, y ⤳ x → y ∉ W → y = x := by
  obtain ⟨y, hy⟩ : ∃ y : X, y ∉ W := by
    by_contra! h
    exact hW (eq_top_iff.mpr fun y _ ↦ h y)
  have hs : IsClosed ((W : Set X)ᶜ) := W.isOpen.isClosed_compl
  let : QuasiSober ((W : Set X)ᶜ : Set X) := hs.isClosedEmbedding_subtypeVal.quasiSober
  obtain ⟨z, hz, -⟩ := hs.exists_genericPoint_specializes (x := y) hy
  refine ⟨z, z.property, fun y hyz hyW ↦ ?_⟩
  exact congrArg Subtype.val (TauCeti.mem_genericPoints_iff.mp hz ⟨y, hyW⟩
    (Topology.IsInducing.subtypeVal.specializes_iff.mp hyz))

/-- Let `x ∉ W` be a point whose proper generizations all lie in the retrocompact open `W`, and
suppose that purity holds for `𝒪_{X,x}`. Then every finite étale cover of `W` extends to a
finite étale cover of an open `W' ⊇ W` containing `x`. -/
private lemma exists_extension_of_purityHolds {X : Scheme.{u}} {W : X.Opens}
    [QuasiCompact W.ι] {x : X} (hxW : x ∉ W) (hgen : ∀ y : X, y ⤳ x → y ∉ W → y = x)
    (hx : IsLocalRing.PurityHolds (X.presheaf.stalk x)) (V : FiniteEtaleScheme W) :
    ∃ (W' : X.Opens) (hW : W ≤ W'), x ∈ W' ∧ ∃ V' : FiniteEtaleScheme W',
      Nonempty ((pullback (X.homOfLE hW)).obj V' ≅ V) := by
  -- The preimage of `W` in `Spec 𝒪_{X,x}` is the punctured spectrum.
  have heq : X.fromSpecStalk x ⁻¹ᵁ W = IsLocalRing.puncturedSpectrum (X.presheaf.stalk x) := by
    ext p
    rw [SetLike.mem_coe, SetLike.mem_coe, Scheme.Hom.mem_preimage]
    refine Iff.trans ?_ (IsLocalRing.mem_puncturedSpectrum_iff _ p).symm
    constructor
    · rintro hp rfl
      exact hxW (by rwa [Scheme.fromSpecStalk_closedPoint] at hp)
    · intro hp
      by_contra hpW
      have hsp : X.fromSpecStalk x p ⤳ x := by
        have : X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x) := ⟨p, rfl⟩
        rwa [Scheme.range_fromSpecStalk] at this
      refine hp ((X.fromSpecStalk x).isEmbedding.injective ?_)
      rw [hgen _ hsp hpW, Scheme.fromSpecStalk_closedPoint]
  have hsq : IsPullback ((Scheme.isoOfEq _ heq).inv ≫ X.fromSpecStalk x ∣_ W)
      (IsLocalRing.puncturedSpectrum (X.presheaf.stalk x)).ι W.ι (X.fromSpecStalk x) :=
    (isPullback_morphismRestrict (X.fromSpecStalk x) W).of_iso (Scheme.isoOfEq _ heq)
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
      (by rw [Iso.refl_hom, Category.comp_id]; exact (Scheme.isoOfEq_hom_ι _ heq).symm)
      (by simp) (by simp)
  -- Purity extends the restriction of `V` to the punctured spectrum, and the extension spreads.
  obtain ⟨Y, ⟨eY⟩⟩ := ((IsLocalRing.purityHolds_iff_essSurj _).mp hx).mem_essImage
    ((pullback ((Scheme.isoOfEq _ heq).inv ≫ X.fromSpecStalk x ∣_ W)).obj V)
  obtain ⟨W', hW, hxW', V', e₁, -⟩ :=
    exists_pullback_iso_of_isPullback_fromSpecStalk hsq V Y eY
  exact ⟨W', hW, hxW', V', e₁⟩

/-- **Extension of finite étale covers across points where purity holds.** Let `U` be an open of
a Noetherian scheme `X` such that purity holds for the local ring of `X` at every point outside
`U`. Then every finite étale cover of `U` is the restriction of a finite étale cover of `X`. -/
@[stacks 0EY7]
theorem essSurj_pullback_ι_of_purityHolds {X : Scheme.{u}} [IsNoetherian X] (U : X.Opens)
    (h : ∀ x : X, x ∉ U → IsLocalRing.PurityHolds (X.presheaf.stalk x)) :
    (pullback U.ι).EssSurj := by
  refine ⟨fun V ↦ ?_⟩
  -- Among the opens containing `U` to which `V` extends, choose a maximal one by Noetherianity.
  let 𝒮 : Set X.Opens := {W | ∃ (hW : U ≤ W) (V' : FiniteEtaleScheme W),
    Nonempty ((pullback (X.homOfLE hW)).obj V' ≅ V)}
  have hU : U ∈ 𝒮 := ⟨le_rfl, V, ⟨eqToIso (by rw [Scheme.homOfLE_rfl]) ≪≫ pullbackId.app V⟩⟩
  obtain ⟨W₀, ⟨hUW₀, V₀, ⟨e₀⟩⟩, hmax⟩ := wellFounded_gt.has_min 𝒮 ⟨U, hU⟩
  -- If the maximal open were not everything, the cover would extend across a further point.
  obtain rfl : W₀ = ⊤ := by
    by_contra hne
    obtain ⟨x, hxW, hgen⟩ := exists_not_mem_forall_specializes hne
    obtain ⟨W', hW, hxW', V', ⟨e'⟩⟩ :=
      exists_extension_of_purityHolds hxW hgen (h x fun hxU ↦ hxW (hUW₀ hxU)) V₀
    refine hmax W' ⟨hUW₀.trans hW, V',
      ⟨eqToIso (by rw [← Scheme.homOfLE_homOfLE X hUW₀ hW]) ≪≫ (pullbackComp _ _).app V' ≪≫
        (pullback _).mapIso e' ≪≫ e₀⟩⟩
      (lt_of_le_of_ne hW fun hWW' ↦ hxW (hWW' ▸ hxW'))
  have hι : U.ι ≫ X.topIso.inv = X.homOfLE hUW₀ := by
    rw [← cancel_mono X.topIso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Scheme.topIso_hom, Scheme.homOfLE_ι]
  exact ⟨(pullback X.topIso.inv).obj V₀,
    ⟨(pullbackComp _ _).symm.app V₀ ≪≫ eqToIso (by rw [hι]) ≪≫ e₀⟩⟩

end Purity

end TauCeti.FiniteEtaleScheme
