/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.PuncturedSpectrum
import Mathlib.RingTheory.Regular.Flat
import TauCeti.AlgebraicGeometry.AffineScheme.Basic
import TauCeti.AlgebraicGeometry.FiniteEtale.Henselian
import TauCeti.AlgebraicGeometry.Pullback.SpecMap
import TauCeti.AlgebraicGeometry.PuncturedSpectrum.Sections
import TauCeti.RingTheory.AdicCompletion.Finite
import TauCeti.RingTheory.Depth.WeaklyRegular
import TauCeti.RingTheory.Etale.HartogsLifting
import TauCeti.RingTheory.QuotSMulTop
import TauCeti.RingTheory.Regular.Monomial

/-!
# Finite étale extension from a hypersurface in a complete local ring

A finite étale cover of a punctured spectrum extends if its restriction to a hypersurface
section extends, provided the local ring is complete along the defining nonzerodivisor and
the hypersurface has depth at least two.

The argument lifts an extension of the cover over the hypersurface by henselianity. The
isomorphism on the punctured hypersurface then lifts to a morphism on the punctured spectrum
by algebraic Hartogs and `Ideal.existsUnique_lift_of_isAdicComplete`. Restriction to the
punctured hypersurface reflects isomorphisms, so the lifted morphism is an isomorphism.

## References

* [Stacks Project, Lemma 58.20.7](https://stacks.math.columbia.edu/tag/0BLM).
* T. Dupuy, T. Tucker and Z. Wang,
  [HypersurfaceLiftingComplete.lean](https://github.com/tdupu/pcfawd-formalization/blob/d28f90d/library/Pcf/Stacks/Purity/HypersurfaceLiftingComplete.lean)
  (Apache-2.0), for the argument by lifting a morphism out of a cover which extends.
-/

public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing RingTheory.Sequence
open scoped TensorProduct

universe u

namespace TauCeti.IsLocalRing

variable {A B C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]

omit [IsNoetherianRing A] in
private lemma etale_localizationAway_of_etale_puncturedSpectrum {a : A}
    (ha : a ∈ maximalIdeal A)
    [Etale (pullback.snd (Spec.algebraMap A C) (puncturedSpectrum A).ι)] :
    Algebra.Etale A (Localization.Away (algebraMap A C a)) := by
  let p := Spec.algebraMap A C
  let i := Spec.algebraMap C (Localization.Away (algebraMap A C a))
  have hi : Set.range i ⊆ (p ⁻¹ᵁ puncturedSpectrum A : Set _) := by
    have h : Set.range i = (PrimeSpectrum.basicOpen (algebraMap A C a) : Set (PrimeSpectrum C)) :=
      PrimeSpectrum.localization_away_comap_range _ (algebraMap A C a)
    rw [h]
    intro x hx
    refine (mem_preimage_puncturedSpectrum_iff A x).mpr fun he ↦ hx ?_
    have hm : a ∈ x.asIdeal.under A := he.symm ▸ ha
    exact (Ideal.mem_comap (f := algebraMap A C)).mp hm
  let i' := IsOpenImmersion.lift (p ⁻¹ᵁ puncturedSpectrum A).ι i
    (by simpa using hi)
  have hi' : IsOpenImmersion i' := by
    have : IsOpenImmersion (i' ≫ (p ⁻¹ᵁ puncturedSpectrum A).ι) := by
      rw [IsOpenImmersion.lift_fac]
      infer_instance
    exact .of_comp i' (p ⁻¹ᵁ puncturedSpectrum A).ι
  have h : Etale (p ∣_ puncturedSpectrum A) := by
    rw [morphismRestrict]
    exact inferInstanceAs (Etale ((pullbackRestrictIsoRestrict p (puncturedSpectrum A)).inv ≫
      pullback.snd (Spec.algebraMap A C) (puncturedSpectrum A).ι))
  have he : Etale (i ≫ p) := by
    rw [← IsOpenImmersion.lift_fac (p ⁻¹ᵁ puncturedSpectrum A).ι i (by simpa using hi),
      Category.assoc, ← morphismRestrict_ι]
    infer_instance
  exact RingHom.etale_algebraMap.mp <| (HasRingHomProperty.Spec_iff (P := @Etale)).mp <| by
    simpa [i, p, Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      IsScalarTower.algebraMap_eq A C (Localization.Away (algebraMap A C a))] using he

private lemma exists_lift_of_etale_puncturedSpectrum [Module.Finite A B] [Module.Flat A B]
    {f a b : A} [IsAdicComplete (Ideal.span {f}) A]
    (ha : a ∈ maximalIdeal A) (hb : b ∈ maximalIdeal A) (hreg : IsWeaklyRegular A [f, a, b])
    [Etale (pullback.snd (Spec.algebraMap A C) (puncturedSpectrum A).ι)]
    (g₀ : C →ₐ[A] B ⧸ (Ideal.span {f}).map (algebraMap A B)) :
    ∃ g : C →ₐ[A] B, (Ideal.Quotient.mkₐ A _).comp g = g₀ := by
  let I : Ideal A := Ideal.span {f}
  let J := I.map (algebraMap A B)
  have : IsAdicComplete I B := IsAdicComplete.of_finite I B
  have : IsAdicComplete J B := (IsAdicComplete.map_algebraMap_iff I B).mpr ‹_›
  have : Algebra.Etale A (Localization.Away (algebraMap A C a)) :=
    etale_localizationAway_of_etale_puncturedSpectrum ha
  have : Algebra.Etale A (Localization.Away (algebraMap A C b)) :=
    etale_localizationAway_of_etale_puncturedSpectrum hb
  have hpow (n : ℕ) : IsWeaklyRegular (B ⧸ J ^ (n + 1)) [a, b] := by
    let K : Ideal A := I ^ (n + 1)
    have hA : IsWeaklyRegular (A ⧸ K) [a, b] := by
      have h := ((isWeaklyRegular_cons_iff A (f ^ (n + 1)) [a, b]).mp
        (hreg.pow_cons n.succ_ne_zero)).2
      have hK : Ideal.span {f ^ (n + 1)} = K := (Ideal.span_singleton_pow _ _).symm
      have e : QuotSMulTop (f ^ (n + 1)) A ≃ₗ[A] A ⧸ K :=
        (Submodule.quotEquivOfEq _ _ (by rw [← hK, Submodule.ideal_span_singleton_smul])).trans
          ((Ideal.quotSMulTopSelfEquiv K).restrictScalars A)
      exact (e.isWeaklyRegular_congr _).mp h
    have hB : IsWeaklyRegular (B ⧸ K.map (algebraMap A B)) [a, b] := by
      let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B K
      have hbase := (isWeaklyRegular_map_algebraMap_iff (A ⧸ K) (A ⧸ K) [a, b]).2 hA
      have hflat := (isWeaklyRegular_map_algebraMap_iff ((A ⧸ K) ⊗[A] B) _ _).mp hbase.of_flat
      exact (isWeaklyRegular_map_algebraMap_iff (A ⧸ K) _ _).mp
        ((e.toLinearEquiv.isWeaklyRegular_congr _).mpr hflat)
    rw [← Ideal.map_pow]
    exact hB
  exact (J.existsUnique_lift_of_isAdicComplete hpow g₀).exists

omit [IsLocalRing A] [IsNoetherianRing A] in
/-- Use Hartogs to extend a morphism from the punctured hypersurface to the affine hypersurface,
then lift its ring map and restrict back to the punctured hypersurface. -/
private lemma exists_overHom_lift_quotient (I : Ideal A) [IsLocalRing (A ⧸ I)]
    (hΓ : IsIso (pullback.fst (Spec.algebraMap (A ⧸ I) (B ⧸ I.map (algebraMap A B)))
      (puncturedSpectrum (A ⧸ I)).ι).appTop)
    (hlift : ∀ g₀ : C →ₐ[A] B ⧸ I.map (algebraMap A B),
      ∃ g : C →ₐ[A] B, (Ideal.Quotient.mkₐ A _).comp g = g₀) :
    let Y := (algSpec (.of A)).obj (.op (CommAlgCat.of A B))
    let Z := (algSpec (.of A)).obj (.op (CommAlgCat.of A C))
    let F := Over.pullback (Spec.algebraMap A (A ⧸ I)) ⋙ Over.pullback (puncturedSpectrum (A ⧸ I)).ι
    ∀ α : F.obj Y ⟶ F.obj Z, ∃ g : Y ⟶ Z, F.map g = α := by
  intro Y Z F α
  let J := I.map (algebraMap A B)
  let j₀ := (puncturedSpectrum (A ⧸ I)).ι
  let q := Spec.algebraMap A (A ⧸ I)
  let p₀ := Spec.algebraMap (A ⧸ I) (B ⧸ J)
  let H := TauCeti.AlgebraicGeometry.isPullback_SpecMap_quotient A B I
  let e : Over.mk p₀ ≅ (Over.pullback q).obj Y := Over.isoMk H.isoPullback H.isoPullback_hom_snd
  let Z₀ := (Over.pullback q).obj Z
  have : IsAffineHom Z₀.hom := inferInstanceAs (IsAffineHom (pullback.snd (Spec.algebraMap A C) q))
  have : IsAffine Z₀.left := isAffine_of_isAffineHom Z₀.hom
  obtain ⟨φ, hφ⟩ := (TauCeti.AlgebraicGeometry.overPullback_map_bijective_of_isIso_appTop j₀
    (Y := Over.mk p₀) (Y' := Z₀) hΓ).surjective ((Over.pullback j₀).map e.hom ≫ α)
  have hφw : φ.left ≫ pullback.snd Z.hom q = p₀ := Over.w φ
  have hp₀ : p₀ ≫ q = Spec.algebraMap A (B ⧸ J) := by
    simp only [p₀, q, Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← IsScalarTower.algebraMap_eq A (A ⧸ I) (B ⧸ J)]
  let ψ : (algSpec (.of A)).obj (.op (CommAlgCat.of A (B ⧸ J))) ⟶ Z :=
    Over.homMk (φ.left ≫ pullback.fst Z.hom q) (calc
      (φ.left ≫ pullback.fst Z.hom q) ≫ Z.hom =
          (φ.left ≫ pullback.snd Z.hom q) ≫ q := by simp only [Category.assoc, pullback.condition]
      _ = p₀ ≫ q := by rw [hφw]
      _ = _ := hp₀)
  let m := (algSpec.fullyFaithful (R := .of A)).preimage ψ
  obtain ⟨g, hg⟩ := hlift m.unop.hom
  let g' : Y ⟶ Z := (algSpec (.of A)).map (CommAlgCat.ofHom g).op
  have hmap : e.hom ≫ (Over.pullback q).map g' = φ := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have hfst : ((Over.pullback q).map g').left ≫ pullback.fst Z.hom q =
          pullback.fst Y.hom q ≫ g'.left := pullback.lift_fst _ _ _
      have he : e.hom.left ≫ pullback.fst Y.hom q = _ := H.isoPullback_hom_fst
      rw [Over.comp_left_assoc, hfst, ← Category.assoc, he]
      have hm : Spec.map (CommRingCat.ofHom m.unop.hom.toRingHom) =
          φ.left ≫ pullback.fst Z.hom q :=
        congrArg (fun k ↦ k.left) ((algSpec.fullyFaithful (R := .of A)).map_preimage ψ)
      have hg' : g'.left = Spec.map (CommRingCat.ofHom g.toRingHom) := rfl
      have heq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫
          Spec.map (CommRingCat.ofHom g.toRingHom) =
          Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mkₐ A J).comp g).toRingHom) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        rfl
      exact (congrArg (fun k ↦ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ k) hg').trans
        (heq.trans ((congrArg (fun k ↦ Spec.map (CommRingCat.ofHom k.toRingHom)) hg).trans hm))
    · exact (Over.w (e.hom ≫ (Over.pullback q).map g')).trans (Over.w φ).symm
  refine ⟨g', (cancel_epi ((Over.pullback j₀).map e.hom)).mp ?_⟩
  dsimp only [F, Functor.comp_map]
  rw [← Functor.map_comp, hmap]
  exact hφ

private lemma exists_overHom_lift_hypersurface [Module.Finite A B] [Module.Flat A B]
    {f : A} [IsAdicComplete (Ideal.span {f}) A] [IsLocalRing (A ⧸ Ideal.span {f})]
    (hreg : IsSMulRegular A f)
    (hdepth₀ : 2 ≤ depth (ModuleCat.of (A ⧸ Ideal.span {f}) (A ⧸ Ideal.span {f})))
    [Etale (pullback.snd (Spec.algebraMap A C) (puncturedSpectrum A).ι)] :
    let I := Ideal.span {f}
    let Y := (algSpec (.of A)).obj (.op (CommAlgCat.of A B))
    let Z := (algSpec (.of A)).obj (.op (CommAlgCat.of A C))
    let F := Over.pullback (Spec.algebraMap A (A ⧸ I)) ⋙ Over.pullback (puncturedSpectrum (A ⧸ I)).ι
    ∀ α : F.obj Y ⟶ F.obj Z, ∃ g : Y ⟶ Z, F.map g = α := by
  let I : Ideal A := Ideal.span {f}
  let A₀ := A ⧸ I
  -- A regular pair on the hypersurface both recovers sections and lifts the ring map.
  let eQuot : QuotSMulTop f A ≃ₗ[A] A₀ :=
    (Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul f ⊤).symm).trans
      ((Ideal.quotSMulTopSelfEquiv I).restrictScalars A)
  obtain ⟨rs, hlen, hmem, hab⟩ := _root_.IsLocalRing.exists_isWeaklyRegular_of_le_depth
    (ModuleCat.of A₀ A₀) (n := 2) hdepth₀
  obtain ⟨a₀, b₀, rfl⟩ := List.length_eq_two.mp hlen
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) a₀
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) b₀
  have hm : IsLocalHom (algebraMap A A₀) := .of_surjective _ Ideal.Quotient.mk_surjective
  have ha₀ := hmem (Ideal.Quotient.mk I a) (by simp)
  have hb₀ := hmem (Ideal.Quotient.mk I b) (by simp)
  have hmem₀ {x : A} (hx : Ideal.Quotient.mk I x ∈ maximalIdeal A₀) : x ∈ maximalIdeal A := by
    rw [← maximalIdeal_comap (f := algebraMap A A₀)]
    exact hx
  have hr : IsWeaklyRegular A [f, a, b] := by
    rw [isWeaklyRegular_cons_iff]
    exact ⟨hreg, (eQuot.isWeaklyRegular_congr _).mpr
      ((isWeaklyRegular_map_algebraMap_iff A₀ A₀ _).mp hab)⟩
  let J := I.map (algebraMap A B)
  have : Module.Flat A₀ (B ⧸ J) := Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).toLinearEquiv
  have hD {t : A₀} (ht : t ∈ maximalIdeal A₀) :
      PrimeSpectrum.basicOpen t ≤ puncturedSpectrum A₀ := fun x hx ↦
    (mem_puncturedSpectrum_iff A₀ x).mpr fun hx' ↦ hx (hx' ▸ ht)
  have hΓ := TauCeti.AlgebraicGeometry.isIso_appTop_pullback_fst_ι_of_isWeaklyRegular
    (B ⧸ J) (puncturedSpectrum A₀) hab (hD ha₀) (hD hb₀)
  exact exists_overHom_lift_quotient I hΓ
    (exists_lift_of_etale_puncturedSpectrum (hmem₀ ha₀) (hmem₀ hb₀) hr)

private lemma nonempty_iso_restrictPunctured_of_iso_quotient {f : A}
    [IsAdicComplete (Ideal.span {f}) A] [IsLocalRing (A ⧸ Ideal.span {f})]
    (hreg : IsSMulRegular A f) (hdepth : 2 ≤ depth (ModuleCat.of A A))
    (hdepth₀ : 2 ≤ depth (ModuleCat.of (A ⧸ Ideal.span {f}) (A ⧸ Ideal.span {f})))
    (B : (CommAlgCat.FiniteEtale.{u} (CommRingCat.of A))ᵒᵖ)
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme)
    (e : (restrictPuncturedQuotient (Ideal.span {f})).obj
      ((restrictPunctured A).obj ((FiniteEtaleScheme.spec (.of A)).obj B)) ≅
      (restrictPuncturedQuotient (Ideal.span {f})).obj V) :
    Nonempty ((restrictPunctured A).obj ((FiniteEtaleScheme.spec (.of A)).obj B) ≅ V) := by
  let I : Ideal A := Ideal.span {f}
  let A₀ := A ⧸ I
  let j := (puncturedSpectrum A).ι
  let j₀ := (puncturedSpectrum A₀).ι
  let q := Spec.algebraMap A A₀
  have hq : ((maximalIdeal A).map (algebraMap A A₀)).radical = maximalIdeal A₀ :=
    radical_map_maximalIdeal_of_surjective (Ideal.Quotient.algebraMap_eq I ▸
      Ideal.Quotient.mk_surjective)
  let r := q.resLE (puncturedSpectrum A) (puncturedSpectrum A₀) (preimage_puncturedSpectrum hq).ge
  let Y := (FiniteEtaleScheme.spec (.of A)).obj B
  let W := (algSpec (.of A)).obj (.op (CommAlgCat.of A B.unop.obj))
  let eY : W ≅ Y.obj := eqToIso (FiniteEtaleScheme.spec_obj_obj (.of A) B).symm
  let C := Γ(V.obj.left, ⊤)
  let : Algebra A C := ((Scheme.ΓSpecIso (.of A)).inv ≫ (V.obj.hom ≫ j).appTop).hom.toAlgebra
  let Z := (algSpec (.of A)).obj (.op (CommAlgCat.of A C))
  let H := (isPullback_puncturedSpectrum_toSpecΓ A hdepth V.obj.hom).flip
  let eC : (Over.pullback j).obj Z ≅ V.obj := Over.isoMk H.isoPullback.symm H.isoPullback_inv_snd
  have : Etale (pullback.snd (Spec.algebraMap A C) j) := by
    have : IsIso eC.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eC.hom))
    have : Etale eC.hom.left := inferInstance
    have h : eC.hom.left ≫ V.obj.hom = pullback.snd (Spec.algebraMap A C) j := Over.w eC.hom
    rw [← h]
    exact Etale.etale_comp eC.hom.left V.obj.hom
  have hcomm : r ≫ j = j₀ ≫ q := Scheme.Hom.resLE_comp_ι _ _
  let β : Over.pullback j ⋙ Over.pullback r ≅ Over.pullback q ⋙ Over.pullback j₀ :=
    (Over.pullbackComp r j).symm ≪≫ eqToIso (congrArg (fun k ↦ Over.pullback k) hcomm) ≪≫
      Over.pullbackComp j₀ q
  let α := (β.app W).symm ≪≫ (Over.pullback j ⋙ Over.pullback r).mapIso eY ≪≫
    (finiteEtaleSchemeProperty _).ι.mapIso e ≪≫
    ((Over.pullback r).mapIso eC).symm ≪≫ β.app Z
  obtain ⟨g, hg⟩ := exists_overHom_lift_hypersurface hreg hdepth₀ α.hom
  let gV : (restrictPunctured A).obj Y ⟶ V :=
    ObjectProperty.homMk ((Over.pullback j).map (eY.inv ≫ g) ≫ eC.hom)
  have : IsIso ((Over.pullback r).map ((Over.pullback j).map g)) := by
    have : IsIso ((Over.pullback r).map ((Over.pullback j).map g) ≫ β.hom.app Z) := by
      rw [← Functor.comp_map, β.hom.naturality, hg]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (β.hom.app Z)
  have : IsIso ((restrictPuncturedQuotient I).map gV) := by
    apply (ObjectProperty.isIso_hom_iff _).mp
    have h : IsIso ((Over.pullback r).map ((Over.pullback j).map (eY.inv ≫ g) ≫ eC.hom)) := by
      simp only [Functor.map_comp]
      infer_instance
    exact h
  have : (restrictPuncturedQuotient I).ReflectsIsomorphisms :=
    pullbackPunctured_reflectsIsomorphisms hq hdepth (dense_compl_singleton_closedPoint_iff.mp
      (dense_compl_singleton_closedPoint_of_one_le_depth (one_le_two.trans hdepth₀)))
  have : IsIso gV := isIso_of_reflects_iso gV (restrictPuncturedQuotient I)
  exact ⟨asIso gV⟩

/-- A finite étale cover of the punctured spectrum of a Noetherian local ring extends if its
restriction to a hypersurface section extends, when the defining element is regular, the ring
is complete along it, and the quotient has depth at least two. -/
@[stacks 0BLM "for a complete local ring along a nonzerodivisor"]
theorem extends_of_extends_quotient_of_isAdicComplete {f : A} (hreg : IsSMulRegular A f)
    [IsAdicComplete (Ideal.span {f}) A]
    [IsLocalRing (A ⧸ Ideal.span {f})]
    (hdepth₀ : 2 ≤ depth (ModuleCat.of (A ⧸ Ideal.span {f}) (A ⧸ Ideal.span {f})))
    (V : FiniteEtaleScheme (puncturedSpectrum A).toScheme)
    (hV : ∃ Y₀ : FiniteEtaleScheme (Spec (.of (A ⧸ Ideal.span {f}))),
      Nonempty ((restrictPunctured (A ⧸ Ideal.span {f})).obj Y₀ ≅
        (restrictPuncturedQuotient (Ideal.span {f})).obj V)) :
    ∃ Y : FiniteEtaleScheme (Spec (.of A)), Nonempty ((restrictPunctured A).obj Y ≅ V) := by
  let I : Ideal A := Ideal.span {f}
  let A₀ := A ⧸ I
  have hI : I ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp (inferInstance : Nontrivial A₀)
  have hf : f ∈ maximalIdeal A := le_maximalIdeal hI (Ideal.mem_span_singleton_self f)
  let q := Spec.algebraMap A A₀
  have hq : ((maximalIdeal A).map (algebraMap A A₀)).radical = maximalIdeal A₀ :=
    radical_map_maximalIdeal_of_surjective (Ideal.Quotient.algebraMap_eq I ▸
      Ideal.Quotient.mk_surjective)
  let eQuot : QuotSMulTop f A ≃ₗ[A] A₀ :=
    (Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul f ⊤).symm).trans
      ((Ideal.quotSMulTopSelfEquiv I).restrictScalars A)
  have hdepth : 2 ≤ depth (ModuleCat.of A A) := by
    have k := depth_quotSMulTop_succ_eq_depth hreg hf
    rw [depth_eq_of_linearEquiv eQuot,
      depth_eq_depth_of_surjective (R := A) (Ideal.Quotient.mk_surjective (I := I))] at k
    exact hdepth₀.trans (le_self_add.trans_eq k)
  obtain ⟨Y₀, ⟨e₀⟩⟩ := hV
  have : HenselianRing A I := IsAdicComplete.henselianRing A I
  have : (FiniteEtaleScheme.pullback q).EssSurj := by
    dsimp only [q, Spec.algebraMap]
    rw [Ideal.Quotient.algebraMap_eq]
    infer_instance
  have : (FiniteEtaleScheme.spec (.of A)).EssSurj := by
    rw [← FiniteEtaleScheme.finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme_functor]
    infer_instance
  let F := FiniteEtaleScheme.spec (.of A) ⋙ FiniteEtaleScheme.pullback q
  obtain ⟨B, ⟨eB⟩⟩ := Functor.EssSurj.mem_essImage F Y₀
  let Y := (FiniteEtaleScheme.spec (.of A)).obj B
  let e := ((restrictPuncturedCompPullbackIso hq).app Y) ≪≫
    (restrictPunctured A₀).mapIso eB ≪≫ e₀
  exact ⟨Y, nonempty_iso_restrictPunctured_of_iso_quotient hreg hdepth hdepth₀ B V e⟩

end TauCeti.IsLocalRing
