/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import TauCeti.AlgebraicGeometry.Morphisms.CodimensionOne.Ramification
import TauCeti.AlgebraicGeometry.Fibers
import TauCeti.AlgebraicGeometry.FiniteEtale.Basic
import TauCeti.AlgebraicGeometry.Normalization.GenericFiber
import TauCeti.AlgebraicGeometry.ResidueField
import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk
import TauCeti.AlgebraicGeometry.Scheme.StalkSpecializes
import TauCeti.RingTheory.DiscreteValuationRing.Normalization

/-!
# Extending finite étale covers over codimension-one stalks

At a regular codimension-one point outside an open subscheme, a finite étale cover unramified in
codimension one extends over the spectrum of the stalk. This is the local extension step of
[Stacks, Lemma 58.31.2](https://stacks.math.columbia.edu/tag/0H2W). The extension is obtained by
normalizing the discrete valuation ring in the finite étale algebra on its generic point.
-/

public section

open CategoryTheory Limits
open TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} {U : X.Opens} {f : Y ⟶ U}

open TauCeti.AlgebraicGeometry.Scheme (SpecMap_stalkSpecializes_residue_fromSpecStalk)

/-- A field factor of the affine generic fibre inherits the base algebra structure through the
residue field of its image in the original cover. -/
private theorem isUnramifiedWRT_of_genericFiber (hf : f.IsUnramifiedInCodimOne)
    (ξ : CodimensionOnePoint X) (hξ : (ξ : X) ∉ U) {x : X} (hx : x ⤳ ξ)
    {S : Type u} [CommRing S] [Algebra (X.residueField x) S]
    (v : Spec (.of S) ⟶ Y) [IsPreimmersion v]
    (hv : v ≫ f ≫ U.ι = Spec.algebraMap (X.residueField x) S ≫ X.fromSpecResidueField x)
    (q : Spec (.of S)) :
    letI := q.isPrime
    letI := (X.presheaf.stalkSpecializes hx ≫ X.residue x).hom.toAlgebra
    letI : Algebra (X.presheaf.stalk ξ) S :=
      ((algebraMap (X.residueField x) S).comp (algebraMap (X.presheaf.stalk ξ) _)).toAlgebra
    TauCeti.Algebra.IsUnramifiedWRT (X.presheaf.stalk ξ) q.asIdeal.ResidueField := by
  have hx' : (f ≫ U.ι) (v q) ⤳ ξ := by
    rw [← Scheme.Hom.comp_apply v (f ≫ U.ι), hv, Scheme.Hom.comp_apply,
      Scheme.fromSpecResidueField_apply]
    exact hx
  let p : PrimeSpectrum S := q
  let := p.isPrime
  let := (X.presheaf.stalkSpecializes hx ≫ X.residue x).hom.toAlgebra
  let : Algebra (X.presheaf.stalk ξ) S :=
    ((algebraMap (X.residueField x) S).comp (algebraMap (X.presheaf.stalk ξ) _)).toAlgebra
  let ψ := X.presheaf.stalkSpecializes hx' ≫ X.residue _ ≫ (f ≫ U.ι).residueFieldMap (v q)
  let := ψ.hom.toAlgebra
  have := Hom.isIso_residueFieldMap_of_surjectiveOnStalks v (q : Spec (.of S))
  let j : (Spec (.of S)).residueField q ≅ CommRingCat.of p.asIdeal.ResidueField :=
    Scheme.Spec.residueFieldIso (.of S) q
  let i := asIso (v.residueFieldMap q) ≪≫ j
  let δ : CommRingCat.of S ⟶ CommRingCat.of p.asIdeal.ResidueField :=
    CommRingCat.ofHom (algebraMap S p.asIdeal.ResidueField)
  let σ : X.residueField x ⟶ .of S := CommRingCat.ofHom (algebraMap (X.residueField x) S)
  let φ := (X.presheaf.stalkSpecializes hx ≫ X.residue x) ≫ σ ≫ δ
  have hφ : Spec.map φ ≫ X.fromSpecStalk ξ = Spec.map δ ≫ v ≫ f ≫ U.ι := by
    dsimp only [φ]
    rw [Spec.map_comp_assoc, SpecMap_stalkSpecializes_residue_fromSpecStalk hx,
      Spec.map_comp_assoc, hv]
    rfl
  have hψ : Spec.map ψ ≫ X.fromSpecStalk ξ = Y.fromSpecResidueField (v q) ≫ f ≫ U.ι := by
    dsimp only [ψ]
    rw [← Category.assoc, Spec.map_comp_assoc, SpecMap_stalkSpecializes_residue_fromSpecStalk hx']
    exact Hom.SpecMap_residueFieldMap_fromSpecResidueField (f := f ≫ U.ι) (v q)
  have hmaps : ψ ≫ i.hom = φ := by
    apply Spec.map_inj.mp
    apply (cancel_mono (X.fromSpecStalk ξ)).mp
    rw [Spec.map_comp, Category.assoc, hψ, hφ]
    simp only [i, Iso.trans_hom, Spec.map_comp, Category.assoc, asIso_hom]
    rw [reassoc_of% (Hom.SpecMap_residueFieldMap_fromSpecResidueField v q)]
    have hj : δ ≫ j.inv = CommRingCat.ofHom (algebraMap S p.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of S) q).inv := rfl
    have hδ : Spec.map j.hom ≫ (Spec (.of S)).fromSpecResidueField q = Spec.map δ := by
      have h := Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of S) q
      calc
        _ = Spec.map j.hom ≫ Spec.map (δ ≫ j.inv) := congrArg (Spec.map j.hom ≫ ·) (by
          simpa only [hj, Spec.map_comp] using h.symm)
        _ = Spec.map δ := by
          rw [← Spec.map_comp, Category.assoc, j.inv_hom_id, Category.comp_id]
    rw [reassoc_of% hδ]
  let e : Y.residueField (v q) ≃ₐ[X.presheaf.stalk ξ] p.asIdeal.ResidueField :=
    AlgEquiv.ofRingEquiv (f := i.commRingCatIsoToRingEquiv)
      fun a ↦ ConcreteCategory.congr_hom hmaps a
  exact (TauCeti.Algebra.isUnramifiedWRT_iff_of_algEquiv e).mp
    ((isUnramifiedInCodimOne_def f).mp hf ξ hξ (v q) hx')

/-- Over the fraction field of the codimension-one stalk, the normalization of the generic
fibre gives a finite étale model. -/
private theorem exists_finiteEtale_model_of_genericFiber [IsFinite f] [Etale f]
    (hf : f.IsUnramifiedInCodimOne) (ξ : CodimensionOnePoint X) (hξ : (ξ : X) ∉ U)
    [IsRegularLocalRing (X.presheaf.stalk ξ)] {x : X} (hx : x ⤳ ξ)
    (t : Spec (X.residueField x) ⟶ U) (ht : t ≫ U.ι = X.fromSpecResidueField x) :
    let k := Spec.map (X.presheaf.stalkSpecializes hx ≫ X.residue x)
    ∃ (Z : Scheme.{u}) (p : Z ⟶ Spec (X.presheaf.stalk ξ)), IsFinite p ∧ Etale p ∧
      Nonempty (Over.mk (pullback.snd p k) ≅ Over.mk (pullback.snd f t)) := by
  let A := X.presheaf.stalk ξ
  let K := X.residueField x
  have : IsDomain A := TauCeti.IsRegularLocalRing.isDomain
  have : IsDiscreteValuationRing A := CodimensionOnePoint.isDiscreteValuationRing_stalk ξ
  let : Algebra A K := (X.presheaf.stalkSpecializes hx ≫ X.residue x).hom.toAlgebra
  have hxU : x ∈ U := by
    let z : Spec (X.residueField x) := IsLocalRing.closedPoint K
    have hz : U.ι (t z) = x := by
      rw [← Scheme.Hom.comp_apply, ht, Scheme.fromSpecResidueField_apply]
    exact hz ▸ (t z).property
  have : IsFractionRing A K :=
    TauCeti.AlgebraicGeometry.Scheme.isFractionRing_residueField_of_specializes hx
      (fun e ↦ hξ (e ▸ hxU))
  have : IsPreimmersion (t ≫ U.ι) :=
    ht ▸ inferInstanceAs (IsPreimmersion (X.fromSpecResidueField x))
  have : IsPreimmersion t := IsPreimmersion.of_comp t U.ι
  obtain ⟨S, ⟨e⟩⟩ := (pullback.snd f t).exists_finiteEtale_algebra
  let v := e.hom.left ≫ pullback.fst f t
  have : IsIso e.hom.left := Functor.map_isIso (Over.forget _) e.hom
  have : IsPreimmersion v := inferInstanceAs (IsPreimmersion (e.hom.left ≫ pullback.fst f t))
  have hv : v ≫ f ≫ U.ι = Spec.algebraMap K S.obj ≫ X.fromSpecResidueField x := by
    simp only [v, Category.assoc, pullback.condition_assoc, ← ht]
    have he : e.hom.left ≫ pullback.snd f t = Spec.algebraMap K S.obj := Over.w e.hom
    rw [← Category.assoc, he]
  let : Algebra A S.obj := ((algebraMap K S.obj).comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K S.obj := .of_algebraMap_eq' rfl
  have : Algebra.Etale A (integralClosure A S.obj) :=
    (TauCeti.Algebra.etale_integralClosure_iff_forall_residueField A K S.obj).mpr fun q ↦
      isUnramifiedWRT_of_genericFiber hf ξ hξ hx v hv q
  have : Module.Finite A (integralClosure A S.obj) := Algebra.IsIntegral.finite
  exact ⟨_, Spec.algebraMap A (integralClosure A S.obj),
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance),
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance),
    ⟨integralClosureGenericFiberIso A K S.obj ≪≫ e⟩⟩

/-- The inverse image of the open at the spectrum of a codimension-one stalk outside it has at
most one point. -/
private theorem subsingleton_preimage_fromSpecStalk (ξ : CodimensionOnePoint X) (hξ : (ξ : X) ∉ U)
    [IsRegularLocalRing (X.presheaf.stalk ξ)] :
    Subsingleton (X.fromSpecStalk ξ ⁻¹ᵁ U).toScheme := by
  let A := X.presheaf.stalk ξ
  let W := X.fromSpecStalk ξ ⁻¹ᵁ U
  have : IsDomain A := TauCeti.IsRegularLocalRing.isDomain
  have : IsDiscreteValuationRing A := CodimensionOnePoint.isDiscreteValuationRing_stalk ξ
  have eqbot (a : W.toScheme) : (W.ι a : PrimeSpectrum A).asIdeal = ⊥ := by
    by_contra hn
    have he := IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hn
      (W.ι a : PrimeSpectrum A).isPrime)
    have hh : W.ι a = IsLocalRing.closedPoint A := PrimeSpectrum.ext he
    exact hξ (Scheme.fromSpecStalk_closedPoint (x := (ξ : X)) ▸ hh ▸ a.property)
  exact ⟨fun a b ↦ Subtype.ext (PrimeSpectrum.ext ((eqbot a).trans (eqbot b).symm))⟩

/-- Extend over the spectrum of a regular codimension-one stalk at a point outside the open. -/
private theorem exists_finiteEtale_extension_fromSpecStalk_of_notMem [IsFinite f] [Etale f]
    (hf : f.IsUnramifiedInCodimOne) (ξ : CodimensionOnePoint X) (hξ : (ξ : X) ∉ U)
    [IsRegularLocalRing (X.presheaf.stalk ξ)] :
    let g := X.fromSpecStalk ξ
    ∃ (Z : Scheme.{u}) (p : Z ⟶ Spec (X.presheaf.stalk ξ)), IsFinite p ∧ Etale p ∧
      Nonempty (Over.mk (pullback.snd p (g ⁻¹ᵁ U).ι) ≅ Over.mk (pullback.snd f (g ∣_ U))) := by
  let A := X.presheaf.stalk ξ
  have : IsDomain A := TauCeti.IsRegularLocalRing.isDomain
  have : IsDiscreteValuationRing A := CodimensionOnePoint.isDiscreteValuationRing_stalk ξ
  let g := X.fromSpecStalk ξ
  let W := g ⁻¹ᵁ U
  rcases isEmpty_or_nonempty W.toScheme with hW | ⟨⟨w⟩⟩
  · let p := pullback.snd f (g ∣_ U)
    exact ⟨_, 𝟙 (Spec A), inferInstance, inferInstance, ⟨Over.isoMk
      (asIso (pullback.snd (𝟙 (Spec A)) W.ι) ≪≫ (asIso p).symm) (by simp [p]; rfl)⟩⟩
  let x := g (W.ι w)
  have hxU : x ∈ U := w.property
  have hx : x ⤳ ξ := by
    exact (Scheme.range_fromSpecStalk (x := (ξ : X))).le ⟨W.ι w, rfl⟩
  let K := X.residueField x
  let : Algebra A K := (X.presheaf.stalkSpecializes hx ≫ X.residue x).hom.toAlgebra
  have : IsFractionRing A K :=
    TauCeti.AlgebraicGeometry.Scheme.isFractionRing_residueField_of_specializes hx
      (fun e ↦ hξ (e ▸ hxU))
  let k := Spec.algebraMap A K
  have hkg : k ≫ g = X.fromSpecResidueField x := SpecMap_stalkSpecializes_residue_fromSpecStalk hx
  have hkW : Set.range k ⊆ W := by
    rintro _ ⟨z, rfl⟩
    exact (show g (k z) ∈ U from by rw [← Scheme.Hom.comp_apply, hkg,
      Scheme.fromSpecResidueField_apply]; exact hxU)
  let i := IsOpenImmersion.lift W.ι k (by rwa [Scheme.Opens.range_ι])
  have hi : i ≫ W.ι = k := IsOpenImmersion.lift_fac ..
  have : IsOpenImmersion k := TauCeti.isOpenImmersion_Spec_map_fractionRing A K
  have : IsOpenImmersion (i ≫ W.ι) := hi ▸ ‹IsOpenImmersion k›
  have : IsOpenImmersion i := IsOpenImmersion.of_comp i W.ι
  have : Subsingleton W.toScheme := subsingleton_preimage_fromSpecStalk ξ hξ
  have hiiso : IsIso i := isIso_of_isOpenImmersion_of_opensRange_eq_top i (by
    apply TopologicalSpace.Opens.ext
    ext z
    exact ⟨fun _ ↦ trivial, fun _ ↦ ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ z⟩⟩)
  let t := i ≫ (g ∣_ U)
  have ht : t ≫ U.ι = X.fromSpecResidueField x := by
    dsimp only [t]
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hi, hkg]
  obtain ⟨Z, p, hp, hp', ⟨e⟩⟩ := exists_finiteEtale_model_of_genericFiber hf ξ hξ hx t ht
  let ec : (Over.pullback (i ≫ W.ι)).obj (Over.mk p) ≅ Over.mk (pullback.snd p k) :=
    Over.isoMk (pullback.congrHom rfl hi) (by simp)
  let ei := (Over.pullbackComp i W.ι).symm.app (Over.mk p) ≪≫ ec ≪≫ e ≪≫
    (Over.pullbackComp i (g ∣_ U)).app (Over.mk f)
  let forgetPullback (q : Over W.toScheme) :
      (Over.map i).obj ((Over.pullback i).obj q) ≅ q :=
    Over.isoMk (asIso (pullback.fst q.hom i)) pullback.condition
  exact ⟨Z, p, hp, hp', ⟨(forgetPullback _).symm ≪≫ (Over.map i).mapIso ei ≪≫ forgetPullback _⟩⟩

/-- If a finite étale cover is unramified in codimension one, its pullback to the inverse image
of the open in the spectrum of a regular codimension-one stalk extends over that spectrum.
This is the local extension step in Stacks, Lemma 58.31.2 (0H2W). -/
theorem IsUnramifiedInCodimOne.exists_finiteEtale_extension_fromSpecStalk [IsFinite f] [Etale f]
    (hf : f.IsUnramifiedInCodimOne) (ξ : CodimensionOnePoint X)
    (hreg : (ξ : X) ∉ U → IsRegularLocalRing (X.presheaf.stalk ξ)) :
    let g := X.fromSpecStalk ξ
    ∃ (Z : Scheme.{u}) (p : Z ⟶ Spec (X.presheaf.stalk ξ)), IsFinite p ∧ Etale p ∧
      Nonempty (Over.mk (pullback.snd p (g ⁻¹ᵁ U).ι) ≅ Over.mk (pullback.snd f (g ∣_ U))) := by
  by_cases hξ : (ξ : X) ∈ U
  · let g := X.fromSpecStalk ξ
    let W := g ⁻¹ᵁ U
    have hW : W = ⊤ := by
      apply top_unique
      intro z _
      have hs : g z ⤳ ξ := (Scheme.range_fromSpecStalk (x := (ξ : X))).le ⟨z, rfl⟩
      exact hs.mem_open U.isOpen hξ
    have : IsIso W.ι := isIso_of_isOpenImmersion_of_opensRange_eq_top W.ι (by simp [hW])
    let q := pullback.snd f (g ∣_ U)
    have hpb : IsPullback (𝟙 _) q (q ≫ W.ι) W.ι := .of_horiz_isIso ⟨by simp⟩
    exact ⟨_, q ≫ W.ι, inferInstance, inferInstance,
      ⟨(Over.isoMk hpb.isoPullback hpb.isoPullback_hom_snd).symm⟩⟩
  · have := hreg hξ
    exact exists_finiteEtale_extension_fromSpecStalk_of_notMem hf ξ hξ

end AlgebraicGeometry.Scheme.Hom
