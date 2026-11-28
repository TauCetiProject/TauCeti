/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Tilde.Hartogs
public import TauCeti.AlgebraicGeometry.PuncturedSpectrum
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Regular.Flat
import TauCeti.AlgebraicGeometry.AffineScheme.Basic
import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.AlgebraicGeometry.Pullback.SpecMap
import TauCeti.AlgebraicGeometry.Scheme.SpecOver
import TauCeti.RingTheory.CohenMacaulay.Normal
import TauCeti.RingTheory.Depth.WeaklyRegular
import TauCeti.RingTheory.IntegralClosure.GoingDown
import TauCeti.RingTheory.KrullDimension.Fiber
import TauCeti.RingTheory.Localization.Module

/-!
# Sections of `Spec B` over the preimage of a punctured spectrum

Let `A` be a local ring with maximal ideal `𝔪`, let `B` be an `A`-algebra, and let `W` be an open
subset of `Spec B` containing every prime of `B` not lying over `𝔪`; for instance the preimage of
the punctured spectrum `Spec A ∖ {𝔪}`. This file gives conditions under which restriction
`Γ(Spec B, 𝒪) → Γ(W, 𝒪)` is bijective, so that `B` is recovered from the sections over `W`:

* `B` is flat over a Noetherian `A` of depth at least two. A weakly regular pair in `𝔪` stays
  weakly regular on `B`, and its basic opens lie in `W`.
* `B` is integral over `A`, Noetherian, and of depth at least two at each maximal ideal. The
  primes outside `W` lie over `𝔪`, hence are maximal, so this is the algebraic Hartogs principle
  for `Spec B`.
* `A` is a Noetherian integrally closed local domain of dimension at least two and `B` is a finite
  torsion-free `A`-algebra whose localizations at maximal ideals are normal domains. By going
  down, these localizations have the dimension of `A`, so they have depth at least two by the
  `(S₂)` property of normal local domains.

These results are the section-recovery input used by Stacks, Lemmas 58.20.2 (0BLK) and 58.20.3
(0BM9); no statement here mentions étale covers. When `A` has depth at least two, the first case
recovers a finite étale `A`-algebra as the ring of sections of its spectrum over the preimage of
the punctured spectrum, as needed for 0BLK. The last case is the corresponding step of a corrected
form of 0BM9: Stacks omits the hypothesis that `B` is torsion-free over `A`, without which 0BM9 is
false (for `B = A × A/𝔪` the sections over the preimage of the punctured spectrum are just `A`),
so the theorem assumes `Module.IsTorsionFree A B`.

For an affine scheme over the punctured spectrum of a Noetherian local ring of depth at least
two, the morphism on spectra of global sections restricts to the original scheme. This is
`TauCeti.AlgebraicGeometry.Spec.isPullback_toSpecΓ_of_isPushout` once the global sections of the
punctured base are identified with the local ring.

In the finite normal case, the same bijectivity says that the base change of `Spec B` to the
punctured spectrum of `A` has `B` as its ring of global functions.

## Main results

* `TauCeti.AlgebraicGeometry.Spec.presheaf_map_leTop_bijective_of_flat`: the flat case.
* `TauCeti.IsLocalRing.isIso_appTop_ι_puncturedSpectrum`: the case `B = A`, as an isomorphism
  from the functions on `Spec A` to those on its punctured spectrum.
* `TauCeti.IsLocalRing.isPullback_puncturedSpectrum_toSpecΓ`: reconstruction of an affine
  scheme over the puncture by restricting the spectrum of its sections.
* `TauCeti.AlgebraicGeometry.Spec.presheaf_map_leTop_bijective_of_isIntegral`: the integral case,
  an affine form of Stacks, Lemma 58.20.1 (0BM8).
* `TauCeti.AlgebraicGeometry.Spec.presheaf_map_leTop_bijective_of_isIntegrallyClosed`: the finite
  normal case.
* `TauCeti.IsLocalRing.exists_overHom_lift_quotient`: section recovery on a punctured quotient
  and lifting algebra homomorphisms across the quotient lift morphisms of affine schemes.
* `TauCeti.IsLocalRing.isIso_appTop_pullback_fst_puncturedSpectrum`: the finite normal case,
  as recovery of `B` from the base change of `Spec B` to the punctured spectrum.

## References

* [Stacks Project, Lemma 58.20.1](https://stacks.math.columbia.edu/tag/0BM8).
* [Stacks Project, Lemma 58.20.2](https://stacks.math.columbia.edu/tag/0BLK).
* [Stacks Project, Lemma 58.20.3](https://stacks.math.columbia.edu/tag/0BM9).
* [Stacks Project, Lemma 31.5.11](https://stacks.math.columbia.edu/tag/0E9I).
-/

public section

universe u

open CategoryTheory Opposite TopologicalSpace IsLocalRing RingTheory.Sequence
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.StructureSheaf

namespace TauCeti.AlgebraicGeometry.Spec

variable {A : Type*} {B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Let `B` be a flat algebra over a Noetherian local ring `A` of depth at least two, and `W` an
open subset of `Spec B` containing every prime not lying over the maximal ideal of `A`. Then
restriction of sections of `Spec B` from `Spec B` to `W` is bijective. -/
theorem presheaf_map_leTop_bijective_of_flat [IsLocalRing A] [IsNoetherianRing A]
    [Module.Flat A B] (hdepth : 2 ≤ depth (ModuleCat.of A A)) (W : (Spec (.of B)).Opens)
    (hW : ∀ p : PrimeSpectrum B, p.asIdeal.under A ≠ maximalIdeal A → p ∈ W) :
    Function.Bijective ((Spec (.of B)).presheaf.map W.leTop.op) := by
  -- The maximal ideal of `A` contains a weakly regular pair.
  obtain ⟨rs, hlen, hmem, hab⟩ :=
    exists_isWeaklyRegular_of_le_depth (ModuleCat.of A A) (n := 2) hdepth
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  -- It stays weakly regular on `B`, and its basic opens lie in `W`.
  have hD (r : A) (hr : r ∈ maximalIdeal A) :
      PrimeSpectrum.basicOpen (algebraMap A B r) ≤ W := fun p hp ↦
    hW p fun h ↦ hp <| Ideal.mem_comap.mp <| by rwa [← Ideal.under_def, h]
  rw [Spec.presheaf_map_leTop_bijective_iff]
  exact StructureSheaf.toOpenₗ_bijective_of_isWeaklyRegular hab.of_flat (hD a (hmem a (by simp)))
    (hD b (hmem b (by simp)))

/-- Let `B` be a Noetherian integral algebra over a local ring `A` such that every localization of
`B` at a maximal ideal has depth at least two, and `W` an open subset of `Spec B` containing every
prime not lying over the maximal ideal of `A`. Then restriction of sections of `Spec B` from
`Spec B` to `W` is bijective. -/
@[stacks 0BM8 "affine form"]
theorem presheaf_map_leTop_bijective_of_isIntegral [IsLocalRing A] [Algebra.IsIntegral A B]
    [IsNoetherianRing B]
    (hdepth : ∀ (𝔮 : Ideal B) [𝔮.IsMaximal],
      2 ≤ depth (ModuleCat.of (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔮)))
    (W : (Spec (.of B)).Opens)
    (hW : ∀ p : PrimeSpectrum B, p.asIdeal.under A ≠ maximalIdeal A → p ∈ W) :
    Function.Bijective ((Spec (.of B)).presheaf.map W.leTop.op) := by
  rw [Spec.presheaf_map_leTop_bijective_iff]
  refine StructureSheaf.toOpenₗ_bijective_of_two_le_depth W fun p hp ↦ ?_
  -- A prime outside `W` lies over the maximal ideal of `A`, so it is maximal.
  have : p.asIdeal.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) _
    (by rw [not_not.mp (mt (hW p) hp)]; infer_instance)
  rw [depth_eq_of_linearEquiv (LocalizedModule.equivLocalization p.asIdeal.primeCompl)]
  exact hdepth p.asIdeal

/-- Let `A` be a Noetherian integrally closed local domain of dimension at least two and `B` a
finite torsion-free `A`-algebra whose localizations at maximal ideals are normal domains. If `W`
is an open subset of `Spec B` containing every prime not lying over the maximal ideal of `A`, then
restriction of sections of `Spec B` from `Spec B` to `W` is bijective. -/
theorem presheaf_map_leTop_bijective_of_isIntegrallyClosed [IsLocalRing A] [IsNoetherianRing A]
    [IsDomain A] [IsIntegrallyClosed A] [Module.Finite A B] [Module.IsTorsionFree A B]
    (hdim : 2 ≤ ringKrullDim A)
    (hnormal : ∀ (𝔮 : Ideal B) [𝔮.IsMaximal],
      IsDomain (Localization.AtPrime 𝔮) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔮))
    (W : (Spec (.of B)).Opens)
    (hW : ∀ p : PrimeSpectrum B, p.asIdeal.under A ≠ maximalIdeal A → p ∈ W) :
    Function.Bijective ((Spec (.of B)).presheaf.map W.leTop.op) := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  refine presheaf_map_leTop_bijective_of_isIntegral (fun 𝔮 _ ↦ ?_) W hW
  obtain ⟨_, _⟩ := hnormal 𝔮
  -- By going down, `B_𝔮` has the dimension of `A`.
  refine two_le_depth_of_isIntegrallyClosed ?_
  rw [Ideal.ringKrullDim_localization_atPrime_eq_height_under A,
    eq_maximalIdeal (inferInstance : (𝔮.under A).IsMaximal),
    maximalIdeal_height_eq_ringKrullDim]
  exact hdim

end TauCeti.AlgebraicGeometry.Spec

namespace TauCeti.IsLocalRing

open CategoryTheory.Limits

/-- If `Spec (B ⧸ I.map (algebraMap A B))` is recovered from its sections over the punctured
spectrum of `A ⧸ I`, and algebra maps from `C` lift across the quotient, then morphisms over
that punctured spectrum lift to maps `Spec B ⟶ Spec C` over `Spec A`. -/
theorem exists_overHom_lift_quotient {A B C : Type u} [CommRing A] [CommRing B]
    [Algebra A B] [CommRing C] [Algebra A C] (I : Ideal A) [IsLocalRing (A ⧸ I)]
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
  have hp₀ : p₀ ≫ q = Spec.algebraMap A (B ⧸ J) := by
    simp only [p₀, q, Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← IsScalarTower.algebraMap_eq A (A ⧸ I) (B ⧸ J)]
  let ψ : (algSpec (.of A)).obj (.op (CommAlgCat.of A (B ⧸ J))) ⟶ Z :=
    Over.homMk (φ.left ≫ pullback.fst Z.hom q) (calc
      (φ.left ≫ pullback.fst Z.hom q) ≫ Z.hom =
          (φ.left ≫ pullback.snd Z.hom q) ≫ q := by simp only [Category.assoc, pullback.condition]
      _ = _ := (congrArg (fun k ↦ k ≫ q) (Over.w φ)).trans hp₀)
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
      have hg' : g'.left = Spec.map (CommRingCat.ofHom g.toRingHom) := by
        rw [algSpec_map_left]
        exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x ↦
          AlgHom.toUnder_right (R := .of A) g x))
      have heq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫
          Spec.map (CommRingCat.ofHom g.toRingHom) =
          Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mkₐ A J).comp g).toRingHom) := by
        exact TauCeti.AlgebraicGeometry.SpecMap_quotient_mk_comp_SpecMap_algHom J g
      exact (congrArg (fun k ↦ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ k) hg').trans
        (heq.trans ((congrArg (fun k ↦ Spec.map (CommRingCat.ofHom k.toRingHom)) hg).trans hm))
    · exact (Over.w (e.hom ≫ (Over.pullback q).map g')).trans (Over.w φ).symm
  refine ⟨g', (cancel_epi ((Over.pullback j₀).map e.hom)).mp ?_⟩
  exact ((Over.pullback j₀).map_comp _ _).symm.trans
    ((congrArg ((Over.pullback j₀).map) hmap).trans hφ)

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- **Algebraic Hartogs on the punctured spectrum.** For a Noetherian local ring of depth at least
two, restriction of global functions from `Spec A` to its punctured spectrum is an isomorphism. -/
theorem isIso_appTop_ι_puncturedSpectrum (hdepth : 2 ≤ depth (ModuleCat.of A A)) :
    IsIso (puncturedSpectrum A).ι.appTop := by
  rw [Scheme.Opens.ι_appTop]
  refine (ConcreteCategory.isIso_iff_bijective _).mpr
    (TauCeti.AlgebraicGeometry.Spec.presheaf_map_leTop_bijective_of_flat
      (A := A) (B := A) hdepth _ fun p hp ↦ ?_)
  rw [Scheme.Opens.ι_image_top]
  apply (mem_puncturedSpectrum_iff A p).mpr
  intro he
  apply hp
  simpa [Ideal.under_def, IsLocalRing.closedPoint] using congrArg PrimeSpectrum.asIdeal he

/-- An affine scheme over the punctured spectrum of a local ring of depth at least two
is the restriction of the spectrum of its global sections. The bottom map is induced by
the canonical `A`-algebra structure on those sections. -/
theorem isPullback_puncturedSpectrum_toSpecΓ
    (hdepth : 2 ≤ depth (ModuleCat.of A A)) {V : Scheme.{u}}
    (f : V ⟶ (puncturedSpectrum A).toScheme) [IsAffineHom f] :
    IsPullback f V.toSpecΓ (puncturedSpectrum A).ι
      (Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫
        (f ≫ (puncturedSpectrum A).ι).appTop)) := by
  let U := puncturedSpectrum A
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp
    (isCompact_puncturedSpectrum_of_fg_maximalIdeal A (IsNoetherian.noetherian _))
  have : IsIso U.ι.appTop := isIso_appTop_ι_puncturedSpectrum A hdepth
  -- Restriction to `U` is an isomorphism on functions, so `Γ(V, ⊤)` is its own base change.
  have H : IsPushout ((Scheme.ΓSpecIso (.of A)).inv ≫ U.ι.appTop)
      ((Scheme.ΓSpecIso (.of A)).inv ≫ (f ≫ U.ι).appTop) f.appTop (𝟙 _) :=
    .of_horiz_isIso ⟨by rw [Category.comp_id, Scheme.Hom.comp_appTop, Category.assoc]⟩
  simpa only [Spec.map_id, Category.comp_id] using
    TauCeti.AlgebraicGeometry.Spec.isPullback_toSpecΓ_of_isPushout f H

/-- Let `A` be a Noetherian integrally closed local domain of dimension at least two, and `B` a
finite torsion-free `A`-algebra whose localizations at maximal ideals are integrally closed
domains. Then the projection from the restriction of `Spec B` to the punctured spectrum onto
`Spec B` is an isomorphism on global functions. -/
theorem isIso_appTop_pullback_fst_puncturedSpectrum [IsDomain A] [IsIntegrallyClosed A]
    (hdim : 2 ≤ ringKrullDim A) {B : Type u} [CommRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B]
    (hnormal : ∀ (𝔮 : Ideal B) [𝔮.IsMaximal],
      IsDomain (Localization.AtPrime 𝔮) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔮)) :
    IsIso (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (puncturedSpectrum A).ι).appTop := by
  set U := puncturedSpectrum A
  set g := Spec.map (CommRingCat.ofHom (algebraMap A B))
  -- Restriction from `Spec B` to the preimage of `U` is bijective by algebraic Hartogs, and the
  -- base change identifies functions on that preimage with its global functions.
  have hΓ := TauCeti.AlgebraicGeometry.Spec.presheaf_map_leTop_bijective_of_isIntegrallyClosed
    (A := A) (B := B) hdim hnormal (g ⁻¹ᵁ U) fun p hp ↦
      (mem_puncturedSpectrum_iff A (g p)).mpr fun he ↦ hp (congrArg PrimeSpectrum.asIdeal he)
  have := (IsPullback.of_hasPullback g U.ι).isIso_appLE
  have : IsIso ((Spec (.of B)).presheaf.map (g ⁻¹ᵁ U).leTop.op) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hΓ
  have h : IsIso ((Spec (.of B)).presheaf.map (g ⁻¹ᵁ U).leTop.op ≫
      (pullback.fst g U.ι).appLE (g ⁻¹ᵁ U) ⊤
        (IsPullback.of_hasPullback g U.ι).toCommSq.top_le_preimage_preimage) := inferInstance
  rw [Scheme.Hom.map_appLE] at h
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact (Scheme.Hom.appLE_congr _ _ rfl (Scheme.Hom.preimage_top _) fun φ ↦ IsIso φ).mpr h

end TauCeti.IsLocalRing
