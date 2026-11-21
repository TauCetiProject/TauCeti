/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Tilde.Hartogs
public import TauCeti.AlgebraicGeometry.PuncturedSpectrum
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.RingTheory.Regular.Flat
import TauCeti.AlgebraicGeometry.Restrict
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
two, the morphism on spectra of global sections restricts to the original scheme. This uses
Mathlib's `AlgebraicGeometry.Scheme.isPullback_toSpecΓ_toSpecΓ` after identifying the global
sections of the punctured base with the local ring. More generally, a scheme affine over a
quasi-compact open `U` of `Spec A` is the restriction of `Spec B` for any `A`-algebra `B` whose
base change to `Γ(U, ⊤)` is its ring of functions. Without the depth bound the punctured spectrum
may be a basic open `D(t)`, whose ring of functions is `A_t`.

In the finite normal case, the same bijectivity says that the base change of `Spec B` to the
punctured spectrum of `A` has `B` as its ring of global functions.

## Main results

* `TauCeti.AlgebraicGeometry.Spec.presheaf_map_leTop_bijective_of_flat`: the flat case.
* `TauCeti.IsLocalRing.isIso_appTop_ι_puncturedSpectrum`: the case `B = A`, as an isomorphism
  from the functions on `Spec A` to those on its punctured spectrum.
* `TauCeti.IsLocalRing.isPullback_puncturedSpectrum_toSpecΓ`: reconstruction of an affine
  scheme over the puncture by restricting the spectrum of its sections.
* `TauCeti.AlgebraicGeometry.Spec.isLocalization_away_of_eq_basicOpen`: the functions on an open
  `D(t)` of `Spec A` form the localization `A_t`.
* `TauCeti.AlgebraicGeometry.Spec.isPullback_toSpecΓ_of_isPushout`: a scheme affine over a
  quasi-compact open `U` of `Spec R` whose ring of functions is `Γ(U, ⊤) ⊗[R] B` is the
  restriction of `Spec B` to `U`.
* `TauCeti.AlgebraicGeometry.Spec.presheaf_map_leTop_bijective_of_isIntegral`: the integral case,
  an affine form of Stacks, Lemma 58.20.1 (0BM8).
* `TauCeti.AlgebraicGeometry.Spec.presheaf_map_leTop_bijective_of_isIntegrallyClosed`: the finite
  normal case.
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

/-- If an open subscheme `U` of `Spec A` is the basic open `D(t)`, its ring of functions is the
localization `A_t`, as an `A`-algebra through restriction from `Spec A`. -/
theorem isLocalization_away_of_eq_basicOpen {U : (Spec (.of A)).Opens} {t : A}
    (ht : U = PrimeSpectrum.basicOpen t) :
    letI := ((Scheme.ΓSpecIso (.of A)).inv ≫ U.ι.appTop).hom.toAlgebra
    IsLocalization.Away t Γ(U.toScheme, ⊤) := by
  let : Algebra Γ(Spec (.of A), ⊤) Γ(Spec (.of A), U.ι ''ᵁ ⊤) :=
    ((Spec (.of A)).presheaf.map (homOfLE le_top : U.ι ''ᵁ ⊤ ⟶ ⊤).op).hom.toAlgebra
  -- Over `Γ(Spec A, ⊤)`, this is the localization of an affine scheme at a basic open.
  have : IsLocalization.Away ((Scheme.ΓSpecIso (.of A)).inv t) Γ(Spec (.of A), U.ι ''ᵁ ⊤) :=
    (isAffineOpen_top (Spec (.of A))).isLocalization_of_eq_basicOpen _ (homOfLE le_top)
      (by rw [Scheme.Opens.ι_image_top, basicOpen_eq_of_affine]; exact ht)
  -- Transport the base ring along `Γ(Spec A, ⊤) ≅ A`.
  have := IsLocalization.isLocalization_of_base_ringEquiv
    (.powers ((Scheme.ΓSpecIso (.of A)).inv t)) Γ(Spec (.of A), U.ι ''ᵁ ⊤)
    (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv
  have he : (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv
      ((Scheme.ΓSpecIso (.of A)).inv t) = t := (Scheme.ΓSpecIso (.of A)).inv_hom_id_apply t
  -- The transported algebra structure is restriction precomposed with `(ΓSpecIso A).inv`, which is
  -- the algebra structure of the statement by definition.
  rwa [Submonoid.map_powers, he] at this

/-- Let `U` be a quasi-compact open subscheme of `Spec R` and `f : V ⟶ U` an affine morphism. If
an `R`-algebra `B` with a map `h : B ⟶ Γ(V, ⊤)` exhibits `Γ(V, ⊤)` as the pushout
`Γ(U, ⊤) ⊗[R] B`, then `V` is the restriction of `Spec B` to `U`, with `V ⟶ Spec B` induced by
`h`. -/
theorem isPullback_toSpecΓ_of_isPushout {R : CommRingCat.{u}} {U : (Spec R).Opens}
    [CompactSpace U] {V : Scheme.{u}} (f : V ⟶ U) [IsAffineHom f] {B : CommRingCat.{u}}
    {g : R ⟶ B} {h : B ⟶ Γ(V, ⊤)}
    (H : IsPushout ((Scheme.ΓSpecIso R).inv ≫ U.ι.appTop) g f.appTop h) :
    IsPullback f (V.toSpecΓ ≫ Spec.map h) U.ι (Spec.map g) := by
  have : U.toScheme.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion U.ι
  -- `V` is the restriction of `Spec Γ(V, ⊤)` to `U`, and `Spec Γ(V, ⊤)` that of `Spec B`.
  have hU : U.toScheme.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ U.ι.appTop) = U.ι := by
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  simpa only [hU] using
    (Scheme.isPullback_toSpecΓ_toSpecΓ f).paste_vert (isPullback_SpecMap_of_isPushout _ _ _ _ H)

end TauCeti.AlgebraicGeometry.Spec

namespace TauCeti.IsLocalRing

open CategoryTheory.Limits

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
  have : U.toScheme.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion U.ι
  have : IsIso U.ι.appTop := isIso_appTop_ι_puncturedSpectrum A hdepth
  let e := asIso (Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫ U.ι.appTop))
  refine (Scheme.isPullback_toSpecΓ_toSpecΓ f).of_iso
    (.refl _) (.refl _) (.refl _) e (by simp) (by simp) ?_ ?_
  · simp only [e, asIso_hom, Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc]
    simp [U]
  · simp only [e, asIso_hom, Spec.map_comp, Scheme.Hom.comp_appTop,
      Iso.refl_hom, Category.id_comp, Category.assoc, U]

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
