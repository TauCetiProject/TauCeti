/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Stalk.Basic
public import TauCeti.RingTheory.CohenMacaulay.Basic

import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import TauCeti.RingTheory.AdicCompletion.LocalRing
import TauCeti.RingTheory.CohenMacaulay.Flat
import TauCeti.RingTheory.Flat.Colimit
import TauCeti.RingTheory.KrullDimension.Fiber
import TauCeti.RingTheory.RegularLocalRing.Flat

/-!
# Completion comparisons and noetherian invariants for stalks of `Spf A`

Building on `TauCeti.AlgebraicGeometry.FormalScheme.Spf.Stalk.Basic`, this module establishes the
deeper comparison properties of the canonical homomorphisms `A_𝔭 → 𝒪_{Spf A, p} → Â_𝔭`:

* both maps are local homomorphisms sending the maximal ideal of the source onto the maximal ideal
  of the target, and induce a commutative triangle of ring isomorphisms between the
  maximal-ideal-adic completions of `A_𝔭`, `𝒪_{Spf A, p}`, and `Â_𝔭`;
* when `A` is discrete, or when `A` is a complete local adic ring and `p` is its closed point, both
  comparison homomorphisms are bijective;
* when `A` is noetherian, both maps are flat and faithfully flat, so `A_𝔭`, `𝒪_{Spf A, p}`, and
  `Â_𝔭` have the same Krull dimension (equal to `ht 𝔭`), and one of them is regular (respectively
  Cohen–Macaulay) if and only if all three are (EGA I, Ch. 0, 7.6.15–7.6.18; Ch. I, 10.1.5–10.1.6).

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.6.15–7.6.18,
  and Ch. I, 10.1.5–10.1.6.
* [Stacks Project, Lemma 15.44.1](https://stacks.math.columbia.edu/tag/07NV)
* [Stacks Project, Lemma 15.44.2](https://stacks.math.columbia.edu/tag/07NX)
* [Stacks Project, Lemma 15.44.4](https://stacks.math.columbia.edu/tag/07NY)
-/

public section

universe u

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry IsLocalRing

namespace TauCeti.FormalScheme.Spf

open AdicRing

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  (p : carrier A)

private theorem quotientMap_bijective_congr {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {I₁ I₂ : Ideal R} {J₁ J₂ : Ideal S} (hI : I₁ = I₂) (hJ : J₁ = J₂)
    {H₁ : I₁ ≤ J₁.comap f} {H₂ : I₂ ≤ J₂.comap f}
    (h : Function.Bijective (Ideal.quotientMap J₁ f H₁)) :
    Function.Bijective (Ideal.quotientMap J₂ f H₂) := by
  subst hI hJ
  exact h

private def toZAlgHom {R S : Type*} [CommRing R] [CommRing S] [Algebra ℤ R] [Algebra ℤ S]
    (f : R →+* S) : R →ₐ[ℤ] S where
  __ := f
  commutes' n := RingHom.congr_fun (RingHom.ext_int (f.comp (algebraMap ℤ R)) (algebraMap ℤ S)) n

/-! ### Locality, maximal ideal generation, and maximal-ideal-adic completions -/

section MaximalIdealCompletion

/-- The maximal ideal of `A_𝔭` generates the maximal ideal of `𝒪_{Spf A, p}`. -/
theorem map_maximalIdeal_localizationToStalk :
    (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)).map
        (localizationToStalk p) =
      maximalIdeal ((Spf A).presheaf.stalk p) :=
  IsLocalRing.map_maximalIdeal_eq_of_quotientMap_bijective (localizationToStalk p)
    (ideal_map_le_maximalIdeal_localization p (IsAdicRing.ideal_spec A).2.1)
    (H := Ideal.le_comap_map)
    (quotientMap_bijective_congr (localizationToStalk p) rfl
      (map_localizationToStalk_map p (IsAdicRing.ideal A)).symm
      (quotientMap_localizationToStalk_bijective_of_isOpen p
        (by simpa [pow_one] using (isAdic_iff.mp (IsAdicRing.ideal_spec A).2.1).1 1)
        (H := map_localizationToStalk_map p (IsAdicRing.ideal A) ▸ Ideal.le_comap_map)))

/-- The canonical homomorphism `A_𝔭 →+* 𝒪_{Spf A, p}` is local. -/
instance isLocalHom_localizationToStalk : IsLocalHom (localizationToStalk p) :=
  ((local_hom_tfae (localizationToStalk p)).out 1 3).mpr
    (map_maximalIdeal_localizationToStalk p).le

private theorem ideal_map_toStalk_le_maximalIdeal :
    (IsAdicRing.ideal A).map (toStalk p) ≤ maximalIdeal ((Spf A).presheaf.stalk p) := by
  rw [← map_maximalIdeal_localizationToStalk p, ← map_localizationToStalk_map p]
  exact Ideal.map_mono (ideal_map_le_maximalIdeal_localization p (IsAdicRing.ideal_spec A).2.1)

/-- The maximal ideal of `𝒪_{Spf A, p}` generates the maximal ideal of `Â_𝔭`. -/
theorem map_maximalIdeal_stalkToLocalCompletion :
    (maximalIdeal ((Spf A).presheaf.stalk p)).map (stalkToLocalCompletion p) =
      maximalIdeal (LocalCompletion p) :=
  IsLocalRing.map_maximalIdeal_eq_of_quotientMap_bijective (stalkToLocalCompletion p)
    (ideal_map_toStalk_le_maximalIdeal p) (H := Ideal.le_comap_map)
    (quotientMap_bijective_congr (stalkToLocalCompletion p) rfl
      (map_stalkToLocalCompletion_map p (IsAdicRing.ideal A)).symm
      (quotientMap_stalkToLocalCompletion_bijective_of_isOpen p
        (by simpa [pow_one] using (isAdic_iff.mp (IsAdicRing.ideal_spec A).2.1).1 1)
        (H := map_stalkToLocalCompletion_map p (IsAdicRing.ideal A) ▸ Ideal.le_comap_map)))

/-- The canonical homomorphism `𝒪_{Spf A, p} →+* Â_𝔭` is local. -/
instance isLocalHom_stalkToLocalCompletion : IsLocalHom (stalkToLocalCompletion p) :=
  ((local_hom_tfae (stalkToLocalCompletion p)).out 1 3).mpr
    (map_maximalIdeal_stalkToLocalCompletion p).le

private theorem pow_quotientMap_localizationToStalk_bijective (n : ℕ) (_ : 1 ≤ n) :
    Function.Bijective (Ideal.quotientMap
      ((((IsAdicRing.ideal A).map
        (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))).map
          (localizationToStalk p)) ^ n)
      (localizationToStalk p)
      ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))) :=
  quotientMap_bijective_congr (localizationToStalk p) (Ideal.map_pow _ _ _)
    (by rw [map_localizationToStalk_map, Ideal.map_pow])
    (quotientMap_localizationToStalk_bijective_of_isOpen p
      ((isAdic_iff.mp (IsAdicRing.ideal_spec A).2.1).1 n)
      (H := map_localizationToStalk_map p (IsAdicRing.ideal A ^ n) ▸ Ideal.le_comap_map))

private theorem pow_quotientMap_stalkToLocalCompletion_bijective (n : ℕ) (_ : 1 ≤ n) :
    Function.Bijective (Ideal.quotientMap
      ((((IsAdicRing.ideal A).map (toStalk p)).map (stalkToLocalCompletion p)) ^ n)
      (stalkToLocalCompletion p)
      ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))) :=
  quotientMap_bijective_congr (stalkToLocalCompletion p) (Ideal.map_pow _ _ _)
    (by rw [map_stalkToLocalCompletion_map, Ideal.map_pow])
    (quotientMap_stalkToLocalCompletion_bijective_of_isOpen p
      ((isAdic_iff.mp (IsAdicRing.ideal_spec A).2.1).1 n)
      (H := map_stalkToLocalCompletion_map p (IsAdicRing.ideal A ^ n) ▸ Ideal.le_comap_map))

private theorem pow_quotientMap_algebraMap_localCompletion_bijective (n : ℕ) (_ : 1 ≤ n) :
    Function.Bijective (Ideal.quotientMap
      ((((IsAdicRing.ideal A).map
        (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))).map
          (algebraMap _ (LocalCompletion p))) ^ n)
      (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (LocalCompletion p))
      ((Ideal.pow_right_mono Ideal.le_comap_map n).trans (Ideal.le_comap_pow _ n))) :=
  AdicCompletion.quotientMap_algebraMap_bijective ((IsAdicRing.ideal_spec A).1.map _) n

/-- The canonical isomorphism between the maximal-ideal-adic completions of `A_𝔭` and
`𝒪_{Spf A, p}`. -/
noncomputable def maximalIdealCompletionLocalizationEquivStalk :
    AdicCompletion (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) ≃+*
      AdicCompletion (maximalIdeal ((Spf A).presheaf.stalk p)) ((Spf A).presheaf.stalk p) :=
  (AdicCompletion.maximalIdealEquivOfQuotientMap (toZAlgHom (localizationToStalk p))
    (ideal_map_le_maximalIdeal_localization p (IsAdicRing.ideal_spec A).2.1)
    (pow_quotientMap_localizationToStalk_bijective p)).toRingEquiv

/-- On elements of `A_𝔭`, `maximalIdealCompletionLocalizationEquivStalk` applies
`localizationToStalk p`. -/
@[simp]
theorem maximalIdealCompletionLocalizationEquivStalk_of
    (x : Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :
    maximalIdealCompletionLocalizationEquivStalk p (AdicCompletion.of _ _ x) =
      AdicCompletion.of _ _ (localizationToStalk p x) :=
  AdicCompletion.maximalIdealEquivOfQuotientMap_of (toZAlgHom (localizationToStalk p))
    (ideal_map_le_maximalIdeal_localization p (IsAdicRing.ideal_spec A).2.1)
    (pow_quotientMap_localizationToStalk_bijective p) x

/-- The canonical isomorphism between the maximal-ideal-adic completions of `𝒪_{Spf A, p}` and
`Â_𝔭`. -/
noncomputable def maximalIdealCompletionStalkEquivLocalCompletion :
    AdicCompletion (maximalIdeal ((Spf A).presheaf.stalk p)) ((Spf A).presheaf.stalk p) ≃+*
      AdicCompletion (maximalIdeal (LocalCompletion p)) (LocalCompletion p) :=
  (AdicCompletion.maximalIdealEquivOfQuotientMap (toZAlgHom (stalkToLocalCompletion p))
    (ideal_map_toStalk_le_maximalIdeal p)
    (pow_quotientMap_stalkToLocalCompletion_bijective p)).toRingEquiv

/-- On elements of `𝒪_{Spf A, p}`, `maximalIdealCompletionStalkEquivLocalCompletion` applies
`stalkToLocalCompletion p`. -/
@[simp]
theorem maximalIdealCompletionStalkEquivLocalCompletion_of
    (x : (Spf A).presheaf.stalk p) :
    maximalIdealCompletionStalkEquivLocalCompletion p (AdicCompletion.of _ _ x) =
      AdicCompletion.of _ _ (stalkToLocalCompletion p x) :=
  AdicCompletion.maximalIdealEquivOfQuotientMap_of (toZAlgHom (stalkToLocalCompletion p))
    (ideal_map_toStalk_le_maximalIdeal p) (pow_quotientMap_stalkToLocalCompletion_bijective p) x

/-- The canonical isomorphism between the maximal-ideal-adic completions of `A_𝔭` and `Â_𝔭`. -/
noncomputable def maximalIdealCompletionLocalizationEquivLocalCompletion :
    AdicCompletion (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal))
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) ≃+*
      AdicCompletion (maximalIdeal (LocalCompletion p)) (LocalCompletion p) :=
  (AdicCompletion.maximalIdealEquivOfQuotientMap
    (toZAlgHom
      (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (LocalCompletion p)))
    (ideal_map_le_maximalIdeal_localization p (IsAdicRing.ideal_spec A).2.1)
    (pow_quotientMap_algebraMap_localCompletion_bijective p)).toRingEquiv

/-- On elements of `A_𝔭`, `maximalIdealCompletionLocalizationEquivLocalCompletion` applies
`algebraMap A_𝔭 Â_𝔭`. -/
@[simp]
theorem maximalIdealCompletionLocalizationEquivLocalCompletion_of
    (x : Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :
    maximalIdealCompletionLocalizationEquivLocalCompletion p (AdicCompletion.of _ _ x) =
      AdicCompletion.of _ _
        (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (LocalCompletion p) x) :=
  AdicCompletion.maximalIdealEquivOfQuotientMap_of
    (toZAlgHom
      (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (LocalCompletion p)))
    (ideal_map_le_maximalIdeal_localization p (IsAdicRing.ideal_spec A).2.1)
    (pow_quotientMap_algebraMap_localCompletion_bijective p) x

/-- The three maximal-ideal-adic completion isomorphisms form a commutative triangle. -/
theorem maximalIdealCompletionLocalizationEquivStalk_trans :
    (maximalIdealCompletionLocalizationEquivStalk p).trans
        (maximalIdealCompletionStalkEquivLocalCompletion p) =
      maximalIdealCompletionLocalizationEquivLocalCompletion p := by
  refine RingEquiv.ext fun x ↦
    AdicCompletion.ext_evalₐ (I := maximalIdeal (LocalCompletion p)) fun n ↦ ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) n x)
  have h1 : maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) ≤
      (maximalIdeal ((Spf A).presheaf.stalk p)).comap
        (toZAlgHom (localizationToStalk p)).toRingHom :=
    (map_maximalIdeal_localizationToStalk p) ▸ Ideal.le_comap_map
  have h2 : maximalIdeal ((Spf A).presheaf.stalk p) ≤
      (maximalIdeal (LocalCompletion p)).comap (toZAlgHom (stalkToLocalCompletion p)).toRingHom :=
    (map_maximalIdeal_stalkToLocalCompletion p) ▸ Ideal.le_comap_map
  have h3 : maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) ≤
      (maximalIdeal (LocalCompletion p)).comap
        (toZAlgHom (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
          (LocalCompletion p))).toRingHom := by
    rw [← Ideal.map_le_iff_le_comap]
    change (maximalIdeal _).map (algebraMap _ (LocalCompletion p)) ≤ _
    rw [← stalkToLocalCompletion_comp_localizationToStalk, ← Ideal.map_map,
      map_maximalIdeal_localizationToStalk, map_maximalIdeal_stalkToLocalCompletion]
  have ha1 : maximalIdealCompletionLocalizationEquivStalk p x =
      AdicCompletion.mapₐ (toZAlgHom (localizationToStalk p)) h1 x :=
    AdicCompletion.maximalIdealEquivOfQuotientMap_apply _ _ _ h1 x
  have ha2 : maximalIdealCompletionStalkEquivLocalCompletion p
      (maximalIdealCompletionLocalizationEquivStalk p x) =
      AdicCompletion.mapₐ (toZAlgHom (stalkToLocalCompletion p)) h2
        (AdicCompletion.mapₐ (toZAlgHom (localizationToStalk p)) h1 x) :=
    (AdicCompletion.maximalIdealEquivOfQuotientMap_apply _ _ _ h2 _).trans (congrArg _ ha1)
  have ha3 : maximalIdealCompletionLocalizationEquivLocalCompletion p x =
      AdicCompletion.mapₐ (toZAlgHom (algebraMap _ (LocalCompletion p))) h3 x :=
    AdicCompletion.maximalIdealEquivOfQuotientMap_apply _ _ _ h3 x
  calc AdicCompletion.evalₐ (maximalIdeal (LocalCompletion p)) n
        (((maximalIdealCompletionLocalizationEquivStalk p).trans
          (maximalIdealCompletionStalkEquivLocalCompletion p)) x)
      = AdicCompletion.evalₐ (maximalIdeal (LocalCompletion p)) n
          (AdicCompletion.mapₐ (toZAlgHom (stalkToLocalCompletion p)) h2
            (AdicCompletion.mapₐ (toZAlgHom (localizationToStalk p)) h1 x)) :=
        congrArg _ ha2
    _ = Ideal.quotientMap (maximalIdeal (LocalCompletion p) ^ n)
          (toZAlgHom (stalkToLocalCompletion p)).toRingHom
          ((Ideal.pow_right_mono h2 n).trans (Ideal.le_comap_pow _ n))
          (Ideal.quotientMap (maximalIdeal ((Spf A).presheaf.stalk p) ^ n)
            (toZAlgHom (localizationToStalk p)).toRingHom
            ((Ideal.pow_right_mono h1 n).trans (Ideal.le_comap_pow _ n))
            (AdicCompletion.evalₐ
              (maximalIdeal (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) n x)) :=
        (AdicCompletion.evalₐ_mapₐ _ h2 n _).trans
          (congrArg _ (AdicCompletion.evalₐ_mapₐ _ h1 n x))
    _ = Ideal.Quotient.mk _ (stalkToLocalCompletion p (localizationToStalk p y)) := by
        rw [← hy, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
        rfl
    _ = Ideal.Quotient.mk _
          (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
            (LocalCompletion p) y) := by
        rw [stalkToLocalCompletion_localizationToStalk]
    _ = AdicCompletion.evalₐ (maximalIdeal (LocalCompletion p)) n
          (AdicCompletion.mapₐ
            (toZAlgHom (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
              (LocalCompletion p))) h3 x) :=
        ((AdicCompletion.evalₐ_mapₐ _ h3 n x).trans (by rw [← hy, Ideal.quotientMap_mk]; rfl)).symm
    _ = AdicCompletion.evalₐ (maximalIdeal (LocalCompletion p)) n
          (maximalIdealCompletionLocalizationEquivLocalCompletion p x) :=
        (congrArg _ ha3).symm

end MaximalIdealCompletion

/-! ### Discrete rings and complete local adic rings -/

section SpecialCases

private theorem bijective_of_quotientMap_bot_bijective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {I : Ideal R} {J : Ideal S} (hI : I = ⊥) (hJ : J = ⊥)
    {H : I ≤ J.comap f} (hbij : Function.Bijective (Ideal.quotientMap J f H)) :
    Function.Bijective f := by
  let e₁ : R ≃+* R ⧸ I := (RingEquiv.quotientBot R).symm.trans (Ideal.quotEquivOfEq hI.symm)
  let e₂ : S ⧸ J ≃+* S := (Ideal.quotEquivOfEq hJ).trans (RingEquiv.quotientBot S)
  have heq : (f : R → S) = e₂ ∘ Ideal.quotientMap J f H ∘ e₁ := by
    ext x
    simp [e₁, e₂]
  rw [heq]
  exact e₂.bijective.comp (hbij.comp e₁.bijective)

/-- For a discrete ring `A`, `A_𝔭 → 𝒪_{Spf A, p}` is bijective. -/
theorem localizationToStalk_bijective_of_discreteTopology [DiscreteTopology A] :
    Function.Bijective (localizationToStalk p) :=
  bijective_of_quotientMap_bot_bijective (localizationToStalk p) Ideal.map_bot Ideal.map_bot
    (quotientMap_localizationToStalk_bijective_of_isOpen p (J := ⊥) (isOpen_discrete _)
      (H := map_localizationToStalk_map p ⊥ ▸ Ideal.le_comap_map))

/-- For a discrete ring `A`, `𝒪_{Spf A, p} → Â_𝔭` is bijective. -/
theorem stalkToLocalCompletion_bijective_of_discreteTopology [DiscreteTopology A] :
    Function.Bijective (stalkToLocalCompletion p) :=
  bijective_of_quotientMap_bot_bijective (stalkToLocalCompletion p) Ideal.map_bot Ideal.map_bot
    (quotientMap_stalkToLocalCompletion_bijective_of_isOpen p (J := ⊥) (isOpen_discrete _)
      (H := map_stalkToLocalCompletion_map p ⊥ ▸ Ideal.le_comap_map))

private noncomputable def atPrimeAlgEquivOfIsLocalRing [IsLocalRing A]
    (hp : (p : PrimeSpectrum A).asIdeal = maximalIdeal A) :
    A ≃ₐ[A] Localization.AtPrime (p : PrimeSpectrum A).asIdeal :=
  IsLocalization.atUnits A (p : PrimeSpectrum A).asIdeal.primeCompl fun x hx ↦ by
    rw [IsUnit.mem_submonoid_iff, ← notMem_maximalIdeal, ← hp]; exact hx

private lemma isAdicComplete_map_of_algEquiv {B : Type*} [CommRing B] [Algebra A B]
    (e : A ≃ₐ[A] B) :
    IsAdicComplete ((IsAdicRing.ideal A).map (algebraMap A B)) B := by
  have h := (IsAdicComplete.congr_ringEquiv (IsAdicRing.ideal A) e.toRingEquiv).mpr
    (IsAdicRing.ideal_spec A).2.2
  have hI : (IsAdicRing.ideal A).map e.toRingEquiv =
      (IsAdicRing.ideal A).map (algebraMap A B) := by
    refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_)
      (Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_)
    · have he : e a = algebraMap A B a := by simpa using e.commutes a
      rw [Ideal.mem_comap]
      change e a ∈ _
      rw [he]
      exact Ideal.mem_map_of_mem _ ha
    · have he : e a = algebraMap A B a := by simpa using e.commutes a
      rw [Ideal.mem_comap, ← he]
      exact Ideal.mem_map_of_mem e.toRingEquiv ha
  exact hI ▸ h

omit [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A] in
private lemma algebraMap_bijective_of_algEquiv {B : Type*} [CommRing B] [Algebra A B]
    (e : A ≃ₐ[A] B) :
    Function.Bijective (algebraMap A B) := by
  have he : (algebraMap A B : A → B) = e := funext fun a ↦ by simp
  exact he ▸ e.bijective

/-- For a complete local adic ring `A` at its unique closed point `p` (with `𝔭 = 𝔪_A`), the
canonical map `A → 𝒪_{Spf A, p}` is bijective. -/
theorem toStalk_bijective_of_isLocalRing [IsLocalRing A]
    (hp : (p : PrimeSpectrum A).asIdeal = maximalIdeal A) :
    Function.Bijective (toStalk p) := by
  let eAt := atPrimeAlgEquivOfIsLocalRing p hp
  have hA_loc : Function.Bijective
      (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) :=
    algebraMap_bijective_of_algEquiv eAt
  have hloc_comp : Function.Bijective
      (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (LocalCompletion p)) := by
    have : IsAdicComplete ((IsAdicRing.ideal A).map
        (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
      isAdicComplete_map_of_algEquiv eAt
    exact AdicCompletion.of_bijective _ _
  have hcomp_bij : Function.Bijective (stalkToLocalCompletion p ∘ toStalk p) := by
    have heq : (stalkToLocalCompletion p ∘ toStalk p : _ → _) =
        algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (LocalCompletion p) ∘
          algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) := by
      ext a
      simp [IsScalarTower.algebraMap_apply A
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) (LocalCompletion p)]
    rw [heq]
    exact hloc_comp.comp hA_loc
  refine ⟨Function.Injective.of_comp hcomp_bij.1, fun s ↦ ?_⟩
  let eColim := completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1
    (IsAdicRing.ideal_spec A).1
  obtain ⟨f, x₀, hx⟩ := Concrete.colimit_exists_rep _ (eColim.inv s)
  let x : CompletedAway A f.elem := x₀
  have hf_unit : IsUnit f.elem := by
    rw [← notMem_maximalIdeal, ← hp]; exact f.notMem
  let eAway : A ≃ₐ[A] Localization.Away f.elem :=
    IsLocalization.atUnits A (Submonoid.powers f.elem) fun _ ⟨n, hn⟩ ↦ hn ▸ hf_unit.pow n
  have haway_bij : Function.Bijective (algebraMap A (Localization.Away f.elem)) :=
    algebraMap_bijective_of_algEquiv eAway
  have : IsAdicComplete ((IsAdicRing.ideal A).map (algebraMap A (Localization.Away f.elem)))
      (Localization.Away f.elem) :=
    isAdicComplete_map_of_algEquiv eAway
  have hA_caway : Function.Bijective (algebraMap A (CompletedAway A f.elem)) := by
    have h1 : Function.Bijective
        (algebraMap (Localization.Away f.elem) (CompletedAway A f.elem)) := by
      have heq : (algebraMap (Localization.Away f.elem) (CompletedAway A f.elem) : _ → _) =
          (CompletedAway.equivAdicCompletion A f.elem).symm ∘
            algebraMap (Localization.Away f.elem) _ := by
        ext y
        exact ((CompletedAway.equivAdicCompletion A f.elem).symm.commutes y).symm
      rw [heq]
      exact (CompletedAway.equivAdicCompletion A f.elem).symm.bijective.comp
        (AdicCompletion.of_bijective _ _)
    have heq : (algebraMap A (CompletedAway A f.elem) : _ → _) =
        algebraMap (Localization.Away f.elem) (CompletedAway A f.elem) ∘
          algebraMap A (Localization.Away f.elem) := by
      ext a
      exact IsScalarTower.algebraMap_apply A (Localization.Away f.elem) (CompletedAway A f.elem) a
    rw [heq]
    exact h1.comp haway_bij
  obtain ⟨a, ha⟩ := hA_caway.2 x
  refine ⟨a, ?_⟩
  rw [toStalk_eq_completedNeighbourhoodColimitIso p f a]
  change eColim.hom (colimit.ι (completedNeighbourhoodDiagram p) f
    (algebraMap A (CompletedAway A f.elem) a)) = s
  rw [show colimit.ι (completedNeighbourhoodDiagram p) f (algebraMap A (CompletedAway A f.elem) a) =
      eColim.inv s from (congrArg (colimit.ι (completedNeighbourhoodDiagram p) f) ha).trans hx]
  exact ConcreteCategory.congr_hom eColim.inv_hom_id s

/-- For a complete local adic ring `A` at its closed point `p`, `A_𝔭 → 𝒪_{Spf A, p}` is
bijective. -/
theorem localizationToStalk_bijective_of_isLocalRing [IsLocalRing A]
    (hp : (p : PrimeSpectrum A).asIdeal = maximalIdeal A) :
    Function.Bijective (localizationToStalk p) := by
  have hA_loc : Function.Bijective
      (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) :=
    algebraMap_bijective_of_algEquiv (atPrimeAlgEquivOfIsLocalRing p hp)
  have hto : Function.Bijective (localizationToStalk p ∘
      algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)) := by
    convert toStalk_bijective_of_isLocalRing p hp
    ext a
    exact localizationToStalk_algebraMap p a
  exact ⟨fun x₁ x₂ h ↦ by
    obtain ⟨a₁, rfl⟩ := hA_loc.2 x₁
    obtain ⟨a₂, rfl⟩ := hA_loc.2 x₂
    exact congrArg _ (hto.1 h), Function.Surjective.of_comp hto.2⟩

/-- For a complete local adic ring `A` at its closed point `p`, `𝒪_{Spf A, p} → Â_𝔭` is
bijective. -/
theorem stalkToLocalCompletion_bijective_of_isLocalRing [IsLocalRing A]
    (hp : (p : PrimeSpectrum A).asIdeal = maximalIdeal A) :
    Function.Bijective (stalkToLocalCompletion p) := by
  have : IsAdicComplete ((IsAdicRing.ideal A).map
      (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))
      (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
    isAdicComplete_map_of_algEquiv (atPrimeAlgEquivOfIsLocalRing p hp)
  have hcomp : Function.Bijective (stalkToLocalCompletion p ∘ localizationToStalk p) := by
    have heq : (stalkToLocalCompletion p ∘ localizationToStalk p : _ → _) =
        AdicCompletion.of
          ((IsAdicRing.ideal A).map
            (algebraMap A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)))
          (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
      funext fun x ↦ (stalkToLocalCompletion_localizationToStalk p x).trans
        (AdicCompletion.algebraMap_apply _ x)
    rw [heq]
    exact AdicCompletion.of_bijective _ _
  have hloc := localizationToStalk_bijective_of_isLocalRing p hp
  exact ⟨fun y₁ y₂ h ↦ by
    obtain ⟨x₁, rfl⟩ := hloc.2 y₁
    obtain ⟨x₂, rfl⟩ := hloc.2 y₂
    exact congrArg _ (hcomp.1 h), Function.Surjective.of_comp hcomp.2⟩

end SpecialCases

/-! ### Flatness, faithful flatness, and local invariants for noetherian `A` -/

section Noetherian

variable [IsNoetherianRing A]

/-- For noetherian `A`, the stalk `𝒪_{Spf A, p}` is flat over `A_𝔭` (EGA I, Ch. 0, 7.6.17). -/
theorem flat_localizationToStalk : (localizationToStalk p).Flat := by
  let : Algebra A ((Spf A).presheaf.stalk p) := (toStalk p).toAlgebra
  let : Algebra (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
      ((Spf A).presheaf.stalk p) := (localizationToStalk p).toAlgebra
  have : IsScalarTower A (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
      ((Spf A).presheaf.stalk p) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (localizationToStalk_algebraMap p a).symm
  change Module.Flat (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
    ((Spf A).presheaf.stalk p)
  rw [Module.flat_iff_of_isLocalization (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
    (p : PrimeSpectrum A).asIdeal.primeCompl]
  -- Lift the completed-neighbourhood diagram and its colimit cocone to `ModuleCat A`.
  let eColim := completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1
    (IsAdicRing.ideal_spec A).1
  let toColim : A →+* (colimit (completedNeighbourhoodDiagram p) : CommRingCat) :=
    eColim.inv.hom.comp (toStalk p)
  have htoColim (f : BasicNeighbourhood p) (a : A) :
      toColim a = colimit.ι (completedNeighbourhoodDiagram p) f
        (algebraMap A (CompletedAway A f.elem) a) := by
    change eColim.inv (toStalk p a) = _
    rw [toStalk_eq_completedNeighbourhoodColimitIso p f a]
    exact ConcreteCategory.congr_hom eColim.hom_inv_id _
  let : Algebra A (colimit (completedNeighbourhoodDiagram p) : CommRingCat) := toColim.toAlgebra
  let F : BasicNeighbourhood p ⥤ ModuleCat.{u} A :=
    { obj := fun f ↦ ModuleCat.of A (CompletedAway A f.elem)
      map := fun {f g} h ↦ ModuleCat.ofHom (CompletedAway.restrict
        ((BasicNeighbourhood.le_iff_mem_radical
          (IsAdicRing.ideal_spec A).2.1).mp h.le)).toLinearMap
      map_id := fun f ↦ by
        ext x
        exact congrArg (· x) (CompletedAway.restrict_self _)
      map_comp := fun h₁ h₂ ↦ by
        ext x
        exact (CompletedAway.restrict_restrict _ _ _ x).symm }
  let c : Cocone F :=
    { pt := ModuleCat.of A (colimit (completedNeighbourhoodDiagram p) : CommRingCat)
      ι :=
        { app := fun f ↦
            let ιf : CompletedAway A f.elem →+*
                (colimit (completedNeighbourhoodDiagram p) : CommRingCat) :=
              (colimit.ι (completedNeighbourhoodDiagram p) f).hom
            ModuleCat.ofHom
              { toFun := ιf
                map_add' := ιf.map_add
                map_smul' := fun a x ↦ by
                  rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
                  exact congrArg (· * ιf x) (htoColim f a).symm }
          naturality := fun {f g} h ↦ by
            ext x
            exact ConcreteCategory.congr_hom
              (colimit.w (completedNeighbourhoodDiagram p) h) x } }
  have hcRing : IsColimit ((forget CommRingCat.{u}).mapCocone
      (colimit.cocone (completedNeighbourhoodDiagram p))) :=
    isColimitOfPreserves (forget CommRingCat.{u})
      (colimit.isColimit (completedNeighbourhoodDiagram p))
  have hc : IsColimit c :=
    isColimitOfReflects (forget (ModuleCat.{u} A)) hcRing
  have : ∀ f : BasicNeighbourhood p, Module.Flat A (F.obj f) := fun f ↦
    CompletedAway.flat A f.elem
  have : Module.Flat A (colimit (completedNeighbourhoodDiagram p) : CommRingCat) :=
    Module.Flat.of_isColimit hc
  let eLin : (Spf A).presheaf.stalk p ≃ₗ[A]
      (colimit (completedNeighbourhoodDiagram p) : CommRingCat) :=
    { eColim.commRingCatIsoToRingEquiv.symm.toAddEquiv with
      map_smul' := fun a s ↦ by
        change eColim.inv (toStalk p a * s) = toColim a * eColim.inv s
        exact map_mul eColim.inv.hom (toStalk p a) s }
  exact Module.Flat.of_linearEquiv eLin

/-- For noetherian `A`, `A_𝔭 → 𝒪_{Spf A, p}` is faithfully flat. -/
theorem faithfullyFlat_localizationToStalk : (localizationToStalk p).FaithfullyFlat := by
  algebraize [localizationToStalk p]
  have : Module.Flat (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
      ((Spf A).presheaf.stalk p) := flat_localizationToStalk p
  have : IsLocalHom (algebraMap (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
      ((Spf A).presheaf.stalk p)) := isLocalHom_localizationToStalk p
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- For noetherian `A`, `𝒪_{Spf A, p} → Â_𝔭` is flat (EGA I, Ch. 0, 7.6.17). -/
theorem flat_stalkToLocalCompletion : (stalkToLocalCompletion p).Flat :=
  stalkToLocalCompletion_eq_comp p ▸
    (RingHom.Flat.of_bijective
      (completedNeighbourhoodColimitIso p (IsAdicRing.ideal_spec A).2.1
        (IsAdicRing.ideal_spec A).1).commRingCatIsoToRingEquiv.symm.bijective).comp
      (flat_colimitToLocalCompletion p)

/-- For noetherian `A`, `𝒪_{Spf A, p} → Â_𝔭` is faithfully flat (EGA I, Ch. 0, 7.6.17). -/
theorem faithfullyFlat_stalkToLocalCompletion : (stalkToLocalCompletion p).FaithfullyFlat := by
  algebraize [stalkToLocalCompletion p]
  have : Module.Flat ((Spf A).presheaf.stalk p) (LocalCompletion p) :=
    flat_stalkToLocalCompletion p
  have : IsLocalHom (algebraMap ((Spf A).presheaf.stalk p) (LocalCompletion p)) :=
    isLocalHom_stalkToLocalCompletion p
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- For noetherian `A`, the stalk `𝒪_{Spf A, p}` and the algebraic localisation `A_𝔭` have the same
Krull dimension. -/
@[stacks 07NV]
theorem ringKrullDim_stalk_eq :
    ringKrullDim ((Spf A).presheaf.stalk p) =
      ringKrullDim (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) := by
  algebraize [localizationToStalk p]
  have : Module.Flat (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
      ((Spf A).presheaf.stalk p) := flat_localizationToStalk p
  exact TauCeti.ringKrullDim_eq_of_hasGoingDown_of_map_maximalIdeal_eq
    (map_maximalIdeal_localizationToStalk p)

/-- For noetherian `A`, the Krull dimension of the stalk `𝒪_{Spf A, p}` is the height of the prime
ideal `𝔭`. -/
theorem ringKrullDim_stalk_eq_height :
    ringKrullDim ((Spf A).presheaf.stalk p) = ((p : PrimeSpectrum A).asIdeal.height : WithBot ℕ∞) :=
  (ringKrullDim_stalk_eq p).trans
    (IsLocalization.AtPrime.ringKrullDim_eq_height (p : PrimeSpectrum A).asIdeal _)

/-- For noetherian `A`, `Â_𝔭` and `𝒪_{Spf A, p}` have the same Krull dimension. -/
@[stacks 07NV]
theorem ringKrullDim_localCompletion_eq_stalk :
    ringKrullDim (LocalCompletion p) = ringKrullDim ((Spf A).presheaf.stalk p) := by
  algebraize [stalkToLocalCompletion p]
  have : Module.Flat ((Spf A).presheaf.stalk p) (LocalCompletion p) :=
    flat_stalkToLocalCompletion p
  exact TauCeti.ringKrullDim_eq_of_hasGoingDown_of_map_maximalIdeal_eq
    (map_maximalIdeal_stalkToLocalCompletion p)

/-- For noetherian `A`, `Â_𝔭` and `A_𝔭` have the same Krull dimension. -/
@[stacks 07NV]
theorem ringKrullDim_localCompletion_eq :
    ringKrullDim (LocalCompletion p) =
      ringKrullDim (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
  (ringKrullDim_localCompletion_eq_stalk p).trans (ringKrullDim_stalk_eq p)

/-- For noetherian `A`, the stalk `𝒪_{Spf A, p}` is a regular local ring if and only if `A_𝔭` is. -/
@[stacks 07NY]
theorem isRegularLocalRing_stalk_iff :
    IsRegularLocalRing ((Spf A).presheaf.stalk p) ↔
      IsRegularLocalRing (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) := by
  algebraize [localizationToStalk p]
  have : Module.Flat (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
      ((Spf A).presheaf.stalk p) := flat_localizationToStalk p
  exact TauCeti.isRegularLocalRing_iff_of_flat_of_map_maximalIdeal_eq
    (map_maximalIdeal_localizationToStalk p)

/-- For noetherian `A`, `Â_𝔭` is a regular local ring if and only if `𝒪_{Spf A, p}` is. -/
@[stacks 07NY]
theorem isRegularLocalRing_localCompletion_iff_stalk :
    IsRegularLocalRing (LocalCompletion p) ↔ IsRegularLocalRing ((Spf A).presheaf.stalk p) := by
  algebraize [stalkToLocalCompletion p]
  have : Module.Flat ((Spf A).presheaf.stalk p) (LocalCompletion p) :=
    flat_stalkToLocalCompletion p
  exact TauCeti.isRegularLocalRing_iff_of_flat_of_map_maximalIdeal_eq
    (map_maximalIdeal_stalkToLocalCompletion p)

/-- For noetherian `A`, `Â_𝔭` is a regular local ring if and only if `A_𝔭` is. -/
@[stacks 07NY]
theorem isRegularLocalRing_localCompletion_iff :
    IsRegularLocalRing (LocalCompletion p) ↔
      IsRegularLocalRing (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
  (isRegularLocalRing_localCompletion_iff_stalk p).trans (isRegularLocalRing_stalk_iff p)

/-- For noetherian `A`, the stalk `𝒪_{Spf A, p}` is Cohen–Macaulay if and only if `A_𝔭` is. -/
@[stacks 07NX]
theorem isCohenMacaulay_stalk_iff :
    Module.IsCohenMacaulay ((Spf A).presheaf.stalk p) ((Spf A).presheaf.stalk p) ↔
      Module.IsCohenMacaulay (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) := by
  algebraize [localizationToStalk p]
  have : Module.Flat (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
      ((Spf A).presheaf.stalk p) := flat_localizationToStalk p
  exact Module.isCohenMacaulay_self_iff_of_flat_of_map_maximalIdeal_eq
    (map_maximalIdeal_localizationToStalk p)

/-- For noetherian `A`, `Â_𝔭` is Cohen–Macaulay if and only if `𝒪_{Spf A, p}` is. -/
@[stacks 07NX]
theorem isCohenMacaulay_localCompletion_iff_stalk :
    Module.IsCohenMacaulay (LocalCompletion p) (LocalCompletion p) ↔
      Module.IsCohenMacaulay ((Spf A).presheaf.stalk p) ((Spf A).presheaf.stalk p) := by
  algebraize [stalkToLocalCompletion p]
  have : Module.Flat ((Spf A).presheaf.stalk p) (LocalCompletion p) :=
    flat_stalkToLocalCompletion p
  exact Module.isCohenMacaulay_self_iff_of_flat_of_map_maximalIdeal_eq
    (map_maximalIdeal_stalkToLocalCompletion p)

/-- For noetherian `A`, `Â_𝔭` is Cohen–Macaulay if and only if `A_𝔭` is. -/
@[stacks 07NX]
theorem isCohenMacaulay_localCompletion_iff :
    Module.IsCohenMacaulay (LocalCompletion p) (LocalCompletion p) ↔
      Module.IsCohenMacaulay (Localization.AtPrime (p : PrimeSpectrum A).asIdeal)
        (Localization.AtPrime (p : PrimeSpectrum A).asIdeal) :=
  (isCohenMacaulay_localCompletion_iff_stalk p).trans (isCohenMacaulay_stalk_iff p)

end Noetherian

end TauCeti.FormalScheme.Spf

