/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.Inertia
public import TauCeti.NumberTheory.NumberField.ComplexConjugation.Friendly.Basic
import TauCeti.RingTheory.RamificationInertia.Bijective

/-!
# Friendly places through complex conjugation

Let `K` be a number field, `E_K` its largest totally real or CM subfield and `K⁺` its maximal real
subfield. A place `v` of `K` is friendly when it is unramified over `ℚ` and, if `E_K` is CM, the
place of `K⁺` below `v` is inert in `E_K` (`IsDedekindDomain.HeightOneSpectrum.IsFriendly`).

The maximal real subfield `E_K⁺` of `E_K` is `K⁺`
(`TauCeti.NumberField.map_maximalRealSubfield_maximalRealOrCMSubfield`), so the place of `E_K⁺`
below the place `u` of `E_K` under `v` has the inertia degree over `ℤ` of the place of `K⁺` below
`v`. For `v` unramified over `ℚ`, so is `u`, and by
`NumberField.IsCMField.inertiaDeg_eq_two_mul_iff_complexConj_smul_eq` applied to the CM field
`E_K`, the inertness condition says that the complex conjugation of `E_K` fixes `u`. This is the
form of friendliness through decomposition groups (Lawrence–Venkatesh, §2.4, Definition 2.7),
relative to `E_K / K⁺`: the decomposition group of `u` in `Gal(E_K / K⁺) = {1, c}` is all of it.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.inertiaDeg_under_maximalRealSubfield_maximalRealOrCMSubfield`:
  for an ideal `P` of `𝓞 K`, the ideals below `P` in `𝓞 E_K⁺` and in `𝓞 K⁺` have the same
  inertia degree over `ℤ`.
* `IsDedekindDomain.HeightOneSpectrum.isFriendly_iff_complexConj_smul_eq`: `v` is friendly if and
  only if it is unramified over `ℚ` and, when `E_K` is CM, the complex conjugation of `E_K` fixes
  the place of `E_K` below `v`.

## References

* B. Lawrence and A. Venkatesh, *Diophantine problems and p-adic period mappings*, §2.4,
  Definition 2.7.
-/

public section

open NumberField TauCeti.NumberField

open scoped Pointwise

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]

/-- The isomorphism `E_K⁺ ≃+* K⁺` induced by the inclusion `E_K ≤ K`. -/
private noncomputable def maximalRealSubfieldEquiv :
    maximalRealSubfield (maximalRealOrCMSubfield K) ≃+* maximalRealSubfield K :=
  RingEquiv.ofBijective
    (((maximalRealOrCMSubfield K).subtype.comp
      (maximalRealSubfield (maximalRealOrCMSubfield K)).subtype).codRestrict _ fun x ↦ by
        rw [← map_maximalRealSubfield_maximalRealOrCMSubfield]
        exact ⟨x, x.property, rfl⟩)
    ⟨RingHom.injective _, fun y ↦ by
      have hy : (y : K) ∈ (maximalRealSubfield (maximalRealOrCMSubfield K)).map
          (maximalRealOrCMSubfield K).subtype := by
        rw [map_maximalRealSubfield_maximalRealOrCMSubfield]
        exact y.property
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

/-- **The places of `E_K⁺` and `K⁺` below an ideal have the same inertia degree.** For an ideal
`P` of `𝓞 K`, the ideal of `𝓞 E_K⁺` below the ideal of `𝓞 E_K` under `P` corresponds to the
ideal of `𝓞 K⁺` under `P` through `E_K⁺ = K⁺`, so both have the same inertia degree over `ℤ`. -/
theorem inertiaDeg_under_maximalRealSubfield_maximalRealOrCMSubfield (P : Ideal (𝓞 K)) :
    ((P.under (𝓞 (maximalRealOrCMSubfield K))).under
        (𝓞 (maximalRealSubfield (maximalRealOrCMSubfield K)))).inertiaDeg ℤ =
      (P.under (𝓞 (maximalRealSubfield K))).inertiaDeg ℤ := by
  set φ := RingOfIntegers.mapRingEquiv (maximalRealSubfieldEquiv (K := K))
  have hP : (P.under (𝓞 (maximalRealOrCMSubfield K))).under
      (𝓞 (maximalRealSubfield (maximalRealOrCMSubfield K))) =
        (P.under (𝓞 (maximalRealSubfield K))).comap φ.toIntAlgEquiv := by
    ext x
    simp only [Ideal.mem_comap]
    exact Iff.of_eq (congrArg (· ∈ P) (RingOfIntegers.ext rfl))
  rw [← Ideal.inertiaDeg_map_algEquiv φ.toIntAlgEquiv, hP,
    Ideal.map_comap_of_surjective _ φ.toIntAlgEquiv.surjective]

/-- **Friendly places through complex conjugation.** A place `v` of a number field `K` is friendly
if and only if it is unramified over `ℚ` and, when the largest totally real or CM subfield `E_K`
is CM, the complex conjugation of `E_K` fixes the place of `E_K` below `v` (Lawrence–Venkatesh,
§2.4, Definition 2.7, relative to `E_K / K⁺`). -/
theorem isFriendly_iff_complexConj_smul_eq (v : HeightOneSpectrum (𝓞 K)) :
    IsFriendly v ↔ v.asIdeal.ramificationIdx ℤ = 1 ∧
      ∀ [IsCMField (maximalRealOrCMSubfield K)],
        IsCMField.complexConj (maximalRealOrCMSubfield K) •
            v.asIdeal.under (𝓞 (maximalRealOrCMSubfield K)) =
          v.asIdeal.under (𝓞 (maximalRealOrCMSubfield K)) := by
  rw [isFriendly_iff]
  refine and_congr_right fun he ↦ forall_congr' fun hCM ↦ ?_
  set u := v.asIdeal.under (𝓞 (maximalRealOrCMSubfield K))
  have hu : u.ramificationIdx ℤ = 1 := by
    rw [Ideal.ramificationIdx_tower u v.asIdeal, mul_eq_one] at he
    exact he.1
  rw [← inertiaDeg_under_maximalRealSubfield_maximalRealOrCMSubfield,
    IsCMField.inertiaDeg_eq_two_mul_iff_complexConj_smul_eq u hu]

end IsDedekindDomain.HeightOneSpectrum
