/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ComplexConjugation.Friendly
public import TauCeti.RingTheory.RamificationInertia.Bijective

/-!
# Friendliness is invariant under isomorphisms of number fields

Let `σ : K ≃+* K'` be an isomorphism of number fields. It carries the maximal real subfield `K⁺`
onto `K'⁺` and the largest totally real or CM subfield `E_K` onto `E_{K'}`
(`TauCeti.NumberField.map_maximalRealOrCMSubfield`), so it induces isomorphisms of their rings of
integers compatible with `𝓞 K ≃+* 𝓞 K'`. Ramification indices and inertia degrees over `ℤ` are
invariant under ring isomorphisms (`Ideal.ramificationIdx_map_algEquiv`,
`Ideal.inertiaDeg_map_algEquiv`), so a place `v` of `K` is friendly exactly when its image in `K'`
is (MordellLawrenceVenkatesh §1.5).

## Main results

* `NumberField.map_maximalRealSubfield`: `σ` carries `K⁺` onto `K'⁺`.
* `IsDedekindDomain.HeightOneSpectrum.isFriendly_equivOfRingEquiv_iff`: the image of a place `v`
  of `K` under `σ` is friendly if and only if `v` is.
-/

public section

open NumberField TauCeti.NumberField

variable {K K' : Type*} [Field K] [Field K']

/-- **An isomorphism of fields carries the maximal real subfield onto the maximal real
subfield.** -/
theorem NumberField.map_maximalRealSubfield (σ : K ≃+* K') :
    (maximalRealSubfield K).map (σ : K →+* K') = maximalRealSubfield K' := by
  ext y
  refine ⟨?_, fun hy ↦ ⟨σ.symm y, fun φ ↦ ?_, σ.apply_symm_apply y⟩⟩
  · rintro ⟨x, hx, rfl⟩ ψ
    exact hx (ψ.comp (σ : K →+* K'))
  · have := hy (φ.comp (σ.symm : K' →+* K))
    simpa using this

/-- The isomorphism of rings of integers of subfields `A` of `K` and `B` of `K'` induced by an
isomorphism `σ : K ≃+* K'` carrying `A` onto `B`. -/
@[expose] noncomputable def NumberField.RingOfIntegers.subfieldMapRingEquiv (σ : K ≃+* K')
    {A : Subfield K} {B : Subfield K'} (h : A.map (σ : K →+* K') = B) : 𝓞 A ≃+* 𝓞 B :=
  RingOfIntegers.mapRingEquiv <| RingEquiv.ofBijective
    ((σ : K →+* K').comp A.subtype |>.codRestrict B fun x ↦ h ▸ ⟨x, x.property, rfl⟩)
    ⟨fun x y hxy ↦ Subtype.ext (σ.injective (congrArg Subtype.val hxy)), fun y ↦ by
      obtain ⟨x, hx, hxy⟩ := (h ▸ y.property : (y : K') ∈ A.map (σ : K →+* K'))
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

theorem NumberField.RingOfIntegers.algebraMap_subfieldMapRingEquiv (σ : K ≃+* K')
    {A : Subfield K} {B : Subfield K'} (h : A.map (σ : K →+* K') = B) (x : 𝓞 A) :
    algebraMap (𝓞 B) (𝓞 K') (subfieldMapRingEquiv σ h x) =
      RingOfIntegers.mapRingEquiv σ (algebraMap (𝓞 A) (𝓞 K) x) :=
  rfl

namespace IsDedekindDomain.HeightOneSpectrum

/-- Transport of the place below `v` in a subfield along an isomorphism carrying the subfield onto
another one: the inertia degree over `ℤ` is unchanged. -/
private theorem inertiaDeg_under_map (σ : K ≃+* K') {A : Subfield K} {B : Subfield K'}
    (h : A.map (σ : K →+* K') = B) (P : Ideal (𝓞 K)) :
    ((P.map (RingOfIntegers.mapRingEquiv σ)).under (𝓞 B)).inertiaDeg ℤ =
      (P.under (𝓞 A)).inertiaDeg ℤ := by
  have : (P.map (RingOfIntegers.mapRingEquiv σ)).under (𝓞 B) =
      (P.under (𝓞 A)).map (RingOfIntegers.subfieldMapRingEquiv σ h).toIntAlgEquiv := by
    set g := RingOfIntegers.subfieldMapRingEquiv σ h
    set τ := RingOfIntegers.mapRingEquiv σ
    have key : (τ.symm : 𝓞 K' →+* 𝓞 K).comp (algebraMap (𝓞 B) (𝓞 K')) =
        (algebraMap (𝓞 A) (𝓞 K)).comp (g.symm : 𝓞 B →+* 𝓞 A) := by
      ext y : 1
      apply τ.injective
      simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        RingEquiv.apply_symm_apply]
      rw [← RingOfIntegers.algebraMap_subfieldMapRingEquiv σ h, RingEquiv.apply_symm_apply]
    change Ideal.under _ (Ideal.map (τ : 𝓞 K →+* 𝓞 K') P) = Ideal.map (g : 𝓞 A →+* 𝓞 B) _
    rw [Ideal.map_comap_of_equiv, Ideal.map_comap_of_equiv, Ideal.under_def, Ideal.under_def]
    ext y
    have hy := RingHom.congr_fun key y
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe] at hy
    simp only [Ideal.mem_comap, hy]
  rw [this, Ideal.inertiaDeg_map_algEquiv]

variable [NumberField K] [NumberField K']

/-- **Friendliness is invariant under isomorphisms of number fields.** For `σ : K ≃+* K'`, the
image of a place `v` of `K` in `K'` is friendly if and only if `v` is. -/
theorem isFriendly_equivOfRingEquiv_iff (σ : K ≃+* K') (v : HeightOneSpectrum (𝓞 K)) :
    IsFriendly (equivOfRingEquiv (RingOfIntegers.mapRingEquiv σ) v) ↔ IsFriendly v := by
  set τ := RingOfIntegers.mapRingEquiv σ
  have hv : (equivOfRingEquiv τ v).asIdeal = v.asIdeal.map τ.toIntAlgEquiv :=
    Ideal.comap_symm τ
  have hE := map_maximalRealOrCMSubfield σ
  have hR := NumberField.map_maximalRealSubfield σ
  have hCM : IsCMField (maximalRealOrCMSubfield K') ↔ IsCMField (maximalRealOrCMSubfield K) := by
    rw [isCMField_maximalRealOrCMSubfield_iff_ne_maximalRealSubfield,
      isCMField_maximalRealOrCMSubfield_iff_ne_maximalRealSubfield, ← hE, ← hR,
      (Subfield.map_injective (σ : K →+* K')).ne_iff]
  rw [isFriendly_iff, isFriendly_iff, hv, Ideal.ramificationIdx_map_algEquiv, hCM]
  change _ ∧ (_ → (Ideal.under _ (v.asIdeal.map τ)).inertiaDeg ℤ =
    2 * (Ideal.under _ (v.asIdeal.map τ)).inertiaDeg ℤ) ↔ _
  rw [inertiaDeg_under_map σ hE, inertiaDeg_under_map σ hR]

end IsDedekindDomain.HeightOneSpectrum
