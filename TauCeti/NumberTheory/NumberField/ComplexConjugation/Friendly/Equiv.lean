/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ComplexConjugation.Friendly.Basic
public import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport
import TauCeti.NumberTheory.NumberField.ComplexConjugation.MaximalRealSubfield
import TauCeti.RingTheory.RamificationInertia.Bijective

/-!
# Friendliness is invariant under isomorphisms of number fields

Let `σ : K ≃+* K'` be an isomorphism of number fields. It carries the maximal real subfield `K⁺`
onto `K'⁺` (`NumberField.map_maximalRealSubfield`) and the largest totally real or CM subfield
`E_K` onto `E_{K'}` (`TauCeti.NumberField.map_maximalRealOrCMSubfield`), so it induces
isomorphisms of their rings of integers compatible with `𝓞 K ≃+* 𝓞 K'`
(`NumberField.RingOfIntegers.subfieldMapRingEquiv`). Ramification indices and inertia degrees over
`ℤ` are invariant under ring isomorphisms (`Ideal.ramificationIdx_map_algEquiv`,
`Ideal.inertiaDeg_map_algEquiv`), so a place `v` of `K` is friendly exactly when its image in `K'`
is.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.isFriendly_equivOfRingEquiv_iff`: the image of a place `v`
  of `K` under `σ` is friendly if and only if `v` is.
-/

public section

open NumberField TauCeti.NumberField

universe u v

variable {K : Type u} {K' : Type v} [Field K] [Field K']

namespace IsDedekindDomain.HeightOneSpectrum

variable [NumberField K] [NumberField K']

/-- **Friendliness is invariant under isomorphisms of number fields.** For `σ : K ≃+* K'`, the
image of a place `v` of `K` in `K'` is friendly if and only if `v` is. -/
theorem isFriendly_equivOfRingEquiv_iff (σ : K ≃+* K') (v : HeightOneSpectrum (𝓞 K)) :
    IsFriendly (equivOfRingEquiv (RingOfIntegers.mapRingEquiv σ) v) ↔ IsFriendly v := by
  set τ := RingOfIntegers.mapRingEquiv σ
  -- `Ideal.ramificationIdx_map_algEquiv` and `Ideal.inertiaDeg_map_algEquiv` are stated for
  -- `ℤ`-algebra isomorphisms, so ring isomorphisms are viewed as such through `toIntAlgEquiv`.
  have hmap {X : Type u} {Y : Type v} [CommRing X] [CommRing Y] (e : X ≃+* Y) (I : Ideal X) :
      I.map e = I.map e.toIntAlgEquiv := by
    rw [← Ideal.map_coe e, ← Ideal.map_coe e.toIntAlgEquiv]
    exact congrArg (Ideal.map · I)
      (RingHom.ext fun x ↦ congrFun (RingEquiv.coe_toIntAlgEquiv e).symm x)
  -- By definition `(equivOfRingEquiv τ v).asIdeal` is `v.asIdeal.comap τ.symm`. The generated
  -- lemma `equivOfRingEquiv_apply` cannot be rewritten with here, since its surjectivity argument
  -- only typechecks after unfolding the coercion of `τ.symm` to a ring homomorphism.
  have hv : (equivOfRingEquiv τ v).asIdeal = v.asIdeal.map τ := Ideal.comap_symm τ
  have hE := map_maximalRealOrCMSubfield σ
  have hR := NumberField.map_maximalRealSubfield σ
  have hCM : IsCMField (maximalRealOrCMSubfield K') ↔ IsCMField (maximalRealOrCMSubfield K) := by
    rw [isCMField_maximalRealOrCMSubfield_iff_ne_maximalRealSubfield,
      isCMField_maximalRealOrCMSubfield_iff_ne_maximalRealSubfield, ← hE, ← hR,
      (Subfield.map_injective (σ : K →+* K')).ne_iff]
  rw [isFriendly_iff, isFriendly_iff, hv, Ideal.under_map_mapRingEquiv σ hE,
    Ideal.under_map_mapRingEquiv σ hR, hCM]
  simp only [hmap, Ideal.ramificationIdx_map_algEquiv, Ideal.inertiaDeg_map_algEquiv]

end IsDedekindDomain.HeightOneSpectrum
