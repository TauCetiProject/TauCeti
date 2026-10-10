/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.CharacterCarry
public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleLocalization

/-!
# Localization of character carry classes on the ideles

Let `K` be a number field, let `χ : G_K → ℚ / ℤ` be a character with open kernel, and let
`a ∈ I_{Kˢ}^{G_K}` be an invariant idele. The carry cocycle of `χ` and `a` represents the class
usually written `a ∪ δχ` in `H²(G_K, I_{Kˢ})`.

This file computes its localization. At a finite place `v`, an embedding of separable closures
`τ : Kˢ → K_vˢ` restricts `χ` along the decomposition map and reads the `v`-component of `a`.
The localized class is the carry class of precisely those two local objects
(`ideleBrLocalization_characterCarryCocycle`). The same statement holds at an infinite place
(`ideleInfiniteBrLocalization_characterCarryCocycle`). In particular, the localization vanishes
where the corresponding component of `a` is `1`.

Together with the local invariant formula for carry classes, these identities let a global
character and an idele concentrated at one place produce an idele-cohomology class with a
prescribed sum of local invariants.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, Lemma 7.3.
* J.-P. Serre, *Local Fields*, Chapter XIV, §1.
-/

public section

noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField ContCohomology

variable {K : Type} [Field K] [NumberField K]

/-! ### Finite places -/

variable {v : HeightOneSpectrum (𝓞 K)}
  (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))

/-- **A global idele carry class localizes to the corresponding local carry class.** The local
character is obtained by restricting along the decomposition map, and its invariant coefficient
is the component of the global idele along the chosen embedding of separable closures. -/
theorem ideleBrLocalization_characterCarryCocycle
    (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))))
    (a : H0 (AbsoluteGaloisGroup K) (IdeleCoeff K)) :
    ideleBrLocalization v (characterCarryCocycle χ hχ a :
      H2 (AbsoluteGaloisGroup K) (IdeleCoeff K)) =
      unitsRepH2Equiv (v.adicCompletion K)
        (characterCarryCocycle
          (χ.comp (absoluteGaloisGroupMap τ :
            AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K).toAdditive)
          (by
            rw [← AddMonoidHom.comap_ker, AddSubgroup.coe_comap]
            exact hχ.preimage (continuous_ofMul.comp
              ((absoluteGaloisGroupMap τ).continuous.comp continuous_toMul)))
          (explicitMap0 (AbsoluteGaloisGroup K) (IdeleCoeff K)
            (absoluteGaloisGroupMap τ) (ideleCoeffComponent τ)
            (ideleCoeffComponent_smul τ) a) :
          H2 (AbsoluteGaloisGroup (v.adicCompletion K))
            (UnitsCoeff (v.adicCompletion K))) := by
  rw [ideleBrLocalization_apply τ, explicitMap2_mk,
    cocyclesMap2_characterCarryCocycle]

/-- A global idele carry class has zero localization at a finite place where its idele coefficient
has component `1` (written `0` in the additive coefficient module). -/
theorem ideleBrLocalization_characterCarryCocycle_eq_zero_of_component_eq_zero
    (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))))
    (a : H0 (AbsoluteGaloisGroup K) (IdeleCoeff K))
    (ha : ideleCoeffComponent τ (a : IdeleCoeff K) = 0) :
    ideleBrLocalization v (characterCarryCocycle χ hχ a :
      H2 (AbsoluteGaloisGroup K) (IdeleCoeff K)) = 0 := by
  rw [ideleBrLocalization_characterCarryCocycle τ]
  have ha' : explicitMap0 (AbsoluteGaloisGroup K) (IdeleCoeff K)
      (absoluteGaloisGroupMap τ :
        AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K)
      (ideleCoeffComponent τ)
      (ideleCoeffComponent_smul τ) a = 0 := by
    apply Subtype.ext
    simpa only [coe_explicitMap0, AddSubgroup.coe_zero] using ha
  rw [ha']
  simp

/-- **The local invariant of a global idele carry class.** Suppose the restricted global
character is the character of a finite unramified extension `E / K_v`, and the selected component
of the invariant idele is the image of `b ∈ K_vˣ`. Then the localized class has invariant
`v(b) · χ_v(Frob)`. -/
theorem invMap_ideleBrLocalization_characterCarryCocycle
    (E : IntermediateField (v.adicCompletion K)
      (SeparableClosure (v.adicCompletion K)))
    [FiniteDimensional (v.adicCompletion K) E]
    [IsGalois (v.adicCompletion K) E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [ValuativeExtension (v.adicCompletion K) E]
    [IsUnramified (v.adicCompletion K) E]
    (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))))
    (χv : Additive Gal(E/(v.adicCompletion K)) →+ AddCircle (1 : ℚ))
    (a : H0 (AbsoluteGaloisGroup K) (IdeleCoeff K)) (b : (v.adicCompletion K)ˣ)
    (hχv : χ.comp (absoluteGaloisGroupMap τ :
        AbsoluteGaloisGroup (v.adicCompletion K) →*
          AbsoluteGaloisGroup K).toAdditive =
      χv.comp (AlgEquiv.restrictNormalHom
        (K₁ := SeparableClosure (v.adicCompletion K)) E).toAdditive)
    (ha : ideleCoeffComponent τ (a : IdeleCoeff K) =
      (baseUnitsEquivInvariants (v.adicCompletion K) (.ofMul b) :
        UnitsCoeff (v.adicCompletion K))) :
    invMap (v.adicCompletion K)
        (ideleBrLocalization v (characterCarryCocycle χ hχ a :
          H2 (AbsoluteGaloisGroup K) (IdeleCoeff K))) =
      (normalizedValuation (v.adicCompletion K) b).toAdd •
        χv (.ofMul (frobeniusAlgEquiv (K := v.adicCompletion K) (L := E))) := by
  rw [ideleBrLocalization_characterCarryCocycle τ]
  have ha' : explicitMap0 (AbsoluteGaloisGroup K) (IdeleCoeff K)
      (absoluteGaloisGroupMap τ :
        AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K)
      (ideleCoeffComponent τ) (ideleCoeffComponent_smul τ) a =
        baseUnitsEquivInvariants (v.adicCompletion K) (.ofMul b) := by
    apply Subtype.ext
    simpa only [coe_explicitMap0] using ha
  simpa only [hχv, ha'] using invMap_characterCarryCocycle E χv b

/-! ### Infinite places -/

variable {w : InfinitePlace K}
  (τ : SeparableClosure K →ₐ[K] SeparableClosure w.Completion)

/-- **A global idele carry class localizes at an infinite place to the corresponding local carry
class.** The local character is the restriction along the archimedean decomposition map and the
coefficient is the selected infinite component of the idele. -/
theorem ideleInfiniteBrLocalization_characterCarryCocycle
    (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))))
    (a : H0 (AbsoluteGaloisGroup K) (IdeleCoeff K)) :
    ideleInfiniteBrLocalization w (characterCarryCocycle χ hχ a :
      H2 (AbsoluteGaloisGroup K) (IdeleCoeff K)) =
      unitsRepH2Equiv w.Completion
        (characterCarryCocycle
          (χ.comp (absoluteGaloisGroupMap τ :
            AbsoluteGaloisGroup w.Completion →* AbsoluteGaloisGroup K).toAdditive)
          (by
            rw [← AddMonoidHom.comap_ker, AddSubgroup.coe_comap]
            exact hχ.preimage (continuous_ofMul.comp
              ((absoluteGaloisGroupMap τ).continuous.comp continuous_toMul)))
          (explicitMap0 (AbsoluteGaloisGroup K) (IdeleCoeff K)
            (absoluteGaloisGroupMap τ) (ideleCoeffInfiniteComponent τ)
            (ideleCoeffInfiniteComponent_smul τ) a) :
          H2 (AbsoluteGaloisGroup w.Completion) (UnitsCoeff w.Completion)) := by
  rw [ideleInfiniteBrLocalization_apply τ, explicitMap2_mk,
    cocyclesMap2_characterCarryCocycle]

/-- A global idele carry class has zero localization at an infinite place where its idele
coefficient has component `1` (written `0` in the additive coefficient module). -/
theorem ideleInfiniteBrLocalization_characterCarryCocycle_eq_zero_of_component_eq_zero
    (χ : Additive (AbsoluteGaloisGroup K) →+ AddCircle (1 : ℚ))
    (hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup K))))
    (a : H0 (AbsoluteGaloisGroup K) (IdeleCoeff K))
    (ha : ideleCoeffInfiniteComponent τ (a : IdeleCoeff K) = 0) :
    ideleInfiniteBrLocalization w (characterCarryCocycle χ hχ a :
      H2 (AbsoluteGaloisGroup K) (IdeleCoeff K)) = 0 := by
  rw [ideleInfiniteBrLocalization_characterCarryCocycle τ]
  have ha' : explicitMap0 (AbsoluteGaloisGroup K) (IdeleCoeff K)
      (absoluteGaloisGroupMap τ :
        AbsoluteGaloisGroup w.Completion →* AbsoluteGaloisGroup K)
      (ideleCoeffInfiniteComponent τ)
      (ideleCoeffInfiniteComponent_smul τ) a = 0 := by
    apply Subtype.ext
    simpa only [coe_explicitMap0, AddSubgroup.coe_zero] using ha
  rw [ha']
  simp

end TauCeti.ClassFieldTheory
