/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Basic
import TauCeti.FieldTheory.Normal.FixedField
import TauCeti.RingTheory.Valuation.Normal
import TauCeti.RingTheory.Valuation.ValuationSubring

/-!
# Valuation spectra of purely inseparable and normal field extensions

This file transfers the extension, uniqueness, and conjugacy theorems for valuation subrings
(`TauCeti.RingTheory.Valuation.Normal`) to the valuation spectrum `Spv`.

* Along any field homomorphism `φ : K →+* L`, the restriction map `Spv L → Spv K` is surjective
  (`TauCeti.ValuationSpectrum.comap_surjective_of_field`).
* Along a purely inseparable field extension `L / K`, restriction `Spv L → Spv K` is bijective
  (`TauCeti.ValuationSpectrum.comap_bijective_of_isPurelyInseparable`). In particular, for any
  normal extension `L / K`, restriction from the fixed field `L^{Aut(L/K)}` to `K` is bijective
  (`TauCeti.ValuationSpectrum.comap_bijective_fixedField_top`).
* For a normal extension `L / K` with `Aut(L/K)` finite, the fibres of `Spv L → Spv K` are the
  `Aut(L/K)`-orbits
  (`TauCeti.ValuationSpectrum.comap_algebraMap_eq_comap_algebraMap_iff_of_normal`).

## References

* A. J. Engler and A. Prestel, *Valued Fields*, Springer, 2005, Theorem 3.2.15.
* D. Hansen, *Quotients of adic spaces by finite groups*, Math. Res. Lett. 28 (2021), Step 1 of
  the proof of Theorem 3.1.
-/

public section

namespace TauCeti.ValuationSpectrum

section Field

variable {K L : Type*} [Field K] [Field L]

/-- **Extension of valuations along a field homomorphism.** Restriction `Spv L → Spv K` along any
field homomorphism `φ : K →+* L` is surjective. -/
theorem comap_surjective_of_field (φ : K →+* L) : Function.Surjective (comap φ) := fun v ↦ by
  obtain ⟨W, hW⟩ := ValuationSubring.comap_surjective φ v.valuation.valuationSubring
  dsimp only at hW
  refine ⟨ofValuation W.valuation, ?_⟩
  rw [comap_ofValuation_valuation, hW, ofValuation_valuationSubring_valuation]

end Field

section PurelyInseparable

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Uniqueness of extensions along a purely inseparable field extension.** Restriction
`Spv L → Spv K` along a purely inseparable extension is bijective. -/
theorem comap_bijective_of_isPurelyInseparable [IsPurelyInseparable K L] :
    Function.Bijective (comap (algebraMap K L)) := by
  refine ⟨fun w₁ w₂ h ↦ ?_, comap_surjective_of_field (algebraMap K L)⟩
  have hsub : w₁.valuation.valuationSubring.comap (algebraMap K L) =
      w₂.valuation.valuationSubring.comap (algebraMap K L) := by
    rw [← valuationSubring_valuation_comap, h, valuationSubring_valuation_comap]
  have heq := ValuationSubring.comap_injective_of_isPurelyInseparable hsub
  rw [← ofValuation_valuationSubring_valuation w₁, heq, ofValuation_valuationSubring_valuation]

/-- For a normal extension `L / K`, restriction on valuation spectra from the fixed field
`L^{Aut(L/K)}` to `K` is bijective, since `L^{Aut(L/K)} / K` is purely inseparable. -/
theorem comap_bijective_fixedField_top [Normal K L] :
    Function.Bijective
      (comap (algebraMap K (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))))) :=
  have := TauCeti.IntermediateField.isPurelyInseparable_fixedField_top K L
  comap_bijective_of_isPurelyInseparable

end PurelyInseparable

section Normal

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Normal K L] [Finite (L ≃ₐ[K] L)]

/-- **Fibres of `Spv L → Spv K` for a normal extension with finite automorphism group.** Two points
of `Spv L` have the same restriction to `K` if and only if they differ by an element of
`L ≃ₐ[K] L`. -/
theorem comap_algebraMap_eq_comap_algebraMap_iff_of_normal {v w : Spv L} :
    comap (algebraMap K L) v = comap (algebraMap K L) w ↔
      ∃ σ : L ≃ₐ[K] L, w = comap (σ : L →+* L) v := by
  constructor
  · intro h
    have hsub : v.valuation.valuationSubring.comap (algebraMap K L) =
        w.valuation.valuationSubring.comap (algebraMap K L) := by
      rw [← valuationSubring_valuation_comap, h, valuationSubring_valuation_comap]
    obtain ⟨σ, hσ⟩ := ValuationSubring.exists_algEquiv_comap_eq_of_comap_eq hsub
    refine ⟨σ, ?_⟩
    rw [← ofValuation_valuationSubring_valuation w, ← hσ, ← comap_ofValuation_valuation,
      ofValuation_valuationSubring_valuation]
  · rintro ⟨σ, rfl⟩
    rw [comap_comap]
    exact congrFun (congrArg comap (RingHom.ext fun a ↦ (σ.commutes a).symm)) v

end Normal

end TauCeti.ValuationSpectrum
