/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.MvPolynomial.Basic

import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Multivariate polynomials over localizations

Clearing denominators in a multivariate polynomial over a localization `M⁻¹ R` multiplies it by
the image of some `d ∈ M` into the image of `MvPolynomial ι R`
(`MvPolynomial.exists_map_eq_smul_of_isLocalization`), preserving nonvanishing and vanishing under
injective algebra maps (`TauCeti.MvPolynomial.exists_ne_zero_and_aeval_eq_zero_of_isLocalization`).

## Main results

* `MvPolynomial.exists_map_eq_smul_of_isLocalization`: clearing denominators in a multivariate
  polynomial over a localization `M⁻¹ R`.
* `TauCeti.MvPolynomial.exists_ne_zero_and_aeval_eq_zero_of_isLocalization`: a nonzero polynomial
  relation over a localization `M⁻¹ R` evaluated along an injective map `D → E` yields a nonzero
  polynomial relation over `R` in `D`.
-/

public section

namespace MvPolynomial

/-- Clearing denominators in a multivariate polynomial `f` over a localization `K` of `R` at `M`
produces `d ∈ M` and a polynomial `f₁` over `R` whose image in `K` equals `d • f`. -/
theorem exists_map_eq_smul_of_isLocalization {R K ι : Type*}
    [CommRing R] [CommRing K] [Algebra R K] (M : Submonoid R) [IsLocalization M K]
    (f : MvPolynomial ι K) :
    ∃ (d : M) (f₁ : MvPolynomial ι R),
      MvPolynomial.map (algebraMap R K) f₁ = algebraMap R K d • f := by
  let := MvPolynomial.algebraMvPolynomial (R := R) (S := K) (σ := ι)
  obtain ⟨⟨f₁, _, d, hd, rfl⟩, h⟩ := IsLocalization.surj (M.map (MvPolynomial.C (σ := ι))) f
  refine ⟨⟨d, hd⟩, f₁, ?_⟩
  dsimp only at h
  rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C, mul_comm, ← MvPolynomial.smul_eq_C_mul] at h
  exact h.symm

end MvPolynomial

namespace TauCeti

/-- Clearing denominators in a nonzero multivariate polynomial over a localization `K` of `R` at
`M` produces a nonzero polynomial over `R` with the same vanishing under an injective algebra map
`D → E`. -/
theorem MvPolynomial.exists_ne_zero_and_aeval_eq_zero_of_isLocalization {R K D E ι : Type*}
    [CommRing R] [CommRing K] [Algebra R K] (M : Submonoid R) [IsLocalization M K]
    [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] [Algebra K E] [Algebra D E]
    [IsScalarTower R K E] [IsScalarTower R D E]
    (hinj : Function.Injective (algebraMap D E)) (y : ι → D) {f : MvPolynomial ι K} (hf : f ≠ 0)
    (heval : MvPolynomial.aeval (fun i ↦ algebraMap D E (y i)) f = 0) :
    ∃ f₁ : MvPolynomial ι R, f₁ ≠ 0 ∧ MvPolynomial.aeval y f₁ = 0 := by
  obtain ⟨d, f₁, hf₁_map⟩ := _root_.MvPolynomial.exists_map_eq_smul_of_isLocalization M f
  refine ⟨f₁, fun h0 ↦ hf ?_, hinj ?_⟩
  · obtain ⟨u, hu⟩ := IsLocalization.map_units K d
    have hsmul : u • f = 0 := by rw [Units.smul_def, hu, ← hf₁_map, h0, map_zero]
    rw [← inv_smul_smul u f, hsmul, smul_zero]
  · have hcomm : (algebraMap K E).comp (algebraMap R K) =
        (algebraMap D E).comp (algebraMap R D) := by
      ext r
      rw [RingHom.comp_apply, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R K E,
        ← IsScalarTower.algebraMap_apply R D E]
    have hmap : algebraMap D E (MvPolynomial.aeval y f₁) =
        MvPolynomial.aeval (fun i ↦ algebraMap D E (y i))
          (MvPolynomial.map (algebraMap R K) f₁) :=
      _root_.MvPolynomial.map_aeval_eq_aeval_map (algebraMap R K) (algebraMap D E) hcomm f₁ y
    rw [map_zero, hmap, hf₁_map, map_smul, heval, smul_zero]

end TauCeti
