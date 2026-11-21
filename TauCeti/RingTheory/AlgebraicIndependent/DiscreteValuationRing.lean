/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.FractionRing

import TauCeti.RingTheory.MvPolynomial.Basic
import TauCeti.RingTheory.MvPolynomial.DiscreteValuationRing

/-!
# Lifting algebraic independence from the residue fibre of a discrete valuation ring

If elements `y : ι → D` of an `R`-algebra `D` without zero divisors over a discrete valuation ring
`R` become algebraically independent over `ResidueField R` modulo an ideal `q` lying over
`maximalIdeal R`, and a uniformizer `π` maps to a nonzero element of `D`, then their images along
any injective algebra map `D → E` into a `K`-algebra `E` (where `K` is a fraction field of `R`) are
algebraically independent over `K` (`AlgebraicIndependent.of_quotient_residueField`).

## Main results

* `AlgebraicIndependent.of_quotient_residueField`: lifting algebraic independence from the special
  fibre modulo `q` to the generic fibre over `K`.
-/

public section

namespace AlgebraicIndependent

/-- Elements of an `R`-algebra `D` without zero divisors over a discrete valuation ring `R` whose
residues modulo an ideal `q` above `maximalIdeal R` are algebraically independent over
`ResidueField R` have images in `E` algebraically independent over `K`, provided `π` maps to a
nonzero element of `D` and `D → E` is injective. -/
theorem of_quotient_residueField {R K D E ι : Type*}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing D] [NoZeroDivisors D] [Algebra R D]
    [CommRing E] [Algebra R E] [Algebra K E] [Algebra D E]
    [IsScalarTower R K E] [IsScalarTower R D E]
    {π : R} (hπ : Irreducible π) (hπD : algebraMap R D π ≠ 0)
    (hinj : Function.Injective (algebraMap D E)) (q : Ideal D)
    [Algebra (IsLocalRing.ResidueField R) (D ⧸ q)]
    [IsScalarTower R (IsLocalRing.ResidueField R) (D ⧸ q)] (y : ι → D)
    (hy : AlgebraicIndependent (IsLocalRing.ResidueField R) fun i ↦ Ideal.Quotient.mk q (y i)) :
    AlgebraicIndependent K (fun i ↦ algebraMap D E (y i)) := by
  rw [algebraicIndependent_iff_injective_aeval] at hy
  rw [algebraicIndependent_iff]
  intro f heval
  by_contra hf
  obtain ⟨f₁, hf₁, heval₁⟩ :=
    TauCeti.MvPolynomial.exists_ne_zero_and_aeval_eq_zero_of_isLocalization
      (nonZeroDivisors R) hinj y hf heval
  obtain ⟨n, g, m₀, rfl, hndvd⟩ := MvPolynomial.exists_C_pow_mul_and_not_dvd_coeff hπ hf₁
  rw [map_mul, MvPolynomial.aeval_C, map_pow, mul_eq_zero] at heval₁
  have hg0 : MvPolynomial.aeval y g = 0 := heval₁.resolve_left (pow_ne_zero n hπD)
  let φ : D →+* D ⧸ q := Ideal.Quotient.mk q
  have hcomm : φ.comp (algebraMap R D) =
      (algebraMap (IsLocalRing.ResidueField R) (D ⧸ q)).comp (IsLocalRing.residue R) := by
    ext r
    exact IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R) (D ⧸ q) r
  have hres : MvPolynomial.aeval (R := IsLocalRing.ResidueField R) (fun i ↦ φ (y i))
      (MvPolynomial.map (IsLocalRing.residue R) g) = 0 := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← hcomm, ← MvPolynomial.hom_eval₂,
      ← MvPolynomial.aeval_def, hg0, map_zero]
  have hg_map : MvPolynomial.map (IsLocalRing.residue R) g = 0 :=
    hy (hres.trans (map_zero _).symm)
  have hm₀_zero : IsLocalRing.residue R (g.coeff m₀) = 0 := by
    rw [← MvPolynomial.coeff_map, hg_map]
    rfl
  rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm₀_zero
  exact hndvd hm₀_zero

end AlgebraicIndependent
