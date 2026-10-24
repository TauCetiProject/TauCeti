/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Minimal polynomials in torsion-free algebras

Over an integrally closed domain `R`, the minimal polynomial of an integral element of a
torsion-free commutative `R`-algebra divides every polynomial annihilating that element.
The algebra may have zero divisors or nilpotents. This permits minimal equations to be used
for finite torsion-free algebras without passing to their domain quotients.

The argument extends the fraction-field comparison in
`minpoly.isIntegrallyClosed_eq_field_fractions`: Gauss's lemma descends the monic minimal
polynomial from a fraction-field algebra, and torsion-freeness makes the localization injective.
No irreducibility of the minimal polynomial is asserted.
-/

public section

open Polynomial
open minpoly (monic)
open scoped TensorProduct

namespace TauCeti.minpoly

variable {R S : Type*} [CommRing R] [IsIntegrallyClosed R]
  [CommRing S] [Algebra R S]

/-- The minimal polynomial over an integrally closed domain of an integral element commutes
with an injection into an algebra over its fraction field. The target algebra need not be a
domain or reduced. -/
theorem isIntegrallyClosed_eq_field_fractions_of_injective
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    {L : Type*} [CommRing L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    (φ : S →ₐ[R] L) (hφ : Function.Injective φ) {s : S} (hs : IsIntegral R s) :
    minpoly K (φ s) = (minpoly R s).map (algebraMap R K) := by
  have hs' : IsIntegral R (φ s) := hs.map φ
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K (monic hs)
    (minpoly.dvd K (φ s) (by
      rw [aeval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero]))
  rw [(monic hs'.tower_top).leadingCoeff, C_1, mul_one] at hp
  have hpm : p.Monic := (IsFractionRing.injective R K).monic_map_iff.mpr
    (hp.symm ▸ monic hs'.tower_top)
  have hps : Polynomial.aeval s p = 0 := by
    apply hφ
    rw [map_zero, ← aeval_algHom_apply φ, ← aeval_map_algebraMap K, hp, minpoly.aeval]
  have heq : p = minpoly R s := by
    apply minpoly.unique' R s hpm hps
    intro q hq
    by_cases hq0 : q = 0
    · exact Or.inl hq0
    refine Or.inr fun hqs ↦ ?_
    have hle := minpoly.degree_le_of_ne_zero K (φ s)
      ((Polynomial.map_ne_zero_iff (IsFractionRing.injective R K)).mpr hq0) (by
        rw [aeval_map_algebraMap K, aeval_algHom_apply, hqs, map_zero])
    rw [← hp, degree_map_eq_of_injective (IsFractionRing.injective R K),
      degree_map_eq_of_injective (IsFractionRing.injective R K)] at hle
    exact hq.not_ge hle
  rw [← hp, heq]

/-- In a torsion-free commutative algebra over an integrally closed domain, the minimal
polynomial of an integral element divides every polynomial annihilating it. This includes
algebras with zero divisors and nilpotents. -/
theorem isIntegrallyClosed_dvd_of_isTorsionFree [IsDomain R] [Module.IsTorsionFree R S]
    {s : S} (hs : IsIntegral R s) {p : R[X]} (hp : Polynomial.aeval s p = 0) : minpoly R s ∣ p := by
  let K := FractionRing R
  let L := K ⊗[R] S
  let φ : S →ₐ[R] L := Algebra.TensorProduct.includeRight
  have hφ : Function.Injective φ :=
    (IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors R) (TensorProduct.mk R K S 1)).mpr
      fun c ↦ (isRegular_iff_mem_nonZeroDivisors.mpr c.2).isSMulRegular
  rw [← map_dvd_map (algebraMap R K) (IsFractionRing.injective R K) (monic hs),
    ← isIntegrallyClosed_eq_field_fractions_of_injective K φ hφ hs]
  exact minpoly.dvd K (φ s) (by
    rw [aeval_map_algebraMap, aeval_algHom_apply, hp, map_zero])

end TauCeti.minpoly
