/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Residual characters of algebras over a local ring

Let `O` be a local ring with residue field `κ` and `H` a commutative `O`-algebra. An `O`-algebra
map `χ : H → κ` is a residual character of `H`, such as the system of eigenvalues of a commuting
family of operators on a residual eigenvector. Its kernel is a prime of `H` lying over the maximal
ideal of `O`. When `O` is a domain and `H` has going down, some prime below that kernel meets `O`
only in zero, and when `H` is moreover integral over `O`, the quotient by such a prime embeds in an
algebraic closure of the fraction field of `O`. These are the first steps of Deligne–Serre's
lifting of a residual character to characteristic zero.

## Main results

* `AlgHom.under_ker_eq_maximalIdeal`: the kernel of a residual character lies over the maximal
  ideal.
* `AlgHom.exists_isPrime_le_ker_under_eq_bot`: under going down, a prime below the kernel of a
  residual character meets the base only in zero.
* `AlgHom.exists_algHom_algebraicClosure_ker_le`: an integral algebra with going down has an
  `O`-algebra map to an algebraic closure of `K` whose kernel lies in the kernel of a given
  residual character.

## References

* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7
  (1974), 507–530, proof of Lemme 6.11.
-/

public section

open IsLocalRing

namespace AlgHom

variable {O H : Type*} [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H]

/-- The kernel of an `O`-algebra map to the residue field of `O` lies over the maximal ideal. -/
theorem under_ker_eq_maximalIdeal (χ : H →ₐ[O] ResidueField O) :
    (RingHom.ker χ).under O = maximalIdeal O := by
  ext x
  simp [Ideal.under, RingHom.mem_ker, ResidueField.algebraMap_eq, residue_eq_zero_iff]

/-- The kernel of a residual character, as a prime lying over the maximal ideal. -/
instance liesOver_ker (χ : H →ₐ[O] ResidueField O) :
    (RingHom.ker χ).LiesOver (maximalIdeal O) :=
  ⟨χ.under_ker_eq_maximalIdeal.symm⟩

/-- Under going down over a local domain `O`, some prime below the kernel of a residual character
meets `O` only in zero. -/
theorem exists_isPrime_le_ker_under_eq_bot [IsDomain O] [Algebra.HasGoingDown O H]
    (χ : H →ₐ[O] ResidueField O) :
    ∃ P ≤ RingHom.ker χ, P.IsPrime ∧ P.under O = ⊥ := by
  have := RingHom.ker_isPrime χ
  obtain ⟨P, hPQ, hP, hlies⟩ :=
    (RingHom.ker χ).exists_ideal_le_liesOver_of_le (p := ⊥) (q := maximalIdeal O) bot_le
  exact ⟨P, hPQ, hP, hlies.over.symm⟩

/-- An integral algebra `H` with going down over a local domain `O` has an `O`-algebra map to an
algebraic closure of the fraction field `K` of `O` whose kernel lies in the kernel of a given
residual character. -/
theorem exists_algHom_algebraicClosure_ker_le [IsDomain O] [Algebra.HasGoingDown O H]
    [Algebra.IsIntegral O H] (χ : H →ₐ[O] ResidueField O) (K : Type*) [Field K] [Algebra O K]
    [IsFractionRing O K] :
    ∃ φ : H →ₐ[O] AlgebraicClosure K, RingHom.ker φ ≤ RingHom.ker χ := by
  obtain ⟨P, hPQ, hP, hbot⟩ := χ.exists_isPrime_le_ker_under_eq_bot
  have hinj : Function.Injective (algebraMap O (H ⧸ P)) := by
    rw [RingHom.injective_iff_ker_eq_bot, ← hbot]
    ext x
    simp [Ideal.under, ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
  have hΩ := algebraMap_injective_of_field_isFractionRing O (AlgebraicClosure K) K
    (AlgebraicClosure K)
  have := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have := Module.isTorsionFree_iff_algebraMap_injective.mpr hΩ
  have : Algebra.IsAlgebraic O (H ⧸ P) := Algebra.IsIntegral.isAlgebraic
  let ι : H ⧸ P →ₐ[O] AlgebraicClosure K := IsAlgClosed.lift
  -- `ι` is injective: its kernel meets `O` only in zero, and `H ⧸ P` is integral over `O`.
  have hι : Function.Injective ι := (RingHom.injective_iff_ker_eq_bot ι).mpr <|
    Ideal.eq_bot_of_under_eq_bot (R := O) <| by
      ext x
      simp [map_eq_zero_iff _ hΩ]
  refine ⟨ι.comp (Ideal.Quotient.mkₐ O P), fun x hx ↦ hPQ ?_⟩
  simpa [map_eq_zero_iff _ hι, Ideal.Quotient.eq_zero_iff_mem] using hx

end AlgHom
