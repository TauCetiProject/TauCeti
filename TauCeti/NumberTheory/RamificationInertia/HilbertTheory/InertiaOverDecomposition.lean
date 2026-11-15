/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.RamificationInertia.HilbertTheory.Basic
public import TauCeti.NumberTheory.RamificationInertia.HilbertTheory.ResidueDegree
public import TauCeti.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Finiteness.Quotient

/-!
# The prime of the decomposition ring in the inertia ring

Let `L/K` be a finite Galois extension, `B` a domain with fraction field `L` over a Dedekind
domain `A` with fraction field `K`, and `P` a maximal ideal of `B`. Hilbert theory cuts out the
tower `K ⊆ D ⊆ E ⊆ L` of the decomposition and inertia fields of `P`, with Dedekind subrings
`A ⊆ 𝓞D ⊆ 𝓞E ⊆ B`. Writing `𝓟D` and `𝓟E` for the primes of `𝓞D` and `𝓞E` below `P`,
`TauCeti/NumberTheory/RamificationInertia/HilbertTheory/ResidueDegree.lean` describes `𝓟D` over
the base, and `TauCeti/NumberTheory/RamificationInertia/HilbertTheory/Basic.lean` describes `P`
over `𝓟E` and `𝓟E` over the base.

This file supplies the middle step of the tower, `𝓟E` over `𝓟D`: the prime `𝓟D` is inert in
`𝓞E`. That is, `𝓟E` is the only prime of `𝓞E` above `𝓟D`, it has ramification index `1` over
`𝓟D`, and its residue degree over `𝓟D` is the separable residue degree `fₛ` of `P` over the
base. These hold without separability of the residue extension at `P`. When that extension is
separable, `fₛ` is the full residue degree `f`: all of the residue degree of `P` is gained between
the decomposition and inertia rings, matching the field degree `[E : D] = f`.

## Main results

* `TauCeti.IsDecompositionField.primesOver_under_eq_singleton_under`: for every ring `S`
  between `𝓞D` and `B`, the prime of `S` below `P` is the only prime of `S` above `𝓟D`; for
  `S = 𝓞E` this is `𝓟E`.
* `TauCeti.IsInertiaField.ramificationIdx_under_eq_one_of_isDecompositionField`: `𝓟E` is
  unramified over `𝓟D`.
* `TauCeti.IsInertiaField.inertiaDeg_under_eq_finSepDegree_of_isDecompositionField`: the
  residue degree of `𝓟E` over `𝓟D` is `fₛ`.
* `TauCeti.IsInertiaField.inertiaDeg_under_eq_of_isDecompositionField`: when the residue
  extension at `P` is separable, the residue degree of `𝓟E` over `𝓟D` is `f`.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer 1999, Ch. I (9.6).
-/

public section

open Ideal MulAction
open scoped Pointwise

namespace TauCeti

namespace IsDecompositionField

variable (K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L] [CommRing B] (P : Ideal B)
  [Algebra B L] [IsFractionRing B L] [MulSemiringAction Gal(L/K) B]
  [SMulDistribClass Gal(L/K) B L]
  (D 𝓞D : Type*) [Field D] [Algebra D L] [IsDecompositionField K L P D] [CommRing 𝓞D]
  [Algebra 𝓞D D] [IsFractionRing 𝓞D D] [Algebra 𝓞D B] [Algebra 𝓞D L] [IsScalarTower 𝓞D D L]
  [IsScalarTower 𝓞D B L]

include K L D in
/-- Let `D` be the decomposition field of `P` in `L/K`. Then for every ring `S` between `𝓞D`
and `B`, the prime `P.under S` is the only prime of `S` above `P.under 𝓞D`. For `S` the inertia
ring, this says that the prime of the decomposition ring below `P` stays prime there. -/
theorem primesOver_under_eq_singleton_under [P.IsPrime] [Finite (stabilizer Gal(L/K) P)]
    [IsIntegrallyClosed 𝓞D] [Algebra.IsIntegral 𝓞D B] (S : Type*) [CommRing S] [Algebra 𝓞D S]
    [Algebra S B] [IsScalarTower 𝓞D S B] [FaithfulSMul S B] :
    primesOver (P.under 𝓞D) S = {P.under S} :=
  have : Algebra.IsIntegral S B := .tower_top 𝓞D
  primesOver_eq_singleton_under_of_primesOver_eq_singleton
    (_root_.IsDecompositionField.primesOver_eq_singleton K L P D 𝓞D (P.under 𝓞D))

end IsDecompositionField

namespace IsInertiaField

attribute [local instance] Ideal.Quotient.field

variable (A K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L] [CommRing A] [CommRing B]
  [Algebra A B] (P : Ideal B)
  [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L] [Algebra B L]
  [IsScalarTower A B L] [IsFractionRing B L] [MulSemiringAction Gal(L/K) B]
  [SMulDistribClass Gal(L/K) B L]

variable (D 𝓞D : Type*) [Field D] [Algebra D L] [IsDecompositionField K L P D] [CommRing 𝓞D]
  [Algebra 𝓞D D] [IsFractionRing 𝓞D D] [Algebra 𝓞D B] [Algebra 𝓞D L] [IsScalarTower 𝓞D D L]
  [IsScalarTower 𝓞D B L]

variable (E 𝓞E : Type*) [Field E] [Algebra E L] [IsInertiaField K L P E] [CommRing 𝓞E]
  [Algebra 𝓞E E] [IsFractionRing 𝓞E E] [Algebra 𝓞E B] [Algebra 𝓞E L] [IsScalarTower 𝓞E E L]
  [IsScalarTower 𝓞E B L] [Algebra 𝓞D 𝓞E] [IsScalarTower 𝓞D 𝓞E B]

variable [IsGalois K L] [FiniteDimensional K L] [IsDedekindDomain A] [IsDomain B]
  [Module.Finite A B]
  [Algebra A 𝓞D] [IsScalarTower A 𝓞D B] [IsDedekindDomain 𝓞D]
  [Algebra A 𝓞E] [IsScalarTower A 𝓞E B] [IsDedekindDomain 𝓞E]
  [P.IsMaximal]

include A K L D E P in
/-- Let `D` and `E` be the decomposition and inertia fields of `P` in `L/K`. Then `P.under 𝓞E`
has ramification index `1` over `P.under 𝓞D`. No separability of the residue extension is
assumed. -/
theorem ramificationIdx_under_eq_one_of_isDecompositionField :
    (P.under 𝓞E).ramificationIdx 𝓞D = 1 := by
  have : FaithfulSMul 𝓞E B := .of_field_isFractionRing 𝓞E B E L
  have h := ramificationIdx_tower (R := 𝓞D) (P.under 𝓞E) P
  rw [IsDecompositionField.ramificationIdx_eq A K L P D 𝓞D,
    ramificationIdx_eq A K L P E 𝓞E] at h
  exact (right_eq_mul₀ (ramificationIdx_pos A P).ne').mp h

include A K L D E P in
/-- Let `D` and `E` be the decomposition and inertia fields of `P` in `L/K`. Then the inertia
degree of `P.under 𝓞E` over `P.under 𝓞D` is the separable residue degree of `P` over
`P.under A`. -/
theorem inertiaDeg_under_eq_finSepDegree_of_isDecompositionField :
    (P.under 𝓞E).inertiaDeg 𝓞D = Field.finSepDegree (A ⧸ P.under A) (B ⧸ P) := by
  have h := inertiaDeg_tower (R := 𝓞D) (P.under 𝓞E) P
  rw [IsDecompositionField.inertiaDeg_eq A K L P D 𝓞D, inertiaDeg_eq_finInsepDegree A K L P E 𝓞E,
    inertiaDeg_eq_of_isMaximal (P.under A) P, ← Field.finSepDegree_mul_finInsepDegree] at h
  exact (Nat.eq_of_mul_eq_mul_right
    (NeZero.pos (Field.finInsepDegree (A ⧸ P.under A) (B ⧸ P))) h).symm

include A K L D E P in
/-- Let `D` and `E` be the decomposition and inertia fields of `P` in `L/K`. When the residue
extension of `P` over `P.under A` is separable, the inertia degree of `P.under 𝓞E` over
`P.under 𝓞D` is the full inertia degree of `P` over `P.under A`. -/
theorem inertiaDeg_under_eq_of_isDecompositionField
    [Algebra.IsSeparable (A ⧸ P.under A) (B ⧸ P)] :
    (P.under 𝓞E).inertiaDeg 𝓞D = P.inertiaDeg A := by
  rw [inertiaDeg_under_eq_finSepDegree_of_isDecompositionField A K L P D 𝓞D E 𝓞E,
    Field.finSepDegree_eq_finrank_of_isSeparable, inertiaDeg_eq_of_isMaximal (P.under A) P]

end IsInertiaField

end TauCeti
