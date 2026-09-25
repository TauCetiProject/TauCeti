/-
Copyright (c) 2026 The Tau Ceti contributors, Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Xavier Roblot
-/
module

public import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
public import TauCeti.NumberTheory.RamificationInertia.SeparableDegree

/-!
# Hilbert theory over arbitrary residue fields

For a finite Galois extension of Dedekind domains, write `D` and `E` for the decomposition
and inertia fields at `P`. The degree formulas are `[L : D] = e * f`, `[D : K] = g`,
`[L : E] = e * fᵢ`, and `[E : D] = fₛ`, where `fₛ` and `fᵢ` are the separable and inseparable
residue degrees. No finiteness or separability of the residue fields is assumed.

The prime of the decomposition ring below `P` has ramification index and inertia degree one
over the base. Thus all the ramification and residue degree at `P` remain above the
decomposition ring, including the inseparable residue degree.

## References

* J. Neukirch, *Algebraic Number Theory*, Ch. I (9.3) and (9.6).
* The decomposition-ring argument adapts Xavier Roblot's
  `Mathlib/NumberTheory/RamificationInertia/HilbertTheory.lean`, replacing its finite-residue
  cardinality input by the general formulas in `RamificationInertia/SeparableDegree.lean`.
-/

public section

open Ideal MulAction
open scoped Pointwise

namespace TauCeti

attribute [local instance] Ideal.Quotient.field

section Degrees

variable (A K L : Type*) {B : Type*} [CommRing A] [CommRing B] [Field K] [Field L]
  [Algebra A B] [Algebra K L] [FiniteDimensional K L] [MulSemiringAction Gal(L/K) B]
  [IsGaloisGroup Gal(L/K) A B] [IsDedekindDomain A] [IsDedekindDomain B]
  [Module.Finite A B] [Module.IsTorsionFree A B] (P : Ideal B) [P.IsMaximal]

variable (D : Type*) [Field D] [Algebra D L] [IsDecompositionField K L P D]

include K P in
/-- The degree above the decomposition field is `e * f`, also for inseparable residue
extensions. -/
theorem IsDecompositionField.finrank_eq_ramificationIdx_mul_inertiaDeg :
    Module.finrank D L = P.ramificationIdx A * P.inertiaDeg A := by
  rw [← IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L]
  exact P.card_stabilizer_eq_ramificationIdx_mul_inertiaDeg (R := A) (G := Gal(L/K))

omit [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [P.IsMaximal] in
/-- The degree of the decomposition field is the number of primes above the contracted prime,
without a residue-field hypothesis. -/
theorem IsDecompositionField.finrank_eq_ncard_primesOver [IsGalois K L]
    [P.IsPrime] [Algebra K D] [IsScalarTower K D L] :
    Module.finrank K D = ((P.under A).primesOver B).ncard := by
  have : FiniteDimensional D L := FiniteDimensional.right K D L
  have h := Nat.card_congr (orbitProdStabilizerEquivGroup Gal(L/K) P)
  rw [Nat.card_prod, Nat.card_coe_set_eq,
    Algebra.IsInvariant.orbit_eq_primesOver A B Gal(L/K) (P.under A) P,
    IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L,
    IsGaloisGroup.card_eq_finrank Gal(L/K) K L] at h
  exact mul_left_injective₀ Module.finrank_pos.ne'
    ((Module.finrank_mul_finrank K D L).trans h.symm)

variable (E : Type*) [Field E] [Algebra E L] [IsInertiaField K L P E]

include K P in
/-- The degree above the inertia field is the ramification index times the inseparable
residue degree. -/
theorem IsInertiaField.finrank_eq_ramificationIdx_mul_finInsepDegree :
    Module.finrank E L =
      P.ramificationIdx A * Field.finInsepDegree (A ⧸ P.under A) (B ⧸ P) := by
  rw [← IsGaloisGroup.card_eq_finrank (inertia Gal(L/K) P) E L]
  exact P.card_inertia_eq_ramificationIdx_mul_finInsepDegree (R := A) (G := Gal(L/K))

omit [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] in
include K L P in
/-- The degree of the inertia field over the decomposition field is the separable residue
degree. -/
theorem IsInertiaField.finrank_eq_finSepDegree [Algebra D E] [IsScalarTower D E L] :
    Module.finrank D E = Field.finSepDegree (A ⧸ P.under A) (B ⧸ P) := by
  have : FiniteDimensional D L := IsGaloisGroup.finiteDimensional (stabilizer Gal(L/K) P) D L
  have : FiniteDimensional E L := IsGaloisGroup.finiteDimensional (inertia Gal(L/K) P) E L
  apply mul_left_injective₀ (b := Module.finrank E L) Module.finrank_pos.ne'
  dsimp only
  rw [Module.finrank_mul_finrank,
    ← IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L,
    ← IsGaloisGroup.card_eq_finrank (inertia Gal(L/K) P) E L,
    card_stabilizer_eq_card_inertia_mul_finSepDegree (G := Gal(L/K)) (P.under A) P,
    mul_comm]

end Degrees

namespace IsDecompositionField

variable (A K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L]
  [CommRing A] [CommRing B] [Algebra A B] (P : Ideal B)
  [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L] [Algebra B L]
  [IsScalarTower A B L] [IsFractionRing B L] [MulSemiringAction Gal(L/K) B]
  [SMulDistribClass Gal(L/K) B L]
  (D 𝓞D : Type*) [Field D] [Algebra D L] [IsDecompositionField K L P D] [CommRing 𝓞D]
  [Algebra 𝓞D D] [IsFractionRing 𝓞D D] [Algebra 𝓞D B] [Algebra 𝓞D L]
  [IsScalarTower 𝓞D D L] [IsScalarTower 𝓞D B L]
  [IsGalois K L] [FiniteDimensional K L] [IsDedekindDomain A] [IsDedekindDomain B]
  [Module.Finite A B] [Module.IsTorsionFree A B] [Algebra A 𝓞D] [Module.Finite A 𝓞D]
  [IsScalarTower A 𝓞D B] [IsDedekindDomain 𝓞D] [P.IsMaximal]

omit [FiniteDimensional K L] [P.IsMaximal] in
include K L D P in
private theorem instances :
    Module.Finite 𝓞D B ∧ Module.IsTorsionFree 𝓞D B ∧ Module.IsTorsionFree A 𝓞D ∧
      IsGaloisGroup Gal(L/K) A B ∧ IsGaloisGroup (stabilizer Gal(L/K) P) 𝓞D B := by
  have : Module.Finite 𝓞D B := Module.Finite.right A 𝓞D B
  have : Module.IsTorsionFree 𝓞D B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    exact Algebra.IsAlgebraic.faithfulSMul_tower_top A 𝓞D B
  have : Module.IsTorsionFree A 𝓞D := Module.IsTorsionFree.of_faithfulSMul _ _ B
  exact ⟨inferInstance, inferInstance, inferInstance,
    .of_isFractionRing _ _ _ K L, .of_isFractionRing _ _ _ D L⟩

include K L D P in
private theorem ramificationIdx_eq_and_inertiaDeg_eq :
    P.ramificationIdx 𝓞D = P.ramificationIdx A ∧ P.inertiaDeg 𝓞D = P.inertiaDeg A := by
  obtain ⟨_, _, _, _, _⟩ := instances A K L P D 𝓞D
  refine eq_and_eq_of_pos_of_le_of_mul_le_mul
    (ramificationIdx_pos 𝓞D P) (inertiaDeg_pos P 𝓞D)
    ((P.under 𝓞D).ramificationIdx_above_le P) (inertiaDeg_above_le (P.under 𝓞D) P) ?_
  have h := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (P.under 𝓞D) B (stabilizer Gal(L/K) P)
  rw [_root_.IsDecompositionField.primesOver_eq_singleton K L P D 𝓞D (P.under 𝓞D),
    Set.ncard_singleton, one_mul,
    ramificationIdxIn_eq_ramificationIdx (P.under 𝓞D) P (stabilizer Gal(L/K) P),
    inertiaDegIn_eq_inertiaDeg (P.under 𝓞D) P (stabilizer Gal(L/K) P),
    card_stabilizer_eq_ramificationIdx_mul_inertiaDeg (R := A) (G := Gal(L/K)) P] at h
  exact h.ge

include K L D P in
/-- Passing to the decomposition ring preserves the ramification index at `P`, with no
residue-field hypothesis. -/
theorem ramificationIdx_eq : P.ramificationIdx 𝓞D = P.ramificationIdx A :=
  (ramificationIdx_eq_and_inertiaDeg_eq A K L P D 𝓞D).1

include K L D P in
/-- Passing to the decomposition ring preserves the full residue degree at `P`, including its
inseparable part. -/
theorem inertiaDeg_eq : P.inertiaDeg 𝓞D = P.inertiaDeg A :=
  (ramificationIdx_eq_and_inertiaDeg_eq A K L P D 𝓞D).2

include K L D P in
/-- The prime contracted to the decomposition ring has ramification index one over the base. -/
theorem ramificationIdx_under_eq_one : (P.under 𝓞D).ramificationIdx A = 1 := by
  obtain ⟨_, _, _, _, _⟩ := instances A K L P D 𝓞D
  have h := ramificationIdx_tower (R := A) (P.under 𝓞D) P
  rw [ramificationIdx_eq A K L P D 𝓞D] at h
  exact (right_eq_mul₀ (ramificationIdx_pos A P).ne').mp h

include K L D P in
/-- The prime contracted to the decomposition ring has residue degree one over the base,
even when the residue extension at `P` is inseparable. -/
theorem inertiaDeg_under_eq_one : (P.under 𝓞D).inertiaDeg A = 1 := by
  obtain ⟨_, _, _, _, _⟩ := instances A K L P D 𝓞D
  have h := inertiaDeg_tower (R := A) (P.under 𝓞D) P
  rw [inertiaDeg_eq A K L P D 𝓞D] at h
  exact (right_eq_mul₀ (inertiaDeg_pos P A).ne').mp h

end IsDecompositionField

end TauCeti
