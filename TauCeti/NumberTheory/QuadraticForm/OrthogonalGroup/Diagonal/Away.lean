/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.Diagonal.Finite
public import TauCeti.Topology.Algebra.RestrictedProduct.Away.Basic

/-!
# Rational orthogonal and Spin points away from a set of primes

The rational diagonals in the restricted products away from `S` are the restrictions of the
finite adelic diagonals. Their coordinates are the usual scalar extensions at the primes outside
`S`, and they commute with the componentwise maps `Spin → SO → O`.

The target groups are instances of `TauCeti.RestrictedProductGroupAway`, with the compatible
orthogonal, special orthogonal and Spin reference families. No finiteness assumption on `S` is
needed to construct the maps. Injectivity needs only one prime outside `S`; in particular it holds
for every finite `S`, by `Set.Finite.exists_notMem`. Omitting every prime would instead leave a
trivial target, so no unconditional injectivity statement is made.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §101.
* A. Weil, *Adeles and Algebraic Groups* (1982), Chapter I.
-/

public section

namespace TauCeti
namespace QuadraticMap
namespace OrthogonalCompactOpens

open _root_.QuadraticMap

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  {Q : QuadraticForm ℚ V} (U : OrthogonalCompactOpens Q) (S : Set Nat.Primes)

/-- The rational orthogonal diagonal away from `S`, obtained by forgetting the finite diagonal's
coordinates in `S`. -/
def awayAdelicOrthogonalDiagonal :
    orthogonalGroup Q →* RestrictedProductGroupAway S U.orthogonal :=
  (restrictAway S U.orthogonal).comp U.finiteAdelicOrthogonalDiagonal

/-- At a prime outside `S`, the orthogonal diagonal is scalar extension to that prime. -/
@[simp]
theorem awayAdelicOrthogonalDiagonal_apply (g : orthogonalGroup Q)
    (p : {p : Nat.Primes // p ∉ S}) :
    U.awayAdelicOrthogonalDiagonal S g p = orthogonalGroupBaseChange (A := ℚ_[(p.1 : ℕ)]) Q g := by
  simp [awayAdelicOrthogonalDiagonal]

/-- Restricting the finite orthogonal diagonal gives the diagonal away from `S`. -/
@[simp]
theorem restrictAway_comp_finiteAdelicOrthogonalDiagonal :
    (restrictAway S U.orthogonal).comp U.finiteAdelicOrthogonalDiagonal =
      U.awayAdelicOrthogonalDiagonal S := (rfl)

/-- The orthogonal diagonal away from `S` is injective when some prime remains. For finite `S`,
the hypothesis is supplied by `Set.Finite.exists_notMem`. -/
theorem awayAdelicOrthogonalDiagonal_injective (hS : ∃ p : Nat.Primes, p ∉ S) :
    Function.Injective (U.awayAdelicOrthogonalDiagonal S) := by
  obtain ⟨p, hp⟩ := hS
  intro g h hgh
  apply orthogonalGroupBaseChange_injective (A := ℚ_[p]) Q
  simpa using congrArg (fun x => x ⟨p, hp⟩) hgh

/-- The rational Spin diagonal away from `S`. Its eventual integrality is inherited from the
finite Spin diagonal. -/
def awayAdelicSpinDiagonal :
    spinGroup Q →* RestrictedProductGroupAway S U.spin :=
  (restrictAway S U.spin).comp U.finiteAdelicSpinDiagonal

/-- At a prime outside `S`, the Spin diagonal is scalar extension to that prime. -/
@[simp]
theorem awayAdelicSpinDiagonal_apply (x : spinGroup Q) (p : {p : Nat.Primes // p ∉ S}) :
    U.awayAdelicSpinDiagonal S x p =
      CliffordAlgebra.spinGroupBaseChange (A := ℚ_[(p.1 : ℕ)]) Q x := by
  simp [awayAdelicSpinDiagonal]

/-- Restricting the finite Spin diagonal gives the diagonal away from `S`. -/
@[simp]
theorem restrictAway_comp_finiteAdelicSpinDiagonal :
    (restrictAway S U.spin).comp U.finiteAdelicSpinDiagonal = U.awayAdelicSpinDiagonal S := (rfl)

/-- The Spin diagonal away from `S` is injective when some prime remains. -/
theorem awayAdelicSpinDiagonal_injective (hS : ∃ p : Nat.Primes, p ∉ S) :
    Function.Injective (U.awayAdelicSpinDiagonal S) := by
  obtain ⟨p, hp⟩ := hS
  intro x y hxy
  apply CliffordAlgebra.spinGroupBaseChange_injective (A := ℚ_[p]) Q
  simpa using congrArg (fun z => z ⟨p, hp⟩) hxy

variable [FiniteDimensional ℚ V]

/-- The rational special orthogonal diagonal away from `S`. Its integrality comes from the
orthogonal reference family. -/
def awayAdelicSpecialOrthogonalDiagonal :
    specialOrthogonalGroup Q →* RestrictedProductGroupAway S U.specialOrthogonal :=
  (restrictAway S U.specialOrthogonal).comp U.finiteAdelicSpecialOrthogonalDiagonal

/-- At a prime outside `S`, the special orthogonal diagonal is scalar extension to that prime. -/
@[simp]
theorem awayAdelicSpecialOrthogonalDiagonal_apply (g : specialOrthogonalGroup Q)
    (p : {p : Nat.Primes // p ∉ S}) :
    U.awayAdelicSpecialOrthogonalDiagonal S g p =
      specialOrthogonalGroupBaseChange (A := ℚ_[(p.1 : ℕ)]) Q g := by
  simp [awayAdelicSpecialOrthogonalDiagonal]

/-- Restricting the finite special orthogonal diagonal gives the diagonal away from `S`. -/
@[simp]
theorem restrictAway_comp_finiteAdelicSpecialOrthogonalDiagonal :
    (restrictAway S U.specialOrthogonal).comp U.finiteAdelicSpecialOrthogonalDiagonal =
      U.awayAdelicSpecialOrthogonalDiagonal S := (rfl)

/-- The special orthogonal diagonal away from `S` is injective when some prime remains. -/
theorem awayAdelicSpecialOrthogonalDiagonal_injective (hS : ∃ p : Nat.Primes, p ∉ S) :
    Function.Injective (U.awayAdelicSpecialOrthogonalDiagonal S) := by
  obtain ⟨p, hp⟩ := hS
  intro g h hgh
  apply specialOrthogonalGroupBaseChange_injective (A := ℚ_[p]) Q
  simpa using congrArg (fun x => x ⟨p, hp⟩) hgh

/-- The componentwise Spin projection away from `S` commutes with the rational diagonals. -/
theorem restrictedProductMapOfForall_comp_awayAdelicSpinDiagonal :
    (restrictedProductMapOfForall
      (fun p : {p : Nat.Primes // p ∉ S} => U.spin p.1)
      (fun p => U.specialOrthogonal p.1)
      (fun p => CliffordAlgebra.spinToSpecialOrthogonal (Q.baseChange ℚ_[(p.1 : ℕ)]))
      (fun p => U.mapsTo_specialOrthogonal p.1)).comp (U.awayAdelicSpinDiagonal S) =
        (U.awayAdelicSpecialOrthogonalDiagonal S).comp
          (CliffordAlgebra.spinToSpecialOrthogonal Q) := by
  ext x p : 2
  have h := congrArg (fun f => f x p.1)
    U.finiteAdelicSpinToSpecialOrthogonal_comp_finiteAdelicSpinDiagonal
  simpa only [MonoidHom.comp_apply, restrictedProductMapOfForall_apply,
    awayAdelicSpinDiagonal_apply, awayAdelicSpecialOrthogonalDiagonal_apply,
    finiteAdelicSpinToSpecialOrthogonal_apply, finiteAdelicSpinDiagonal_apply,
    finiteAdelicSpecialOrthogonalDiagonal_apply] using h

/-- The componentwise special orthogonal inclusion away from `S` commutes with the rational
diagonals. -/
theorem restrictedProductMapOfForall_comp_awayAdelicSpecialOrthogonalDiagonal :
    (restrictedProductMapOfForall
      (fun p : {p : Nat.Primes // p ∉ S} => U.specialOrthogonal p.1)
      (fun p => U.orthogonal p.1)
      (fun p => specialOrthogonalToOrthogonal (Q.baseChange ℚ_[(p.1 : ℕ)]))
      (fun p _ hg => (U.mem_specialOrthogonal_iff p.1 _).mp hg)).comp
        (U.awayAdelicSpecialOrthogonalDiagonal S) =
          (U.awayAdelicOrthogonalDiagonal S).comp (specialOrthogonalToOrthogonal Q) := by
  ext g p : 2
  have h := congrArg (fun f => f g p.1)
    U.finiteAdelicSpecialOrthogonalToOrthogonal_comp_finiteAdelicSpecialOrthogonalDiagonal
  calc
    _ = specialOrthogonalToOrthogonal (Q.baseChange ℚ_[(p.1 : ℕ)])
        (U.awayAdelicSpecialOrthogonalDiagonal S g p) :=
      restrictedProductMapOfForall_apply _ _ _ _ _ p
    _ = _ := by
      simpa only [MonoidHom.comp_apply, awayAdelicSpecialOrthogonalDiagonal_apply,
        awayAdelicOrthogonalDiagonal_apply, finiteAdelicSpecialOrthogonalToOrthogonal_apply,
        finiteAdelicSpecialOrthogonalDiagonal_apply, finiteAdelicOrthogonalDiagonal_apply] using h

end

end OrthogonalCompactOpens
end QuadraticMap
end TauCeti
