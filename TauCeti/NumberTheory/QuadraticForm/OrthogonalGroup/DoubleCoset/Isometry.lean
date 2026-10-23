/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.DoubleCoset.Basic
public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.Diagonal.Isometry

/-!
# Isometric transport of finite adelic class sets

A rational isometry which carries the local reference subgroups onto one another at every prime
identifies the finite adelic orthogonal, special orthogonal and Spin double-coset sets. Rational
points are transported by the rational isometry, so preservation of the left diagonal subgroup
is proved, rather than required as extra input. Preservation at every prime identifies the right
everywhere-integral subgroup; agreement at almost every prime alone would not suffice.

The forward and inverse representative formulas compute the comparison by the corresponding
local isometries. These identifications let class sets be computed in convenient quadratic
coordinates, including when the source and target vector spaces have different carriers.

The constructions use `DoubleCoset.quotientCongr`, through the general componentwise comparisons
in `DoubleCoset.Basic`, and the diagonal naturality theorems in `Diagonal.Isometry`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §101–102.
* A. Weil, *Adeles and Algebraic Groups* (1982), Chapter I.
-/

public section

namespace TauCeti.QuadraticMap.OrthogonalCompactOpens

open Filter
open _root_.QuadraticMap

noncomputable section

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {Q : QuadraticForm ℚ V} {Q' : QuadraticForm ℚ W}
  (U : OrthogonalCompactOpens Q) (U' : OrthogonalCompactOpens Q')
  (e : Q.IsometryEquiv Q')

/-- A rational isometry preserving every orthogonal reference subgroup identifies the
finite adelic orthogonal class sets. -/
def finiteAdelicOrthogonalDoubleCosetEquivOfIsometry
    (he : ∀ p : Nat.Primes, Set.BijOn (e.baseChange ℚ_[p]).orthogonalGroupCongr
      (U.orthogonal p) (U'.orthogonal p)) :
    U.finiteAdelicOrthogonalDoubleCoset ≃ U'.finiteAdelicOrthogonalDoubleCoset :=
  U.finiteAdelicOrthogonalDoubleCosetCongr U'
    (fun p : Nat.Primes ↦ (e.baseChange ℚ_[p]).orthogonalGroupCongr) he
    (U.map_range_finiteAdelicOrthogonalDiagonal_of_isometry U' e (.of_forall he))

/-- Isometric transport of orthogonal class sets applies the local isometries to representatives. -/
@[simp]
theorem finiteAdelicOrthogonalDoubleCosetEquivOfIsometry_apply_mk
    (he : ∀ p : Nat.Primes, Set.BijOn (e.baseChange ℚ_[p]).orthogonalGroupCongr
      (U.orthogonal p) (U'.orthogonal p)) (x : U.finiteAdelicOrthogonal) :
    U.finiteAdelicOrthogonalDoubleCosetEquivOfIsometry U' e he
        (DoubleCoset.mk U.finiteAdelicOrthogonalDiagonal.range (integralSubgroup U.orthogonal) x) =
      DoubleCoset.mk U'.finiteAdelicOrthogonalDiagonal.range (integralSubgroup U'.orthogonal)
        (restrictedProductCongrRight U.orthogonal U'.orthogonal
          (fun p : Nat.Primes ↦ (e.baseChange ℚ_[p]).orthogonalGroupCongr)
          (.of_forall he) x) := by
  rw [finiteAdelicOrthogonalDoubleCosetEquivOfIsometry,
    finiteAdelicOrthogonalDoubleCosetCongr_apply_mk]

/-- Inverse transport of orthogonal class sets applies the inverse local isometries to
representatives. -/
@[simp]
theorem finiteAdelicOrthogonalDoubleCosetEquivOfIsometry_symm_apply_mk
    (he : ∀ p : Nat.Primes, Set.BijOn (e.baseChange ℚ_[p]).orthogonalGroupCongr
      (U.orthogonal p) (U'.orthogonal p)) (y : U'.finiteAdelicOrthogonal) :
    (U.finiteAdelicOrthogonalDoubleCosetEquivOfIsometry U' e he).symm
        (DoubleCoset.mk U'.finiteAdelicOrthogonalDiagonal.range
          (integralSubgroup U'.orthogonal) y) =
      DoubleCoset.mk U.finiteAdelicOrthogonalDiagonal.range (integralSubgroup U.orthogonal)
        ((restrictedProductCongrRight U.orthogonal U'.orthogonal
          (fun p : Nat.Primes ↦ (e.baseChange ℚ_[p]).orthogonalGroupCongr)
          (.of_forall he)).symm y) := by
  rw [finiteAdelicOrthogonalDoubleCosetEquivOfIsometry,
    finiteAdelicOrthogonalDoubleCosetCongr_symm_apply_mk]

/-- A rational isometry preserving every Spin reference subgroup identifies the
finite adelic Spin class sets. -/
def finiteAdelicSpinDoubleCosetEquivOfIsometry
    (he : ∀ p : Nat.Primes, Set.BijOn (e.baseChange ℚ_[p]).spinGroupEquiv
      (U.spin p) (U'.spin p)) :
    U.finiteAdelicSpinDoubleCoset ≃ U'.finiteAdelicSpinDoubleCoset :=
  U.finiteAdelicSpinDoubleCosetCongr U'
    (fun p : Nat.Primes ↦ (e.baseChange ℚ_[p]).spinGroupEquiv) he
    (U.map_range_finiteAdelicSpinDiagonal_of_isometry U' e (.of_forall he))

/-- Isometric transport of Spin class sets applies the local isometries to representatives. -/
@[simp]
theorem finiteAdelicSpinDoubleCosetEquivOfIsometry_apply_mk
    (he : ∀ p : Nat.Primes, Set.BijOn (e.baseChange ℚ_[p]).spinGroupEquiv
      (U.spin p) (U'.spin p)) (x : U.finiteAdelicSpin) :
    U.finiteAdelicSpinDoubleCosetEquivOfIsometry U' e he
        (DoubleCoset.mk U.finiteAdelicSpinDiagonal.range (integralSubgroup U.spin) x) =
      DoubleCoset.mk U'.finiteAdelicSpinDiagonal.range (integralSubgroup U'.spin)
        (restrictedProductCongrRight U.spin U'.spin
          (fun p : Nat.Primes ↦ (e.baseChange ℚ_[p]).spinGroupEquiv)
          (.of_forall he) x) := by
  rw [finiteAdelicSpinDoubleCosetEquivOfIsometry, finiteAdelicSpinDoubleCosetCongr_apply_mk]

/-- Inverse transport of Spin class sets applies the inverse local isometries to
representatives. -/
@[simp]
theorem finiteAdelicSpinDoubleCosetEquivOfIsometry_symm_apply_mk
    (he : ∀ p : Nat.Primes, Set.BijOn (e.baseChange ℚ_[p]).spinGroupEquiv
      (U.spin p) (U'.spin p)) (y : U'.finiteAdelicSpin) :
    (U.finiteAdelicSpinDoubleCosetEquivOfIsometry U' e he).symm
        (DoubleCoset.mk U'.finiteAdelicSpinDiagonal.range (integralSubgroup U'.spin) y) =
      DoubleCoset.mk U.finiteAdelicSpinDiagonal.range (integralSubgroup U.spin)
        ((restrictedProductCongrRight U.spin U'.spin
          (fun p : Nat.Primes ↦ (e.baseChange ℚ_[p]).spinGroupEquiv)
          (.of_forall he)).symm y) := by
  rw [finiteAdelicSpinDoubleCosetEquivOfIsometry, finiteAdelicSpinDoubleCosetCongr_symm_apply_mk]

variable [FiniteDimensional ℚ V] [FiniteDimensional ℚ W]

/-- A rational isometry preserving every special orthogonal reference subgroup identifies the
finite adelic special orthogonal class sets. -/
def finiteAdelicSpecialOrthogonalDoubleCosetEquivOfIsometry
    (he : ∀ p : Nat.Primes, Set.BijOn (e.baseChange ℚ_[p]).specialOrthogonalGroupCongr
      (U.specialOrthogonal p) (U'.specialOrthogonal p)) :
    U.finiteAdelicSpecialOrthogonalDoubleCoset ≃ U'.finiteAdelicSpecialOrthogonalDoubleCoset :=
  U.finiteAdelicSpecialOrthogonalDoubleCosetCongr U'
    (fun p : Nat.Primes ↦ (e.baseChange ℚ_[p]).specialOrthogonalGroupCongr) he
    (U.map_range_finiteAdelicSpecialOrthogonalDiagonal_of_isometry U' e (.of_forall he))

/-- Isometric transport of special orthogonal class sets applies the local isometries
to representatives. -/
@[simp]
theorem finiteAdelicSpecialOrthogonalDoubleCosetEquivOfIsometry_apply_mk
    (he : ∀ p : Nat.Primes, Set.BijOn (e.baseChange ℚ_[p]).specialOrthogonalGroupCongr
      (U.specialOrthogonal p) (U'.specialOrthogonal p)) (x : U.finiteAdelicSpecialOrthogonal) :
    U.finiteAdelicSpecialOrthogonalDoubleCosetEquivOfIsometry U' e he
        (DoubleCoset.mk U.finiteAdelicSpecialOrthogonalDiagonal.range
          (integralSubgroup U.specialOrthogonal) x) =
      DoubleCoset.mk U'.finiteAdelicSpecialOrthogonalDiagonal.range
          (integralSubgroup U'.specialOrthogonal)
        (restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal
          (fun p : Nat.Primes ↦ (e.baseChange ℚ_[p]).specialOrthogonalGroupCongr)
          (.of_forall he) x) := by
  rw [finiteAdelicSpecialOrthogonalDoubleCosetEquivOfIsometry,
    finiteAdelicSpecialOrthogonalDoubleCosetCongr_apply_mk]

/-- Inverse transport of special orthogonal class sets applies the inverse local isometries to
representatives. -/
@[simp]
theorem finiteAdelicSpecialOrthogonalDoubleCosetEquivOfIsometry_symm_apply_mk
    (he : ∀ p : Nat.Primes, Set.BijOn (e.baseChange ℚ_[p]).specialOrthogonalGroupCongr
      (U.specialOrthogonal p) (U'.specialOrthogonal p)) (y : U'.finiteAdelicSpecialOrthogonal) :
    (U.finiteAdelicSpecialOrthogonalDoubleCosetEquivOfIsometry U' e he).symm
        (DoubleCoset.mk U'.finiteAdelicSpecialOrthogonalDiagonal.range
          (integralSubgroup U'.specialOrthogonal) y) =
      DoubleCoset.mk U.finiteAdelicSpecialOrthogonalDiagonal.range
          (integralSubgroup U.specialOrthogonal)
        ((restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal
          (fun p : Nat.Primes ↦ (e.baseChange ℚ_[p]).specialOrthogonalGroupCongr)
          (.of_forall he)).symm y) := by
  rw [finiteAdelicSpecialOrthogonalDoubleCosetEquivOfIsometry,
    finiteAdelicSpecialOrthogonalDoubleCosetCongr_symm_apply_mk]

end

end TauCeti.QuadraticMap.OrthogonalCompactOpens
