/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.Diagonal.Finite
public import TauCeti.Topology.Algebra.RestrictedProduct.Congr.DoubleCoset

/-!
# Finite adelic double cosets of orthogonal and Spin groups

Let `Q` be a quadratic form over `ℚ` and let `U` be compatible compact-open reference data.
The finite adelic class sets attached to `U` are

`G(ℚ) \ G(𝔸_f) / ∏_p U_p`

for `G = O`, `SO`, and `Spin`. The left subgroup is the range of the corresponding rational
diagonal, rather than an unrelated copy of `G(ℚ)`, and the right subgroup is the
everywhere-integral subgroup of the restricted product.

The comparisons for these types are deliberately the general double-coset constructions:

* the `finiteAdelic*DoubleCosetMapOfLE` maps are the surjections obtained by enlarging the right
  compact-open subgroup;
* the `finiteAdelic*DoubleCosetConj` equivalences compare a right compact-open subgroup with its
  conjugate by right translation;
* the `finiteAdelic*DoubleCosetCongr` equivalences compare the actual class sets attached to two
  compatible tuples when componentwise equivalences preserve every reference subgroup and the
  rational diagonals.

Keeping these maps separate matters. An eventual change of reference family canonically
identifies the ambient restricted products, but need not carry one everywhere-integral subgroup
to the other.

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
  {Q : QuadraticForm ℚ V} (U : OrthogonalCompactOpens Q)

/-- The finite adelic orthogonal double-coset set
`O(V)(ℚ) \ O(V)(𝔸_f) / ∏_p U_p^O`. -/
abbrev finiteAdelicOrthogonalDoubleCoset : Type _ :=
  DoubleCoset.Quotient (U.finiteAdelicOrthogonalDiagonal.range : Set U.finiteAdelicOrthogonal)
    (integralSubgroup U.orthogonal : Set U.finiteAdelicOrthogonal)

/-- The finite adelic Spin double-coset set
`Spin(V)(ℚ) \ Spin(V)(𝔸_f) / ∏_p U_p^{Spin}`. -/
abbrev finiteAdelicSpinDoubleCoset : Type _ :=
  DoubleCoset.Quotient (U.finiteAdelicSpinDiagonal.range : Set U.finiteAdelicSpin)
    (integralSubgroup U.spin : Set U.finiteAdelicSpin)

variable [FiniteDimensional ℚ V]

/-- The finite adelic special-orthogonal double-coset set
`SO(V)(ℚ) \ SO(V)(𝔸_f) / ∏_p U_p^{SO}`. -/
abbrev finiteAdelicSpecialOrthogonalDoubleCoset : Type _ :=
  DoubleCoset.Quotient
    (U.finiteAdelicSpecialOrthogonalDiagonal.range : Set U.finiteAdelicSpecialOrthogonal)
    (integralSubgroup U.specialOrthogonal : Set U.finiteAdelicSpecialOrthogonal)

/-! ### Enlargement and conjugation of the right subgroup -/

/-- Enlarging the right subgroup of the finite adelic orthogonal class set gives a surjection. -/
def finiteAdelicOrthogonalDoubleCosetMapOfLE
    (K : Subgroup U.finiteAdelicOrthogonal) (hK : integralSubgroup U.orthogonal ≤ K) :
    U.finiteAdelicOrthogonalDoubleCoset →
      DoubleCoset.Quotient (U.finiteAdelicOrthogonalDiagonal.range :
        Set U.finiteAdelicOrthogonal) K :=
  DoubleCoset.quotientMapOfLERight U.finiteAdelicOrthogonalDiagonal.range hK

omit [FiniteDimensional ℚ V] in
/-- Enlarging the orthogonal right subgroup preserves representatives. -/
@[simp]
theorem finiteAdelicOrthogonalDoubleCosetMapOfLE_apply_mk
    (K : Subgroup U.finiteAdelicOrthogonal) (hK : integralSubgroup U.orthogonal ≤ K)
    (x : U.finiteAdelicOrthogonal) :
    U.finiteAdelicOrthogonalDoubleCosetMapOfLE K hK
        (DoubleCoset.mk U.finiteAdelicOrthogonalDiagonal.range
          (integralSubgroup U.orthogonal) x) =
      DoubleCoset.mk U.finiteAdelicOrthogonalDiagonal.range K x :=
  DoubleCoset.quotientMapOfLERight_apply_mk U.finiteAdelicOrthogonalDiagonal.range hK x

omit [FiniteDimensional ℚ V] in
/-- The finite adelic orthogonal double-coset map obtained by enlarging the right subgroup is
surjective. -/
theorem finiteAdelicOrthogonalDoubleCosetMapOfLE_surjective
    (K : Subgroup U.finiteAdelicOrthogonal) (hK : integralSubgroup U.orthogonal ≤ K) :
    Function.Surjective (U.finiteAdelicOrthogonalDoubleCosetMapOfLE K hK) :=
  DoubleCoset.quotientMapOfLERight_surjective U.finiteAdelicOrthogonalDiagonal.range hK

/-- Right translation identifies the finite adelic orthogonal class set with the quotient by the
conjugate of its right compact-open subgroup. -/
def finiteAdelicOrthogonalDoubleCosetConj (g : U.finiteAdelicOrthogonal) :
    U.finiteAdelicOrthogonalDoubleCoset ≃
      DoubleCoset.Quotient (U.finiteAdelicOrthogonalDiagonal.range :
        Set U.finiteAdelicOrthogonal)
        (↑((integralSubgroup U.orthogonal).map
          ((MulAut.conj g).symm : U.finiteAdelicOrthogonal →* U.finiteAdelicOrthogonal)) :
          Set U.finiteAdelicOrthogonal) :=
  DoubleCoset.quotientConjRight U.finiteAdelicOrthogonalDiagonal.range
    (integralSubgroup U.orthogonal) g

omit [FiniteDimensional ℚ V] in
/-- Orthogonal right translation sends the class of `x` to the class of `x * g`. -/
theorem finiteAdelicOrthogonalDoubleCosetConj_apply_mk (g x : U.finiteAdelicOrthogonal) :
    U.finiteAdelicOrthogonalDoubleCosetConj g
        (DoubleCoset.mk U.finiteAdelicOrthogonalDiagonal.range
          (integralSubgroup U.orthogonal) x) =
      DoubleCoset.mk U.finiteAdelicOrthogonalDiagonal.range
        ((integralSubgroup U.orthogonal).map
          ((MulAut.conj g).symm : U.finiteAdelicOrthogonal →* U.finiteAdelicOrthogonal))
        (x * g) :=
  DoubleCoset.quotientConjRight_apply_mk U.finiteAdelicOrthogonalDiagonal.range
    (integralSubgroup U.orthogonal) g x

omit [FiniteDimensional ℚ V] in
/-- The inverse orthogonal right translation sends the class of `y` to the class of `y * g⁻¹`. -/
theorem finiteAdelicOrthogonalDoubleCosetConj_symm_apply_mk (g y : U.finiteAdelicOrthogonal) :
    (U.finiteAdelicOrthogonalDoubleCosetConj g).symm
        (DoubleCoset.mk U.finiteAdelicOrthogonalDiagonal.range
          ((integralSubgroup U.orthogonal).map
            ((MulAut.conj g).symm : U.finiteAdelicOrthogonal →* U.finiteAdelicOrthogonal)) y) =
      DoubleCoset.mk U.finiteAdelicOrthogonalDiagonal.range
        (integralSubgroup U.orthogonal) (y * g⁻¹) :=
  DoubleCoset.quotientConjRight_symm_apply_mk U.finiteAdelicOrthogonalDiagonal.range
    (integralSubgroup U.orthogonal) g y

/-- Enlarging the right subgroup of the finite adelic Spin class set gives a surjection. -/
def finiteAdelicSpinDoubleCosetMapOfLE
    (K : Subgroup U.finiteAdelicSpin) (hK : integralSubgroup U.spin ≤ K) :
    U.finiteAdelicSpinDoubleCoset →
      DoubleCoset.Quotient (U.finiteAdelicSpinDiagonal.range : Set U.finiteAdelicSpin) K :=
  DoubleCoset.quotientMapOfLERight U.finiteAdelicSpinDiagonal.range hK

omit [FiniteDimensional ℚ V] in
/-- Enlarging the Spin right subgroup preserves representatives. -/
@[simp]
theorem finiteAdelicSpinDoubleCosetMapOfLE_apply_mk
    (K : Subgroup U.finiteAdelicSpin) (hK : integralSubgroup U.spin ≤ K)
    (x : U.finiteAdelicSpin) :
    U.finiteAdelicSpinDoubleCosetMapOfLE K hK
        (DoubleCoset.mk U.finiteAdelicSpinDiagonal.range (integralSubgroup U.spin) x) =
      DoubleCoset.mk U.finiteAdelicSpinDiagonal.range K x :=
  DoubleCoset.quotientMapOfLERight_apply_mk U.finiteAdelicSpinDiagonal.range hK x

omit [FiniteDimensional ℚ V] in
/-- The finite adelic Spin double-coset map obtained by enlarging the right subgroup is
surjective. -/
theorem finiteAdelicSpinDoubleCosetMapOfLE_surjective
    (K : Subgroup U.finiteAdelicSpin) (hK : integralSubgroup U.spin ≤ K) :
    Function.Surjective (U.finiteAdelicSpinDoubleCosetMapOfLE K hK) :=
  DoubleCoset.quotientMapOfLERight_surjective U.finiteAdelicSpinDiagonal.range hK

/-- Right translation identifies the finite adelic Spin class set with the quotient by the
conjugate of its right compact-open subgroup. -/
def finiteAdelicSpinDoubleCosetConj (g : U.finiteAdelicSpin) :
    U.finiteAdelicSpinDoubleCoset ≃
      DoubleCoset.Quotient (U.finiteAdelicSpinDiagonal.range : Set U.finiteAdelicSpin)
        (↑((integralSubgroup U.spin).map
          ((MulAut.conj g).symm : U.finiteAdelicSpin →* U.finiteAdelicSpin)) :
          Set U.finiteAdelicSpin) :=
  DoubleCoset.quotientConjRight U.finiteAdelicSpinDiagonal.range (integralSubgroup U.spin) g

omit [FiniteDimensional ℚ V] in
/-- Spin right translation sends the class of `x` to the class of `x * g`. -/
theorem finiteAdelicSpinDoubleCosetConj_apply_mk (g x : U.finiteAdelicSpin) :
    U.finiteAdelicSpinDoubleCosetConj g
        (DoubleCoset.mk U.finiteAdelicSpinDiagonal.range (integralSubgroup U.spin) x) =
      DoubleCoset.mk U.finiteAdelicSpinDiagonal.range
        ((integralSubgroup U.spin).map
          ((MulAut.conj g).symm : U.finiteAdelicSpin →* U.finiteAdelicSpin)) (x * g) :=
  DoubleCoset.quotientConjRight_apply_mk U.finiteAdelicSpinDiagonal.range
    (integralSubgroup U.spin) g x

omit [FiniteDimensional ℚ V] in
/-- The inverse Spin right translation sends the class of `y` to the class of `y * g⁻¹`. -/
theorem finiteAdelicSpinDoubleCosetConj_symm_apply_mk (g y : U.finiteAdelicSpin) :
    (U.finiteAdelicSpinDoubleCosetConj g).symm
        (DoubleCoset.mk U.finiteAdelicSpinDiagonal.range
          ((integralSubgroup U.spin).map
            ((MulAut.conj g).symm : U.finiteAdelicSpin →* U.finiteAdelicSpin)) y) =
      DoubleCoset.mk U.finiteAdelicSpinDiagonal.range (integralSubgroup U.spin) (y * g⁻¹) :=
  DoubleCoset.quotientConjRight_symm_apply_mk U.finiteAdelicSpinDiagonal.range
    (integralSubgroup U.spin) g y

/-- Enlarging the right subgroup of the finite adelic special-orthogonal class set gives a
surjection. -/
def finiteAdelicSpecialOrthogonalDoubleCosetMapOfLE
    (K : Subgroup U.finiteAdelicSpecialOrthogonal)
    (hK : integralSubgroup U.specialOrthogonal ≤ K) :
    U.finiteAdelicSpecialOrthogonalDoubleCoset →
      DoubleCoset.Quotient (U.finiteAdelicSpecialOrthogonalDiagonal.range :
        Set U.finiteAdelicSpecialOrthogonal) K :=
  DoubleCoset.quotientMapOfLERight U.finiteAdelicSpecialOrthogonalDiagonal.range hK

/-- Enlarging the special-orthogonal right subgroup preserves representatives. -/
@[simp]
theorem finiteAdelicSpecialOrthogonalDoubleCosetMapOfLE_apply_mk
    (K : Subgroup U.finiteAdelicSpecialOrthogonal)
    (hK : integralSubgroup U.specialOrthogonal ≤ K) (x : U.finiteAdelicSpecialOrthogonal) :
    U.finiteAdelicSpecialOrthogonalDoubleCosetMapOfLE K hK
        (DoubleCoset.mk U.finiteAdelicSpecialOrthogonalDiagonal.range
          (integralSubgroup U.specialOrthogonal) x) =
      DoubleCoset.mk U.finiteAdelicSpecialOrthogonalDiagonal.range K x :=
  DoubleCoset.quotientMapOfLERight_apply_mk
    U.finiteAdelicSpecialOrthogonalDiagonal.range hK x

/-- The finite adelic special-orthogonal double-coset map obtained by enlarging the right subgroup
is surjective. -/
theorem finiteAdelicSpecialOrthogonalDoubleCosetMapOfLE_surjective
    (K : Subgroup U.finiteAdelicSpecialOrthogonal)
    (hK : integralSubgroup U.specialOrthogonal ≤ K) :
    Function.Surjective (U.finiteAdelicSpecialOrthogonalDoubleCosetMapOfLE K hK) :=
  DoubleCoset.quotientMapOfLERight_surjective U.finiteAdelicSpecialOrthogonalDiagonal.range hK

/-- Right translation identifies the finite adelic special-orthogonal class set with the quotient
by the conjugate of its right compact-open subgroup. -/
def finiteAdelicSpecialOrthogonalDoubleCosetConj
    (g : U.finiteAdelicSpecialOrthogonal) :
    U.finiteAdelicSpecialOrthogonalDoubleCoset ≃
      DoubleCoset.Quotient (U.finiteAdelicSpecialOrthogonalDiagonal.range :
        Set U.finiteAdelicSpecialOrthogonal)
        (↑((integralSubgroup U.specialOrthogonal).map
          ((MulAut.conj g).symm :
            U.finiteAdelicSpecialOrthogonal →* U.finiteAdelicSpecialOrthogonal)) :
          Set U.finiteAdelicSpecialOrthogonal) :=
  DoubleCoset.quotientConjRight U.finiteAdelicSpecialOrthogonalDiagonal.range
    (integralSubgroup U.specialOrthogonal) g

/-- Special-orthogonal right translation sends the class of `x` to the class of `x * g`. -/
theorem finiteAdelicSpecialOrthogonalDoubleCosetConj_apply_mk
    (g x : U.finiteAdelicSpecialOrthogonal) :
    U.finiteAdelicSpecialOrthogonalDoubleCosetConj g
        (DoubleCoset.mk U.finiteAdelicSpecialOrthogonalDiagonal.range
          (integralSubgroup U.specialOrthogonal) x) =
      DoubleCoset.mk U.finiteAdelicSpecialOrthogonalDiagonal.range
        ((integralSubgroup U.specialOrthogonal).map
          ((MulAut.conj g).symm :
            U.finiteAdelicSpecialOrthogonal →* U.finiteAdelicSpecialOrthogonal)) (x * g) :=
  DoubleCoset.quotientConjRight_apply_mk U.finiteAdelicSpecialOrthogonalDiagonal.range
    (integralSubgroup U.specialOrthogonal) g x

/-- The inverse special-orthogonal right translation sends the class of `y` to the class of
`y * g⁻¹`. -/
theorem finiteAdelicSpecialOrthogonalDoubleCosetConj_symm_apply_mk
    (g y : U.finiteAdelicSpecialOrthogonal) :
    (U.finiteAdelicSpecialOrthogonalDoubleCosetConj g).symm
        (DoubleCoset.mk U.finiteAdelicSpecialOrthogonalDiagonal.range
          ((integralSubgroup U.specialOrthogonal).map
            ((MulAut.conj g).symm :
              U.finiteAdelicSpecialOrthogonal →* U.finiteAdelicSpecialOrthogonal)) y) =
      DoubleCoset.mk U.finiteAdelicSpecialOrthogonalDiagonal.range
        (integralSubgroup U.specialOrthogonal) (y * g⁻¹) :=
  DoubleCoset.quotientConjRight_symm_apply_mk U.finiteAdelicSpecialOrthogonalDiagonal.range
    (integralSubgroup U.specialOrthogonal) g y

/-! ### Change of compatible tuple -/

/-- Componentwise equivalences which preserve every orthogonal reference subgroup and carry the
rational diagonal subgroup onto the target diagonal subgroup identify the finite adelic class
sets. -/
def finiteAdelicOrthogonalDoubleCosetCongr (U' : OrthogonalCompactOpens Q)
    (φ : ∀ p : Nat.Primes,
      orthogonalGroup (Q.baseChange ℚ_[p]) ≃* orthogonalGroup (Q.baseChange ℚ_[p]))
    (hφ : ∀ p, Set.BijOn (φ p) (U.orthogonal p) (U'.orthogonal p))
    (hdiag : U.finiteAdelicOrthogonalDiagonal.range.map
      (restrictedProductCongrRight U.orthogonal U'.orthogonal φ (.of_forall hφ) :
        U.finiteAdelicOrthogonal →* U'.finiteAdelicOrthogonal) =
      U'.finiteAdelicOrthogonalDiagonal.range) :
    U.finiteAdelicOrthogonalDoubleCoset ≃ U'.finiteAdelicOrthogonalDoubleCoset := by
  apply DoubleCoset.quotientCongr U.finiteAdelicOrthogonalDiagonal.range
    (integralSubgroup U.orthogonal)
    (restrictedProductCongrRight U.orthogonal U'.orthogonal φ (.of_forall hφ)) hdiag
    (map_integralSubgroup_restrictedProductCongrRight U.orthogonal U'.orthogonal φ hφ)

omit [FiniteDimensional ℚ V] in
/-- Change of orthogonal tuple applies the componentwise equivalence to representatives. -/
@[simp]
theorem finiteAdelicOrthogonalDoubleCosetCongr_apply_mk (U' : OrthogonalCompactOpens Q)
    (φ : ∀ p : Nat.Primes,
      orthogonalGroup (Q.baseChange ℚ_[p]) ≃* orthogonalGroup (Q.baseChange ℚ_[p]))
    (hφ : ∀ p, Set.BijOn (φ p) (U.orthogonal p) (U'.orthogonal p))
    (hdiag : U.finiteAdelicOrthogonalDiagonal.range.map
      (restrictedProductCongrRight U.orthogonal U'.orthogonal φ (.of_forall hφ) :
        U.finiteAdelicOrthogonal →* U'.finiteAdelicOrthogonal) =
      U'.finiteAdelicOrthogonalDiagonal.range)
    (x : U.finiteAdelicOrthogonal) :
    U.finiteAdelicOrthogonalDoubleCosetCongr U' φ hφ hdiag
        (DoubleCoset.mk U.finiteAdelicOrthogonalDiagonal.range
          (integralSubgroup U.orthogonal) x) =
      DoubleCoset.mk U'.finiteAdelicOrthogonalDiagonal.range
        (integralSubgroup U'.orthogonal)
        (restrictedProductCongrRight U.orthogonal U'.orthogonal φ (.of_forall hφ) x) :=
  DoubleCoset.quotientCongr_apply_mk U.finiteAdelicOrthogonalDiagonal.range
    (integralSubgroup U.orthogonal)
    (restrictedProductCongrRight U.orthogonal U'.orthogonal φ (.of_forall hφ)) hdiag
    (map_integralSubgroup_restrictedProductCongrRight U.orthogonal U'.orthogonal φ hφ) x

omit [FiniteDimensional ℚ V] in
/-- The inverse change of orthogonal tuple applies the inverse componentwise equivalence to
representatives. -/
@[simp]
theorem finiteAdelicOrthogonalDoubleCosetCongr_symm_apply_mk (U' : OrthogonalCompactOpens Q)
    (φ : ∀ p : Nat.Primes,
      orthogonalGroup (Q.baseChange ℚ_[p]) ≃* orthogonalGroup (Q.baseChange ℚ_[p]))
    (hφ : ∀ p, Set.BijOn (φ p) (U.orthogonal p) (U'.orthogonal p))
    (hdiag : U.finiteAdelicOrthogonalDiagonal.range.map
      (restrictedProductCongrRight U.orthogonal U'.orthogonal φ (.of_forall hφ) :
        U.finiteAdelicOrthogonal →* U'.finiteAdelicOrthogonal) =
      U'.finiteAdelicOrthogonalDiagonal.range)
    (y : U'.finiteAdelicOrthogonal) :
    (U.finiteAdelicOrthogonalDoubleCosetCongr U' φ hφ hdiag).symm
        (DoubleCoset.mk U'.finiteAdelicOrthogonalDiagonal.range
          (integralSubgroup U'.orthogonal) y) =
      DoubleCoset.mk U.finiteAdelicOrthogonalDiagonal.range
        (integralSubgroup U.orthogonal)
        ((restrictedProductCongrRight U.orthogonal U'.orthogonal φ (.of_forall hφ)).symm y) :=
  DoubleCoset.quotientCongr_symm_apply_mk U.finiteAdelicOrthogonalDiagonal.range
    (integralSubgroup U.orthogonal)
    (restrictedProductCongrRight U.orthogonal U'.orthogonal φ (.of_forall hφ)) hdiag
    (map_integralSubgroup_restrictedProductCongrRight U.orthogonal U'.orthogonal φ hφ) y

/-- Componentwise equivalences which preserve every Spin reference subgroup and carry the
rational diagonal subgroup onto the target diagonal subgroup identify the finite adelic class
sets. -/
def finiteAdelicSpinDoubleCosetCongr (U' : OrthogonalCompactOpens Q)
    (φ : ∀ p : Nat.Primes,
      spinGroup (Q.baseChange ℚ_[p]) ≃* spinGroup (Q.baseChange ℚ_[p]))
    (hφ : ∀ p, Set.BijOn (φ p) (U.spin p) (U'.spin p))
    (hdiag : U.finiteAdelicSpinDiagonal.range.map
      (restrictedProductCongrRight U.spin U'.spin φ (.of_forall hφ) :
        U.finiteAdelicSpin →* U'.finiteAdelicSpin) = U'.finiteAdelicSpinDiagonal.range) :
    U.finiteAdelicSpinDoubleCoset ≃ U'.finiteAdelicSpinDoubleCoset := by
  apply DoubleCoset.quotientCongr U.finiteAdelicSpinDiagonal.range
    (integralSubgroup U.spin)
    (restrictedProductCongrRight U.spin U'.spin φ (.of_forall hφ)) hdiag
    (map_integralSubgroup_restrictedProductCongrRight U.spin U'.spin φ hφ)

omit [FiniteDimensional ℚ V] in
/-- Change of Spin tuple applies the componentwise equivalence to representatives. -/
@[simp]
theorem finiteAdelicSpinDoubleCosetCongr_apply_mk (U' : OrthogonalCompactOpens Q)
    (φ : ∀ p : Nat.Primes,
      spinGroup (Q.baseChange ℚ_[p]) ≃* spinGroup (Q.baseChange ℚ_[p]))
    (hφ : ∀ p, Set.BijOn (φ p) (U.spin p) (U'.spin p))
    (hdiag : U.finiteAdelicSpinDiagonal.range.map
      (restrictedProductCongrRight U.spin U'.spin φ (.of_forall hφ) :
        U.finiteAdelicSpin →* U'.finiteAdelicSpin) = U'.finiteAdelicSpinDiagonal.range)
    (x : U.finiteAdelicSpin) :
    U.finiteAdelicSpinDoubleCosetCongr U' φ hφ hdiag
        (DoubleCoset.mk U.finiteAdelicSpinDiagonal.range (integralSubgroup U.spin) x) =
      DoubleCoset.mk U'.finiteAdelicSpinDiagonal.range (integralSubgroup U'.spin)
        (restrictedProductCongrRight U.spin U'.spin φ (.of_forall hφ) x) :=
  DoubleCoset.quotientCongr_apply_mk U.finiteAdelicSpinDiagonal.range
    (integralSubgroup U.spin)
    (restrictedProductCongrRight U.spin U'.spin φ (.of_forall hφ)) hdiag
    (map_integralSubgroup_restrictedProductCongrRight U.spin U'.spin φ hφ) x

omit [FiniteDimensional ℚ V] in
/-- The inverse change of Spin tuple applies the inverse componentwise equivalence to
representatives. -/
@[simp]
theorem finiteAdelicSpinDoubleCosetCongr_symm_apply_mk (U' : OrthogonalCompactOpens Q)
    (φ : ∀ p : Nat.Primes,
      spinGroup (Q.baseChange ℚ_[p]) ≃* spinGroup (Q.baseChange ℚ_[p]))
    (hφ : ∀ p, Set.BijOn (φ p) (U.spin p) (U'.spin p))
    (hdiag : U.finiteAdelicSpinDiagonal.range.map
      (restrictedProductCongrRight U.spin U'.spin φ (.of_forall hφ) :
        U.finiteAdelicSpin →* U'.finiteAdelicSpin) = U'.finiteAdelicSpinDiagonal.range)
    (y : U'.finiteAdelicSpin) :
    (U.finiteAdelicSpinDoubleCosetCongr U' φ hφ hdiag).symm
        (DoubleCoset.mk U'.finiteAdelicSpinDiagonal.range (integralSubgroup U'.spin) y) =
      DoubleCoset.mk U.finiteAdelicSpinDiagonal.range (integralSubgroup U.spin)
        ((restrictedProductCongrRight U.spin U'.spin φ (.of_forall hφ)).symm y) :=
  DoubleCoset.quotientCongr_symm_apply_mk U.finiteAdelicSpinDiagonal.range
    (integralSubgroup U.spin)
    (restrictedProductCongrRight U.spin U'.spin φ (.of_forall hφ)) hdiag
    (map_integralSubgroup_restrictedProductCongrRight U.spin U'.spin φ hφ) y

/-- Componentwise equivalences which preserve every special-orthogonal reference subgroup and
carry the rational diagonal subgroup onto the target diagonal subgroup identify the finite adelic
class sets. -/
def finiteAdelicSpecialOrthogonalDoubleCosetCongr (U' : OrthogonalCompactOpens Q)
    (φ : ∀ p : Nat.Primes,
      specialOrthogonalGroup (Q.baseChange ℚ_[p]) ≃*
        specialOrthogonalGroup (Q.baseChange ℚ_[p]))
    (hφ : ∀ p, Set.BijOn (φ p) (U.specialOrthogonal p) (U'.specialOrthogonal p))
    (hdiag : U.finiteAdelicSpecialOrthogonalDiagonal.range.map
      (restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal φ (.of_forall hφ) :
        U.finiteAdelicSpecialOrthogonal →* U'.finiteAdelicSpecialOrthogonal) =
      U'.finiteAdelicSpecialOrthogonalDiagonal.range) :
    U.finiteAdelicSpecialOrthogonalDoubleCoset ≃
      U'.finiteAdelicSpecialOrthogonalDoubleCoset := by
  apply DoubleCoset.quotientCongr U.finiteAdelicSpecialOrthogonalDiagonal.range
    (integralSubgroup U.specialOrthogonal)
    (restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal φ (.of_forall hφ))
    hdiag (map_integralSubgroup_restrictedProductCongrRight U.specialOrthogonal
      U'.specialOrthogonal φ hφ)

/-- Change of special-orthogonal tuple applies the componentwise equivalence to
representatives. -/
@[simp]
theorem finiteAdelicSpecialOrthogonalDoubleCosetCongr_apply_mk
    (U' : OrthogonalCompactOpens Q)
    (φ : ∀ p : Nat.Primes,
      specialOrthogonalGroup (Q.baseChange ℚ_[p]) ≃*
        specialOrthogonalGroup (Q.baseChange ℚ_[p]))
    (hφ : ∀ p, Set.BijOn (φ p) (U.specialOrthogonal p) (U'.specialOrthogonal p))
    (hdiag : U.finiteAdelicSpecialOrthogonalDiagonal.range.map
      (restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal φ (.of_forall hφ) :
        U.finiteAdelicSpecialOrthogonal →* U'.finiteAdelicSpecialOrthogonal) =
      U'.finiteAdelicSpecialOrthogonalDiagonal.range)
    (x : U.finiteAdelicSpecialOrthogonal) :
    U.finiteAdelicSpecialOrthogonalDoubleCosetCongr U' φ hφ hdiag
        (DoubleCoset.mk U.finiteAdelicSpecialOrthogonalDiagonal.range
          (integralSubgroup U.specialOrthogonal) x) =
      DoubleCoset.mk U'.finiteAdelicSpecialOrthogonalDiagonal.range
        (integralSubgroup U'.specialOrthogonal)
        (restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal φ
          (.of_forall hφ) x) :=
  DoubleCoset.quotientCongr_apply_mk U.finiteAdelicSpecialOrthogonalDiagonal.range
    (integralSubgroup U.specialOrthogonal)
    (restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal φ (.of_forall hφ))
    hdiag (map_integralSubgroup_restrictedProductCongrRight U.specialOrthogonal
      U'.specialOrthogonal φ hφ) x

/-- The inverse change of special-orthogonal tuple applies the inverse componentwise equivalence
to representatives. -/
@[simp]
theorem finiteAdelicSpecialOrthogonalDoubleCosetCongr_symm_apply_mk
    (U' : OrthogonalCompactOpens Q)
    (φ : ∀ p : Nat.Primes,
      specialOrthogonalGroup (Q.baseChange ℚ_[p]) ≃*
        specialOrthogonalGroup (Q.baseChange ℚ_[p]))
    (hφ : ∀ p, Set.BijOn (φ p) (U.specialOrthogonal p) (U'.specialOrthogonal p))
    (hdiag : U.finiteAdelicSpecialOrthogonalDiagonal.range.map
      (restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal φ (.of_forall hφ) :
        U.finiteAdelicSpecialOrthogonal →* U'.finiteAdelicSpecialOrthogonal) =
      U'.finiteAdelicSpecialOrthogonalDiagonal.range)
    (y : U'.finiteAdelicSpecialOrthogonal) :
    (U.finiteAdelicSpecialOrthogonalDoubleCosetCongr U' φ hφ hdiag).symm
        (DoubleCoset.mk U'.finiteAdelicSpecialOrthogonalDiagonal.range
          (integralSubgroup U'.specialOrthogonal) y) =
      DoubleCoset.mk U.finiteAdelicSpecialOrthogonalDiagonal.range
        (integralSubgroup U.specialOrthogonal)
        ((restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal φ
          (.of_forall hφ)).symm y) :=
  DoubleCoset.quotientCongr_symm_apply_mk U.finiteAdelicSpecialOrthogonalDiagonal.range
    (integralSubgroup U.specialOrthogonal)
    (restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal φ (.of_forall hφ))
    hdiag (map_integralSubgroup_restrictedProductCongrRight U.specialOrthogonal
      U'.specialOrthogonal φ hφ) y

end

end OrthogonalCompactOpens
end QuadraticMap
end TauCeti
