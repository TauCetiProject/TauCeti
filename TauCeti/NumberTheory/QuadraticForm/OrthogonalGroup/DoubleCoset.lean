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

/-- Enlarging the right subgroup of the finite adelic Spin class set gives a surjection. -/
def finiteAdelicSpinDoubleCosetMapOfLE
    (K : Subgroup U.finiteAdelicSpin) (hK : integralSubgroup U.spin ≤ K) :
    U.finiteAdelicSpinDoubleCoset →
      DoubleCoset.Quotient (U.finiteAdelicSpinDiagonal.range : Set U.finiteAdelicSpin) K :=
  DoubleCoset.quotientMapOfLERight U.finiteAdelicSpinDiagonal.range hK

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

/-- Enlarging the right subgroup of the finite adelic special-orthogonal class set gives a
surjection. -/
def finiteAdelicSpecialOrthogonalDoubleCosetMapOfLE
    (K : Subgroup U.finiteAdelicSpecialOrthogonal)
    (hK : integralSubgroup U.specialOrthogonal ≤ K) :
    U.finiteAdelicSpecialOrthogonalDoubleCoset →
      DoubleCoset.Quotient (U.finiteAdelicSpecialOrthogonalDiagonal.range :
        Set U.finiteAdelicSpecialOrthogonal) K :=
  DoubleCoset.quotientMapOfLERight U.finiteAdelicSpecialOrthogonalDiagonal.range hK

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

/-! ### Change of compatible tuple -/

/-- Componentwise equivalences which preserve every orthogonal reference subgroup and every
rational diagonal point identify the actual finite adelic orthogonal class sets. -/
def finiteAdelicOrthogonalDoubleCosetCongr (U' : OrthogonalCompactOpens Q)
    (φ : ∀ p : Nat.Primes,
      orthogonalGroup (Q.baseChange ℚ_[p]) ≃* orthogonalGroup (Q.baseChange ℚ_[p]))
    (hφ : ∀ p, Set.BijOn (φ p) (U.orthogonal p) (U'.orthogonal p))
    (hdiag : ∀ (g : orthogonalGroup Q) (p : Nat.Primes),
      φ p (orthogonalGroupBaseChange (A := ℚ_[p]) Q g) =
        orthogonalGroupBaseChange (A := ℚ_[p]) Q g) :
    U.finiteAdelicOrthogonalDoubleCoset ≃ U'.finiteAdelicOrthogonalDoubleCoset := by
  let e := restrictedProductCongrRight U.orthogonal U'.orthogonal φ (.of_forall hφ)
  apply DoubleCoset.quotientCongr U.finiteAdelicOrthogonalDiagonal.range
    (integralSubgroup U.orthogonal) e
  · rw [MonoidHom.map_range]
    congr 1
    ext g p : 2
    change (e (U.finiteAdelicOrthogonalDiagonal g)) p =
      U'.finiteAdelicOrthogonalDiagonal g p
    rw [show (e (U.finiteAdelicOrthogonalDiagonal g)) p =
      φ p (U.finiteAdelicOrthogonalDiagonal g p) from
        restrictedProductCongrRight_apply U.orthogonal U'.orthogonal φ (.of_forall hφ)
          _ p]
    simpa only [finiteAdelicOrthogonalDiagonal_apply] using hdiag g p
  · exact map_integralSubgroup_restrictedProductCongrRight U.orthogonal U'.orthogonal φ hφ

/-- Componentwise equivalences which preserve every Spin reference subgroup and every rational
diagonal point identify the actual finite adelic Spin class sets. -/
def finiteAdelicSpinDoubleCosetCongr (U' : OrthogonalCompactOpens Q)
    (φ : ∀ p : Nat.Primes,
      spinGroup (Q.baseChange ℚ_[p]) ≃* spinGroup (Q.baseChange ℚ_[p]))
    (hφ : ∀ p, Set.BijOn (φ p) (U.spin p) (U'.spin p))
    (hdiag : ∀ (x : spinGroup Q) (p : Nat.Primes),
      φ p (CliffordAlgebra.spinGroupBaseChange (A := ℚ_[p]) Q x) =
        CliffordAlgebra.spinGroupBaseChange (A := ℚ_[p]) Q x) :
    U.finiteAdelicSpinDoubleCoset ≃ U'.finiteAdelicSpinDoubleCoset := by
  let e := restrictedProductCongrRight U.spin U'.spin φ (.of_forall hφ)
  apply DoubleCoset.quotientCongr U.finiteAdelicSpinDiagonal.range
    (integralSubgroup U.spin) e
  · rw [MonoidHom.map_range]
    congr 1
    ext x p : 2
    change (e (U.finiteAdelicSpinDiagonal x)) p = U'.finiteAdelicSpinDiagonal x p
    rw [show (e (U.finiteAdelicSpinDiagonal x)) p =
      φ p (U.finiteAdelicSpinDiagonal x p) from
        restrictedProductCongrRight_apply U.spin U'.spin φ (.of_forall hφ) _ p]
    simpa only [finiteAdelicSpinDiagonal_apply] using hdiag x p
  · exact map_integralSubgroup_restrictedProductCongrRight U.spin U'.spin φ hφ

/-- Componentwise equivalences which preserve every special-orthogonal reference subgroup and
every rational diagonal point identify the actual finite adelic special-orthogonal class sets. -/
def finiteAdelicSpecialOrthogonalDoubleCosetCongr (U' : OrthogonalCompactOpens Q)
    (φ : ∀ p : Nat.Primes,
      specialOrthogonalGroup (Q.baseChange ℚ_[p]) ≃*
        specialOrthogonalGroup (Q.baseChange ℚ_[p]))
    (hφ : ∀ p, Set.BijOn (φ p) (U.specialOrthogonal p) (U'.specialOrthogonal p))
    (hdiag : ∀ (g : specialOrthogonalGroup Q) (p : Nat.Primes),
      φ p (specialOrthogonalGroupBaseChange (A := ℚ_[p]) Q g) =
        specialOrthogonalGroupBaseChange (A := ℚ_[p]) Q g) :
    U.finiteAdelicSpecialOrthogonalDoubleCoset ≃
      U'.finiteAdelicSpecialOrthogonalDoubleCoset := by
  let e := restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal φ
    (.of_forall hφ)
  apply DoubleCoset.quotientCongr U.finiteAdelicSpecialOrthogonalDiagonal.range
    (integralSubgroup U.specialOrthogonal) e
  · rw [MonoidHom.map_range]
    congr 1
    ext g p : 2
    change (e (U.finiteAdelicSpecialOrthogonalDiagonal g)) p =
      U'.finiteAdelicSpecialOrthogonalDiagonal g p
    rw [show (e (U.finiteAdelicSpecialOrthogonalDiagonal g)) p =
      φ p (U.finiteAdelicSpecialOrthogonalDiagonal g p) from
        restrictedProductCongrRight_apply U.specialOrthogonal U'.specialOrthogonal φ
          (.of_forall hφ) _ p]
    simpa only [finiteAdelicSpecialOrthogonalDiagonal_apply] using hdiag g p
  · exact map_integralSubgroup_restrictedProductCongrRight U.specialOrthogonal
      U'.specialOrthogonal φ hφ

end

end OrthogonalCompactOpens
end QuadraticMap
end TauCeti
