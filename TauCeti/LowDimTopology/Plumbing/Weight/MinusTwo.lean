/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Plumbing.Weight.Sublevel

/-!
# The canonical weight of an all-minus-two plumbing

When every sphere of a plumbing has self-intersection `-2`, its canonical characteristic
covector vanishes. The corresponding characteristic weight is therefore half the negative
self-intersection of a lattice point. When the self-pairing is nonpositive, this weight is
nonnegative with infimum zero; negative-definiteness further makes the origin its unique zero.

This identifies the bottom lattice point in the canonical spin-c structure of a
negative-definite all-`-2` plumbing. In particular it supplies the minimal generator needed to
compute the lattice homology of Dynkin plumbings such as the negative-definite `E8` plumbing.

## Main results

* `TauCeti.PlumbingGraph.canonicalCharacteristic_eq_zero_of_weight_eq_neg_two`: the canonical
  covector vanishes when every framing is `-2`.
* `TauCeti.PlumbingGraph.characteristicWeight_canonical_of_weight_eq_neg_two`: the canonical
  weight is half the negative intersection-form self-pairing.
* `TauCeti.PlumbingGraph.characteristicWeight_canonical_nonneg_of_weight_eq_neg_two` and
  `TauCeti.PlumbingGraph.sInfCharacteristicWeight_canonical_eq_zero_of_weight_eq_neg_two`: when
  the self-pairing is nonpositive, this weight is nonnegative with infimum zero.
* `TauCeti.PlumbingGraph.characteristicWeight_canonical_eq_zero_iff_of_weight_eq_neg_two`: on a
  negative-definite plumbing this weight has the origin as its unique zero.

## References

The characteristic-weight convention is that of A. Nemethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Sections 2--3, after Ozsvath--Szabo,
[arXiv:math/0203265](https://arxiv.org/abs/math/0203265).
-/

public section

namespace TauCeti

namespace PlumbingGraph

variable {V : Type*} (P : PlumbingGraph V)

variable [DecidableEq V] [Fintype V]

/-- For an all-`-2` plumbing, the canonical characteristic weight is half the negative
self-intersection of the lattice point. -/
theorem characteristicWeight_canonical_of_weight_eq_neg_two
    (hweight : ∀ v : V, P.weight v = -2) (x : V → ℤ) :
    P.characteristicWeight
        ⟨P.canonicalCharacteristic, P.isCharacteristicVector_canonicalCharacteristic⟩ x =
      -(P.intersectionForm x x / 2) := by
  rw [P.characteristicWeight_def, P.characteristicWeightNumerator_def]
  simp_rw [congrFun (P.canonicalCharacteristic_eq_zero_of_weight_eq_neg_two hweight)]
  simp

/-- For an all-`-2` plumbing, twice the canonical characteristic weight is the negative
self-intersection of the lattice point. -/
theorem two_mul_characteristicWeight_canonical_of_weight_eq_neg_two
    (hweight : ∀ v : V, P.weight v = -2) (x : V → ℤ) :
    2 * P.characteristicWeight
        ⟨P.canonicalCharacteristic, P.isCharacteristicVector_canonicalCharacteristic⟩ x =
      -P.intersectionForm x x := by
  rw [P.two_mul_characteristicWeight, P.characteristicWeightNumerator_def]
  simp_rw [congrFun (P.canonicalCharacteristic_eq_zero_of_weight_eq_neg_two hweight)]
  simp

/-- On an all-`-2` plumbing with nonpositive self-pairing, the canonical characteristic weight is
nonnegative. -/
theorem characteristicWeight_canonical_nonneg_of_weight_eq_neg_two
    (hnonpos : ∀ x : V → ℤ, P.intersectionForm x x ≤ 0)
    (hweight : ∀ v : V, P.weight v = -2) (x : V → ℤ) :
    0 ≤ P.characteristicWeight
      ⟨P.canonicalCharacteristic, P.isCharacteristicVector_canonicalCharacteristic⟩ x := by
  have hpair := hnonpos x
  have hdouble := P.two_mul_characteristicWeight_canonical_of_weight_eq_neg_two hweight x
  omega

/-- On a negative-definite all-`-2` plumbing, the canonical characteristic weight vanishes
exactly at the origin. -/
@[simp]
theorem characteristicWeight_canonical_eq_zero_iff_of_weight_eq_neg_two
    (hneg : P.IsNegativeDefinite) (hweight : ∀ v : V, P.weight v = -2) (x : V → ℤ) :
    P.characteristicWeight
        ⟨P.canonicalCharacteristic, P.isCharacteristicVector_canonicalCharacteristic⟩ x = 0 ↔
      x = 0 := by
  constructor
  · intro hx
    apply (hneg.intersectionForm_self_eq_zero_iff x).mp
    have hdouble := P.two_mul_characteristicWeight_canonical_of_weight_eq_neg_two hweight x
    omega
  · rintro rfl
    exact P.characteristicWeight_zero _

/-- The infimum of the canonical characteristic weight of an all-`-2` plumbing with nonpositive
self-pairing is zero. -/
@[simp]
theorem sInfCharacteristicWeight_canonical_eq_zero_of_weight_eq_neg_two
    (hnonpos : ∀ x : V → ℤ, P.intersectionForm x x ≤ 0)
    (hweight : ∀ v : V, P.weight v = -2) :
    P.sInfCharacteristicWeight
      ⟨P.canonicalCharacteristic, P.isCharacteristicVector_canonicalCharacteristic⟩ = 0 := by
  apply le_antisymm
  · rw [P.sInfCharacteristicWeight_def]
    apply csInf_le
    · exact ⟨0, by rintro _ ⟨x, rfl⟩; exact
        P.characteristicWeight_canonical_nonneg_of_weight_eq_neg_two hnonpos hweight x⟩
    · exact ⟨0, P.characteristicWeight_zero _⟩
  · exact P.le_sInfCharacteristicWeight _ fun x =>
      P.characteristicWeight_canonical_nonneg_of_weight_eq_neg_two hnonpos hweight x

end PlumbingGraph

end TauCeti
