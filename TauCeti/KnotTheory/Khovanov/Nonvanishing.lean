/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.EulerCharacteristic
public import TauCeti.KnotTheory.Khovanov.Parity
public import TauCeti.KnotTheory.PDCode.VertexResolution

/-!
# Khovanov homology at `q = 1` and its nonvanishing

For a planar oriented code `D` with `n` crossings, `n₋` of them negative, and `c` components, the
graded Euler characteristic of its Khovanov homology at `q = 1` is the normalized enhanced state
sum

`E(D) = ∑ₛ (-1) ^ (|S| - n₋) 2 ^ k(s) = 2 ^ c`,

where `S` is the set of crossings at which the state `s` selects the `B`-smoothing and `k(s)` is
the number of circles of the smoothing by `s`. In particular Khovanov homology never vanishes:
over a nontrivial Noetherian ring with the rank-nullity property, such as `ℤ` or `ℚ`, some group
`Khⁱʲ(D; R)` is nonzero, the empty diagram included.

The proof combines two facts. By the component parity of the quantum grading, `|S| + k(s)` has
the parity of `n₊ + c` for every state
(`TauCeti.OrientedPDCode.stateQuantumShift_add_stateLoopCount_mod_two`), so every state
contributes `(-1) ^ (n + c) (-2) ^ k(s)`. The unoriented state sum `∑ₛ (-2) ^ k(s)` is
`(-1) ^ (n + c) 2 ^ c` (`TauCeti.PDCode.sum_neg_two_pow_stateLoopCount`), by resolving one
crossing at a time and following the number of components
(`TauCeti.PDCode.componentCount_resolveCrossing_cases`).

## Main results

* `TauCeti.OrientedPDCode.sum_negOnePow_stateCochainDegree_mul_two_pow`: `E(D) = 2 ^ c`.
* `TauCeti.OrientedPDCode.eval₂_one_enhancedStateSum`: the enhanced state sum at `q = 1` is `2 ^ c`.
* `TauCeti.OrientedPDCode.eval₂_one_khovanovEulerChar`: the graded Euler characteristic of
  Khovanov homology at `q = 1` is `2 ^ c`.
* `TauCeti.OrientedPDCode.exists_not_isZero_khovanovHomology`: Khovanov homology is nonzero.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), 359-426.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3, for
  the Kauffman bracket state sum, whose loop value at `A = 1` is `-2`.
-/

public section

open CategoryTheory CategoryTheory.Limits LaurentPolynomial

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar)
include hD

/-- On a planar code, the state with `B`-smoothing set `S` and `k` circles contributes
`(-1) ^ (n + c) (-2) ^ k` to the normalized enhanced state sum, by the component parity of the
quantum grading. -/
private theorem negOnePow_stateCochainDegree_mul_two_pow (s : Fin n → Bool) :
    ((D.stateCochainDegree s).negOnePow : ℤ) * 2 ^ D.stateLoopCount s =
      (-1) ^ (n + D.componentCount) * (-2) ^ D.stateLoopCount s := by
  have hpar := D.stateQuantumShift_add_stateLoopCount_mod_two hD s
  have hcount := D.positiveCrossingCount_add_negativeCrossingCount
  have hsign : (D.stateCochainDegree s).negOnePow =
      ((n + D.componentCount + D.stateLoopCount s : ℕ) : ℤ).negOnePow := by
    rw [Int.negOnePow_eq_iff, Int.even_iff, stateCochainDegree_def]
    rw [stateQuantumShift_def] at hpar
    push_cast at hpar ⊢
    omega
  rw [hsign, Int.coe_negOnePow_natCast, neg_pow (2 : ℤ)]
  ring

/-- **The normalized enhanced state sum is `2 ^ c`.** For a planar oriented code with `c`
components, `∑ₛ (-1) ^ (|S| - n₋) 2 ^ k(s) = 2 ^ c`, where `S` is the set of `B`-smoothings of
the state `s` and `k(s)` the number of its circles. This is the graded Euler characteristic of
Khovanov homology at `q = 1`. -/
theorem sum_negOnePow_stateCochainDegree_mul_two_pow :
    ∑ s : Fin n → Bool, ((D.stateCochainDegree s).negOnePow : ℤ) * 2 ^ D.stateLoopCount s =
      2 ^ D.componentCount := by
  simp_rw [D.negOnePow_stateCochainDegree_mul_two_pow hD]
  rw [← Finset.mul_sum, D.toPDCode.sum_neg_two_pow_stateLoopCount, ← mul_assoc, ← pow_add,
    Even.neg_one_pow ⟨_, rfl⟩, one_mul]

/-- **The enhanced state sum at `q = 1`** of a planar oriented code with `c` components
is `2 ^ c`. -/
theorem eval₂_one_enhancedStateSum :
    eval₂ (RingHom.id ℤ) 1 D.enhancedStateSum = 2 ^ D.componentCount := by
  rw [← D.sum_negOnePow_stateCochainDegree_mul_two_pow hD, enhancedStateSum_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [map_mul, map_zsmul_unit, eval₂_T, one_zpow, Units.val_one, map_pow, map_add,
    smul_one_mul]
  rw [Units.smul_def, smul_eq_mul, one_add_one_eq_two]

variable (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [HasRankNullity.{u} R]

/-- **The graded Euler characteristic of Khovanov homology at `q = 1`** of a planar oriented code
with `c` components is `2 ^ c`: the alternating sum `∑ᵢⱼ (-1) ^ i rank Khⁱʲ(D; R)` over a
Noetherian ring with the rank-nullity property, such as `ℤ` or a field. -/
theorem eval₂_one_khovanovEulerChar :
    eval₂ (RingHom.id ℤ) 1 (D.khovanovEulerChar hD R) = 2 ^ D.componentCount := by
  rw [khovanovEulerChar_eq_enhancedStateSum, D.eval₂_one_enhancedStateSum hD]

/-- **Khovanov homology does not vanish.** Over a nontrivial Noetherian ring with the rank-nullity
property, such as `ℤ` or `ℚ`, some Khovanov homology group of a planar oriented code is nonzero,
the empty code included: otherwise its graded Euler characteristic would vanish at `q = 1`. -/
theorem exists_not_isZero_khovanovHomology :
    ∃ i j, ¬IsZero (D.khovanovHomology hD R i j) := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hzero : D.khovanovEulerChar hD R = 0 := by
    ext j
    rw [coeff_khovanovEulerChar_eq_sum]
    simp [ModuleCat.finrank_eq_zero_of_isZero (h _ j)]
  have hval := D.eval₂_one_khovanovEulerChar hD R
  rw [hzero, map_zero] at hval
  exact pow_ne_zero _ two_ne_zero hval.symm

end TauCeti.OrientedPDCode
