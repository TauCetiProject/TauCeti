/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere
public import TauCeti.Geometry.Manifold.Morse.Inequalities
import Mathlib.Data.ENat.BigOperators
import TauCeti.Geometry.Manifold.Morse.Generic.Basic

/-!
# Morse functions and the Euler characteristic

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `m`, with `cᵢ`
critical points of index `i`. Euler's equality says that the alternating sum of the dimensions of
the singular homology of `M`, with coefficients in a finite-dimensional module `V` over a division
ring, is `dim V · ∑ᵢ (-1)ⁱ cᵢ`. This file draws the classical consequences of that equality.

* The homology of `M` vanishes above `m`, so its alternating sum of dimensions is a finite sum,
  equal to `dim V · ∑ᵢ₌₀ᵐ (-1)ⁱ cᵢ`
  (`TauCeti.IsMorse.finsum_neg_one_pow_mul_finrank_singularHomology`). If `M` has finite CW type,
  `∑ᵢ₌₀ᵐ (-1)ⁱ cᵢ` is its Euler characteristic (`TauCeti.IsMorse.eulerChar_eq`).
* Replacing `f` by `-f` exchanges `cᵢ` and `c_{m-i}`, so it multiplies `∑ᵢ (-1)ⁱ cᵢ` by `(-1)ᵐ`
  (`TauCeti.IsMorse.sum_range_neg_one_pow_mul_criticalCount_neg`). Both functions compute the
  same homology, so in odd dimension `∑ᵢ (-1)ⁱ cᵢ = 0` for every Morse function
  (`TauCeti.IsMorse.sum_range_neg_one_pow_mul_criticalCount_eq_zero_of_odd_finrank`), and a
  compact odd-dimensional manifold has Euler characteristic zero
  (`TauCeti.finsum_neg_one_pow_mul_finrank_singularHomology_eq_zero_of_odd_finrank` and
  `TauCeti.eulerChar_eq_zero_of_odd_finrank`).
* Since `(-1)ⁱ ≡ 1` modulo `2`, the number of critical points of `f` has the parity of the Euler
  characteristic of `M` (`TauCeti.IsMorse.totalCriticalCount_toNat_modEq` and
  `TauCeti.IsMorse.totalCriticalCount_toNat_modEq_eulerChar`). The sphere `Sⁿ` has Euler
  characteristic `1 + (-1)ⁿ`, so every Morse function on a sphere has an even number of critical
  points (`TauCeti.IsMorse.even_totalCriticalCount_sphere`).

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Theorem 2.44.
-/

public section

noncomputable section

open Metric Module Set Topology
open scoped ContDiff Manifold

universe u

namespace TauCeti

section Negation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] {f : M → ℝ}

/-- **The alternating critical count of `-f`.** Replacing a Morse function `f` on an
`m`-dimensional manifold by `-f` multiplies `∑ᵢ₌₀ᵐ (-1)ⁱ cᵢ` by `(-1)ᵐ`, where `cᵢ` is the number of
critical points of index `i`. -/
theorem IsMorse.sum_range_neg_one_pow_mul_criticalCount_neg (hf : IsMorse I f) :
    ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (criticalCount I (-f) i).toNat =
      (-1) ^ finrank ℝ E *
        ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat := by
  rw [Finset.mul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi : i ≤ finrank ℝ E := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [hf.criticalCount_neg (by lia), Nat.add_sub_cancel, Nat.sub_sub_self hi, ← mul_assoc,
    ← pow_add, (by lia : finrank ℝ E + i = finrank ℝ E - i + 2 * i), pow_add, pow_mul,
    neg_one_sq, one_pow, mul_one]

end Negation

/-- A division ring has dimension one over itself, as an object of `ModuleCat`. -/
private theorem finrank_of_self (k : Type u) [DivisionRing k] : finrank k (ModuleCat.of k k) = 1 :=
  finrank_self k

section Compact

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V]

/-- **Euler's equality as a finite sum.** For a Morse function `f` on a compact boundaryless
manifold `M` of dimension `m`, the singular homology `Hᵢ(M; V)` vanishes for `i > m`, and
`∑ᵢ (-1)ⁱ dim Hᵢ(M; V) = dim V · ∑ᵢ₌₀ᵐ (-1)ⁱ cᵢ`, where `cᵢ` is the number of critical points of
index `i`. -/
theorem IsMorse.finsum_neg_one_pow_mul_finrank_singularHomology (hf : IsMorse I f) :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of M)) =
      finrank k V *
        ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat := by
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (finrank ℝ E + 1)) fun i hi ↦ ?_]
  · exact hf.sum_range_neg_one_pow_mul_finrank_singularHomology_eq V le_rfl
  -- Above the dimension there are no critical points, so the weak inequality kills homology.
  by_contra hlt
  have hle := hf.finrank_singularHomology_le V i
  rw [criticalCount_eq_zero_of_finrank_lt (by simpa using hlt), ENat.toNat_zero, zero_mul,
    Nat.le_zero] at hle
  simp [hle] at hi

/-- **The Euler characteristic of a manifold with a Morse function.** If a compact boundaryless
manifold `M` of dimension `m` has finite CW type, its Euler characteristic is `∑ᵢ₌₀ᵐ (-1)ⁱ cᵢ`
for every Morse function on `M`, where `cᵢ` is the number of critical points of index `i`. -/
theorem IsMorse.eulerChar_eq [FiniteCWType M] (hf : IsMorse I f) :
    eulerChar M =
      ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat := by
  rw [eulerChar_eq_finsum_finrank_singularHomology M (ULift.{u} ℚ),
    hf.finsum_neg_one_pow_mul_finrank_singularHomology (.of (ULift.{u} ℚ) (ULift.{u} ℚ)),
    finrank_of_self, Nat.cast_one, one_mul]

/-- **Morse functions in odd dimension.** On a compact boundaryless manifold of odd dimension `m`,
every Morse function `f` satisfies `∑ᵢ₌₀ᵐ (-1)ⁱ cᵢ = 0`, where `cᵢ` is the number of critical
points of index `i`: the functions `f` and `-f` compute the same homology, while passing to `-f`
changes the sign of this sum. -/
theorem IsMorse.sum_range_neg_one_pow_mul_criticalCount_eq_zero_of_odd_finrank (hf : IsMorse I f)
    (hodd : Odd (finrank ℝ E)) :
    ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat = 0 := by
  have h := (hf.finsum_neg_one_pow_mul_finrank_singularHomology
    (ModuleCat.of (ULift.{u} ℚ) (ULift.{u} ℚ))).symm.trans
      (hf.neg.finsum_neg_one_pow_mul_finrank_singularHomology _)
  rw [hf.sum_range_neg_one_pow_mul_criticalCount_neg, hodd.neg_one_pow, finrank_of_self,
    Nat.cast_one, one_mul, neg_one_mul] at h
  linarith

variable (I) in
include I in
/-- **The Euler characteristic in odd dimension.** The alternating sum of the dimensions of the
singular homology of a compact boundaryless manifold of odd dimension vanishes, for every
finite-dimensional coefficient module. -/
theorem finsum_neg_one_pow_mul_finrank_singularHomology_eq_zero_of_odd_finrank
    (hodd : Odd (finrank ℝ E)) :
    ∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of M)) = 0 := by
  obtain ⟨f, hf⟩ := exists_isMorse (I := I) (M := M)
  rw [hf.finsum_neg_one_pow_mul_finrank_singularHomology V,
    hf.sum_range_neg_one_pow_mul_criticalCount_eq_zero_of_odd_finrank hodd, mul_zero]

variable (I) in
include I in
/-- **A compact odd-dimensional manifold has Euler characteristic zero.** -/
theorem eulerChar_eq_zero_of_odd_finrank [FiniteCWType M] (hodd : Odd (finrank ℝ E)) :
    eulerChar M = 0 := by
  obtain ⟨f, hf⟩ := exists_isMorse (I := I) (M := M)
  rw [hf.eulerChar_eq, hf.sum_range_neg_one_pow_mul_criticalCount_eq_zero_of_odd_finrank hodd]

omit [T2Space M] in
/-- The number of critical points of a Morse function on a compact boundaryless manifold of
dimension `m` is congruent modulo `2` to `∑ᵢ₌₀ᵐ (-1)ⁱ cᵢ`, where `cᵢ` is the number of critical
points of index `i`. -/
private theorem IsMorse.totalCriticalCount_toNat_modEq_sum (hf : IsMorse I f) :
    ((totalCriticalCount I f).toNat : ℤ) ≡
      ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat
      [ZMOD 2] := by
  rw [← sum_criticalCount_eq_totalCriticalCount,
    ENat.toNat_sum fun i _ ↦ hf.criticalCount_ne_top i]
  refine (ZMod.intCast_eq_intCast_iff _ _ 2).1 ?_
  push_cast
  simp [CharTwo.neg_eq]

/-- **The parity of the number of critical points.** The number of critical points of a Morse
function on a compact boundaryless manifold `M` is congruent modulo `2` to the alternating sum of
the dimensions of the singular homology of `M` with coefficients in a division ring `k`. -/
theorem IsMorse.totalCriticalCount_toNat_modEq (hf : IsMorse I f) :
    ((totalCriticalCount I f).toNat : ℤ) ≡
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj
          (ModuleCat.of k k)).obj (TopCat.of M)) [ZMOD 2] := by
  rw [hf.finsum_neg_one_pow_mul_finrank_singularHomology (.of k k), finrank_of_self, Nat.cast_one,
    one_mul]
  exact hf.totalCriticalCount_toNat_modEq_sum

/-- **The parity of the number of critical points.** If a compact boundaryless manifold `M` has
finite CW type, the number of critical points of every Morse function on `M` is congruent modulo
`2` to the Euler characteristic of `M`. -/
theorem IsMorse.totalCriticalCount_toNat_modEq_eulerChar [FiniteCWType M] (hf : IsMorse I f) :
    ((totalCriticalCount I f).toNat : ℤ) ≡ eulerChar M [ZMOD 2] := by
  rw [hf.eulerChar_eq]
  exact hf.totalCriticalCount_toNat_modEq_sum

end Compact

section Sphere

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {f : sphere (0 : E) 1 → ℝ}

/-- **A Morse function on a sphere has an even number of critical points.** The parity of the
number of critical points is that of the Euler characteristic `1 + (-1)ⁿ` of `Sⁿ`. -/
theorem IsMorse.even_totalCriticalCount_sphere (hf : IsMorse (𝓡 n) f) :
    Even (totalCriticalCount (𝓡 n) f) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have h := hf.totalCriticalCount_toNat_modEq_eulerChar
  rw [eulerChar_sphere (Fact.out : finrank ℝ E = n + 1)] at h
  have heven : Even ((totalCriticalCount (𝓡 n) f).toNat) := by
    rw [← Int.even_natCast, Int.even_iff, h.eq]
    rcases neg_one_pow_eq_or ℤ n with h' | h' <;> simp [h']
  rw [← ENat.natCast_toNat hf.totalCriticalCount_ne_top]
  exact heven.natCast

end Sphere

end TauCeti
