/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Morse.Inequalities
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Field.ULift
import Mathlib.Data.ENat.BigOperators
import TauCeti.AlgebraicTopology.Singular.Sphere
import TauCeti.Geometry.Manifold.Morse.Generic.Basic

/-!
# The Euler characteristic and the parity of critical counts

Let `M` be a compact boundaryless manifold of dimension `m`, and write `cᵢ(f)` for the number of
critical points of index `i` of a Morse function `f` on `M`. Euler's equality
(`TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_eq`) identifies the
alternating sum `c₀(f) - c₁(f) + ⋯ ± cₘ(f)` with the Euler characteristic
`χ(M; k) = b₀ - b₁ + ⋯ ± bₘ` of `M`, where `bᵢ` is the dimension of `Hᵢ(M; k)` over a field `k`.
This file draws the numerical consequences.

* The alternating sum of the critical counts is the same for every Morse function on `M`.
* The number of critical points of a Morse function has the parity of `χ(M; k)`, since `cᵢ` and
  `(-1)ⁱ cᵢ` have the same parity.
* If `m` is odd, then `χ(M; k) = 0`. Replacing `f` by `-f` exchanges `cᵢ` and `cₘ₋ᵢ`
  (`TauCeti.IsMorse.criticalCount_neg`), which multiplies the alternating sum by `(-1)ᵐ = -1`;
  as both alternating sums are `χ(M; k)`, it vanishes. Every compact manifold carries a Morse
  function (`TauCeti.exists_isMorse`), so the statement involves no Morse function. In
  particular a Morse function on a closed odd-dimensional manifold has an even number of critical
  points.
* A Morse function on the sphere `Sⁿ` has an even number of critical points, since
  `χ(Sⁿ; k) = 1 + (-1)ⁿ`.

## Main results

* `TauCeti.IsMorse.sum_range_neg_one_pow_mul_criticalCount_eq`: the alternating count of critical
  points does not depend on the Morse function.
* `TauCeti.IsMorse.totalCriticalCount_modEq_sum_range_neg_one_pow_mul_finrank_singularHomology`:
  the number of critical points is congruent to the Euler characteristic modulo `2`.
* `TauCeti.IsMorse.sum_range_neg_one_pow_mul_criticalCount_eq_zero` and
  `TauCeti.sum_range_neg_one_pow_mul_finrank_singularHomology_eq_zero`: in odd dimension the
  alternating count of critical points and the Euler characteristic vanish.
* `TauCeti.IsMorse.even_totalCriticalCount_of_odd_finrank`: in odd dimension a Morse function has
  an even number of critical points.
* `TauCeti.IsMorse.even_totalCriticalCount_sphere`: a Morse function on a sphere has an even
  number of critical points.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
-/

public section

noncomputable section

open Module Set
open scoped ContDiff Manifold

universe u

namespace TauCeti

section General

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  {f g : M → ℝ}

/-- The alternating count of critical points may be summed up to any degree `n ≥ dim M`. -/
private theorem sum_range_neg_one_pow_mul_criticalCount_eq_of_le (f : M → ℝ) {n : ℕ}
    (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat =
      ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat := by
  refine (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun i _ hi ↦ ?_).symm
  rw [criticalCount_eq_zero_of_finrank_lt (by simp at hi; omega)]
  simp

variable [I.Boundaryless]

/-- Replacing a Morse function `f` by `-f` multiplies the alternating count of critical points by
`(-1) ^ dim M`, as it exchanges the numbers of critical points of index `i` and `dim M - i`. -/
private theorem IsMorse.sum_range_neg_one_pow_mul_criticalCount_neg (hf : IsMorse I f) :
    ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (criticalCount I (-f) i).toNat =
      (-1 : ℤ) ^ finrank ℝ E *
        ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat := by
  rw [← sum_range_neg_one_pow_sub_mul, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi : i ≤ finrank ℝ E := Finset.mem_range_succ_iff.1 hi
  rw [add_tsub_cancel_right, hf.criticalCount_neg (Nat.sub_le _ _), Nat.sub_sub_self hi]

variable [IsManifold I ∞ M] [CompactSpace M]

/-- The number of critical points of a Morse function on a compact manifold is congruent modulo `2`
to the alternating count `c₀ - c₁ + ⋯ ± cₙ`, for every `n ≥ dim M`. -/
private theorem IsMorse.totalCriticalCount_modEq_sum_range_neg_one_pow_mul_criticalCount
    (hf : IsMorse I f) {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ((totalCriticalCount I f).toNat : ℤ) ≡
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat [ZMOD 2] := by
  have hsum : (totalCriticalCount I f).toNat =
      ∑ i ∈ Finset.range (finrank ℝ E + 1), (criticalCount I f i).toNat := by
    rw [← sum_criticalCount_eq_totalCriticalCount,
      ENat.toNat_sum fun i _ ↦ hf.criticalCount_ne_top i]
  rw [sum_range_neg_one_pow_mul_criticalCount_eq_of_le f hn, hsum, Nat.cast_sum]
  refine (Int.ModEq.sum fun i _ ↦ ?_).symm
  simpa using ((show (-1 : ℤ) ≡ 1 [ZMOD 2] by decide).pow i).mul_right
    ((criticalCount I f i).toNat : ℤ)

variable [T2Space M]

section Coefficients

variable (k : Type u) [DivisionRing k]

/-- The alternating count of critical points of a Morse function on a compact manifold is the
Euler characteristic of `M` with coefficients in a division ring `k`. -/
private theorem IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_self_eq
    (hf : IsMorse I f) {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj
          (ModuleCat.of k k)).obj (TopCat.of M)) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat := by
  simpa using hf.sum_range_neg_one_pow_mul_finrank_singularHomology_eq (ModuleCat.of k k) hn

/-- **The alternating count of critical points is independent of the Morse function.** For Morse
functions `f` and `g` on a compact boundaryless manifold `M`, the alternating sums
`c₀ - c₁ + ⋯ ± cₙ` of their numbers of critical points of each index agree for every
`n ≥ dim M`: both are the Euler characteristic of `M`. -/
theorem IsMorse.sum_range_neg_one_pow_mul_criticalCount_eq (hf : IsMorse I f) (hg : IsMorse I g)
    {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I g i).toNat := by
  rw [← hf.sum_range_neg_one_pow_mul_finrank_singularHomology_self_eq (ULift.{u} ℚ) hn,
    hg.sum_range_neg_one_pow_mul_finrank_singularHomology_self_eq (ULift.{u} ℚ) hn]

/-- **The number of critical points has the parity of the Euler characteristic.** For a Morse
function `f` on a compact boundaryless manifold `M`, a division ring `k` and every `n ≥ dim M`,
the number of critical points of `f` is congruent modulo `2` to
`∑ᵢ₌₀ⁿ (-1)ⁱ dim Hᵢ(M; k)`. -/
theorem IsMorse.totalCriticalCount_modEq_sum_range_neg_one_pow_mul_finrank_singularHomology
    (hf : IsMorse I f) {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ((totalCriticalCount I f).toNat : ℤ) ≡
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj
          (ModuleCat.of k k)).obj (TopCat.of M)) [ZMOD 2] := by
  rw [hf.sum_range_neg_one_pow_mul_finrank_singularHomology_self_eq k hn]
  exact hf.totalCriticalCount_modEq_sum_range_neg_one_pow_mul_criticalCount hn

/-- **In odd dimension the alternating count of critical points vanishes.** For a Morse function
`f` on a compact boundaryless manifold of odd dimension, `c₀ - c₁ + ⋯ ± cₙ = 0` for every
`n ≥ dim M`, where `cᵢ` is the number of critical points of index `i`. -/
theorem IsMorse.sum_range_neg_one_pow_mul_criticalCount_eq_zero (hf : IsMorse I f)
    (hodd : Odd (finrank ℝ E)) {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat = 0 := by
  have h := hf.sum_range_neg_one_pow_mul_criticalCount_eq hf.neg hn
  rw [sum_range_neg_one_pow_mul_criticalCount_eq_of_le f hn,
    sum_range_neg_one_pow_mul_criticalCount_eq_of_le (-f) hn,
    hf.sum_range_neg_one_pow_mul_criticalCount_neg, hodd.neg_one_pow] at h
  rw [sum_range_neg_one_pow_mul_criticalCount_eq_of_le f hn]
  linarith

variable (I) {k} in
include I in
/-- **A closed odd-dimensional manifold has Euler characteristic zero.** For a compact boundaryless
manifold `M` of odd dimension and a finite-dimensional module `V` over a division ring,
`∑ᵢ₌₀ⁿ (-1)ⁱ dim Hᵢ(M; V) = 0` for every `n ≥ dim M`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_eq_zero (V : ModuleCat.{u} k)
    [Module.Finite k V] (hodd : Odd (finrank ℝ E)) {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of M)) = 0 := by
  obtain ⟨f, hf⟩ := exists_isMorse (I := I) (M := M)
  rw [hf.sum_range_neg_one_pow_mul_finrank_singularHomology_eq V hn,
    hf.sum_range_neg_one_pow_mul_criticalCount_eq_zero hodd hn, mul_zero]

end Coefficients

/-- **In odd dimension a Morse function has an even number of critical points.** -/
theorem IsMorse.even_totalCriticalCount_of_odd_finrank (hf : IsMorse I f)
    (hodd : Odd (finrank ℝ E)) : Even (totalCriticalCount I f).toNat := by
  have h := hf.totalCriticalCount_modEq_sum_range_neg_one_pow_mul_criticalCount le_rfl
  rw [hf.sum_range_neg_one_pow_mul_criticalCount_eq_zero hodd le_rfl] at h
  exact (Int.even_natCast _).1 (Int.even_iff.2 h)

end General

section Sphere

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {f : Metric.sphere (0 : E) 1 → ℝ}

/-- **A Morse function on a sphere has an even number of critical points.** The Euler
characteristic of `Sⁿ` is `1 + (-1)ⁿ`, which is even. -/
theorem IsMorse.even_totalCriticalCount_sphere (hf : IsMorse (𝓡 n) f) :
    Even (totalCriticalCount (𝓡 n) f).toNat := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have h := hf.totalCriticalCount_modEq_sum_range_neg_one_pow_mul_finrank_singularHomology
    (ULift.{u} ℚ) (n := n) (by simp)
  have hχ : ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
      finrank (ULift.{u} ℚ) (((AlgebraicTopology.singularHomologyFunctor
        (ModuleCat.{u} (ULift.{u} ℚ)) i).obj (ModuleCat.of (ULift.{u} ℚ) (ULift.{u} ℚ))).obj
          (TopCat.of (Metric.sphere (0 : E) 1))) = (-1) ^ n + 1 := by
    simp [ModuleCat.finrank_singularHomology_sphere_of_finrank_eq _
      (Fact.out : finrank ℝ E = n + 1), mul_add, Finset.sum_add_distrib]
  rw [hχ] at h
  have h1 : (-1 : ℤ) ^ n + 1 ≡ 0 [ZMOD 2] :=
    (((show (-1 : ℤ) ≡ 1 [ZMOD 2] by decide).pow n).add_right 1).trans (by simp)
  exact (Int.even_natCast _).1 (Int.even_iff.2 (h.trans h1))

end Sphere

end TauCeti
