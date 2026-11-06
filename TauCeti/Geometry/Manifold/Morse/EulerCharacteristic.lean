/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Geometry.Manifold.Morse.Inequalities
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
import Mathlib.Algebra.BigOperators.ModEq
import TauCeti.Geometry.Manifold.Morse.Generic.Basic

/-!
# The Euler characteristic and the parity of critical counts

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `m`, and let `cᵢ`
be the number of critical points of `f` of Morse index `i`. By Euler's equality in the Morse
inequalities, the alternating sum `∑ᵢ (-1)ⁱ cᵢ` is the alternating sum of the Betti numbers of `M`
over any field; when `M` has finite CW type it is the Euler characteristic `χ(M)`. This file
draws the classical consequences.

* The alternating sum is the same for all Morse functions on `M`, and it is congruent modulo `2`
  to the total number of critical points, since `(-1)ⁱ ≡ 1`. So the number of critical points of
  a Morse function has the parity of `χ(M)`.
* The function `-f` is Morse, with `cᵢ(-f) = c_{m - i}(f)`, so its alternating sum is `(-1)ᵐ`
  times that of `f`. Comparing `f` and `-f`, the alternating sum, and with it the alternating sum
  of the Betti numbers of `M`, vanishes when `m` is odd. In particular a closed odd-dimensional
  manifold has Euler characteristic `0`, and every Morse function on it has an even number of
  critical points.
* On the sphere `Sⁿ` the height function has one critical point of index `0` and one of index
  `n`, so every Morse function on `Sⁿ` has alternating sum `1 + (-1)ⁿ`, and an even number of
  critical points.

## Main results

* `TauCeti.sum_range_neg_one_pow_mul_criticalCount_eq_sum`: for finitely many critical points,
  `∑ᵢ (-1)ⁱ cᵢ` is the sum of `(-1) ^ λ(x)` over the critical points `x` of index `λ(x)`.
* `TauCeti.sum_range_neg_one_pow_mul_criticalCount_modEq`: it is congruent modulo `2` to the
  number of critical points.
* `TauCeti.IsMorse.sum_range_neg_one_pow_mul_criticalCount_neg`: the alternating sum of `-f` is
  `(-1) ^ dim M` times that of `f`.
* `TauCeti.IsMorse.sum_range_neg_one_pow_mul_criticalCount_eq`: two Morse functions on a compact
  manifold have the same alternating sum.
* `TauCeti.IsMorse.sum_range_neg_one_pow_mul_criticalCount_eq_zero` and
  `TauCeti.IsMorse.even_totalCriticalCount`: in odd dimension the alternating sum vanishes and the
  number of critical points is even.
* `TauCeti.sum_range_neg_one_pow_mul_finrank_singularHomology_eq_zero`: the alternating sum of
  the Betti numbers of a compact odd-dimensional manifold vanishes.
* `TauCeti.IsMorse.eulerChar_eq`, `TauCeti.IsMorse.toNat_totalCriticalCount_modEq_eulerChar` and
  `TauCeti.eulerChar_eq_zero`: for `M` of finite CW type, `χ(M) = ∑ᵢ (-1)ⁱ cᵢ`, the number of
  critical points has the parity of `χ(M)`, and `χ(M) = 0` in odd dimension.
* `TauCeti.IsMorse.sum_range_neg_one_pow_mul_criticalCount_sphere` and
  `TauCeti.IsMorse.even_totalCriticalCount_sphere`: Morse functions on spheres.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
-/

public section

open Metric Module Set
open scoped ContDiff Manifold

universe u

namespace TauCeti

section Count

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  {f : M → ℝ} {n : ℕ}

/-- The alternating sum of the critical counts may stop at any `n ≥ dim M`, since there are no
critical points of larger index. -/
private theorem sum_range_neg_one_pow_mul_criticalCount_eq_finrank (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat =
      ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat := by
  refine (Finset.sum_subset (Finset.range_subset_range.2 (by lia)) fun i _ hi ↦ ?_).symm
  rw [criticalCount_eq_zero_of_finrank_lt (by simpa using hi)]
  simp

/-- If `f` has finitely many critical points, the alternating sum `∑ᵢ (-1)ⁱ cᵢ` of the numbers
`cᵢ` of critical points of index `i` is the sum of `(-1) ^ λ(x)` over the critical points `x`, where
`λ(x)` is the Morse index of `f` at `x`. -/
theorem sum_range_neg_one_pow_mul_criticalCount_eq_sum (hfin : (criticalPoints I f).Finite)
    (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat =
      ∑ x ∈ hfin.toFinset, (-1 : ℤ) ^ manifoldMorseIndex I f x := by
  classical
  have hc (i : ℕ) : (criticalCount I f i).toNat =
      {x ∈ hfin.toFinset | manifoldMorseIndex I f x = i}.card := by
    have : {x ∈ criticalPoints I f | manifoldMorseIndex I f x = i} =
        ↑{x ∈ hfin.toFinset | manifoldMorseIndex I f x = i} := by
      ext
      simp
    rw [criticalCount_def, this, encard_coe_eq_coe_finsetCard, ENat.toNat_natCast]
  have hmaps : ∀ x ∈ hfin.toFinset, manifoldMorseIndex I f x ∈ Finset.range (n + 1) :=
    fun _ _ ↦ Finset.mem_range.2 (Nat.lt_succ_of_le (manifoldMorseIndex_le_finrank.trans hn))
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_const, nsmul_eq_mul, hc, mul_comm]

/-- **Parity of the critical count.** If `f` has finitely many critical points, the alternating
sum `∑ᵢ (-1)ⁱ cᵢ` of the numbers of critical points of each index is congruent modulo `2` to the
number of critical points. -/
theorem sum_range_neg_one_pow_mul_criticalCount_modEq (hfin : (criticalPoints I f).Finite)
    (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat ≡
      (totalCriticalCount I f).toNat [ZMOD 2] := by
  rw [sum_range_neg_one_pow_mul_criticalCount_eq_sum hfin hn, totalCriticalCount_def,
    hfin.encard_eq_coe_toFinset_card, ENat.toNat_natCast, Finset.card_eq_sum_ones, Nat.cast_sum,
    Nat.cast_one]
  refine Int.ModEq.sum fun x _ ↦ ?_
  rcases neg_one_pow_eq_or ℤ (manifoldMorseIndex I f x) with h | h <;> rw [h]
  decide

/-- **Duality of the alternating critical count.** For a Morse function `f` on a boundaryless
manifold of dimension `m`, the alternating sum `∑ᵢ (-1)ⁱ cᵢ` for `-f` is `(-1)ᵐ` times that for
`f`, since `-f` has as many critical points of index `i` as `f` has of index `m - i`. -/
theorem IsMorse.sum_range_neg_one_pow_mul_criticalCount_neg [I.Boundaryless] (hf : IsMorse I f)
    (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I (-f) i).toNat =
      (-1) ^ finrank ℝ E *
        ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat := by
  rw [sum_range_neg_one_pow_mul_criticalCount_eq_finrank hn,
    sum_range_neg_one_pow_mul_criticalCount_eq_finrank hn, Finset.mul_sum,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj : j ≤ finrank ℝ E := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  -- Reindexing by `j ↦ m - j` turns the sign `(-1) ^ (m - j)` into `(-1) ^ m * (-1) ^ j`.
  have hsign : (-1 : ℤ) ^ (finrank ℝ E - j) = (-1) ^ finrank ℝ E * (-1) ^ j := by
    rw [← Nat.sub_add_cancel hj, pow_add, Nat.add_sub_cancel, mul_assoc, ← pow_add, ← two_mul,
      pow_mul, neg_one_sq, one_pow, mul_one]
  rw [add_tsub_cancel_right, hf.criticalCount_neg (Nat.sub_le _ _), Nat.sub_sub_self hj, hsign,
    mul_assoc]

end Count

section Compact

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [CompactSpace M] {f g : M → ℝ} {n : ℕ}

/-- Euler's equality with coefficients in a division ring `k`: the alternating sum of the Betti
numbers of a compact manifold over `k` is the alternating sum of the critical counts of a Morse
function. -/
private theorem IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_self_eq
    (hf : IsMorse I f) (k : Type u) [DivisionRing k] (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj
          (ModuleCat.of k k)).obj (TopCat.of M)) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat := by
  simpa using hf.sum_range_neg_one_pow_mul_finrank_singularHomology_eq (ModuleCat.of k k) hn

/-- **Topological invariance of the alternating critical count.** Two Morse functions on a compact
boundaryless manifold have the same alternating sum `∑ᵢ (-1)ⁱ cᵢ` of their numbers of critical
points of each index: both equal the alternating sum of the Betti numbers of the manifold. -/
theorem IsMorse.sum_range_neg_one_pow_mul_criticalCount_eq (hf : IsMorse I f) (hg : IsMorse I g)
    (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I g i).toNat := by
  rw [← hf.sum_range_neg_one_pow_mul_finrank_singularHomology_self_eq (ULift.{u} ℚ) hn,
    hg.sum_range_neg_one_pow_mul_finrank_singularHomology_self_eq (ULift.{u} ℚ) hn]

/-- The alternating sum `∑ᵢ (-1)ⁱ cᵢ` of the numbers of critical points of each index of a Morse
function on a compact boundaryless manifold of odd dimension vanishes. -/
theorem IsMorse.sum_range_neg_one_pow_mul_criticalCount_eq_zero (hf : IsMorse I f)
    (hodd : Odd (finrank ℝ E)) (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat = 0 := by
  have h := hf.sum_range_neg_one_pow_mul_criticalCount_eq hf.neg hn
  rw [hf.sum_range_neg_one_pow_mul_criticalCount_neg hn, hodd.neg_one_pow] at h
  lia

/-- **A Morse function on a closed odd-dimensional manifold has an even number of critical
points.** -/
theorem IsMorse.even_totalCriticalCount (hf : IsMorse I f) (hodd : Odd (finrank ℝ E)) :
    Even (totalCriticalCount I f) := by
  have h := (sum_range_neg_one_pow_mul_criticalCount_modEq hf.finite_criticalPoints le_rfl).dvd
  rw [hf.sum_range_neg_one_pow_mul_criticalCount_eq_zero hodd le_rfl] at h
  rw [← ENat.natCast_toNat hf.totalCriticalCount_ne_top]
  exact (Nat.even_iff.2 (by lia)).natCast

variable (I) in
include I in
/-- **The Euler characteristic of a closed odd-dimensional manifold vanishes.** On a compact
boundaryless manifold of odd dimension, the alternating sum of the dimensions of the singular
homology with coefficients in a finite-dimensional module `V` over a division ring is zero. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_eq_zero {k : Type u} [DivisionRing k]
    (V : ModuleCat.{u} k) [Module.Finite k V] (hodd : Odd (finrank ℝ E)) (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of M)) = 0 := by
  obtain ⟨f, hf⟩ := exists_isMorse (I := I) (M := M)
  rw [hf.sum_range_neg_one_pow_mul_finrank_singularHomology_eq V hn,
    hf.sum_range_neg_one_pow_mul_criticalCount_eq_zero hodd hn, mul_zero]

section FiniteCWType

variable [FiniteCWType M]

/-- **The Euler characteristic as an alternating critical count.** If a compact boundaryless
manifold `M` has finite CW type, its Euler characteristic is `∑ᵢ (-1)ⁱ cᵢ` for every Morse function
on `M`, where `cᵢ` is the number of critical points of index `i`. -/
theorem IsMorse.eulerChar_eq (hf : IsMorse I f) (hn : finrank ℝ E ≤ n) :
    eulerChar M = ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat := by
  rw [eulerChar_eq_finsum_finrank_singularHomology M (ULift.{u} ℚ),
    ← hf.sum_range_neg_one_pow_mul_finrank_singularHomology_self_eq (ULift.{u} ℚ) hn]
  -- Above `n ≥ dim M` the homology vanishes by the weak Morse inequalities.
  refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
  rw [Finset.coe_range, mem_Iio]
  by_contra! hi'
  have h := hf.finrank_singularHomology_le (ModuleCat.of (ULift.{u} ℚ) (ULift.{u} ℚ)) i
  rw [criticalCount_eq_zero_of_finrank_lt (by lia), ENat.toNat_zero, zero_mul,
    Nat.le_zero] at h
  exact hi (by simp only [h, Nat.cast_zero, mul_zero])

/-- **Parity of the critical count.** If a compact boundaryless manifold `M` has finite CW type,
every Morse function on `M` has a number of critical points congruent to the Euler characteristic
of `M` modulo `2`. -/
theorem IsMorse.toNat_totalCriticalCount_modEq_eulerChar (hf : IsMorse I f) :
    (totalCriticalCount I f).toNat ≡ eulerChar M [ZMOD 2] := by
  rw [hf.eulerChar_eq le_rfl]
  exact (sum_range_neg_one_pow_mul_criticalCount_modEq hf.finite_criticalPoints le_rfl).symm

variable (I) in
include I in
/-- **The Euler characteristic of a closed odd-dimensional manifold vanishes.** -/
theorem eulerChar_eq_zero (hodd : Odd (finrank ℝ E)) : eulerChar M = 0 := by
  obtain ⟨f, hf⟩ := exists_isMorse (I := I) (M := M)
  rw [hf.eulerChar_eq le_rfl, hf.sum_range_neg_one_pow_mul_criticalCount_eq_zero hodd le_rfl]

end FiniteCWType

end Compact

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {f : sphere (0 : E) 1 → ℝ}

/-- **The alternating critical count of a Morse function on a sphere.** Every Morse function on
the unit sphere `Sⁿ` has `∑ᵢ (-1)ⁱ cᵢ = 1 + (-1)ⁿ`, the Euler characteristic of `Sⁿ`, where `cᵢ`
is the number of critical points of index `i`. -/
theorem IsMorse.sum_range_neg_one_pow_mul_criticalCount_sphere (hf : IsMorse (𝓡 n) f) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount (𝓡 n) f i).toNat = 1 + (-1) ^ n := by
  classical
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : Nontrivial E :=
    nontrivial_of_finrank_pos (by rw [Fact.out (p := finrank ℝ E = n + 1)]; lia)
  obtain ⟨v⟩ : Nonempty (sphere (0 : E) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  have hn : finrank ℝ (EuclideanSpace ℝ (Fin n)) ≤ n := by simp
  have hh := isMorse_sphereHeight (n := n) v
  have hfin := hh.finite_criticalPoints
  have hpoles : hfin.toFinset = {v, -v} := by
    ext
    simp
  rw [hf.sum_range_neg_one_pow_mul_criticalCount_eq hh hn,
    sum_range_neg_one_pow_mul_criticalCount_eq_sum hfin hn, hpoles,
    Finset.sum_pair (ne_neg_of_mem_unit_sphere ℝ v), manifoldMorseIndex_sphereHeight_self,
    manifoldMorseIndex_sphereHeight_neg, pow_zero, add_comm]

/-- **A Morse function on a sphere has an even number of critical points.** -/
theorem IsMorse.even_totalCriticalCount_sphere (hf : IsMorse (𝓡 n) f) :
    Even (totalCriticalCount (𝓡 n) f) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have h := (sum_range_neg_one_pow_mul_criticalCount_modEq hf.finite_criticalPoints
    (finrank_euclideanSpace_fin (𝕜 := ℝ)).le).dvd
  rw [hf.sum_range_neg_one_pow_mul_criticalCount_sphere] at h
  rw [← ENat.natCast_toNat hf.totalCriticalCount_ne_top]
  refine (Nat.even_iff.2 ?_).natCast
  rcases neg_one_pow_eq_or ℤ n with h' | h' <;> rw [h'] at h <;> lia

end Sphere

end TauCeti
