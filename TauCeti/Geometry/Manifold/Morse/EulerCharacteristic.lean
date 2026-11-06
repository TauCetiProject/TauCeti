/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Morse.Inequalities
import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere
import TauCeti.Geometry.Manifold.Morse.Generic.Basic

/-!
# The Euler characteristic from critical points

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `m`, and write
`cᵢ` for the number of critical points of `f` of index `i`. Euler's equality
(`TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_eq`) identifies the
alternating critical count `∑ᵢ (-1)ⁱ cᵢ` with the Euler characteristic
`χ(M) = ∑ᵢ (-1)ⁱ dim Hᵢ(M; k)` of singular homology over any division ring `k`. This file draws
the classical consequences.

* The alternating count `∑ᵢ (-1)ⁱ cᵢ` is the sum of `(-1) ^ ind x` over the critical points `x`,
  so it has the same parity as the total number of critical points.
* Replacing `f` by `-f` exchanges the indices `i` and `m - i`, so it multiplies the alternating
  count by `(-1) ^ m`. Since all Morse functions on `M` have the same alternating count, a compact
  boundaryless manifold of odd dimension has Euler characteristic `0`, and every Morse function on
  it has an even number of critical points.
* The number of critical points of a Morse function has the parity of `χ(M)`, so all Morse
  functions on `M` have numbers of critical points of the same parity.
* When `M` has finite CW type, the alternating count is `TauCeti.eulerChar M`. On the sphere `Sⁿ`
  it is therefore `1 + (-1) ^ n` (`TauCeti.eulerChar_sphere`), which is even, so every Morse
  function on `Sⁿ` has an even number of critical points.

Critical counts are the `ℕ∞`-valued `TauCeti.criticalCount` and `TauCeti.totalCriticalCount`, read
as natural numbers through `ENat.toNat`; this loses nothing here, because a Morse function on a
compact manifold has finitely many critical points. Since every compact boundaryless manifold
carries a Morse function (`TauCeti.exists_isMorse`), the statements about `χ(M)` assume no
function.

The elementary facts about the alternating count, that it is a sum over the critical points
(`TauCeti.sum_range_neg_one_pow_mul_criticalCount_eq_finsum`) and that `-f` multiplies it by
`(-1) ^ m` (`TauCeti.IsMorse.sum_range_neg_one_pow_mul_criticalCount_neg`), live with the critical
counts in `TauCeti.Geometry.Manifold.Morse.CriticalPoints`.

## Main results

* `TauCeti.IsMorse.sum_range_neg_one_pow_mul_criticalCount_eq`: any two Morse functions on a
  compact manifold have the same alternating critical count.
* `TauCeti.sum_range_neg_one_pow_mul_finrank_singularHomology_eq_zero` and
  `TauCeti.eulerChar_eq_zero_of_odd_finrank`: **a compact boundaryless manifold of odd dimension
  has Euler characteristic `0`.**
* `TauCeti.IsMorse.totalCriticalCount_modEq_sum_range_neg_one_pow_mul_finrank_singularHomology`
  and `TauCeti.IsMorse.totalCriticalCount_modEq`: the number of critical points has the parity of
  the Euler characteristic, independently of the Morse function.
* `TauCeti.IsMorse.even_totalCriticalCount_of_odd_finrank`: in odd dimension the number of
  critical points is even.
* `TauCeti.IsMorse.sum_range_neg_one_pow_mul_criticalCount_eq_eulerChar`: for `M` of finite CW
  type the alternating critical count is `TauCeti.eulerChar M`.
* `TauCeti.IsMorse.sum_range_neg_one_pow_mul_criticalCount_sphere` and
  `TauCeti.IsMorse.even_totalCriticalCount_sphere`: Morse functions on `Sⁿ` have alternating count
  `1 + (-1) ^ n` and an even number of critical points.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 5.
-/

public section

noncomputable section

open Metric Module Set
open scoped ContDiff Manifold

universe u

namespace TauCeti

section Compact

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [CompactSpace M] {f g : M → ℝ}
  {k : Type u} [DivisionRing k]

/-- Euler's equality with coefficients in `k` itself, with the critical count summed over
`0, …, dim M`. -/
private theorem IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_self_eq
    (hf : IsMorse I f) {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj
          (ModuleCat.of k k)).obj (TopCat.of M)) =
      ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat := by
  rw [hf.sum_range_neg_one_pow_mul_finrank_singularHomology_eq (ModuleCat.of k k) hn,
    sum_range_neg_one_pow_mul_criticalCount_of_le hn]
  have h1 : finrank k (ModuleCat.of k k) = 1 := finrank_self k
  rw [h1, Nat.cast_one, one_mul]

/-- **The alternating critical count is independent of the Morse function.** Any two Morse
functions on a compact boundaryless manifold have the same alternating critical count
`∑ᵢ (-1)ⁱ cᵢ`, namely the Euler characteristic of the manifold. -/
theorem IsMorse.sum_range_neg_one_pow_mul_criticalCount_eq (hf : IsMorse I f) (hg : IsMorse I g) :
    ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat =
      ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (criticalCount I g i).toNat :=
  (hf.sum_range_neg_one_pow_mul_finrank_singularHomology_self_eq (k := ULift.{u} ℚ)
    le_rfl).symm.trans (hg.sum_range_neg_one_pow_mul_finrank_singularHomology_self_eq le_rfl)

/-- On a compact boundaryless manifold of odd dimension, every Morse function has alternating
critical count `∑ᵢ (-1)ⁱ cᵢ = 0`. -/
theorem IsMorse.sum_range_neg_one_pow_mul_criticalCount_eq_zero (hf : IsMorse I f)
    (hE : Odd (finrank ℝ E)) :
    ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat = 0 := by
  have h := hf.neg.sum_range_neg_one_pow_mul_criticalCount_eq hf
  rw [hf.sum_range_neg_one_pow_mul_criticalCount_neg, hE.neg_one_pow] at h
  linarith

variable (I M) in
include I in
/-- **A compact boundaryless manifold of odd dimension has Euler characteristic `0`.** For every
finite-dimensional module `V` over a division ring and every `n ≥ dim M`,
`∑ᵢ₌₀ⁿ (-1)ⁱ dim Hᵢ(M; V) = 0`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_eq_zero (V : ModuleCat.{u} k)
    [Module.Finite k V] (hE : Odd (finrank ℝ E)) {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of M)) = 0 := by
  obtain ⟨f, hf⟩ := exists_isMorse (I := I) (M := M)
  rw [hf.sum_range_neg_one_pow_mul_finrank_singularHomology_eq V hn,
    sum_range_neg_one_pow_mul_criticalCount_of_le hn,
    hf.sum_range_neg_one_pow_mul_criticalCount_eq_zero hE, mul_zero]

/-- **The number of critical points has the parity of the Euler characteristic.** For a Morse
function on a compact boundaryless manifold `M`, a division ring `k` and every `n ≥ dim M`, the
number of critical points is congruent modulo `2` to `∑ᵢ₌₀ⁿ (-1)ⁱ dim Hᵢ(M; k)`. -/
theorem IsMorse.totalCriticalCount_modEq_sum_range_neg_one_pow_mul_finrank_singularHomology
    (hf : IsMorse I f) {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ((totalCriticalCount I f).toNat : ℤ) ≡
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj
          (ModuleCat.of k k)).obj (TopCat.of M)) [ZMOD 2] := by
  rw [hf.sum_range_neg_one_pow_mul_finrank_singularHomology_self_eq hn]
  exact totalCriticalCount_modEq_sum_range_neg_one_pow_mul_criticalCount hf.finite_criticalPoints

/-- Any two Morse functions on a compact boundaryless manifold have numbers of critical points of
the same parity. -/
theorem IsMorse.totalCriticalCount_modEq (hf : IsMorse I f) (hg : IsMorse I g) :
    (totalCriticalCount I f).toNat ≡ (totalCriticalCount I g).toNat [MOD 2] := by
  have hf' := totalCriticalCount_modEq_sum_range_neg_one_pow_mul_criticalCount
    hf.finite_criticalPoints
  have hg' := totalCriticalCount_modEq_sum_range_neg_one_pow_mul_criticalCount
    hg.finite_criticalPoints
  rw [hf.sum_range_neg_one_pow_mul_criticalCount_eq hg] at hf'
  exact Int.natCast_modEq_iff.1 (hf'.trans hg'.symm)

/-- On a compact boundaryless manifold of odd dimension, every Morse function has an even number of
critical points. -/
theorem IsMorse.even_totalCriticalCount_of_odd_finrank (hf : IsMorse I f)
    (hE : Odd (finrank ℝ E)) : Even (totalCriticalCount I f).toNat := by
  have h := totalCriticalCount_modEq_sum_range_neg_one_pow_mul_criticalCount
    hf.finite_criticalPoints
  rw [hf.sum_range_neg_one_pow_mul_criticalCount_eq_zero hE] at h
  exact even_iff_two_dvd.2 (by exact_mod_cast Int.modEq_zero_iff_dvd.1 h)

/-- **The alternating critical count is the Euler characteristic.** For a Morse function on a
compact boundaryless manifold `M` of finite CW type, `∑ᵢ (-1)ⁱ cᵢ = χ(M)`, where `cᵢ` is the
number of critical points of index `i`. -/
theorem IsMorse.sum_range_neg_one_pow_mul_criticalCount_eq_eulerChar [FiniteCWType M]
    (hf : IsMorse I f) :
    ∑ i ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat =
      eulerChar M := by
  rw [eulerChar_eq_finsum_finrank_singularHomology M (ULift.{u} ℚ),
    finsum_eq_sum_of_support_subset (s := Finset.range (finrank ℝ E + 1)) _ ?_,
    hf.sum_range_neg_one_pow_mul_finrank_singularHomology_self_eq le_rfl]
  -- Above the dimension there are no critical points, so homology vanishes by the weak Morse
  -- inequalities.
  intro i hi
  rw [Finset.coe_range, mem_Iio, Nat.lt_succ_iff]
  by_contra hlt
  have h := hf.finrank_singularHomology_le (ModuleCat.of (ULift.{u} ℚ) (ULift.{u} ℚ)) i
  rw [criticalCount_eq_zero_of_finrank_lt (not_le.1 hlt), ENat.toNat_zero, zero_mul,
    Nat.le_zero] at h
  simp [h] at hi

variable (I M) in
include I in
/-- **A compact boundaryless manifold of odd dimension and finite CW type has Euler
characteristic `0`.** -/
theorem eulerChar_eq_zero_of_odd_finrank [FiniteCWType M] (hE : Odd (finrank ℝ E)) :
    eulerChar M = 0 := by
  obtain ⟨f, hf⟩ := exists_isMorse (I := I) (M := M)
  rw [← hf.sum_range_neg_one_pow_mul_criticalCount_eq_eulerChar,
    hf.sum_range_neg_one_pow_mul_criticalCount_eq_zero hE]

end Compact

section Sphere

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {f : sphere (0 : E) 1 → ℝ}

/-- Every Morse function on the sphere `Sⁿ` has alternating critical count
`∑ᵢ (-1)ⁱ cᵢ = 1 + (-1) ^ n`, the Euler characteristic of `Sⁿ`. -/
theorem IsMorse.sum_range_neg_one_pow_mul_criticalCount_sphere (hf : IsMorse (𝓡 n) f) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount (𝓡 n) f i).toNat =
      1 + (-1) ^ n := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have h := hf.sum_range_neg_one_pow_mul_criticalCount_eq_eulerChar
  rw [finrank_euclideanSpace_fin] at h
  rw [h, eulerChar_sphere (Fact.out : finrank ℝ E = n + 1)]

/-- **Morse functions on a sphere have an even number of critical points.** -/
theorem IsMorse.even_totalCriticalCount_sphere (hf : IsMorse (𝓡 n) f) :
    Even (totalCriticalCount (𝓡 n) f).toNat := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have h := totalCriticalCount_modEq_sum_range_neg_one_pow_mul_criticalCount
    hf.finite_criticalPoints
  rw [finrank_euclideanSpace_fin, hf.sum_range_neg_one_pow_mul_criticalCount_sphere] at h
  have h2 := h.trans (Int.modEq_zero_iff_dvd.2 (odd_one.add_odd odd_neg_one.pow).two_dvd)
  exact even_iff_two_dvd.2 (by exact_mod_cast Int.modEq_zero_iff_dvd.1 h2)

end Sphere

end TauCeti
