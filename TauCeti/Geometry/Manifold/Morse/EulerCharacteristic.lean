/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Geometry.Manifold.Morse.Inequalities
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Field.ULift
import TauCeti.Geometry.Manifold.Morse.Generic.Basic

/-!
# Euler characteristics from Morse functions

Let `M` be a compact boundaryless manifold of dimension `m` and `V` a finite-dimensional module
over a division ring `k`. Write `χ(M; V) = ∑ᵢ₌₀ⁿ (-1)ⁱ dim Hᵢ(M; V)` for any `n ≥ m`. Euler's
equality (`TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_eq`) computes
`χ(M; V)` as `dim V` times the signed count `∑ᵢ (-1)ⁱ cᵢ(f)` of the critical points of any Morse
function `f`. This file draws the classical consequences of that identity.

The signed count is the sum of `(-1)^λ` over the critical points, `λ` being the Morse index
(`TauCeti.sum_range_neg_one_pow_mul_toNat_criticalCount_eq_sum`). Since the indices of `f` and
`-f` at a critical point add up to `m`, the signed counts of `f` and `-f` differ by the factor
`(-1)ᵐ` (`TauCeti.IsMorse.sum_range_neg_one_pow_mul_toNat_criticalCount_neg`). Applying Euler's
equality to both `f` and `-f`, for a Morse function which exists on every compact manifold
(`TauCeti.exists_isMorse`), gives `χ(M; V) = -χ(M; V)` when `m` is odd:

* a compact boundaryless manifold of odd dimension has Euler characteristic `0`
  (`TauCeti.sum_range_neg_one_pow_mul_finrank_singularHomology_eq_zero_of_odd`).

The same comparison, with Euler's equality over a field, shows that all Morse functions on `M`
have the same signed count (`TauCeti.IsMorse.sum_range_neg_one_pow_mul_toNat_criticalCount_eq`),
which vanishes in odd dimension
(`TauCeti.IsMorse.sum_range_neg_one_pow_mul_toNat_criticalCount_eq_zero`).

Since `(-1)^λ ≡ 1` modulo `2`, the signed count has the parity of the number of critical points:

* `χ(M; V) ≡ dim V · #Crit(f)` modulo `2` for every Morse function `f`
  (`TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_modEq`), so any two Morse
  functions on `M` have numbers of critical points of the same parity
  (`TauCeti.IsMorse.toNat_totalCriticalCount_modEq`), and in odd dimension every Morse function
  has an even number of critical points
  (`TauCeti.IsMorse.even_toNat_totalCriticalCount_of_odd`).

When `M` has finite CW type, the signed count is the cellular Euler characteristic
`TauCeti.eulerChar M`
(`TauCeti.IsMorse.sum_range_neg_one_pow_mul_toNat_criticalCount_eq_eulerChar`), which therefore
vanishes in odd dimension (`TauCeti.eulerChar_eq_zero_of_odd`).

The counts are the natural-number values `(criticalCount I f i).toNat`, which are the actual
numbers of critical points whenever the critical set is finite, in particular for a Morse function
on a compact manifold.

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

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  {f : M → ℝ}

/-! ### Compact manifolds -/

section Compact

variable [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {k : Type u} [DivisionRing k] (V : ModuleCat.{u} k) [Module.Finite k V]

variable (I) in
include I in
/-- **The Euler characteristic of an odd-dimensional manifold vanishes.** For a compact
boundaryless manifold `M` of odd dimension, `∑ᵢ₌₀ⁿ (-1)ⁱ dim Hᵢ(M; V) = 0` for every `n ≥ dim M`
and every finite-dimensional module `V` over a division ring. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_eq_zero_of_odd
    (hodd : Odd (finrank ℝ E)) {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of M)) = 0 := by
  obtain ⟨f, hf⟩ := exists_isMorse (I := I) (M := M)
  have h := hf.sum_range_neg_one_pow_mul_finrank_singularHomology_eq V hn
  have h' := hf.neg.sum_range_neg_one_pow_mul_finrank_singularHomology_eq V hn
  rw [hf.sum_range_neg_one_pow_mul_toNat_criticalCount_neg hn, hodd.neg_one_pow] at h'
  linarith

/-- **Parity of the number of critical points.** For a Morse function `f` on a compact boundaryless
manifold `M`, the Euler characteristic `∑ᵢ₌₀ⁿ (-1)ⁱ dim Hᵢ(M; V)`, for any `n ≥ dim M`, is congruent
modulo `2` to `dim V` times the number of critical points of `f`. -/
theorem IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_modEq (hf : IsMorse I f)
    {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of M)) ≡
      finrank k V * (totalCriticalCount I f).toNat [ZMOD 2] := by
  have hfin := hf.finite_criticalPoints
  rw [hf.sum_range_neg_one_pow_mul_finrank_singularHomology_eq V hn,
    sum_range_neg_one_pow_mul_toNat_criticalCount_eq_sum hfin.toFinset hfin.coe_toFinset hn,
    totalCriticalCount_def, hfin.encard_eq_coe_toFinset_card, ENat.toNat_natCast,
    Finset.card_eq_sum_ones]
  push_cast
  refine (Int.ModEq.sum fun x _ ↦ ?_).mul_left _
  simpa using ((show (-1 : ℤ) ≡ 1 [ZMOD 2] by decide).pow (manifoldMorseIndex I f x))

/-- Any two Morse functions on a compact boundaryless manifold have numbers of critical points of
the same parity. -/
theorem IsMorse.toNat_totalCriticalCount_modEq {g : M → ℝ} (hf : IsMorse I f) (hg : IsMorse I g) :
    (totalCriticalCount I f).toNat ≡ (totalCriticalCount I g).toNat [MOD 2] := by
  -- Compare both counts with the Euler characteristic with coefficients in a field.
  let K := ULift.{u} ℚ
  have h₁ := hf.sum_range_neg_one_pow_mul_finrank_singularHomology_modEq (ModuleCat.of K K) le_rfl
  have h₂ := hg.sum_range_neg_one_pow_mul_finrank_singularHomology_modEq (ModuleCat.of K K) le_rfl
  have hK : finrank K (ModuleCat.of K K) = 1 := finrank_self K
  rw [hK, Nat.cast_one, one_mul] at h₁ h₂
  exact Int.natCast_modEq_iff.1 (h₁.symm.trans h₂)

/-- Euler's equality with coefficients in `k` itself. -/
private theorem IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_self_eq
    (hf : IsMorse I f) {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj
          (ModuleCat.of k k)).obj (TopCat.of M)) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat := by
  rw [hf.sum_range_neg_one_pow_mul_finrank_singularHomology_eq (ModuleCat.of k k) hn,
    show finrank k (ModuleCat.of k k) = 1 from finrank_self k, Nat.cast_one, one_mul]

/-- **The signed count is independent of the Morse function.** Any two Morse functions on a
compact boundaryless manifold have the same signed count `∑ᵢ₌₀ⁿ (-1)ⁱ cᵢ` of critical points, for
every `n ≥ dim M`, namely the Euler characteristic of the manifold. -/
theorem IsMorse.sum_range_neg_one_pow_mul_toNat_criticalCount_eq {g : M → ℝ} (hf : IsMorse I f)
    (hg : IsMorse I g) {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I g i).toNat :=
  (hf.sum_range_neg_one_pow_mul_finrank_singularHomology_self_eq (k := ULift.{u} ℚ)
    hn).symm.trans (hg.sum_range_neg_one_pow_mul_finrank_singularHomology_self_eq hn)

/-- On a compact boundaryless manifold of odd dimension, every Morse function has signed count
`∑ᵢ₌₀ⁿ (-1)ⁱ cᵢ = 0` for every `n ≥ dim M`. -/
theorem IsMorse.sum_range_neg_one_pow_mul_toNat_criticalCount_eq_zero (hf : IsMorse I f)
    (hodd : Odd (finrank ℝ E)) {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat = 0 := by
  have h := hf.neg.sum_range_neg_one_pow_mul_toNat_criticalCount_eq hf hn
  rw [hf.sum_range_neg_one_pow_mul_toNat_criticalCount_neg hn, hodd.neg_one_pow] at h
  linarith

/-- On a compact boundaryless manifold of odd dimension, every Morse function has an even number
of critical points. -/
theorem IsMorse.even_toNat_totalCriticalCount_of_odd (hf : IsMorse I f)
    (hodd : Odd (finrank ℝ E)) : Even (totalCriticalCount I f).toNat := by
  let K := ULift.{u} ℚ
  have h := hf.sum_range_neg_one_pow_mul_finrank_singularHomology_modEq (ModuleCat.of K K) le_rfl
  rw [sum_range_neg_one_pow_mul_finrank_singularHomology_eq_zero_of_odd (M := M) I
    (ModuleCat.of K K) hodd le_rfl, show finrank K (ModuleCat.of K K) = 1 from finrank_self K,
    Nat.cast_one, one_mul] at h
  exact even_iff_two_dvd.2 (by exact_mod_cast Int.modEq_zero_iff_dvd.1 h.symm)

/-- **The signed count is the Euler characteristic.** For a Morse function on a compact
boundaryless manifold `M` of finite CW type, `∑ᵢ₌₀ⁿ (-1)ⁱ cᵢ = χ(M)` for every `n ≥ dim M`, where
`cᵢ` is the number of critical points of index `i`. -/
theorem IsMorse.sum_range_neg_one_pow_mul_toNat_criticalCount_eq_eulerChar [FiniteCWType M]
    (hf : IsMorse I f) {n : ℕ} (hn : finrank ℝ E ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (criticalCount I f i).toNat = eulerChar M := by
  rw [eulerChar_eq_finsum_finrank_singularHomology M (ULift.{u} ℚ),
    finsum_eq_sum_of_support_subset (s := Finset.range (n + 1)) _ ?_,
    hf.sum_range_neg_one_pow_mul_finrank_singularHomology_self_eq hn]
  -- Above the dimension there are no critical points, so homology vanishes by the weak Morse
  -- inequalities.
  intro i hi
  rw [Finset.coe_range, mem_Iio, Nat.lt_succ_iff]
  by_contra hlt
  have h := hf.finrank_singularHomology_le (ModuleCat.of (ULift.{u} ℚ) (ULift.{u} ℚ)) i
  rw [criticalCount_eq_zero_of_finrank_lt (hn.trans_lt (not_le.1 hlt)), ENat.toNat_zero,
    zero_mul, Nat.le_zero] at h
  simp [h] at hi

variable (I) in
include I in
/-- **A compact boundaryless manifold of odd dimension and finite CW type has Euler
characteristic `0`.** -/
theorem eulerChar_eq_zero_of_odd [FiniteCWType M] (hodd : Odd (finrank ℝ E)) :
    eulerChar M = 0 := by
  obtain ⟨f, hf⟩ := exists_isMorse (I := I) (M := M)
  rw [← hf.sum_range_neg_one_pow_mul_toNat_criticalCount_eq_eulerChar le_rfl,
    hf.sum_range_neg_one_pow_mul_toNat_criticalCount_eq_zero hodd le_rfl]

end Compact

end TauCeti
