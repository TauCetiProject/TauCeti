/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Inequalities
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Field.ULift
import TauCeti.Analysis.Normed.Module.Ball
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

Since `(-1)^λ ≡ 1` modulo `2`, the signed count has the parity of the number of critical points:

* `χ(M; V) ≡ dim V · #Crit(f)` modulo `2` for every Morse function `f`
  (`TauCeti.IsMorse.sum_range_neg_one_pow_mul_finrank_singularHomology_modEq`), so any two Morse
  functions on `M` have numbers of critical points of the same parity
  (`TauCeti.IsMorse.toNat_totalCriticalCount_modEq`).

On the sphere `Sⁿ` the height function has a minimum and a maximum and no other critical point.
Hence `χ(Sⁿ; V) = (1 + (-1)ⁿ) dim V`
(`TauCeti.sum_range_neg_one_pow_mul_finrank_singularHomology_sphere`) and every Morse function
on `Sⁿ` has an even number of critical points
(`TauCeti.IsMorse.even_toNat_totalCriticalCount_sphere`).

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

end Compact

/-! ### Spheres -/

section Sphere

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- **The Euler characteristic of the sphere.** For the unit sphere `Sⁿ`,
`∑ᵢ₌₀ᴺ (-1)ⁱ dim Hᵢ(Sⁿ; V) = (1 + (-1)ⁿ) dim V` for every `N ≥ n`: the height function is a Morse
function with one critical point of index `0` and one of index `n`. -/
theorem sum_range_neg_one_pow_mul_finrank_singularHomology_sphere {k : Type u} [DivisionRing k]
    (V : ModuleCat.{u} k) [Module.Finite k V] {N : ℕ} (hN : n ≤ N) :
    ∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i *
        finrank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) i).obj V).obj
          (TopCat.of (sphere (0 : E) 1))) =
      finrank k V * (1 + (-1) ^ n) := by
  classical
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  obtain ⟨v⟩ : Nonempty (sphere (0 : E) 1) := nonempty_sphere n
  have hN' : finrank ℝ (EuclideanSpace ℝ (Fin n)) ≤ N := by rwa [finrank_euclideanSpace_fin]
  rw [(isMorse_sphereHeight v).sum_range_neg_one_pow_mul_finrank_singularHomology_eq V hN',
    sum_range_neg_one_pow_mul_toNat_criticalCount_eq_sum {v, -v}
      (by rw [Finset.coe_pair, criticalPoints_sphereHeight]) hN',
    Finset.sum_pair (ne_neg_of_mem_unit_sphere ℝ v), manifoldMorseIndex_sphereHeight_self,
    manifoldMorseIndex_sphereHeight_neg, pow_zero, add_comm]

/-- **Morse functions on a sphere have an even number of critical points.** -/
theorem IsMorse.even_toNat_totalCriticalCount_sphere {f : sphere (0 : E) 1 → ℝ}
    (hf : IsMorse (𝓡 n) f) : Even (totalCriticalCount (𝓡 n) f).toNat := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  obtain ⟨v⟩ : Nonempty (sphere (0 : E) 1) := nonempty_sphere n
  have h₂ : totalCriticalCount (𝓡 n) (sphereHeight v) = 2 := by
    rw [totalCriticalCount_def, criticalPoints_sphereHeight,
      encard_pair (ne_neg_of_mem_unit_sphere ℝ v)]
  have h := hf.toNat_totalCriticalCount_modEq (isMorse_sphereHeight v)
  rw [h₂] at h
  exact Nat.even_iff.2 h

end Sphere

end TauCeti
