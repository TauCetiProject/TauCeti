/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.Star
public import TauCeti.Algebra.TypeAHeckeAlgebra.WenzlParam
public import TauCeti.Analysis.StarAlgebra.GNS.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.LeftSlice
import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.WenzlInterval
import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace.Zero

/-!
# Positivity of the Ocneanu trace on Wenzl's positive-real parameter set

For a real nonzero parameter `q : ℂˣ` (`IsSelfAdjoint (q : ℂ)`) with `Q = q ^ 2 > 0` and any
projection parameter `η ∈ TauCeti.wenzlPositiveSet Q`, the Ocneanu trace with Markov parameter
`z = q * η - q⁻¹ * (1 - η)` is `⋆`-positive on `TauCeti.InfiniteTypeAHeckeAlgebra ℂ q`
(`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_star_mul_self_nonneg`, bundled as
`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuPositiveFunctional`).

The proof combines:
1. The countable geometric models on `ℕ ⊕ₗ ℕᵒᵈ` for `1 < Q` and `0 < Q < 1`
   (`TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.WenzlInterval`).
2. Positivity of the `z = 0` Ocneanu trace at `Q = 1`, `η = 1 / 2`
   (`TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace.Zero`).
3. The finite positive and negative geometric atomic models for the discrete series `a_d(Q)`
   (`TauCeti.TypeAHeckeAlgebra.atomicTrace_geometric_eq`,
   `TauCeti.TypeAHeckeAlgebra.atomicTrace_negGeometric_eq`).

## Main definitions

* `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuPositiveFunctional`: the Ocneanu trace at
  `z = q * η - q⁻¹ * (1 - η)` bundled as a `StarPositiveFunctional`.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_star_mul_self_nonneg`: positivity of
  `ocneanuTrace ℂ q (q * η - q⁻¹ * (1 - η))` across `wenzlPositiveSet Q`.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §3.
* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7 and §3.1.
-/

public section

open scoped ComplexOrder

namespace TauCeti.InfiniteTypeAHeckeAlgebra

private theorem ocneanuTrace_wenzlParam_nonneg {q : ℂˣ} [Fact (IsSelfAdjoint (q : ℂ))]
    {Q : ℝ} (hQ0 : 0 < Q) (hQ : (Q : ℂ) = (q : ℂ) ^ 2) (b : Bool) (r : ℕ) {n : ℕ}
    (y : TypeAHeckeAlgebra ℂ q n) :
    let d : ℤ := if b then ((r + 1 : ℕ) : ℤ) else -((r + 1 : ℕ) : ℤ)
    0 ≤ ocneanuTrace ℂ q ((q : ℂ) * ((wenzlParam d Q : ℝ) : ℂ) -
        (↑q⁻¹ : ℂ) * (1 - ((wenzlParam d Q : ℝ) : ℂ)))
      (TypeAHeckeAlgebra.toInfinite ℂ q n (star y * y)) := by
  set Z : ℝ := ∑ a ∈ Finset.range (r + 1), Q ^ a
  have hZ0 : 0 < Z :=
    Finset.sum_pos (fun a _ ↦ pow_pos hQ0 a) (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero r))
  set c : ℝ := Z⁻¹
  have hcZ : (c : ℂ) * ∑ a ∈ Finset.range (r + 1), ((q : ℂ) ^ 2) ^ a = 1 := by
    simpa [c, Z, hQ] using congrArg ((↑) : ℝ → ℂ) (inv_mul_cancel₀ hZ0.ne')
  have h1Q : 1 + (q : ℂ) ^ 2 ≠ 0 := by
    rw [← hQ, ← Complex.ofReal_one, ← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  have hw (a : Fin (r + 1)) : (0 : ℂ) ≤ (c : ℂ) * ((q : ℂ) ^ 2) ^ (a : ℕ) := by
    have hcQ : 0 ≤ c * Q ^ (a : ℕ) := by positivity
    simpa [hQ] using Complex.zero_le_real.mpr hcQ
  have hmap (d : ℤ) : ((wenzlParam d Q : ℝ) : ℂ) = wenzlParam d ((q : ℂ) ^ 2) := by
    simpa [hQ] using map_wenzlParam Complex.ofRealHom d Q
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, hmap, mul_wenzlParam_neg_natCast_sub h1Q hcZ,
      ← TypeAHeckeAlgebra.atomicTrace_negGeometric_eq q hcZ (star y * y)]
    exact TypeAHeckeAlgebra.atomicTrace_star_mul_self_nonneg _ q hw y
  · simp only [↓reduceIte, hmap, mul_wenzlParam_natCast_sub h1Q hcZ,
      ← TypeAHeckeAlgebra.atomicTrace_geometric_eq q hcZ (star y * y)]
    exact TypeAHeckeAlgebra.atomicTrace_star_mul_self_nonneg _ q hw y

/-- **Positivity of the Ocneanu trace across Wenzl's positive-real parameter set.** For real nonzero
`q : ℂˣ` with `(Q : ℂ) = (q : ℂ) ^ 2` and `η ∈ wenzlPositiveSet Q`, the Ocneanu trace at
`z = q * η - q⁻¹ * (1 - η)` is nonnegative on every `star x * x`. -/
theorem ocneanuTrace_star_mul_self_nonneg {q : ℂˣ} [Fact (IsSelfAdjoint (q : ℂ))] {Q : ℝ}
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q)
    (x : InfiniteTypeAHeckeAlgebra ℂ q) :
    0 ≤ ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) (star x * x) := by
  have hQ0 : 0 < Q := by
    have hre : (q : ℂ) = ((q : ℂ).re : ℂ) :=
      (Complex.conj_eq_iff_re.mp (Fact.out : IsSelfAdjoint (q : ℂ)).star_eq).symm
    rw [Complex.ofReal_injective
      (hQ.trans ((congrArg (· ^ 2) hre).trans (Complex.ofReal_pow _ 2).symm))]
    exact sq_pos_of_ne_zero fun h0 ↦ q.ne_zero (by rw [hre, h0, Complex.ofReal_zero])
  obtain ⟨n, hx⟩ := exists_mem_stage x
  rw [← TypeAHeckeAlgebra.range_toInfinite, AlgHom.mem_range] at hx; obtain ⟨y, rfl⟩ := hx
  rw [← TypeAHeckeAlgebra.toInfinite_star, ← map_mul]
  rcases mem_wenzlPositiveSet_iff.mp hη with hIcc | ⟨d, hd, rfl⟩
  · rcases lt_trichotomy Q 1 with hQ1 | rfl | hQ1
    · have hle : Q / (1 + Q) ≤ 1 / (1 + Q) := div_le_div_of_nonneg_right hQ1.le (by linarith)
      rw [min_eq_right hle, max_eq_left hle] at hIcc
      rw [← TypeAHeckeAlgebra.countableAtomicTrace_wenzlLtOneWeight_eq_ocneanuTrace hQ0 hQ1 hQ.symm]
      exact TypeAHeckeAlgebra.countableAtomicTrace_star_mul_self_nonneg _ q _
        (fun a ↦ Complex.zero_le_real.mpr (TypeAHeckeAlgebra.wenzlLtOneWeight_nonneg hQ0 hIcc a)) y
    · rw [one_add_one_eq_two, min_self, max_self, Set.Icc_self, Set.mem_singleton_iff] at hIcc
      subst hIcc
      have hz0 : (q : ℂ) * ((1 / 2 : ℝ) : ℂ) - (↑q⁻¹ : ℂ) * (1 - ((1 / 2 : ℝ) : ℂ)) = 0 := by
        have _ := q.ne_zero; have hq2 : (q : ℂ) ^ 2 = 1 := by simpa using hQ.symm
        rw [Units.val_inv_eq_inv_val]; push_cast; field_simp; linear_combination hq2
      rw [hz0, map_mul, TypeAHeckeAlgebra.toInfinite_star]
      exact ocneanuTrace_zero_star_mul_self_nonneg _
    · have hle : 1 / (1 + Q) ≤ Q / (1 + Q) := div_le_div_of_nonneg_right hQ1.le (by linarith)
      rw [min_eq_left hle, max_eq_right hle] at hIcc
      rw [← TypeAHeckeAlgebra.countableAtomicTrace_wenzlGtOneWeight_eq_ocneanuTrace hQ1 hQ.symm]
      exact TypeAHeckeAlgebra.countableAtomicTrace_star_mul_self_nonneg _ q _
        (fun a ↦ Complex.zero_le_real.mpr (TypeAHeckeAlgebra.wenzlGtOneWeight_nonneg hQ1 hIcc a)) y
  · obtain ⟨_ | r, rfl | rfl⟩ := Int.eq_nat_or_neg d
    · exact absurd rfl hd
    · simp at hd
    · exact ocneanuTrace_wenzlParam_nonneg hQ0 hQ true r y
    · exact ocneanuTrace_wenzlParam_nonneg hQ0 hQ false r y

/-- The complex Ocneanu trace on `InfiniteTypeAHeckeAlgebra ℂ q` bundled as a
`StarPositiveFunctional` for real nonzero `q : ℂˣ` and `η ∈ wenzlPositiveSet Q`. -/
noncomputable def ocneanuPositiveFunctional (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] {Q : ℝ}
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q) :
    StarPositiveFunctional (InfiniteTypeAHeckeAlgebra ℂ q) where
  toLinearMap := ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η))
  square_nonneg := ocneanuTrace_star_mul_self_nonneg hQ hη

/-- Forgetting positivity recovers the underlying Ocneanu trace. -/
@[simp]
theorem toLinearMap_ocneanuPositiveFunctional (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] {Q : ℝ}
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q) :
    (ocneanuPositiveFunctional q hQ hη).toLinearMap =
      ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) := (rfl)

/-- Evaluating `ocneanuPositiveFunctional` at an element recovers `ocneanuTrace`. -/
@[simp]
theorem ocneanuPositiveFunctional_apply (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] {Q : ℝ}
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q)
    (x : InfiniteTypeAHeckeAlgebra ℂ q) :
    ocneanuPositiveFunctional q hQ hη x =
      ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) x := (rfl)

end TauCeti.InfiniteTypeAHeckeAlgebra
