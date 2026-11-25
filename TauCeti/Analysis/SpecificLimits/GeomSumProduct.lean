/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Topology.Algebra.InfiniteSum.GroupCompletion
import TauCeti.Analysis.Normed.Ring.Basic
import TauCeti.Analysis.SpecificLimits.Normed
import TauCeti.Topology.Algebra.InfiniteSum.LinearRecurrence

/-!
# The generating function of a product of two geometric partial sums

Write `S_a(k) = ∑_{i ≤ k} aⁱ`. In a normed field, if `x`, `a x`, `b x` and `a b x` all have norm
less than one, then

`∑_k S_a(k) S_b(k) xᵏ = (1 - a b x²) / ((1 - x) (1 - a x) (1 - b x) (1 - a b x))`.

No hypothesis `a ≠ 1` or `b ≠ 1` is needed: instead of the closed form of `S_a(k)`, the proof uses
the first-order recurrences `S_a(k + 1) = a S_a(k) + 1` and
`S_a(k + 1) S_b(k + 1) = a b S_a(k) S_b(k) + S_a(k + 1) + S_b(k + 1) - 1`, summed by
`HasSum.eq_smul_add_of_linearRec₁`. The series converges absolutely, since its `k`-th term has norm
at most `(k + 1)² Rᵏ`, where `R < 1` is the largest of the four norms. Completeness is not needed:
the identity is proved in the completion of the field and pulled back.

At `a = p^α`, `b = p^β` and `x = p^(-s)` this is the local factor at a prime `p` of the Dirichlet
series of `σ_α(n) σ_β(n)` (Ramanujan's identity).

## Main results

* `TauCeti.summable_norm_geom_sum_mul_geom_sum_mul_geometric`: the series converges absolutely.
* `TauCeti.hasSum_geom_sum_mul_geom_sum_mul_geometric`: the identity above.

## References

* Alex Kontorovich, Terence Tao and contributors, [Prime Number Theorem and More][PNTGeomSum],
  `IwaniecKowalskiCh1.lean`, `ramanujan_geom_product_sum` (over `ℂ`, assuming summability).

[PNTGeomSum]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/301f8be/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean
-/

public section

open Finset

namespace TauCeti

variable {K : Type*} [NormedField K] {a b x : K}

/-- For `i, j ≤ k`, the monomial `aⁱ bʲ xᵏ` has norm at most `Rᵏ`, where `R` is the largest of
`‖x‖`, `‖a x‖`, `‖b x‖` and `‖a b x‖`. -/
private theorem norm_pow_mul_pow_mul_pow_le {i j k : ℕ} (hi : i ≤ k) (hj : j ≤ k) :
    ‖a ^ i * b ^ j * x ^ k‖ ≤ max (max ‖x‖ ‖a * x‖) (max ‖b * x‖ ‖a * b * x‖) ^ k := by
  wlog hij : i ≤ j generalizing a b i j
  · calc ‖a ^ i * b ^ j * x ^ k‖ = ‖b ^ j * a ^ i * x ^ k‖ := by rw [mul_comm (a ^ i)]
      _ ≤ max (max ‖x‖ ‖b * x‖) (max ‖a * x‖ ‖b * a * x‖) ^ k := this hj hi (by omega)
      _ = _ := by rw [mul_comm b a, max_max_max_comm, max_max_max_comm ‖x‖ ‖a * x‖]
  set R := max (max ‖x‖ ‖a * x‖) (max ‖b * x‖ ‖a * b * x‖)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hij
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  -- `aⁱ b^(i + j) x^(i + j + k) = (a b x)ⁱ (b x)ʲ xᵏ`
  have h : a ^ i * b ^ (i + j) * x ^ (i + j + k) = (a * b * x) ^ i * (b * x) ^ j * x ^ k := by
    ring
  rw [h, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, pow_add, pow_add]
  gcongr
  · exact le_max_of_le_right (le_max_right _ _)
  · exact le_max_of_le_right (le_max_left _ _)
  · exact le_max_of_le_left (le_max_left _ _)

/-- If `x`, `a x`, `b x` and `a b x` have norm less than one, the series
`∑_k S_a(k) S_b(k) xᵏ`, where `S_a(k) = ∑_{i ≤ k} aⁱ`, converges absolutely: its `k`-th term has
norm at most `(k + 1)² Rᵏ`, where `R < 1` is the largest of `‖x‖`, `‖a x‖`, `‖b x‖` and
`‖a b x‖`. -/
theorem summable_norm_geom_sum_mul_geom_sum_mul_geometric (hx : ‖x‖ < 1) (ha : ‖a * x‖ < 1)
    (hb : ‖b * x‖ < 1) (hab : ‖a * b * x‖ < 1) :
    Summable fun k : ℕ ↦
      ‖(∑ i ∈ range (k + 1), a ^ i) * (∑ i ∈ range (k + 1), b ^ i) * x ^ k‖ := by
  set R := max (max ‖x‖ ‖a * x‖) (max ‖b * x‖ ‖a * b * x‖)
  have hR0 : 0 ≤ R := le_max_of_le_left (le_max_of_le_left (norm_nonneg x))
  have hR : ‖R‖ < 1 := by
    rw [Real.norm_of_nonneg hR0]
    exact max_lt (max_lt hx ha) (max_lt hb hab)
  refine .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ ?_)
    (summable_add_pow_mul_geometric_of_norm_lt_one 1 2 hR)
  simp_rw [sum_mul_sum, sum_mul]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i ∈ range (k + 1), ‖∑ j ∈ range (k + 1), a ^ i * b ^ j * x ^ k‖
      ≤ ∑ _i ∈ range (k + 1), ∑ _j ∈ range (k + 1), R ^ k := by
        gcongr with _ hi
        refine (norm_sum_le _ _).trans (sum_le_sum fun _ hj ↦ ?_)
        exact norm_pow_mul_pow_mul_pow_le (Nat.lt_succ_iff.mp (mem_range.mp hi))
          (Nat.lt_succ_iff.mp (mem_range.mp hj))
    _ = ((k : ℝ) + 1) ^ 2 * R ^ k := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      push_cast
      ring

/-- The identity in a complete normed field. -/
private theorem hasSum_geom_sum_mul_geom_sum_mul_geometric_of_complete [CompleteSpace K]
    (hx : ‖x‖ < 1) (ha : ‖a * x‖ < 1) (hb : ‖b * x‖ < 1) (hab : ‖a * b * x‖ < 1) :
    HasSum (fun k : ℕ ↦ (∑ i ∈ range (k + 1), a ^ i) * (∑ i ∈ range (k + 1), b ^ i) * x ^ k)
      ((1 - a * b * x ^ 2) / ((1 - x) * (1 - a * x) * (1 - b * x) * (1 - a * b * x))) := by
  -- the one-factor series `∑ S_c(k) xᵏ`, the case `b = 0` of the summability above
  have hone (c : K) (hc : ‖c * x‖ < 1) :
      HasSum (fun k : ℕ ↦ (∑ i ∈ range (k + 1), c ^ i) * x ^ k) ((1 - x)⁻¹ * (1 - c * x)⁻¹) := by
    have hs :=
      (summable_norm_geom_sum_mul_geom_sum_mul_geometric (b := 0) hx hc (by simp) (by simp))
        |>.of_norm.hasSum
    simp only [zero_pow_eq, sum_ite_eq', mem_range, Nat.zero_lt_succ, ↓reduceIte, mul_one] at hs
    have H := hs.eq_smul_add_of_linearRec₁ (D := c * x) (hasSum_geometric_of_norm_lt_one hx)
      (by simp) fun r ↦ by simp only [smul_eq_mul, geom_sum_succ, pow_succ]; ring
    rw [smul_eq_mul, ← sub_eq_iff_eq_add', ← one_sub_mul] at H
    rw [← H, mul_comm, inv_mul_cancel_left₀ (one_sub_ne_zero_of_norm_lt_one hc)]
    exact hs
  have h := (summable_norm_geom_sum_mul_geom_sum_mul_geometric hx ha hb hab).of_norm.hasSum
  have H := h.eq_smul_add_of_linearRec₁ (D := a * b * x)
    (((hone a ha).add (hone b hb)).sub (hasSum_geometric_of_norm_lt_one hx)) (by simp)
    fun r ↦ by simp only [smul_eq_mul, geom_sum_succ, pow_succ]; ring
  convert h using 1
  have h0 := one_sub_ne_zero_of_norm_lt_one hx
  have h1 := one_sub_ne_zero_of_norm_lt_one ha
  have h2 := one_sub_ne_zero_of_norm_lt_one hb
  have h3 := one_sub_ne_zero_of_norm_lt_one hab
  rw [smul_eq_mul] at H
  field_simp at H ⊢
  linear_combination -H

/-- **The generating function of `S_a(k) S_b(k)`.** In a normed field, if `x`, `a x`, `b x` and
`a b x` have norm less than one, then, with `S_a(k) = ∑_{i ≤ k} aⁱ`,
`∑_k S_a(k) S_b(k) xᵏ = (1 - a b x²) / ((1 - x) (1 - a x) (1 - b x) (1 - a b x))`. -/
theorem hasSum_geom_sum_mul_geom_sum_mul_geometric (hx : ‖x‖ < 1) (ha : ‖a * x‖ < 1)
    (hb : ‖b * x‖ < 1) (hab : ‖a * b * x‖ < 1) :
    HasSum (fun k : ℕ ↦ (∑ i ∈ range (k + 1), a ^ i) * (∑ i ∈ range (k + 1), b ^ i) * x ^ k)
      ((1 - a * b * x ^ 2) / ((1 - x) * (1 - a * x) * (1 - b * x) * (1 - a * b * x))) := by
  let φ := UniformSpace.Completion.coeRingHom (α := K)
  have hφ (y : K) : ‖φ y‖ = ‖y‖ := UniformSpace.Completion.norm_coe y
  have h := hasSum_geom_sum_mul_geom_sum_mul_geometric_of_complete (a := φ a) (b := φ b)
    (x := φ x) (by rwa [hφ]) (by rwa [← map_mul, hφ]) (by rwa [← map_mul, hφ])
    (by rwa [← map_mul, ← map_mul, hφ])
  -- `toCompl` and `coeRingHom` are both the coercion `K → Completion K`
  have hcoe (y : K) : (y : UniformSpace.Completion K) = φ y := by
    simp [φ, UniformSpace.Completion.coeRingHom]
  have htoCompl (y : K) : UniformSpace.Completion.toCompl y = φ y := by
    simp [UniformSpace.Completion.toCompl, hcoe]
  rw [← hasSum_iff_hasSum_compl]
  simp only [Function.comp_def, htoCompl, hcoe]
  simpa only [map_div₀, map_sub, map_mul, map_one, map_pow, map_sum] using h

end TauCeti
