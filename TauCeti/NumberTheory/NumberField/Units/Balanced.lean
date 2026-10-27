/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.House
public import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Balanced representatives modulo units and bounded divisors

Let `K` be a number field of degree `d` and let `u` be a family of `rank K` units of maximal rank,
so that their logarithmic embeddings form a basis of the logarithmic space. Rounding the
coordinates of a vector of the logarithmic space down on this basis approximates it by the
logarithmic embedding of a product `∏ j, u j ^ n j`, within the sum of the norms of the
logarithmic embeddings of the `u j`.

Applied to the vector `(log |N(x)| / d - log w(x))_w`, this multiplies any nonzero `x : K` by a
unit `ε` so that every `log w(ε x)` lies within `c₁(u) = rank K * ∑ j, ‖log u j‖` of its average
value `log |N(x)| / d`. In particular every conjugate of `ε x` has absolute value between
`exp (-c₁(u)) * |N(x)| ^ (1 / d)` and `exp c₁(u) * |N(x)| ^ (1 / d)`.

For a nonzero algebraic integer `α`, the divisors of `α` whose house is at most
`exp c₁(u) * |N(α)| ^ (1 / d)` form a finite set `boundedDivisors u α`. By the balancing
argument, every divisor of `α` is a unit times a member of this set. This reduces equations
whose solutions factor into divisors of a fixed integer, such as Thue equations, to finitely many
unit equations.

## Main results

* `TauCeti.NumberField.Units.exists_norm_sub_logEmbedding_prod_zpow_le`: every vector of the
  logarithmic space lies within `∑ j, ‖log u j‖` of the logarithmic embedding of a product of
  powers of the `u j`.
* `TauCeti.NumberField.Units.exists_unit_mul_balanced`: every nonzero `x` has a multiple by a
  product of powers of the `u j` whose logarithmic absolute values are all within `c₁(u)` of
  `log |N(x)| / d`.
* `TauCeti.NumberField.Units.exists_forall_norm_embedding_prod_zpow_mul_mem_Icc`: the same
  statement for the absolute values of the complex embeddings.
* `TauCeti.NumberField.Units.boundedDivisors`: the divisors of `α` whose house is at most
  `exp c₁(u) * |N(α)| ^ (1 / d)`.
* `TauCeti.NumberField.Units.boundedDivisors_finite`: this set is finite.
* `TauCeti.NumberField.Units.exists_mem_boundedDivisors_of_dvd`: for `u` of maximal rank and
  `α ≠ 0`, every divisor of `α` is a unit times a member of `boundedDivisors u α`.

## References

* [J.-H. Evertse, *Diophantine Approximation*, lecture notes, Leiden/Mastermath, 2019],
  Chapter 5, Lemma 5.10 and Corollary 5.11, pp. 92–94.
-/

public section

open Module NumberField NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem
open scoped NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical in
/-- **Approximation in the logarithmic space.** If `u` has maximal rank, every vector of the
logarithmic space lies within `∑ j, ‖log u j‖` of the logarithmic embedding of a product of
integer powers of the `u j`. -/
theorem exists_norm_sub_logEmbedding_prod_zpow_le {u : Fin (rank K) → (𝓞 K)ˣ}
    (hu : IsMaxRank u) (v : logSpace K) :
    ∃ n : Fin (rank K) → ℤ, ‖v - logEmbedding K (Additive.ofMul (∏ j, u j ^ n j))‖ ≤
      ∑ j, ‖logEmbedding K (Additive.ofMul (u j))‖ := by
  set b := basisOfIsMaxRank hu
  refine ⟨fun j ↦ ⌊b.repr v j⌋, ?_⟩
  have hfloor : logEmbedding K (Additive.ofMul (∏ j, u j ^ ⌊b.repr v j⌋)) =
      (ZSpan.floor b v : logSpace K) := by
    simp [ZSpan.floor, b]
  rw [hfloor, ← ZSpan.fract_apply]
  simpa [b] using ZSpan.norm_fract_le b v

/-- The sum over the infinite places of `mult w * log w(x)` is `log |N(x)|`. -/
private theorem sum_mult_mul_log_eq_log_abs_norm {x : K} (hx : x ≠ 0) :
    ∑ w : InfinitePlace K, mult w * Real.log (w x) = Real.log |(Algebra.norm ℚ x : ℝ)| := by
  rw [← Rat.cast_abs, ← prod_eq_abs_norm, Real.log_prod (fun w _ ↦ pow_ne_zero _
    ((map_ne_zero w).mpr hx))]
  simp [Real.log_pow]

open scoped Classical in
/-- **Balanced representatives modulo units.** If `u` has maximal rank, every nonzero `x : K` can
be multiplied by a product of integer powers of the `u j` so that at every infinite place `w`,
`log w(ε x)` is within `rank K * ∑ j, ‖log u j‖` of `log |N(x)| / [K : ℚ]`. -/
theorem exists_unit_mul_balanced {u : Fin (rank K) → (𝓞 K)ˣ} (hu : IsMaxRank u) {x : K}
    (hx : x ≠ 0) :
    ∃ n : Fin (rank K) → ℤ, ∀ w : InfinitePlace K,
      |Real.log (w (((∏ j, u j ^ n j : (𝓞 K)ˣ) : K) * x)) -
          Real.log |(Algebra.norm ℚ x : ℝ)| / finrank ℚ K| ≤
        rank K * ∑ j, ‖logEmbedding K (Additive.ofMul (u j))‖ := by
  set L := Real.log |(Algebra.norm ℚ x : ℝ)| / finrank ℚ K
  set c := ∑ j, ‖logEmbedding K (Additive.ofMul (u j))‖
  -- Approximate the vector `(mult w * (L - log w(x)))_w` by a logarithmic embedding.
  obtain ⟨n, hn⟩ := exists_norm_sub_logEmbedding_prod_zpow_le hu
    (fun w ↦ mult w.1 * (L - Real.log (w.1 x)))
  refine ⟨n, ?_⟩
  set ε : (𝓞 K)ˣ := ∏ j, u j ^ n j
  -- The deviation of `log w(ε x)` from `L`, weighted by `mult w`.
  set f : InfinitePlace K → ℝ := fun w ↦ mult w * (Real.log (w ((ε : K) * x)) - L) with hf
  have hlog (w : InfinitePlace K) : Real.log (w ((ε : K) * x)) =
      Real.log (w (ε : K)) + Real.log (w x) := by
    rw [map_mul, Real.log_mul (pos_at_place ε w).ne' ((map_ne_zero w).mpr hx)]
  -- Away from `w₀`, the deviation is a coordinate of the approximation error.
  have hcoord (w : {w : InfinitePlace K // w ≠ w₀}) : |f w| ≤ c := by
    have h := (norm_le_pi_norm (fun w ↦ mult w.1 * (L - Real.log (w.1 x)) -
      logEmbedding K (Additive.ofMul ε) w) w).trans hn
    rw [Real.norm_eq_abs, ← abs_neg] at h
    convert h using 2
    simp only [hf, hlog, logEmbedding_component]
    ring
  -- The deviations sum to zero, since `|N(ε x)| = |N(x)|` and `∑ w, mult w = [K : ℚ]`.
  have hsum : ∑ w, f w = 0 := by
    simp only [hf, mul_sub, Finset.sum_sub_distrib, hlog, mul_add, Finset.sum_add_distrib,
      sum_mult_mul_log, sum_mult_mul_log_eq_log_abs_norm hx, ← Finset.sum_mul, ← Nat.cast_sum,
      sum_mult_eq, L, zero_add]
    rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr finrank_pos.ne'), sub_self]
  have hc : 0 ≤ c := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  intro w
  -- It suffices to bound the weighted deviation, since `1 ≤ mult w`.
  refine le_trans ?_ (show |f w| ≤ rank K * c from ?_)
  · rw [hf, abs_mul, Nat.abs_cast]
    exact le_mul_of_one_le_left (abs_nonneg _) one_le_mult
  by_cases hw : w = w₀
  · -- At `w₀`, the deviation is minus the sum of the others.
    have hw₀ : f w = -∑ w' : {w' : InfinitePlace K // w' ≠ w₀}, f w' := by
      rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hsum
      rw [hw]
      linarith
    rw [hw₀, abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun w' _ ↦ hcoord w').trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq, rank]
  · -- Away from `w₀`, the rank is positive since there are two infinite places.
    have hr : 1 ≤ rank K := by
      rw [rank, Nat.one_le_iff_ne_zero, Nat.sub_ne_zero_iff_lt]
      exact Fintype.one_lt_card_iff.mpr ⟨w, w₀, hw⟩
    exact (hcoord ⟨w, hw⟩).trans (le_mul_of_one_le_left hc (by exact_mod_cast hr))

open scoped Classical in
/-- **Balanced representatives modulo units, for embeddings.** If `u` has maximal rank, every
nonzero `x : K` can be multiplied by a product `ε` of integer powers of the `u j` so that every
complex embedding `φ` satisfies
`exp (-c₁) * |N(x)| ^ (1 / d) ≤ ‖φ (ε x)‖ ≤ exp c₁ * |N(x)| ^ (1 / d)`, where
`c₁ = rank K * ∑ j, ‖log u j‖` and `d = [K : ℚ]`. -/
theorem exists_forall_norm_embedding_prod_zpow_mul_mem_Icc {u : Fin (rank K) → (𝓞 K)ˣ}
    (hu : IsMaxRank u) {x : K} (hx : x ≠ 0) :
    ∃ n : Fin (rank K) → ℤ, ∀ φ : K →+* ℂ, ‖φ (((∏ j, u j ^ n j : (𝓞 K)ˣ) : K) * x)‖ ∈
      Set.Icc
        (Real.exp (-(rank K * ∑ j, ‖logEmbedding K (Additive.ofMul (u j))‖)) *
          |(Algebra.norm ℚ x : ℝ)| ^ (1 / (finrank ℚ K : ℝ)))
        (Real.exp (rank K * ∑ j, ‖logEmbedding K (Additive.ofMul (u j))‖) *
          |(Algebra.norm ℚ x : ℝ)| ^ (1 / (finrank ℚ K : ℝ))) := by
  obtain ⟨n, hn⟩ := exists_unit_mul_balanced hu hx
  refine ⟨n, fun φ ↦ ?_⟩
  have hN : 0 < |(Algebra.norm ℚ x : ℝ)| := by
    simpa [Algebra.norm_eq_zero_iff] using hx
  have hpos : 0 < ‖φ (((∏ j, u j ^ n j : (𝓞 K)ˣ) : K) * x)‖ :=
    norm_pos_iff.mpr ((map_ne_zero φ).mpr (mul_ne_zero (coe_ne_zero _) hx))
  have h := abs_le.mp (hn (InfinitePlace.mk φ))
  rw [InfinitePlace.apply] at h
  rw [Real.rpow_def_of_pos hN, mul_one_div, ← Real.exp_add, ← Real.exp_add, ← Real.exp_log hpos]
  constructor <;> rw [Real.exp_le_exp] <;> linarith [h.1, h.2]

open scoped Classical in
/-- The divisors `γ` of `α` with `house γ ≤ exp c₁ * |N(α)| ^ (1 / d)`, where
`c₁ = rank K * ∑ j, ‖log u j‖` and `d = [K : ℚ]`. When `u` has maximal rank and `α ≠ 0`, every
divisor of `α` is a unit times a member of this set (`exists_mem_boundedDivisors_of_dvd`), and the
set is finite (`boundedDivisors_finite`). -/
noncomputable def boundedDivisors (u : Fin (rank K) → (𝓞 K)ˣ) (α : 𝓞 K) : Set (𝓞 K) :=
  {γ | γ ∣ α ∧ house (γ : K) ≤
    Real.exp (rank K * ∑ j, ‖logEmbedding K (Additive.ofMul (u j))‖) *
      |(Algebra.norm ℚ (α : K) : ℝ)| ^ (1 / (finrank ℚ K : ℝ))}

open scoped Classical in
@[simp]
theorem mem_boundedDivisors {u : Fin (rank K) → (𝓞 K)ˣ} {α γ : 𝓞 K} :
    γ ∈ boundedDivisors u α ↔ γ ∣ α ∧ house (γ : K) ≤
      Real.exp (rank K * ∑ j, ‖logEmbedding K (Additive.ofMul (u j))‖) *
        |(Algebra.norm ℚ (α : K) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) :=
  Iff.rfl

/-- Every member of `boundedDivisors u α` divides `α`. -/
theorem boundedDivisors_subset_dvd (u : Fin (rank K) → (𝓞 K)ˣ) (α : 𝓞 K) :
    boundedDivisors u α ⊆ {γ | γ ∣ α} :=
  fun _ hγ ↦ hγ.1

open scoped Classical in
/-- The set `boundedDivisors u α` is finite: its members are algebraic integers of bounded
house. -/
theorem boundedDivisors_finite (u : Fin (rank K) → (𝓞 K)ˣ) (α : 𝓞 K) :
    (boundedDivisors u α).Finite := by
  refine ((Embeddings.finite_of_norm_le K ℂ (Real.exp
    (rank K * ∑ j, ‖logEmbedding K (Additive.ofMul (u j))‖) *
      |(Algebra.norm ℚ (α : K) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)))).preimage
    RingOfIntegers.coe_injective.injOn).subset fun γ hγ ↦ ?_
  exact ⟨γ.isIntegral_coe, fun φ ↦ (norm_embedding_le_house _ φ).trans hγ.2⟩

open scoped Classical in
/-- Multiplying `α` by a unit does not change `boundedDivisors u α`. -/
@[simp]
theorem boundedDivisors_mul_unit (u : Fin (rank K) → (𝓞 K)ˣ) (η : (𝓞 K)ˣ) (α : 𝓞 K) :
    boundedDivisors u (η * α) = boundedDivisors u α := by
  have hη : |(Algebra.norm ℚ (η : K) : ℝ)| = 1 := by
    rw [← Rat.cast_abs, Units.norm, Rat.cast_one]
  ext γ
  simp [mem_boundedDivisors, abs_mul, hη]

/-- The absolute value of the norm of a nonzero algebraic integer is at least one. -/
private theorem one_le_abs_norm {α : 𝓞 K} (hα : α ≠ 0) :
    (1 : ℝ) ≤ |(Algebra.norm ℚ (α : K) : ℝ)| := by
  rw [← Algebra.coe_norm_int, Rat.cast_intCast, ← Int.cast_abs, ← Int.cast_one, Int.cast_le]
  exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr hα)

open scoped Classical in
/-- For `α ≠ 0`, the divisor `1` belongs to `boundedDivisors u α`, since `|N(α)| ≥ 1`. -/
theorem one_mem_boundedDivisors (u : Fin (rank K) → (𝓞 K)ˣ) {α : 𝓞 K} (hα : α ≠ 0) :
    1 ∈ boundedDivisors u α := by
  refine ⟨one_dvd α, ?_⟩
  rw [RingOfIntegers.coe_eq_algebraMap, map_one, ← Int.cast_one, house_intCast, abs_one,
    Int.cast_one]
  refine one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity)) ?_
  exact Real.one_le_rpow (one_le_abs_norm hα) (by positivity)

open scoped Classical in
/-- **Divisors modulo units.** If `u` has maximal rank and `α ≠ 0`, every divisor `β` of `α` is a
unit times a member of `boundedDivisors u α`. -/
theorem exists_mem_boundedDivisors_of_dvd {u : Fin (rank K) → (𝓞 K)ˣ} (hu : IsMaxRank u)
    {α β : 𝓞 K} (hα : α ≠ 0) (hβ : β ∣ α) :
    ∃ γ ∈ boundedDivisors u α, ∃ ε : (𝓞 K)ˣ, β = ε * γ := by
  have hβ0 : β ≠ 0 := by
    rintro rfl
    exact hα (zero_dvd_iff.mp hβ)
  obtain ⟨n, hn⟩ := exists_forall_norm_embedding_prod_zpow_mul_mem_Icc hu
    (RingOfIntegers.coe_ne_zero_iff.mpr hβ0)
  set ε : (𝓞 K)ˣ := ∏ j, u j ^ n j
  refine ⟨ε * β, ⟨(Units.mul_left_dvd).mpr hβ, ?_⟩, ε⁻¹, by simp⟩
  -- A divisor of `α` has norm at most `|N(α)|` in absolute value.
  have hnorm : |(Algebra.norm ℚ (β : K) : ℝ)| ≤ |(Algebra.norm ℚ (α : K) : ℝ)| := by
    obtain ⟨δ, rfl⟩ := hβ
    have hδ : δ ≠ 0 := right_ne_zero_of_mul hα
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, Rat.cast_mul, abs_mul]
    exact le_mul_of_one_le_right (abs_nonneg _) (one_le_abs_norm hδ)
  rw [house, pi_norm_le_iff_of_nonneg (by positivity)]
  intro φ
  rw [canonicalEmbedding.apply_at, RingOfIntegers.coe_eq_algebraMap, map_mul]
  exact (hn φ).2.trans (by gcongr)

end TauCeti.NumberField.Units
