/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Analysis.InnerProductSpace.Gram.Selberg

/-!
# Bombieri's additive large sieve inequality

This file proves Bombieri's additive large sieve inequality for trigonometric polynomials evaluated
at points well-spaced in the circle `UnitAddCircle = ℝ / ℤ`, following Bombieri's 1971 Hilbert-space
proof via Selberg's weighted Gram inequality (`TauCeti.sum_norm_inner_sq_le_of_diag_offDiag`) and
tapered Fourier vectors.

## Main definitions

* `TauCeti.taperWeight`: the trapezoidal weight `w(n) = (max 0 (N + L - |n|) - max 0 (N - |n|)) / L`
  on `ℤ`, equal to `1` on the flat core `|n| ≤ N`, decaying linearly over `N ≤ |n| ≤ N + L`, and
  vanishing outside `|n| < N + L`.
* `TauCeti.taperedFourierVec`: the vector in `EuclideanSpace ℂ (Fin (2 * (N + L) + 1))` with
  frequency `n = k - (N + L)` carrying entry `√(taperWeight N L n) * Real.fourierChar (-n * x)`.

## Main results

* `TauCeti.sum_Icc_max_sub_abs_mul_fourierChar`: the triangular Fourier sum identity
  `∑ n ∈ Icc (-K) K, max 0 (M - |n|) * e(n * t) = ‖∑ k ∈ range M, e(k * t)‖ ^ 2` for `M ≤ K`.
* `TauCeti.norm_sum_range_fourierChar_mul_abs_sin` and
  `TauCeti.norm_sum_range_fourierChar_sq_eq_sin_div_sq`: closed forms for the norm of a geometric
  exponential sum in terms of `Real.sin`.
* `TauCeti.two_mul_norm_unitAddCircle_le_abs_sin` and
  `TauCeti.four_mul_norm_unitAddCircle_sq_le_sin_sq`: the circular sine lower bound
  `2 * ‖(t : UnitAddCircle)‖ ≤ |sin (π * t)|`.
* `TauCeti.card_filter_floor_div_norm_unitAddCircle_le_two`: circular radial bin-packing bound
  showing that at most two points of a `δ`-separated family lie in each shell
  `m δ ≤ ‖x_i - x_j‖ < (m + 1) δ`.
* `TauCeti.sum_erase_inv_sin_sq_le`: the cosecant row bound
  `∑ j ∈ s.erase i, (sin (π * (x i - x j)) ^ 2)⁻¹ ≤ π ^ 2 / (12 * δ ^ 2)`.
* `TauCeti.inner_taperedFourierVec`, `TauCeti.norm_taperedFourierVec_sq`, and
  `TauCeti.norm_inner_taperedFourierVec_le`: Gram entries of `taperedFourierVec`.
* `TauCeti.sum_norm_sum_fourierChar_sq_le_of_sum_inv_sin_sq_le`: the cosecant-row large sieve for
  core-supported vectors.
* `TauCeti.sum_norm_sum_Ico_fourierChar_sq_le` and `TauCeti.sum_norm_sum_fourierChar_sq_le`:
  **Bombieri's additive large sieve inequality** with constant `H + 2 / δ` for arbitrary `H : ℕ`,
  `M : ℤ`, `0 < δ`, and `δ`-separated points in `UnitAddCircle`.

## References

* E. Bombieri, *A note on the large sieve*, Acta Arithmetica **18** (1971), 401–404,
  Proposition 1 and Theorem 2.
-/

public section

open scoped InnerProductSpace ComplexConjugate

namespace TauCeti

/-! ### Finite Fourier sums and triangular weights -/

/-- For `M ≤ K`, the triangular Fourier polynomial over `[-K, K]` equals the squared norm of the
first `M` additive characters `k ↦ Real.fourierChar (k * t)`. -/
theorem sum_Icc_max_sub_abs_mul_fourierChar {M K : ℕ} (hMK : M ≤ K) (t : ℝ) :
    ∑ n ∈ Finset.Icc (-(K : ℤ)) K,
        ((max (0 : ℝ) ((M : ℝ) - |(n : ℝ)|) : ℝ) : ℂ) *
          (Real.fourierChar ((n : ℝ) * t) : ℂ) =
      (‖∑ k ∈ Finset.range M, (Real.fourierChar ((k : ℝ) * t) : ℂ)‖ ^ 2 : ℝ) := by
  have hexp :
      ((‖∑ k ∈ Finset.range M, (Real.fourierChar ((k : ℝ) * t) : ℂ)‖ ^ 2 : ℝ) : ℂ) =
        ∑ i ∈ Finset.range M, ∑ j ∈ Finset.range M,
          (Real.fourierChar ((((i : ℤ) - j : ℤ) : ℝ) * t) : ℂ) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, ← Circle.coe_mul,
      ← AddChar.map_add_eq_mul]
    congr 2; push_cast; ring
  have hsplit :
      ∀ i ∈ Finset.range M, ∀ j ∈ Finset.range M,
        (Real.fourierChar ((((i : ℤ) - j : ℤ) : ℝ) * t) : ℂ) =
          ∑ n ∈ Finset.Icc (-(K : ℤ)) K,
            if (i : ℤ) - j = n then (Real.fourierChar ((n : ℝ) * t) : ℂ) else 0 := by
    intro i hi j hj
    have hiM : i < M := Finset.mem_range.mp hi
    have hjM : j < M := Finset.mem_range.mp hj
    have hmem : (i : ℤ) - j ∈ Finset.Icc (-(K : ℤ)) K :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [Finset.sum_ite_eq, ite_eq_left hmem]
  rw [hexp, Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ hsplit i hi j hj,
    Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [Finset.sum_range_sum_range_ite_int_sub_eq_nsmul, nsmul_eq_mul]
  congr 1
  have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hcast : ((M - n.natAbs : ℕ) : ℝ) = max (0 : ℝ) ((M : ℝ) - |(n : ℝ)|) := by
    rw [← habs]
    by_cases hn : n.natAbs ≤ M
    · rw [Nat.cast_sub hn, max_eq_right (sub_nonneg.mpr (Nat.cast_le.mpr hn))]
    · rw [Nat.sub_eq_zero_of_le (le_of_not_ge hn), Nat.cast_zero,
        max_eq_left (sub_nonpos.mpr (Nat.cast_le.mpr (le_of_not_ge hn)))]
  exact_mod_cast hcast.symm

/-- Closed-form product identity for the norm of a geometric exponential sum:
`‖∑ k ∈ range M, Real.fourierChar (k * t)‖ * |sin (π * t)| = |sin (π * M * t)|`. -/
theorem norm_sum_range_fourierChar_mul_abs_sin (M : ℕ) (t : ℝ) :
    ‖∑ k ∈ Finset.range M, (Real.fourierChar ((k : ℝ) * t) : ℂ)‖ * |Real.sin (Real.pi * t)| =
      |Real.sin (Real.pi * (M : ℝ) * t)| := by
  let z : ℂ := (Real.fourierChar t : ℂ)
  have hpow : ∀ k : ℕ, (Real.fourierChar ((k : ℝ) * t) : ℂ) = z ^ k := by
    intro k
    rw [← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  simp_rw [hpow]
  have hgeom := congrArg norm (geom_sum_mul z M)
  rw [norm_mul] at hgeom
  have hz1 : ‖z - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
    have h1 : z = Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
      simp only [z, Real.fourierChar_apply, mul_comm]
    rw [h1, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
    congr 3; ring
  have hzM : ‖z ^ M - 1‖ = 2 * |Real.sin (Real.pi * (M : ℝ) * t)| := by
    have hM : z ^ M = Complex.exp (Complex.I * ((2 * Real.pi * (M : ℝ) * t : ℝ) : ℂ)) := by
      rw [← hpow M, Real.fourierChar_apply, mul_comm]
      congr 2; push_cast; ring
    rw [hM, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
    congr 3; ring
  rw [hz1, hzM] at hgeom
  linarith

/-- Whenever `sin (π * t) ≠ 0`, the squared norm of the geometric exponential sum of length `M`
equals `(sin (π * M * t) / sin (π * t)) ^ 2`. -/
theorem norm_sum_range_fourierChar_sq_eq_sin_div_sq (M : ℕ) {t : ℝ}
    (ht : Real.sin (Real.pi * t) ≠ 0) :
    ‖∑ k ∈ Finset.range M, (Real.fourierChar ((k : ℝ) * t) : ℂ)‖ ^ 2 =
      (Real.sin (Real.pi * (M : ℝ) * t) / Real.sin (Real.pi * t)) ^ 2 := by
  have h := congrArg (fun r : ℝ ↦ r ^ 2) (norm_sum_range_fourierChar_mul_abs_sin M t)
  rw [mul_pow, sq_abs, sq_abs] at h
  rw [div_pow, eq_div_iff (pow_ne_zero 2 ht)]
  exact h

/-! ### Circular separation and cosecant row bounds -/

/-- Jordan's sine lower bound on `UnitAddCircle = ℝ / ℤ`:
`2 * ‖(t : UnitAddCircle)‖ ≤ |sin (π * t)|`. -/
theorem two_mul_norm_unitAddCircle_le_abs_sin (t : ℝ) :
    2 * ‖(t : UnitAddCircle)‖ ≤ |Real.sin (Real.pi * t)| := by
  set u : ℝ := t - round t
  have hu : ‖(t : UnitAddCircle)‖ = |u| := UnitAddCircle.norm_eq
  have hle : |u| ≤ 1 / 2 := abs_sub_round t
  have hsin_le : 2 * |u| ≤ Real.sin (Real.pi / 2 * (2 * |u|)) :=
    Real.le_sin_mul (by positivity) (by linarith)
  have harg : Real.pi / 2 * (2 * |u|) = Real.pi * |u| := by ring
  have habs_u : |Real.sin (Real.pi * |u|)| = |Real.sin (Real.pi * u)| := by
    rcases abs_cases u with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, Real.sin_neg, abs_neg]
  have habs_t : |Real.sin (Real.pi * u)| = |Real.sin (Real.pi * t)| := by
    have hsub : Real.pi * u = Real.pi * t - (round t : ℤ) * Real.pi := by
      simp only [u]; ring
    rw [hsub, Real.sin_sub_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  calc
    2 * ‖(t : UnitAddCircle)‖ = 2 * |u| := by rw [hu]
    _ ≤ Real.sin (Real.pi * |u|) := harg ▸ hsin_le
    _ ≤ |Real.sin (Real.pi * |u|)| := le_abs_self _
    _ = |Real.sin (Real.pi * t)| := habs_u.trans habs_t

/-- Squared form of Jordan's sine lower bound on `UnitAddCircle`:
`4 * ‖(t : UnitAddCircle)‖ ^ 2 ≤ sin (π * t) ^ 2`. -/
theorem four_mul_norm_unitAddCircle_sq_le_sin_sq (t : ℝ) :
    4 * ‖(t : UnitAddCircle)‖ ^ 2 ≤ Real.sin (Real.pi * t) ^ 2 := by
  nlinarith [two_mul_norm_unitAddCircle_le_abs_sin t, sq_abs (Real.sin (Real.pi * t)),
    norm_nonneg (t : UnitAddCircle)]

/-- Circular radial bin-packing bound: around any center `c : ℝ`, each radial bin
`⌊‖c - x j‖ / δ⌋₊ = m` of a `δ`-separated finite family in `UnitAddCircle` contains at most two
indices `j ∈ s` (at most one on each side of `c`). -/
theorem card_filter_floor_div_norm_unitAddCircle_le_two {ι : Type*}
    {s : Finset ι} {x : ι → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ ‖((x i - x j : ℝ) : UnitAddCircle)‖)
    (c : ℝ) (m : ℕ) :
    (s.filter fun j ↦ ⌊‖((c - x j : ℝ) : UnitAddCircle)‖ / δ⌋₊ = m).card ≤ 2 := by
  classical
  let B : Finset ι :=
    s.filter fun j ↦ ⌊‖((c - x j : ℝ) : UnitAddCircle)‖ / δ⌋₊ = m
  let u : ι → ℝ := fun j ↦ (c - x j) - round (c - x j)
  have hdiff_le : ∀ j₁ j₂, ‖((x j₁ - x j₂ : ℝ) : UnitAddCircle)‖ ≤ |u j₂ - u j₁| := by
    intro j₁ j₂
    have hcoe : ((x j₁ - x j₂ : ℝ) : UnitAddCircle) = ((u j₂ - u j₁ : ℝ) : UnitAddCircle) := by
      let k : ℤ := round (c - x j₁) - round (c - x j₂)
      have hsub : u j₂ - u j₁ = (x j₁ - x j₂) + k • (1 : ℝ) := by
        simp only [u, k, zsmul_eq_mul, mul_one, Int.cast_sub]; ring
      rw [hsub, AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, add_zero]
    rw [hcoe, UnitAddCircle.norm_eq]
    simpa using round_le (u j₂ - u j₁) 0
  have hbin : ∀ j ∈ B, (m : ℝ) * δ ≤ |u j| ∧ |u j| < ((m : ℝ) + 1) * δ := by
    intro j hj
    have hm : ⌊‖((c - x j : ℝ) : UnitAddCircle)‖ / δ⌋₊ = m := (Finset.mem_filter.mp hj).2
    rw [← UnitAddCircle.norm_eq (x := c - x j)]
    exact ⟨(le_div_iff₀ hδ).mp (hm ▸ Nat.floor_le (by positivity)),
      (div_lt_iff₀ hδ).mp (hm ▸ Nat.lt_floor_add_one _)⟩
  have hside : ∀ (P : ℝ → Prop) [DecidablePred P],
      (∀ r₁ r₂, P r₁ → P r₂ → |r₂ - r₁| = |(|r₂| - |r₁|)|) →
      (B.filter fun j ↦ P (u j)).card ≤ 1 := by
    intro P _ hP
    refine Finset.card_le_one.mpr fun j₁ hj₁ j₂ hj₂ ↦ ?_
    by_contra hne
    rcases Finset.mem_filter.mp hj₁ with ⟨hj₁B, hP₁⟩
    rcases Finset.mem_filter.mp hj₂ with ⟨hj₂B, hP₂⟩
    have hb₁ := hbin j₁ hj₁B
    have hb₂ := hbin j₂ hj₂B
    have hlt : |u j₂ - u j₁| < δ := by
      rw [hP (u j₁) (u j₂) hP₁ hP₂, abs_lt]
      exact ⟨by linarith, by linarith⟩
    linarith [hsep j₁ (Finset.mem_filter.mp hj₁B).1 j₂ (Finset.mem_filter.mp hj₂B).1 hne,
      hdiff_le j₁ j₂]
  have hpos_card := hside (0 ≤ ·) fun r₁ r₂ h₁ h₂ ↦ by rw [abs_of_nonneg h₁, abs_of_nonneg h₂]
  have hneg_card := hside (¬ 0 ≤ ·) fun r₁ r₂ h₁ h₂ ↦ by
    rw [abs_of_neg (lt_of_not_ge h₁), abs_of_neg (lt_of_not_ge h₂), ← abs_neg (r₂ - r₁)]
    congr 1; ring
  have hpart := Finset.card_filter_add_card_filter_not (s := B) (fun j ↦ 0 ≤ u j)
  dsimp only [B] at hpart hpos_card hneg_card
  omega

/-- Bombieri's cosecant row bound: for any `δ`-separated finite family in `UnitAddCircle` (`0 < δ`)
and any `i ∈ s`, `∑ j ∈ s.erase i, (sin (π * (x i - x j)) ^ 2)⁻¹ ≤ π ^ 2 / (12 * δ ^ 2)`. -/
theorem sum_erase_inv_sin_sq_le {ι : Type*} [DecidableEq ι] {s : Finset ι} {x : ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ ‖((x i - x j : ℝ) : UnitAddCircle)‖)
    {i : ι} (hi : i ∈ s) :
    ∑ j ∈ s.erase i, (Real.sin (Real.pi * (x i - x j)) ^ 2)⁻¹ ≤
      Real.pi ^ 2 / (12 * δ ^ 2) := by
  let b : ι → ℕ := fun j ↦ ⌊‖((x i - x j : ℝ) : UnitAddCircle)‖ / δ⌋₊
  have hterm : ∀ j ∈ s.erase i,
      (Real.sin (Real.pi * (x i - x j)) ^ 2)⁻¹ ≤
        (4 * δ ^ 2)⁻¹ * ((1 : ℝ) / (b j : ℝ) ^ 2) := by
    intro j hj
    have hsep_ij := hsep i hi j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm
    have hb_pos : 0 < b j := Nat.floor_pos.mpr ((one_le_div hδ).mpr hsep_ij)
    have hb_le : (b j : ℝ) * δ ≤ ‖((x i - x j : ℝ) : UnitAddCircle)‖ :=
      (le_div_iff₀ hδ).mp (Nat.floor_le (by positivity))
    have hsin_lb : 4 * ((b j : ℝ) * δ) ^ 2 ≤ Real.sin (Real.pi * (x i - x j)) ^ 2 := by
      have hsq := pow_le_pow_left₀ (by positivity) hb_le 2
      linarith [four_mul_norm_unitAddCircle_sq_le_sin_sq (x i - x j)]
    calc
      (Real.sin (Real.pi * (x i - x j)) ^ 2)⁻¹
          ≤ (4 * ((b j : ℝ) * δ) ^ 2)⁻¹ := inv_anti₀ (by positivity) hsin_lb
      _ = (4 * δ ^ 2)⁻¹ * ((1 : ℝ) / (b j : ℝ) ^ 2) := by ring
  have hfib :
      ∑ j ∈ s.erase i, ((1 : ℝ) / (b j : ℝ) ^ 2) ≤
        2 * ∑ m ∈ (s.erase i).image b, ((1 : ℝ) / (m : ℝ) ^ 2) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := b) (t := (s.erase i).image b)
      (fun j hj ↦ Finset.mem_image_of_mem b hj), Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ ↦ ?_
    have hcongr :
        (∑ j ∈ (s.erase i).filter (fun j ↦ b j = m), ((1 : ℝ) / (b j : ℝ) ^ 2)) =
          (((s.erase i).filter (fun j ↦ b j = m)).card : ℝ) * ((1 : ℝ) / (m : ℝ) ^ 2) := by
      rw [Finset.sum_congr rfl fun j hj ↦ by rw [(Finset.mem_filter.mp hj).2],
        Finset.sum_const, nsmul_eq_mul]
    rw [hcongr]
    have hsep' : ∀ a ∈ s.erase i, ∀ b ∈ s.erase i, a ≠ b →
        δ ≤ ‖((x a - x b : ℝ) : UnitAddCircle)‖ :=
      fun a ha b hb ↦ hsep a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast card_filter_floor_div_norm_unitAddCircle_le_two hδ hsep' (x i) m)
      (by positivity)
  have hzeta :
      ∑ m ∈ (s.erase i).image b, ((1 : ℝ) / (m : ℝ) ^ 2) ≤ Real.pi ^ 2 / 6 :=
    sum_le_hasSum ((s.erase i).image b) (fun n _ ↦ by positivity) hasSum_zeta_two
  calc
    ∑ j ∈ s.erase i, (Real.sin (Real.pi * (x i - x j)) ^ 2)⁻¹
        ≤ ∑ j ∈ s.erase i, (4 * δ ^ 2)⁻¹ * ((1 : ℝ) / (b j : ℝ) ^ 2) := Finset.sum_le_sum hterm
    _ = (4 * δ ^ 2)⁻¹ * ∑ j ∈ s.erase i, ((1 : ℝ) / (b j : ℝ) ^ 2) := (Finset.mul_sum _ _ _).symm
    _ ≤ (4 * δ ^ 2)⁻¹ * (2 * ∑ m ∈ (s.erase i).image b, ((1 : ℝ) / (m : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hfib (by positivity)
    _ ≤ (4 * δ ^ 2)⁻¹ * (2 * (Real.pi ^ 2 / 6)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hzeta (by positivity)) (by positivity)
    _ = Real.pi ^ 2 / (12 * δ ^ 2) := by ring

/-- Because every point of `UnitAddCircle` has norm at most `1 / 2`, a `δ`-separated finite family
with `1 / 2 < δ` has cardinality at most `1`. -/
theorem card_le_one_of_half_lt_norm_unitAddCircle {ι : Type*} {s : Finset ι} {x : ι → ℝ} {δ : ℝ}
    (hδ : 1 / 2 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ ‖((x i - x j : ℝ) : UnitAddCircle)‖) :
    s.card ≤ 1 := by
  refine Finset.card_le_one.mpr fun i hi j hj ↦ ?_
  by_contra hne
  have hle : ‖((x i - x j : ℝ) : UnitAddCircle)‖ ≤ 1 / 2 := by
    simpa using AddCircle.norm_le_half_period (p := (1 : ℝ)) one_ne_zero
      (x := ((x i - x j : ℝ) : UnitAddCircle))
  linarith [hsep i hi j hj hne]

/-! ### Bombieri's tapered Fourier vectors -/

/-- Bombieri's trapezoidal Fourier taper weight on `ℤ`: equal to `1` on `|n| ≤ N`, decaying
linearly across `N ≤ |n| ≤ N + L`, and vanishing for `|n| ≥ N + L` (and identically `0` when
`L = 0`). -/
noncomputable def taperWeight (N L : ℕ) (n : ℤ) : ℝ :=
  (max (0 : ℝ) (((N + L : ℕ) : ℝ) - |(n : ℝ)|) - max (0 : ℝ) ((N : ℝ) - |(n : ℝ)|)) / (L : ℝ)

/-- Definitional formula for `taperWeight`. -/
theorem taperWeight_def (N L : ℕ) (n : ℤ) :
    taperWeight N L n =
      (max (0 : ℝ) (((N + L : ℕ) : ℝ) - |(n : ℝ)|) - max (0 : ℝ) ((N : ℝ) - |(n : ℝ)|)) /
        (L : ℝ) :=
  (rfl)

/-- For taper width `L = 0`, `taperWeight` vanishes identically. -/
@[simp]
theorem taperWeight_zero (N : ℕ) (n : ℤ) : taperWeight N 0 n = 0 := by
  simp [taperWeight_def]

/-- `taperWeight` is an even function of the frequency `n : ℤ`. -/
@[simp]
theorem taperWeight_neg (N L : ℕ) (n : ℤ) : taperWeight N L (-n) = taperWeight N L n := by
  simp [taperWeight_def]

/-- `taperWeight` is nonnegative. -/
theorem taperWeight_nonneg (N L : ℕ) (n : ℤ) : 0 ≤ taperWeight N L n := by
  rw [taperWeight_def]
  refine div_nonneg (sub_nonneg.mpr ?_) (Nat.cast_nonneg L)
  exact max_le_max_left 0 (sub_le_sub_right (Nat.cast_le.mpr (Nat.le_add_right N L)) _)

/-- `taperWeight` is at most `1`. -/
theorem taperWeight_le_one (N L : ℕ) (n : ℤ) : taperWeight N L n ≤ 1 := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  rw [taperWeight_def, div_le_one (Nat.cast_pos.mpr hL), sub_le_iff_le_add]
  refine max_le ?_ ?_
  · linarith [le_max_left (0 : ℝ) ((N : ℝ) - |(n : ℝ)|), Nat.cast_nonneg (α := ℝ) L]
  · push_cast
    linarith [le_max_right (0 : ℝ) ((N : ℝ) - |(n : ℝ)|)]

/-- On the flat core `|n| ≤ N` with positive taper width `0 < L`, `taperWeight N L n = 1`. -/
theorem taperWeight_eq_one {N L : ℕ} {n : ℤ} (hL : 0 < L) (hn : |n| ≤ (N : ℤ)) :
    taperWeight N L n = 1 := by
  have hn' : |(n : ℝ)| ≤ (N : ℝ) := by exact_mod_cast hn
  have h1 : max (0 : ℝ) (((N + L : ℕ) : ℝ) - |(n : ℝ)|) = (N : ℝ) + (L : ℝ) - |(n : ℝ)| := by
    push_cast
    exact max_eq_right (by linarith [Nat.cast_nonneg (α := ℝ) L])
  have h2 : max (0 : ℝ) ((N : ℝ) - |(n : ℝ)|) = (N : ℝ) - |(n : ℝ)| :=
    max_eq_right (by linarith)
  rw [taperWeight_def, h1, h2]
  have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  field_simp [hLne]
  ring

/-- In the transition region `N ≤ |n| ≤ N + L`, `taperWeight N L n = (N + L - |n|) / L`. -/
theorem taperWeight_eq_div {N L : ℕ} {n : ℤ} (h1 : (N : ℤ) ≤ |n|)
    (h2 : |n| ≤ ((N + L : ℕ) : ℤ)) :
    taperWeight N L n = (((N + L : ℕ) : ℝ) - |(n : ℝ)|) / (L : ℝ) := by
  have h1' : (N : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast h1
  have h2' : |(n : ℝ)| ≤ ((N + L : ℕ) : ℝ) := by exact_mod_cast h2
  rw [taperWeight_def, max_eq_right (sub_nonneg.mpr h2'), max_eq_left (sub_nonpos.mpr h1'),
    sub_zero]

/-- Outside the open interval `|n| < N + L`, `taperWeight N L n = 0`. -/
theorem taperWeight_eq_zero {N L : ℕ} {n : ℤ} (hn : ((N + L : ℕ) : ℤ) ≤ |n|) :
    taperWeight N L n = 0 := by
  have hn' : ((N + L : ℕ) : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast hn
  have hN' : (N : ℝ) ≤ |(n : ℝ)| :=
    le_trans (Nat.cast_le.mpr (Nat.le_add_right N L)) hn'
  rw [taperWeight_def, max_eq_left (sub_nonpos.mpr hn'), max_eq_left (sub_nonpos.mpr hN'),
    sub_self, zero_div]

/-- Bombieri's tapered Fourier vector in `EuclideanSpace ℂ (Fin (2 * (N + L) + 1))`, with coordinate
`k` indexing the centered integer frequency `n = k - (N + L)` and carrying weight
`√(taperWeight N L n)` times the conjugated character `Real.fourierChar (-n * x)`. -/
noncomputable def taperedFourierVec (N L : ℕ) (x : ℝ) :
    EuclideanSpace ℂ (Fin (2 * (N + L) + 1)) :=
  WithLp.toLp 2 fun k : Fin (2 * (N + L) + 1) ↦
    (Real.sqrt (taperWeight N L ((k : ℤ) - ((N + L : ℕ) : ℤ))) : ℂ) *
      (Real.fourierChar (-((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * x)) : ℂ)

/-- Coordinate formula for `taperedFourierVec`. -/
@[simp]
theorem taperedFourierVec_apply (N L : ℕ) (x : ℝ) (k : Fin (2 * (N + L) + 1)) :
    taperedFourierVec N L x k =
      (Real.sqrt (taperWeight N L ((k : ℤ) - ((N + L : ℕ) : ℤ))) : ℂ) *
        (Real.fourierChar (-((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * x)) : ℂ) :=
  (rfl)

/-- For taper width `L = 0`, `taperedFourierVec` is the zero vector. -/
@[simp]
theorem taperedFourierVec_zero (N : ℕ) (x : ℝ) : taperedFourierVec N 0 x = 0 := by
  ext k
  simp [taperedFourierVec_apply]

/-- On the flat core `|k - (N + L)| ≤ N` with `0 < L`, `taperedFourierVec N L x k` has unit
weight. -/
theorem taperedFourierVec_apply_of_abs_le {N L : ℕ} (hL : 0 < L) (x : ℝ)
    {k : Fin (2 * (N + L) + 1)} (hk : |(k : ℤ) - ((N + L : ℕ) : ℤ)| ≤ (N : ℤ)) :
    taperedFourierVec N L x k =
      (Real.fourierChar (-((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * x)) : ℂ) := by
  rw [taperedFourierVec_apply, taperWeight_eq_one hL hk, Real.sqrt_one, Complex.ofReal_one, one_mul]

/-- Exact Gram inner product of two tapered Fourier vectors as a difference of two Fejér sums. -/
theorem inner_taperedFourierVec (N L : ℕ) (x y : ℝ) :
    ⟪taperedFourierVec N L x, taperedFourierVec N L y⟫_ℂ =
      (((‖∑ k ∈ Finset.range (N + L), (Real.fourierChar ((k : ℝ) * (x - y)) : ℂ)‖ ^ 2 -
          ‖∑ k ∈ Finset.range N, (Real.fourierChar ((k : ℝ) * (x - y)) : ℂ)‖ ^ 2) /
          (L : ℝ) : ℝ) : ℂ) := by
  have hsum :
      ⟪taperedFourierVec N L x, taperedFourierVec N L y⟫_ℂ =
        ∑ k : Fin (2 * (N + L) + 1),
          (taperWeight N L ((k : ℤ) - ((N + L : ℕ) : ℤ)) : ℂ) *
            (Real.fourierChar (((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * (x - y))) : ℂ) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    set n : ℤ := (k : ℤ) - ((N + L : ℕ) : ℤ)
    rw [RCLike.inner_apply, taperedFourierVec_apply, taperedFourierVec_apply, map_mul,
      Complex.conj_ofReal, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg,
      mul_mul_mul_comm, ← Complex.ofReal_mul, Real.mul_self_sqrt (taperWeight_nonneg N L n),
      ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 3; ring
  have hreindex :
      (∑ k : Fin (2 * (N + L) + 1),
          (taperWeight N L ((k : ℤ) - ((N + L : ℕ) : ℤ)) : ℂ) *
            (Real.fourierChar (((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * (x - y))) : ℂ)) =
        ∑ n ∈ Finset.Icc (-((N + L : ℕ) : ℤ)) (N + L : ℕ),
          (taperWeight N L n : ℂ) * (Real.fourierChar ((n : ℝ) * (x - y)) : ℂ) := by
    refine Finset.sum_bij (fun (k : Fin (2 * (N + L) + 1)) _ ↦ (k : ℤ) - ((N + L : ℕ) : ℤ))
      (fun k _ ↦ Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      (fun k₁ _ k₂ _ h ↦ Fin.ext (by omega)) (fun n hn ↦ ?_) (fun _ _ ↦ rfl)
    rcases Finset.mem_Icc.mp hn with ⟨hlo, hhi⟩
    exact ⟨⟨(n + ((N + L : ℕ) : ℤ)).toNat, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
  rw [hsum, hreindex]
  simp_rw [taperWeight_def, Complex.ofReal_div, Complex.ofReal_sub, div_mul_eq_mul_div,
    sub_mul, ← Finset.sum_div, Finset.sum_sub_distrib]
  rw [sum_Icc_max_sub_abs_mul_fourierChar le_rfl (x - y),
    sum_Icc_max_sub_abs_mul_fourierChar (Nat.le_add_right N L) (x - y)]

/-- For positive taper width `0 < L`, `‖taperedFourierVec N L x‖ ^ 2 = 2 * N + L`. -/
theorem norm_taperedFourierVec_sq {N L : ℕ} (hL : 0 < L) (x : ℝ) :
    ‖taperedFourierVec N L x‖ ^ 2 = 2 * (N : ℝ) + (L : ℝ) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_taperedFourierVec]
  simp only [RCLike.re_to_complex, Complex.ofReal_re, sub_self, mul_zero,
    AddChar.map_zero_eq_one, Circle.coe_one, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one, Complex.norm_natCast]
  have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  push_cast
  field_simp [hLne]
  ring

/-- Off-diagonal Gram bound for tapered Fourier vectors: whenever `sin (π * (x - y)) ≠ 0`,
`‖⟪taperedFourierVec N L x, taperedFourierVec N L y⟫_ℂ‖ ≤ (L * sin (π * (x - y)) ^ 2)⁻¹`. -/
theorem norm_inner_taperedFourierVec_le (N L : ℕ) {x y : ℝ}
    (hxy : Real.sin (Real.pi * (x - y)) ≠ 0) :
    ‖⟪taperedFourierVec N L x, taperedFourierVec N L y⟫_ℂ‖ ≤
      ((L : ℝ) * Real.sin (Real.pi * (x - y)) ^ 2)⁻¹ := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  rw [inner_taperedFourierVec, Complex.norm_real, Real.norm_eq_abs,
    norm_sum_range_fourierChar_sq_eq_sin_div_sq (N + L) hxy,
    norm_sum_range_fourierChar_sq_eq_sin_div_sq N hxy]
  have hsin_pos : 0 < Real.sin (Real.pi * (x - y)) ^ 2 := sq_pos_of_ne_zero hxy
  have hL_pos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL
  have hrew :
      ((Real.sin (Real.pi * ((N + L : ℕ) : ℝ) * (x - y)) / Real.sin (Real.pi * (x - y))) ^ 2 -
        (Real.sin (Real.pi * (N : ℝ) * (x - y)) / Real.sin (Real.pi * (x - y))) ^ 2) / (L : ℝ) =
        (Real.sin (Real.pi * ((N + L : ℕ) : ℝ) * (x - y)) ^ 2 -
          Real.sin (Real.pi * (N : ℝ) * (x - y)) ^ 2) /
          ((L : ℝ) * Real.sin (Real.pi * (x - y)) ^ 2) := by
    field_simp [hxy, hL_pos.ne']
  rw [hrew, abs_div, abs_of_pos (mul_pos hL_pos hsin_pos), ← one_div]
  refine div_le_div_of_nonneg_right ?_ (mul_pos hL_pos hsin_pos).le
  have h1 := Real.sin_sq_le_one (Real.pi * ((N + L : ℕ) : ℝ) * (x - y))
  have h2 := Real.sin_sq_le_one (Real.pi * (N : ℝ) * (x - y))
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg (Real.sin (Real.pi * ((N + L : ℕ) : ℝ) * (x - y)))],
    by nlinarith [sq_nonneg (Real.sin (Real.pi * (N : ℝ) * (x - y)))]⟩

/-- Pairing `taperedFourierVec N L x` with a vector supported on the flat core `|k - (N + L)| ≤ N`
recovers its exact untapered Fourier sum. -/
theorem inner_taperedFourierVec_eq_sum {N L : ℕ} (hL : 0 < L) (x : ℝ)
    (f : EuclideanSpace ℂ (Fin (2 * (N + L) + 1)))
    (hf : ∀ k : Fin (2 * (N + L) + 1), (N : ℤ) < |(k : ℤ) - ((N + L : ℕ) : ℤ)| → f k = 0) :
    ⟪taperedFourierVec N L x, f⟫_ℂ =
      ∑ k : Fin (2 * (N + L) + 1),
        f k * (Real.fourierChar ((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * x) : ℂ) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  by_cases hk : |(k : ℤ) - ((N + L : ℕ) : ℤ)| ≤ (N : ℤ)
  · rw [RCLike.inner_apply, taperedFourierVec_apply_of_abs_le hL x hk, ← Circle.coe_inv_eq_conj,
      ← AddChar.map_neg_eq_inv, neg_neg]
  · rw [hf k (lt_of_not_ge hk), inner_zero_right, zero_mul]

/-- Cosecant-row large sieve for vectors supported on the flat core `|k - (N + L)| ≤ N`: if the
off-diagonal cosecant row sums are bounded by `S ≥ 0`, then the sum of squared Fourier polynomial
norms is at most `(2 * N + L + S / L) * ‖f‖ ^ 2`. -/
theorem sum_norm_sum_fourierChar_sq_le_of_sum_inv_sin_sq_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) {N L : ℕ} (hL : 0 < L)
    (f : EuclideanSpace ℂ (Fin (2 * (N + L) + 1)))
    (hf : ∀ k : Fin (2 * (N + L) + 1), (N : ℤ) < |(k : ℤ) - ((N + L : ℕ) : ℤ)| → f k = 0)
    {S : ℝ} (hS : 0 ≤ S)
    (hsin : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Real.sin (Real.pi * (x i - x j)) ≠ 0)
    (hrow : ∀ i ∈ s, ∑ j ∈ s.erase i, (Real.sin (Real.pi * (x i - x j)) ^ 2)⁻¹ ≤ S) :
    ∑ i ∈ s,
        ‖∑ k : Fin (2 * (N + L) + 1),
            f k * (Real.fourierChar ((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * x i) : ℂ)‖ ^ 2 ≤
      (2 * (N : ℝ) + (L : ℝ) + S / (L : ℝ)) * ‖f‖ ^ 2 := by
  have hinner :
      (∑ i ∈ s,
          ‖∑ k : Fin (2 * (N + L) + 1),
              f k * (Real.fourierChar ((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * x i) : ℂ)‖ ^ 2) =
        ∑ i ∈ s, ‖⟪f, taperedFourierVec N L (x i)⟫_ℂ‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [norm_inner_symm, inner_taperedFourierVec_eq_sum hL (x i) f hf]
  rw [hinner]
  refine sum_norm_inner_sq_le_of_diag_offDiag s (fun i ↦ taperedFourierVec N L (x i)) f
    (by positivity) (fun i _ ↦ (norm_taperedFourierVec_sq hL (x i)).le) fun i hi ↦ ?_
  calc
    ∑ j ∈ s.erase i, ‖⟪taperedFourierVec N L (x i), taperedFourierVec N L (x j)⟫_ℂ‖
        ≤ ∑ j ∈ s.erase i, ((L : ℝ) * Real.sin (Real.pi * (x i - x j)) ^ 2)⁻¹ :=
      Finset.sum_le_sum fun j hj ↦
        norm_inner_taperedFourierVec_le N L
          (hsin i hi j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm)
    _ = (L : ℝ)⁻¹ * ∑ j ∈ s.erase i, (Real.sin (Real.pi * (x i - x j)) ^ 2)⁻¹ := by
      simp_rw [mul_inv, Finset.mul_sum]
    _ ≤ (L : ℝ)⁻¹ * S := mul_le_mul_of_nonneg_left (hrow i hi) (by positivity)
    _ = S / (L : ℝ) := by ring

/-! ### Bombieri's additive large sieve -/

/-- Centered core additive large sieve for `0 < δ ≤ 1 / 2`: taking taper width `L = ⌊1 / δ⌋₊`
yields the explicit constant `2 * N + 2 / δ`. -/
theorem sum_norm_sum_fourierChar_sq_le_of_support {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ ‖((x i - x j : ℝ) : UnitAddCircle)‖)
    (N : ℕ) (f : EuclideanSpace ℂ (Fin (2 * (N + ⌊1 / δ⌋₊) + 1)))
    (hf : ∀ k : Fin (2 * (N + ⌊1 / δ⌋₊) + 1),
      (N : ℤ) < |(k : ℤ) - ((N + ⌊1 / δ⌋₊ : ℕ) : ℤ)| → f k = 0) :
    ∑ i ∈ s,
        ‖∑ k : Fin (2 * (N + ⌊1 / δ⌋₊) + 1),
            f k *
              (Real.fourierChar ((((k : ℤ) - ((N + ⌊1 / δ⌋₊ : ℕ) : ℤ) : ℤ) : ℝ) * x i) : ℂ)‖ ^ 2 ≤
      (2 * (N : ℝ) + 2 / δ) * ‖f‖ ^ 2 := by
  classical
  let L : ℕ := ⌊1 / δ⌋₊
  have hL_ge_two : 2 ≤ L := Nat.le_floor (by rw [Nat.cast_ofNat, le_div_iff₀ hδ]; linarith)
  have hL_pos : 0 < L := by omega
  have hr_le : (L : ℝ) * δ ≤ 1 := (le_div_iff₀ hδ).mp (Nat.floor_le (by positivity))
  have hr_ge : 2 / 3 ≤ (L : ℝ) * δ := by
    have h1 : (1 : ℝ) < ((L : ℝ) + 1) * δ := (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (1 / δ))
    have h2 : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge_two
    nlinarith
  have hwidth : (L : ℝ) + (Real.pi ^ 2 / (12 * δ ^ 2)) / (L : ℝ) ≤ 2 / δ := by
    have hL_rpos : (0 : ℝ) < (L : ℝ) := Nat.cast_pos.mpr hL_pos
    have hquad : ((L : ℝ) * δ) ^ 2 + Real.pi ^ 2 / 12 ≤ 2 * ((L : ℝ) * δ) := by
      nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have hmul :
        ((L : ℝ) + (Real.pi ^ 2 / (12 * δ ^ 2)) / (L : ℝ)) * ((L : ℝ) * δ ^ 2) ≤
          (2 / δ) * ((L : ℝ) * δ ^ 2) := by
      have hLHS :
          ((L : ℝ) + (Real.pi ^ 2 / (12 * δ ^ 2)) / (L : ℝ)) * ((L : ℝ) * δ ^ 2) =
            ((L : ℝ) * δ) ^ 2 + Real.pi ^ 2 / 12 := by
        field_simp [hL_rpos.ne', hδ.ne']
      have hRHS : (2 / δ) * ((L : ℝ) * δ ^ 2) = 2 * ((L : ℝ) * δ) := by
        field_simp [hδ.ne']
      rw [hLHS, hRHS]
      exact hquad
    exact le_of_mul_le_mul_right hmul (by positivity)
  have hsin : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Real.sin (Real.pi * (x i - x j)) ≠ 0 := by
    intro i hi j hj hne hzero
    have hlb := two_mul_norm_unitAddCircle_le_abs_sin (x i - x j)
    rw [hzero, abs_zero] at hlb
    linarith [hsep i hi j hj hne]
  have hmain := sum_norm_sum_fourierChar_sq_le_of_sum_inv_sin_sq_le s x hL_pos f hf
    (by positivity) hsin (fun i hi ↦ sum_erase_inv_sin_sq_le hδ hsep hi)
  exact le_trans hmain (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))

/-- Small-spacing branch (`δ ≤ 1 / 2`) of Bombieri's additive large sieve on `Finset.Ico M (M + H)`,
obtained by shifting and zero-padding `[M, M + H)` into the flat core of `taperedFourierVec`. -/
private theorem sum_norm_sum_Ico_fourierChar_sq_le_of_le_half {ι : Type*}
    (s : Finset ι) (M : ℤ) (H : ℕ) (a : ℤ → ℂ) (x : ι → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ ‖((x i - x j : ℝ) : UnitAddCircle)‖) :
    ∑ i ∈ s, ‖∑ n ∈ Finset.Ico M (M + H), a n * (Real.fourierChar ((n : ℝ) * x i) : ℂ)‖ ^ 2 ≤
      ((H : ℝ) + 2 / δ) * ∑ n ∈ Finset.Ico M (M + H), ‖a n‖ ^ 2 := by
  let N : ℕ := H / 2
  let L : ℕ := ⌊1 / δ⌋₊
  -- Embed `[M, M + H)` at offset `L` inside the flat core `|k - (N + L)| ≤ N`.
  let f : EuclideanSpace ℂ (Fin (2 * (N + L) + 1)) :=
    WithLp.toLp 2 fun k ↦
      if L ≤ k.val ∧ k.val - L < H then a (M + ((k.val - L : ℕ) : ℤ)) else 0
  have hf_supp : ∀ k : Fin (2 * (N + L) + 1),
      (N : ℤ) < |(k : ℤ) - ((N + L : ℕ) : ℤ)| → f k = 0 := by
    intro k hk
    have hnot : ¬ (L ≤ k.val ∧ k.val - L < H) := by
      dsimp only [N, L] at hk ⊢
      rcases abs_cases ((k : ℤ) - (((H / 2 + ⌊1 / δ⌋₊ : ℕ) : ℤ))) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    simp [f, hnot]
  have hbij : ∀ {α : Type} [AddCommMonoid α] (g : ℤ → α),
      (∑ k : Fin (2 * (N + L) + 1),
          if L ≤ k.val ∧ k.val - L < H then g (M + ((k.val - L : ℕ) : ℤ)) else 0) =
        ∑ n ∈ Finset.Ico M (M + H), g n := by
    intro α _ g
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun (k : Fin (2 * (N + L) + 1)) _ ↦ M + ((k.val - L : ℕ) : ℤ))
      (fun k hk ↦ Finset.mem_Ico.mpr (by have := (Finset.mem_filter.mp hk).2; omega))
      (fun k₁ hk₁ k₂ hk₂ h ↦ Fin.ext (by
        have := (Finset.mem_filter.mp hk₁).2; have := (Finset.mem_filter.mp hk₂).2; omega))
      (fun n hn ↦ ?_) (fun _ _ ↦ rfl)
    rcases Finset.mem_Ico.mp hn with ⟨hlo, hhi⟩
    exact ⟨⟨L + (n - M).toNat, by dsimp only [N, L]; omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩, by dsimp; omega⟩
  -- Identify `‖f‖ ^ 2` and the unimodularly shifted Fourier sums with those on `Ico M (M + H)`.
  have hnorm_f : ‖f‖ ^ 2 = ∑ n ∈ Finset.Ico M (M + H), ‖a n‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, ← hbij (fun n ↦ ‖a n‖ ^ 2)]
    exact Finset.sum_congr rfl fun k _ ↦ by by_cases hk : L ≤ k.val ∧ k.val - L < H <;> simp [f, hk]
  have hsum_norm (t : ℝ) :
      ‖∑ n ∈ Finset.Ico M (M + H), a n * (Real.fourierChar ((n : ℝ) * t) : ℂ)‖ =
        ‖∑ k : Fin (2 * (N + L) + 1),
            f k * (Real.fourierChar ((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * t) : ℂ)‖ := by
    rw [← one_mul (‖∑ k : Fin (2 * (N + L) + 1), _‖),
      ← Circle.norm_coe (Real.fourierChar (((M + (N : ℤ) : ℤ) : ℝ) * t)), ← norm_mul,
      Finset.mul_sum, ← hbij (fun n ↦ a n * (Real.fourierChar ((n : ℝ) * t) : ℂ))]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hk : L ≤ k.val ∧ k.val - L < H
    · simp only [f, hk, and_self, ↓reduceIte]
      rw [← mul_assoc, mul_comm (Real.fourierChar _ : ℂ), mul_assoc, ← Circle.coe_mul,
        ← AddChar.map_add_eq_mul]
      congr 3
      have heq : M + ((k.val - L : ℕ) : ℤ) = (M + (N : ℤ)) + ((k : ℤ) - ((N + L : ℕ) : ℤ)) := by
        omega
      rw [heq]; push_cast; ring
    · simp [f, hk]
  -- Apply the centered core large sieve and replace `2 * (H / 2) ≤ H`.
  have h2N : 2 * (N : ℝ) ≤ (H : ℝ) := by exact_mod_cast (by omega : 2 * (H / 2) ≤ H)
  simp_rw [hsum_norm]
  calc
    ∑ i ∈ s,
        ‖∑ k : Fin (2 * (N + L) + 1),
            f k * (Real.fourierChar ((((k : ℤ) - ((N + L : ℕ) : ℤ) : ℤ) : ℝ) * x i) : ℂ)‖ ^ 2
        ≤ (2 * (N : ℝ) + 2 / δ) * ‖f‖ ^ 2 :=
      sum_norm_sum_fourierChar_sq_le_of_support s x hδ hδ' hsep N f hf_supp
    _ = (2 * (N : ℝ) + 2 / δ) * ∑ n ∈ Finset.Ico M (M + H), ‖a n‖ ^ 2 := by rw [hnorm_f]
    _ ≤ ((H : ℝ) + 2 / δ) * ∑ n ∈ Finset.Ico M (M + H), ‖a n‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

/-- **Bombieri's additive large sieve inequality** (Bombieri 1971, Theorem 2) on an integer interval
`Finset.Ico M (M + H)`: for any finite family of `δ`-separated real frequencies (`0 < δ`) in
`UnitAddCircle`, `∑ i ∈ s, ‖∑ n ∈ Ico M (M + H), a n * e(n * x i)‖ ^ 2 ≤`
`(H + 2 / δ) * ∑ n ∈ Ico M (M + H), ‖a n‖ ^ 2`.
Handles all `H : ℕ` (including `H = 0`) and all `δ > 0` (including `δ > 1 / 2`). -/
theorem sum_norm_sum_Ico_fourierChar_sq_le {ι : Type*} (s : Finset ι) (M : ℤ) (H : ℕ)
    (a : ℤ → ℂ) (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ ‖((x i - x j : ℝ) : UnitAddCircle)‖) :
    ∑ i ∈ s, ‖∑ n ∈ Finset.Ico M (M + H), a n * (Real.fourierChar ((n : ℝ) * x i) : ℂ)‖ ^ 2 ≤
      ((H : ℝ) + 2 / δ) * ∑ n ∈ Finset.Ico M (M + H), ‖a n‖ ^ 2 := by
  by_cases hδ' : δ ≤ 1 / 2
  · exact sum_norm_sum_Ico_fourierChar_sq_le_of_le_half s M H a x hδ hδ' hsep
  have hcard : (s.card : ℝ) ≤ 1 := by
    exact_mod_cast card_le_one_of_half_lt_norm_unitAddCircle (lt_of_not_ge hδ') hsep
  have hsingle : ∀ i ∈ s,
      ‖∑ n ∈ Finset.Ico M (M + H), a n * (Real.fourierChar ((n : ℝ) * x i) : ℂ)‖ ^ 2 ≤
        ((H : ℝ) + 2 / δ) * ∑ n ∈ Finset.Ico M (M + H), ‖a n‖ ^ 2 := by
    intro i _
    have htri :
        ‖∑ n ∈ Finset.Ico M (M + H), a n * (Real.fourierChar ((n : ℝ) * x i) : ℂ)‖ ≤
          ∑ n ∈ Finset.Ico M (M + H), ‖a n‖ := by
      refine le_trans (norm_sum_le _ _) ?_
      simp [Circle.norm_coe]
    have hcs :
        (∑ n ∈ Finset.Ico M (M + H), ‖a n‖) ^ 2 ≤
          (H : ℝ) * ∑ n ∈ Finset.Ico M (M + H), ‖a n‖ ^ 2 := by
      have hIco : ((Finset.Ico M (M + (H : ℤ))).card : ℝ) = (H : ℝ) := by
        rw [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast]
      simpa [hIco] using sq_sum_le_card_mul_sum_sq (s := Finset.Ico M (M + H)) (f := fun n ↦ ‖a n‖)
    calc
      ‖∑ n ∈ Finset.Ico M (M + H), a n * (Real.fourierChar ((n : ℝ) * x i) : ℂ)‖ ^ 2
          ≤ (∑ n ∈ Finset.Ico M (M + H), ‖a n‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ ≤ (H : ℝ) * ∑ n ∈ Finset.Ico M (M + H), ‖a n‖ ^ 2 := hcs
      _ ≤ ((H : ℝ) + 2 / δ) * ∑ n ∈ Finset.Ico M (M + H), ‖a n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [div_pos (two_pos : (0 : ℝ) < 2) hδ])
          (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  calc
    ∑ i ∈ s, ‖∑ n ∈ Finset.Ico M (M + H), a n * (Real.fourierChar ((n : ℝ) * x i) : ℂ)‖ ^ 2
        ≤ ∑ _i ∈ s, (((H : ℝ) + 2 / δ) * ∑ n ∈ Finset.Ico M (M + H), ‖a n‖ ^ 2) :=
      Finset.sum_le_sum hsingle
    _ = (s.card : ℝ) * (((H : ℝ) + 2 / δ) * ∑ n ∈ Finset.Ico M (M + H), ‖a n‖ ^ 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 * (((H : ℝ) + 2 / δ) * ∑ n ∈ Finset.Ico M (M + H), ‖a n‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hcard
        (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
    _ = ((H : ℝ) + 2 / δ) * ∑ n ∈ Finset.Ico M (M + H), ‖a n‖ ^ 2 := one_mul _

/-- **Bombieri's additive large sieve inequality** (Bombieri 1971, Theorem 2) indexed by `Fin H`:
for any finite family of `δ`-separated real frequencies (`0 < δ`) in `UnitAddCircle` and any
starting frequency `M : ℤ`,
`∑ i ∈ s, ‖∑ j : Fin H, a j * e((M + j) * x i)‖ ^ 2 ≤ (H + 2 / δ) * ∑ j : Fin H, ‖a j‖ ^ 2`. -/
theorem sum_norm_sum_fourierChar_sq_le {ι : Type*} (s : Finset ι) (M : ℤ) (H : ℕ)
    (a : Fin H → ℂ) (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ ‖((x i - x j : ℝ) : UnitAddCircle)‖) :
    ∑ i ∈ s, ‖∑ j : Fin H, a j * (Real.fourierChar (((M : ℝ) + (j : ℕ)) * x i) : ℂ)‖ ^ 2 ≤
      ((H : ℝ) + 2 / δ) * ∑ j : Fin H, ‖a j‖ ^ 2 := by
  let b : ℤ → ℂ := fun n ↦
    if h : 0 ≤ n - M ∧ (n - M).toNat < H then a ⟨(n - M).toNat, h.2⟩ else 0
  have hb : ∀ j : Fin H, b (M + (j : ℤ)) = a j := by
    intro j
    have h1 : 0 ≤ M + (j : ℤ) - M := by omega
    have h2 : (M + (j : ℤ) - M).toNat < H := by omega
    simp only [b, h1, h2, and_self, ↓reduceDIte]
    congr 1; ext; dsimp; omega
  have hbij : ∀ {α : Type} [AddCommMonoid α] (g : ℤ → α),
      (∑ j : Fin H, g (M + (j : ℤ))) = ∑ n ∈ Finset.Ico M (M + H), g n := by
    intro α _ g
    refine Finset.sum_bij (fun (j : Fin H) _ ↦ M + (j : ℤ))
      (fun j _ ↦ Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
      (fun j₁ _ j₂ _ h ↦ Fin.ext (by omega))
      (fun n hn ↦ ?_) (fun _ _ ↦ rfl)
    rcases Finset.mem_Ico.mp hn with ⟨hlo, hhi⟩
    exact ⟨⟨(n - M).toNat, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
  have hsum_norm_sq : (∑ n ∈ Finset.Ico M (M + H), ‖b n‖ ^ 2) = ∑ j : Fin H, ‖a j‖ ^ 2 := by
    rw [← hbij (fun n ↦ ‖b n‖ ^ 2)]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hb j]
  have hsum_fourier : ∀ t : ℝ,
      (∑ n ∈ Finset.Ico M (M + H), b n * (Real.fourierChar ((n : ℝ) * t) : ℂ)) =
        ∑ j : Fin H, a j * (Real.fourierChar (((M : ℝ) + (j : ℕ)) * t) : ℂ) := by
    intro t
    rw [← hbij (fun n ↦ b n * (Real.fourierChar ((n : ℝ) * t) : ℂ))]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hb j]; push_cast; rfl
  simpa only [hsum_fourier, hsum_norm_sq] using
    sum_norm_sum_Ico_fourierChar_sq_le s M H b x hδ hsep

end TauCeti
