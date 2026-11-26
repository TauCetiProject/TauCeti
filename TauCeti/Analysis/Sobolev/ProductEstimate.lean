/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Measure.Haar.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.Lp
import TauCeti.Analysis.FunctionalSpaces.SobolevInequality
import TauCeti.Analysis.Sobolev.GagliardoNirenberg
import TauCeti.Analysis.Sobolev.Morrey.Basic
import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# The product estimate for `kp > n` by Sobolev embeddings

Let `E` be a finite-dimensional real normed space of dimension `n` with an additive Haar measure,
let `1 ≤ p < ∞` and let `k p > n`. This file proves that for a continuous bilinear map `B` and
compactly supported `C^k` functions `u` and `v` with values in finite-dimensional spaces, every
derivative of order `i ≤ k` of `x ↦ B (u x) (v x)` satisfies

`‖Dⁱ (B (u, v))‖_{Lᵖ} ≤ C ‖B‖ (‖u‖_∞ + ∑_{l ≤ k} ‖Dˡ u‖_{Lᵖ}) (‖v‖_∞ + ∑_{l ≤ k} ‖Dˡ v‖_{Lᵖ})`,

provided `p ≠ n` (`TauCeti.exists_eLpNorm_iteratedFDeriv_bilinear_le_of_ne_finrank`). This is the
estimate behind the algebra property of `W^{k,p}` for `k p > n`. Unlike the Moser product estimate
`TauCeti.exists_eLpNorm_iteratedFDeriv_bilinear_le`, which rests on the Gagliardo–Nirenberg
inequality and needs `p ≥ 2`, it holds for every `p ≥ 1` with `p ≠ n`; the price is the full
`W^{k,p}` norm of both factors on the right.

## The argument

By the Leibniz rule and Hölder's inequality
(`ContinuousLinearMap.eLpNorm_iteratedFDeriv_le_of_bilinear`), `‖Dⁱ (B (u, v))‖_p` is at most a sum
of the products `‖Dʲ u‖_{q_j} ‖D^{i - j} v‖_{r_j}`, `j ≤ i`, with `1 / q_j = j / (i p)` and
`1 / r_j = (i - j) / (i p)`. It remains to bound `‖Dʲ u‖_{i p / j}` by the `W^{k,p}` norm of `u`
and `‖u‖_∞`. For `j = 0` this is `‖u‖_∞` and for `j = i` it is `‖Dⁱ u‖_p`. For `0 < j < i`:

* if `p < n`, `Dʲ u` has `k - j` derivatives in `Lᵖ` and
  `1 / p - (k - j) / n ≤ j / (i p)`, because `n (i - j) < k p (i - j) ≤ i p (k - j)`; the Sobolev
  inequality of order `k - j` (`TauCeti.exists_eLpNorm_iteratedFDeriv_le_sum_of_lt_finrank`)
  applies;
* if `p > n`, Morrey's inequality bounds `‖Dʲ u‖_∞` by `‖Dʲ u‖_p + ‖D^{j + 1} u‖_p`
  (`TauCeti.exists_eLpNorm_top_le_mul_eLpNorm_add_eLpNorm_fderiv`), since `j < k`, and
  `‖Dʲ u‖_{i p / j}` lies between `‖Dʲ u‖_p` and `‖Dʲ u‖_∞`.

At `p = n` neither applies: `W^{1,n}` does not embed in `L^∞`. For `p = n ≥ 2` the Moser product
estimate covers this case, so for `1 < p < ∞` the estimate holds without exception
(`TauCeti.exists_eLpNorm_iteratedFDeriv_bilinear_le_of_finrank_lt_mul`).

## Main results

* `TauCeti.exists_eLpNorm_iteratedFDeriv_bilinear_le_of_ne_finrank`: the product estimate for
  `1 ≤ p < ∞`, `k p > n` and `p ≠ n`, with values in finite-dimensional spaces.
* `TauCeti.exists_eLpNorm_iteratedFDeriv_bilinear_le_of_finrank_lt_mul`: the product estimate for
  `1 < p < ∞` and `k p > n`, with values in finite-dimensional inner product spaces.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Pure and Applied Mathematics 140,
  Academic Press, 2003, Theorem 4.39.
-/

public section

namespace TauCeti

open MeasureTheory Module
open scoped ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

section NormedSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] [FiniteDimensional ℝ F] in
/-- Each `Lᵖ` norm of a derivative of order at most `k` is at most
`‖u‖_∞ + ∑_{l ≤ k} ‖Dˡ u‖_{Lᵖ}`. -/
private theorem eLpNorm_iteratedFDeriv_le_eLpNorm_top_add_sum (u : E → F) (p : ℝ≥0∞) {k l : ℕ}
    (hl : l ≤ k) : eLpNorm (iteratedFDeriv ℝ l u) p μ ≤
      eLpNorm u ∞ μ + ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l u) p μ :=
  (Finset.single_le_sum (f := fun l ↦ eLpNorm (iteratedFDeriv ℝ l u) p μ)
    (fun _ _ ↦ zero_le) (Finset.mem_range.2 (Nat.lt_succ_of_le hl))).trans le_add_self

/-- The exponent `i p / j` lies within `k - j` Sobolev steps of `p` when `k p > n`:
`1 / p - (k - j) / n ≤ j / (i p)` for `0 < j ≤ i ≤ k`, since
`n (i - j) ≤ k p (i - j) ≤ i p (k - j)`. -/
private theorem inv_sub_div_le_div_mul {n p i j k : ℝ} (hn : 0 < n) (hp : 0 < p) (hj : 0 < j)
    (hji : j ≤ i) (hik : i ≤ k) (hk : n < k * p) : p⁻¹ - (k - j) / n ≤ j / (i * p) := by
  have hip : 0 < i * p := mul_pos (hj.trans_le hji) hp
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add', inv_eq_one_div,
    div_sub_div _ _ hp.ne' hip.ne', div_le_div_iff₀ (mul_pos hp hip) hn]
  nlinarith [mul_le_mul_of_nonneg_left hk.le (sub_nonneg.2 hji),
    mul_nonneg (mul_nonneg hj.le hp.le) (sub_nonneg.2 hik)]

/-- For `p < n`, the derivative `Dʲ u`, `j ≤ k`, of a compactly supported `C^k` function lies in
`L^q` whenever `p ≤ q < ∞` and `1 / q ≥ 1 / p - (k - j) / n`, with norm controlled by the `Lᵖ`
norms of the derivatives of `u` through order `k`. -/
private theorem exists_eLpNorm_iteratedFDeriv_le_add_sum_of_lt_finrank {p : ℝ≥0} (hp : 1 ≤ p)
    (hpn : (p : ℝ) < finrank ℝ E) {j k : ℕ} (hjk : j ≤ k) {q : ℝ≥0} (hpq : p ≤ q)
    (hq : (p : ℝ)⁻¹ - ((k - j : ℕ) : ℝ) / finrank ℝ E ≤ (q : ℝ)⁻¹) :
    ∃ c : ℝ≥0, ∀ u : E → F, ContDiff ℝ k u → HasCompactSupport u →
      eLpNorm (iteratedFDeriv ℝ j u) q μ ≤
        c * (eLpNorm u ∞ μ + ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l u) p μ) := by
  obtain ⟨c, hc⟩ := exists_eLpNorm_iteratedFDeriv_le_sum_of_lt_finrank (F := F) μ hp hpn j
    (k - j) hpq hq
  refine ⟨c, fun u hu hcu ↦ ?_⟩
  -- The derivatives `D^{j + l} u`, `l ≤ k - j`, are among the `Dˡ u`, `l ≤ k`.
  have hsum : ∑ l ∈ Finset.range (k - j + 1), eLpNorm (iteratedFDeriv ℝ (j + l) u) p μ ≤
      ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l u) p μ := by
    rw [show k + 1 = j + (k - j + 1) by omega,
      Finset.sum_range_add (fun l ↦ eLpNorm (iteratedFDeriv ℝ l u) p μ)]
    exact le_add_self
  exact (hc u (hu.of_le (by exact_mod_cast (Nat.add_sub_cancel' hjk).le)) hcu).trans
    (mul_le_mul_of_nonneg_left (hsum.trans le_add_self) zero_le)

/-- For `p > n`, the derivative `Dʲ u`, `j < k`, of a `C^k` function lies in every `L^q`,
`q ≥ p`, with norm controlled by the `Lᵖ` norms of the derivatives of `u` through order `k`:
`‖Dʲ u‖_q` lies between `‖Dʲ u‖_p` and `‖Dʲ u‖_∞`, which Morrey's inequality bounds by
`‖Dʲ u‖_p + ‖D^{j + 1} u‖_p`. -/
private theorem exists_eLpNorm_iteratedFDeriv_le_add_sum_of_finrank_lt {p : ℝ≥0} (hp : 1 ≤ p)
    (hpn : (finrank ℝ E : ℝ) < p) {j k : ℕ} (hjk : j < k) {q : ℝ≥0} (hpq : p ≤ q) :
    ∃ c : ℝ≥0, ∀ u : E → F, ContDiff ℝ k u →
      eLpNorm (iteratedFDeriv ℝ j u) q μ ≤
        c * (eLpNorm u ∞ μ + ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l u) p μ) := by
  obtain ⟨c, hc⟩ := exists_eLpNorm_top_le_mul_eLpNorm_add_eLpNorm_fderiv (μ := μ)
    (F := ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ E) F) hp (by exact_mod_cast hpn)
  refine ⟨1 + 2 * c, fun u hu ↦ ?_⟩
  have hu₁ : ContDiff ℝ 1 (iteratedFDeriv ℝ j u) :=
    hu.iteratedFDeriv_right (by exact_mod_cast (show 1 + j ≤ k by omega))
  have ha := eLpNorm_iteratedFDeriv_le_eLpNorm_top_add_sum (μ := μ) u p hjk.le
  have hb := eLpNorm_iteratedFDeriv_le_eLpNorm_top_add_sum (μ := μ) u p (Nat.succ_le_of_lt hjk)
  calc eLpNorm (iteratedFDeriv ℝ j u) q μ
      ≤ max (eLpNorm (iteratedFDeriv ℝ j u) p μ) (eLpNorm (iteratedFDeriv ℝ j u) ∞ μ) :=
        eLpNorm_le_max_of_le_of_le (by simpa using (zero_lt_one.trans_le hp).ne')
          (by exact_mod_cast hpq) le_top
    _ ≤ eLpNorm (iteratedFDeriv ℝ j u) p μ +
          c * (eLpNorm (iteratedFDeriv ℝ j u) p μ + eLpNorm (iteratedFDeriv ℝ (j + 1) u) p μ) :=
        max_le le_self_add (by
          rw [← eLpNorm_fderiv_iteratedFDeriv]
          exact (hc _ hu₁).trans le_add_self)
    _ ≤ _ := by
        refine (add_le_add ha (mul_le_mul_of_nonneg_left (add_le_add ha hb) zero_le)).trans_eq ?_
        push_cast
        ring

/-- For `k p > n` and `p ≠ n`, the intermediate derivative `Dʲ u` of a compactly supported `C^k`
function `u` lies in `L^{i p / j}` for `j ≤ i ≤ k`, `i ≠ 0`, with norm controlled by `‖u‖_∞` and the
`Lᵖ` norms of the derivatives of `u` through order `k`. -/
private theorem exists_eLpNorm_iteratedFDeriv_le_of_ne_finrank {p : ℝ≥0} (hp : 1 ≤ p)
    (hpn : (p : ℝ) ≠ finrank ℝ E) {k : ℕ} (hk : (finrank ℝ E : ℝ) < k * p) {i : ℕ}
    (hi : i ≠ 0) (hik : i ≤ k) :
    ∃ c : ℕ → ℝ≥0, ∀ j ≤ i, ∀ u : E → F, ContDiff ℝ k u → HasCompactSupport u →
      eLpNorm (iteratedFDeriv ℝ j u) ((j : ℝ≥0∞) / (i * p))⁻¹ μ ≤
        c j * (eLpNorm u ∞ μ + ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l u) p μ) := by
  suffices h : ∀ j, ∃ c : ℝ≥0, j ≤ i → ∀ u : E → F, ContDiff ℝ k u → HasCompactSupport u →
      eLpNorm (iteratedFDeriv ℝ j u) ((j : ℝ≥0∞) / (i * p))⁻¹ μ ≤
        c * (eLpNorm u ∞ μ + ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l u) p μ) by
    choose c hc using h
    exact ⟨c, hc⟩
  intro j
  by_cases hji : j ≤ i
  swap
  · exact ⟨0, fun h ↦ absurd h hji⟩
  refine (?_ : ∃ c : ℝ≥0, _).imp fun c hc _ ↦ hc
  have hp0 : (0 : ℝ) < p := by exact_mod_cast zero_lt_one.trans_le hp
  have hip : (i : ℝ≥0∞) * p ≠ ∞ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.coe_ne_top
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · -- `j = 0`: the exponent is `∞`.
    refine ⟨1, fun u _ _ ↦ ?_⟩
    rw [Nat.cast_zero, ENNReal.zero_div, ENNReal.inv_zero, eLpNorm_iteratedFDeriv_zero,
      ENNReal.coe_one, one_mul]
    exact le_self_add
  rcases hji.eq_or_lt with rfl | hji'
  · -- `j = i`: the exponent is `p`.
    refine ⟨1, fun u _ _ ↦ ?_⟩
    have hi0 : (j : ℝ≥0∞) ≠ 0 := by simpa using hi
    have hpj : ((j : ℝ≥0∞) / (j * p))⁻¹ = p :=
      calc ((j : ℝ≥0∞) / (j * p))⁻¹ = j * p / (j * 1) := by
            rw [mul_one, ENNReal.inv_div (Or.inl hip) (Or.inl (mul_ne_zero hi0 (by simpa using
              hp0.ne')))]
        _ = p := by rw [ENNReal.mul_div_mul_left _ _ hi0 (ENNReal.natCast_ne_top _), div_one]
    rw [hpj, ENNReal.coe_one, one_mul]
    exact eLpNorm_iteratedFDeriv_le_eLpNorm_top_add_sum u p hik
  -- `0 < j < i`: the exponent is `q = i p / j`, with `p < q < ∞`.
  have hq : ((j : ℝ≥0∞) / (i * p))⁻¹ = ((i * p / j : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.inv_div (Or.inl hip) (Or.inr (by simpa using hj0.ne')),
      ENNReal.coe_div (by simpa using hj0.ne')]
    push_cast
    rfl
  have hpq : p ≤ i * p / j := by
    rw [le_div_iff₀ (by exact_mod_cast hj0), mul_comm (i : ℝ≥0)]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hji) zero_le
  simp only [hq]
  rcases hpn.lt_or_gt with hlt | hgt
  · refine exists_eLpNorm_iteratedFDeriv_le_add_sum_of_lt_finrank hp hlt (hji'.trans_le hik).le
      hpq ?_
    rw [Nat.cast_sub (hji'.trans_le hik).le, NNReal.coe_div, NNReal.coe_mul, inv_div,
      NNReal.coe_natCast, NNReal.coe_natCast]
    exact inv_sub_div_le_div_mul (hp0.trans hlt) hp0 (by exact_mod_cast hj0)
      (by exact_mod_cast hji) (by exact_mod_cast hik) hk
  · exact (exists_eLpNorm_iteratedFDeriv_le_add_sum_of_finrank_lt hp hgt (hji'.trans_le hik)
      hpq).imp fun c hc u hu _ ↦ hc u hu

variable {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **The product estimate for `k p > n`, `p ≠ n`.** Let `1 ≤ p < ∞` with `k p > n` and `p ≠ n`,
where `n` is the dimension of `E`, and let `i ≤ k`. There is a constant `C` such that for every
continuous bilinear map `B` and all compactly supported `C^k` functions `u` and `v` with values in
finite-dimensional spaces,

`‖Dⁱ (B (u, v))‖_{Lᵖ} ≤ C ‖B‖ (‖u‖_∞ + ∑_{l ≤ k} ‖Dˡ u‖_{Lᵖ}) (‖v‖_∞ + ∑_{l ≤ k} ‖Dˡ v‖_{Lᵖ})`.

The intermediate terms of the Leibniz expansion are estimated by Hölder's inequality and the
Sobolev inequalities for compactly supported functions. -/
theorem exists_eLpNorm_iteratedFDeriv_bilinear_le_of_ne_finrank {p : ℝ≥0} (hp : 1 ≤ p)
    (hpn : (p : ℝ) ≠ finrank ℝ E) {k : ℕ} (hk : (finrank ℝ E : ℝ) < k * p) {i : ℕ} (hik : i ≤ k) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (u : E → F) (v : E → G), ContDiff ℝ k u →
      HasCompactSupport u → ContDiff ℝ k v → HasCompactSupport v →
      eLpNorm (iteratedFDeriv ℝ i (fun x ↦ B (u x) (v x))) p μ ≤
        C * ‖B‖ₑ *
          (eLpNorm u ∞ μ + ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l u) p μ) *
          (eLpNorm v ∞ μ + ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l v) p μ) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · -- `‖B (u, v)‖_p ≤ ‖B‖ ‖u‖_∞ ‖v‖_p`.
    refine ⟨1, fun B u v hu _ hv _ ↦ ?_⟩
    have h := B.eLpNorm_iteratedFDeriv_le_of_bilinear (μ := μ) hu hv zero_le hp1
      (q := fun _ ↦ ∞) (r := fun _ ↦ p) fun _ _ ↦ inferInstance
    simp only [zero_add, Finset.sum_range_one, Nat.choose_self, Nat.cast_one, mul_one,
      eLpNorm_iteratedFDeriv_zero] at h
    rw [eLpNorm_iteratedFDeriv_zero]
    refine h.trans ?_
    rw [ENNReal.coe_one, one_mul]
    gcongr
    · exact le_self_add
    · exact eLpNorm_iteratedFDeriv_le_eLpNorm_top_add_sum (μ := μ) v p (Nat.zero_le k)
  -- The exponents `1 / q_j = j / (i p)` and `1 / r_j = (i - j) / (i p)`.
  set q : ℕ → ℝ≥0∞ := fun j ↦ ((j : ℝ≥0∞) / (i * p))⁻¹
  have hqr : ∀ j ≤ i, ENNReal.HolderTriple (q j) (q (i - j)) p := fun j hj ↦ by
    refine ⟨?_⟩
    simp only [q, inv_inv]
    rw [ENNReal.div_add_div_same, ← Nat.cast_add, Nat.add_sub_cancel' hj,
      ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by simpa using hi0.ne'))
        (Or.inl (by simp)), mul_comm (i : ℝ≥0∞)⁻¹, mul_assoc,
      ENNReal.inv_mul_cancel (by simpa using hi0.ne') (by simp), mul_one]
  obtain ⟨cu, hcu⟩ :=
    exists_eLpNorm_iteratedFDeriv_le_of_ne_finrank (μ := μ) (F := F) hp hpn hk hi0.ne' hik
  obtain ⟨cv, hcv⟩ :=
    exists_eLpNorm_iteratedFDeriv_le_of_ne_finrank (μ := μ) (F := G) hp hpn hk hi0.ne' hik
  refine ⟨∑ j ∈ Finset.range (i + 1), i.choose j * cu j * cv (i - j),
    fun B u v hu hcu' hv hcv' ↦ ?_⟩
  set U := eLpNorm u ∞ μ + ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l u) p μ
  set V := eLpNorm v ∞ μ + ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l v) p μ
  calc eLpNorm (iteratedFDeriv ℝ i (fun x ↦ B (u x) (v x))) p μ
      ≤ ∑ j ∈ Finset.range (i + 1), ‖B‖ₑ * (i.choose j : ℝ≥0∞) *
          eLpNorm (iteratedFDeriv ℝ j u) (q j) μ *
            eLpNorm (iteratedFDeriv ℝ (i - j) v) (q (i - j)) μ :=
        B.eLpNorm_iteratedFDeriv_le_of_bilinear hu hv (by exact_mod_cast hik) hp1 hqr
    _ ≤ ∑ j ∈ Finset.range (i + 1), ‖B‖ₑ * (i.choose j : ℝ≥0∞) * (cu j * U) *
          (cv (i - j) * V) := by
        refine Finset.sum_le_sum fun j hj ↦ ?_
        have hji := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        gcongr
        exacts [hcu j hji u hu hcu', hcv (i - j) (Nat.sub_le _ _) v hv hcv']
    _ = _ := by
        push_cast
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ ↦ by ring

end NormedSpace

section InnerProductSpace

variable {F G H : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] [NormedAddCommGroup H]
  [NormedSpace ℝ H]

/-- **The product estimate for `k p > n`.** Let `1 < p < ∞` with `k p > n`, where `n` is the
dimension of `E`, and let `i ≤ k`. There is a constant `C` such that for every continuous bilinear
map `B` and all compactly supported `C^k` functions `u` and `v` with values in finite-dimensional
inner product spaces,

`‖Dⁱ (B (u, v))‖_{Lᵖ} ≤ C ‖B‖ (‖u‖_∞ + ∑_{l ≤ k} ‖Dˡ u‖_{Lᵖ}) (‖v‖_∞ + ∑_{l ≤ k} ‖Dˡ v‖_{Lᵖ})`.

For `p ≠ n` this is `TauCeti.exists_eLpNorm_iteratedFDeriv_bilinear_le_of_ne_finrank`; for
`p = n`, which forces `p ≥ 2`, it follows from the Moser product estimate
`TauCeti.exists_eLpNorm_iteratedFDeriv_bilinear_le`. -/
theorem exists_eLpNorm_iteratedFDeriv_bilinear_le_of_finrank_lt_mul {p : ℝ≥0} (hp : 1 < p)
    {k : ℕ} (hk : (finrank ℝ E : ℝ) < k * p) {i : ℕ} (hik : i ≤ k) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (u : E → F) (v : E → G), ContDiff ℝ k u →
      HasCompactSupport u → ContDiff ℝ k v → HasCompactSupport v →
      eLpNorm (iteratedFDeriv ℝ i (fun x ↦ B (u x) (v x))) p μ ≤
        C * ‖B‖ₑ *
          (eLpNorm u ∞ μ + ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l u) p μ) *
          (eLpNorm v ∞ μ + ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l v) p μ) := by
  by_cases hpn : (p : ℝ) = finrank ℝ E
  swap
  · exact exists_eLpNorm_iteratedFDeriv_bilinear_le_of_ne_finrank hp.le hpn hk hik
  -- `p = n` is an integer greater than one.
  have hp2 : (2 : ℝ≥0∞) ≤ p := by
    have h1 : (1 : ℝ) < finrank ℝ E := hpn ▸ (by exact_mod_cast hp)
    have h2 : (2 : ℝ) ≤ finrank ℝ E := by exact_mod_cast (show 2 ≤ finrank ℝ E by exact_mod_cast h1)
    rw [← ENNReal.coe_ofNat, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, hpn]
    exact_mod_cast h2
  obtain ⟨c, hc⟩ := exists_eLpNorm_iteratedFDeriv_bilinear_le (μ := μ) (F := F) (G := G) (H := H)
    hp2 ENNReal.coe_ne_top i
  refine ⟨2 * c, fun B u v hu hcu hv hcv ↦ (hc B u v (hu.of_le (by exact_mod_cast hik)) hcu
    (hv.of_le (by exact_mod_cast hik)) hcv).trans ?_⟩
  have hu₀ := eLpNorm_iteratedFDeriv_le_eLpNorm_top_add_sum (μ := μ) u p hik
  have hv₀ := eLpNorm_iteratedFDeriv_le_eLpNorm_top_add_sum (μ := μ) v p hik
  calc (c : ℝ≥0∞) * ‖B‖ₑ * (eLpNorm u ∞ μ * eLpNorm (iteratedFDeriv ℝ i v) p μ +
        eLpNorm (iteratedFDeriv ℝ i u) p μ * eLpNorm v ∞ μ)
      ≤ c * ‖B‖ₑ *
          ((eLpNorm u ∞ μ + ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l u) p μ) *
            (eLpNorm v ∞ μ + ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l v) p μ) +
          (eLpNorm u ∞ μ + ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l u) p μ) *
            (eLpNorm v ∞ μ + ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l v) p μ)) := by
        gcongr
        exacts [le_self_add, le_self_add]
    _ = _ := by
        push_cast
        ring

end InnerProductSpace

end TauCeti
