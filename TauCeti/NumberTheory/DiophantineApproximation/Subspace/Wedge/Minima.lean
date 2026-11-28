/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Rank
public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Wedge.Domain

import TauCeti.LinearAlgebra.LinearIndependent.Unitriangular

/-!
# The successive minima of the wedge domain

Let `μ 0 ≤ ⋯ ≤ μ (N - 1)` be the successive minima over `K` of an approximation domain
`approxDomain S₀ L c Q` of `K^ι`, `N = card ι`, realized by linearly independent vectors `x l`.
For `k + p = N` with `0 < p`, Evertse's lemma corrects the `x l` triangularly to
vectors `y l` whose Plücker vectors `y J`, for the `p`-subsets `J` meeting `{0, …, k - 1}`, lie in
the wedge domain `S(Q)`, the approximation domain of the wedge forms `wedgeForms (L v) p` with
the exponents `wedgeExponent` (`TauCeti.NumberField.exists_plucker_mem_approxDomain_wedgeForms`).

This file proves Bombieri–Gubler's Lemma 7.5.31: if `ν` are the successive minima over `K` of
`S(Q)`, of which there are `M = N.choose p`, then all but the last are at most `1`, and the last is
at least `c₀ · μ k / μ (k - 1)`, with `c₀ > 0` independent of the exponents `c`, of the level `Q`
and of `k` (`TauCeti.NumberField.exists_successiveMinimum_wedge`). The first statement holds
because the `M - 1` Plücker vectors above lie in `S(Q)` and span a hyperplane, Lemma 7.5.33
(`TauCeti.finrank_wedgeSpan_add_one`). For the second, Minkowski's second theorem over `K` bounds
`∏ l, ν l ^ d`, with `d = [K : ℚ]`, below by a constant times `Q ^ (-w)`, where `w` is the weight of
`S(Q)`; since every minimum but the last is at most `1`, the same lower bound holds for
`ν (M - 1) ^ d` (`TauCeti.NumberField.exists_pos_mul_rpow_le_successiveMinimum_pow`). `Q` raised to
the weight of `S(Q)` is at most a constant times `(μ (k - 1) / μ k) ^ d` by Minkowski's second
theorem for the original domain (`TauCeti.NumberField.rpow_approxWeight_wedgeExponent_le`).

A large jump between consecutive minima exists whenever the domain has rank `R` with
`1 ≤ R < N` (Bombieri–Gubler (7.41)): some `k ∈ [R, N)` has
`(μ (k - 1) / μ k) ^ (N - R) ≤ μ (N - 1)⁻¹` (`TauCeti.NumberField.exists_div_pow_le_inv`), since
the ratios `μ (k - 1) / μ k` over `k ∈ [R, N)` multiply to `μ (R - 1) / μ (N - 1)` and
`μ (R - 1) ≤ 1`. For that `k`, the last minimum of `S(Q)` satisfies
`ν (M - 1) ^ (N - R) ≥ c₀ · μ (N - 1)` (`TauCeti.NumberField.exists_successiveMinimum_wedge_pow`).
When the weight of the original domain is negative, Minkowski's second theorem makes `μ (N - 1)`
grow with `Q`, so this bound pushes the last minimum of `S(Q)` above `1` for large `Q`; then `S(Q)`
has rank exactly `M - 1`.

## Main results

* `TauCeti.NumberField.exists_pos_mul_approxWeight_wedgeExponent_le`: a quantitative upper
  bound on the wedge weight after a large jump, using `rpow_approxWeight_wedgeExponent_le`
  and the Minkowski lower bound on the last minimum.
* `TauCeti.NumberField.eventually_approxWeight_wedgeExponent_le`: a uniform negative margin
  for the wedge weight when the original weight is bounded away from zero.
* `TauCeti.NumberField.exists_successiveMinimum_wedge`: Lemma 7.5.31, the successive minima of
  the wedge domain.
* `TauCeti.NumberField.exists_successiveMinimum_wedge_pow`: Lemma 7.5.31 combined with (7.41).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  7.5.30, (7.41) and Lemma 7.5.31.
* J.-H. Evertse, *An improvement of the quantitative Subspace theorem*, Compositio Math. 101
  (1996), 225–311.
-/

public section

open Finset Module NumberField NumberField.mixedEmbedding Set.powersetCard
open scoped Pointwise

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-! ### The successive minima of the wedge domain -/

/-- For fixed forms, exterior degree `0 < p`, jump index `k` with `k + p = card ι` and constant
`C > 0`, there is `A > 0` such that `Q ^ approxWeight` of the wedge exponents is at most
`A · (μ (k - 1) / μ k) ^ [K : ℚ]` for all exponents `c`, levels `0 < Q ≠ 1` and bijections `σ`,
where `μ` are the successive minima over `K` of `approxDomain S₀ L c Q`. -/
private theorem exists_pos_rpow_approxWeight_wedgeExponent_le {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) {k p : ℕ} (hp : 0 < p)
    (hkp : k + p = Fintype.card ι) {C : ℝ} (hC : 0 < C) :
    ∃ A : ℝ, 0 < A ∧ ∀ (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}, 0 < Q → Q ≠ 1 →
      ∀ σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι,
      Q ^ approxWeight S₀ (wedgeExponent c p k σ
          ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) ≤
        A * ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) (k - 1) /
          (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) k) ^ finrank ℚ K := by
  have := approxConst_pos hLinf hLfin
  have : 0 < ∏ v ∈ S₀, (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ Fintype.card ι :=
    prod_pos fun v _ ↦ pow_pos (by
      exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v.maximalIdeal).pos) _
  exact ⟨_, by positivity, fun c Q hQ hQ₁ σ ↦
    rpow_approxWeight_wedgeExponent_le hLinf hLfin c hp hkp σ hC hQ hQ₁⟩

/-- A large jump between successive minima forces a weight gap for the wedge exponents
(Bombieri–Gubler, 7.5.30–7.5.32). For `N = card ι`, the wedge weight multiplied by `N²` is
bounded above by the original weight plus `logb Q D`. For nonzero wedge constant, `D > 0`
is independent of the exponents, the level, the jump index and the bijections. The jump bound
follows from `exists_div_pow_le_inv`, since its power and ratio are at most `card ι` and `1`,
respectively. -/
theorem exists_pos_mul_approxWeight_wedgeExponent_le {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) {C : ℝ} (hC : C ≠ 0) :
    ∃ D : ℝ, 0 < D ∧ ∀ (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}, 1 < Q →
      ∀ {k p : ℕ}, 0 < p → k + p = Fintype.card ι →
      ∀ σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι,
        ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) (k - 1) /
          (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) k) ^ Fintype.card ι ≤
          ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)
            (Fintype.card ι - 1))⁻¹ →
        (Fintype.card ι : ℝ) ^ 2 * approxWeight S₀ (wedgeExponent c p k σ
          ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) ≤
          approxWeight S₀ c + Real.logb Q D := by
  let N := Fintype.card ι
  let d := finrank ℚ K
  obtain ⟨A, hA, hlast⟩ := exists_pos_mul_rpow_le_last_successiveMinimum_pow hLinf hLfin
  let B (p : ℕ) : ℝ :=
    ((2 : ℝ) ^ (d * N) * (∏ v ∈ S₀, (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ N) /
      approxConst S₀ L) ^ (N - 1).choose (p - 1) * |C| ^ (N.choose p * d)
  let U := max 1 ((range (N + 1)).sup' nonempty_range_add_one B)
  have hU : 0 < U := lt_max_of_lt_left one_pos
  refine ⟨U ^ (N ^ 2) / A, by positivity, fun c Q hQ k p hp hkp σ hjump ↦ ?_⟩
  set μ := (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)
  set r := μ (k - 1) / μ k
  set w := approxWeight S₀ c
  set W := approxWeight S₀ (wedgeExponent c p k σ μ C Q)
  have hQ₀ : 0 < Q := zero_lt_one.trans hQ
  have hμ (l : ℕ) (hl : l < N) : 0 < μ l := successiveMinimum_approx_pos hLinf hLfin c hQ₀ hl
  have hr : 0 < r := div_pos (hμ _ (by omega)) (hμ _ (by omega))
  have h₁ : Real.logb Q A - w ≤ ((d * N : ℕ) : ℝ) * Real.logb Q (μ (N - 1)) := by
    have h := Real.logb_le_logb_of_le hQ (mul_pos hA (Real.rpow_pos_of_pos hQ₀ _))
      (hlast c hQ₀)
    rwa [Real.logb_mul hA.ne' (Real.rpow_pos_of_pos hQ₀ _).ne',
      Real.logb_rpow hQ₀ hQ.ne', Real.logb_pow, ← sub_eq_add_neg] at h
  have h₂ : W ≤ Real.logb Q U + d * Real.logb Q r := by
    have hBU : B p ≤ U :=
      (le_sup' B (mem_range.2 (by omega))).trans (le_max_right _ _)
    have h : Q ^ W ≤ B p * r ^ d := by
      simpa only [wedgeExponent_abs] using
        rpow_approxWeight_wedgeExponent_le hLinf hLfin c hp hkp σ (abs_pos.2 hC) hQ₀ hQ.ne'
    have h' := h.trans (mul_le_mul_of_nonneg_right hBU (pow_nonneg hr.le d))
    rw [← Real.logb_pow, ← Real.logb_mul hU.ne' (pow_ne_zero _ hr.ne')]
    exact (Real.le_logb_iff_rpow_le hQ (mul_pos hU (pow_pos hr _))).2 h'
  have h₃ : (N : ℝ) * Real.logb Q r ≤ -Real.logb Q (μ (N - 1)) := by
    have h := Real.logb_le_logb_of_le hQ (pow_pos hr _) hjump
    rwa [Real.logb_pow, Real.logb_inv] at h
  have h₄ : (N : ℝ) ^ 2 * W ≤ w + (N : ℝ) ^ 2 * Real.logb Q U - Real.logb Q A := by
    calc
      (N : ℝ) ^ 2 * W ≤ (N : ℝ) ^ 2 * (Real.logb Q U + d * Real.logb Q r) := by gcongr
      _ = (N : ℝ) ^ 2 * Real.logb Q U + ((d * N : ℕ) : ℝ) * (N * Real.logb Q r) := by
        push_cast
        ring
      _ ≤ (N : ℝ) ^ 2 * Real.logb Q U - ((d * N : ℕ) : ℝ) * Real.logb Q (μ (N - 1)) := by
        rw [sub_eq_add_neg, ← mul_neg]
        gcongr
      _ ≤ _ := by linarith
  rw [Real.logb_div (pow_ne_zero _ hU.ne') hA.ne', Real.logb_pow]
  push_cast
  linarith

/-- Beyond a level uniform in the exponents and bijections, a sufficiently large jump yields
wedge weight at most `-ε / (2 * (card ι)^2)` when the original weight is at most `-ε`.
This margin allows an upward perturbation of the wedge exponents while keeping negative weight
(Bombieri–Gubler, 7.5.30–7.5.32). -/
theorem eventually_approxWeight_wedgeExponent_le {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℝ in Filter.atTop,
      ∀ (c : AbsoluteValue K ℝ → ι → ℝ), approxWeight S₀ c ≤ -ε →
      ∀ {k p : ℕ}, 0 < p → k + p = Fintype.card ι →
      ∀ σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι,
        ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) (k - 1) /
          (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) k) ^ Fintype.card ι ≤
          ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)
            (Fintype.card ι - 1))⁻¹ →
        approxWeight S₀ (wedgeExponent c p k σ
          ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) ≤
          -ε / (2 * (Fintype.card ι : ℝ) ^ 2) := by
  by_cases hC : C = 0
  · subst C
    apply Filter.Eventually.of_forall
    intro Q c hc k p hp hkp σ _
    rw [approxWeight_wedgeExponent_zero hp]
    have he : 1 ≤ (Fintype.card ι - 1).choose (p - 1) :=
      Nat.choose_pos (by omega)
    have hN : 1 ≤ Fintype.card ι := by omega
    have he' : (1 : ℝ) ≤ ((Fintype.card ι - 1).choose (p - 1) : ℝ) := Nat.one_le_cast.mpr he
    have hN' : (1 : ℝ) ≤ Fintype.card ι := Nat.one_le_cast.mpr hN
    have hdenom : (1 : ℝ) ≤ 2 * (Fintype.card ι : ℝ) ^ 2 := by nlinarith
    have hw := mul_le_mul_of_nonpos_right he' (hc.trans (neg_nonpos.mpr hε.le))
    apply (le_div_iff₀ (zero_lt_one.trans_le hdenom)).2
    nlinarith only [hw, hc, hdenom, hε]
  obtain ⟨D, -, hD⟩ := exists_pos_mul_approxWeight_wedgeExponent_le hLinf hLfin hC
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.log D / ε)]
    with Q hQ hlog c hc k p hp hkp σ hjump
  have hlogb : Real.logb Q D ≤ ε / 2 := by
    rw [← Real.log_div_log, div_le_iff₀ (Real.log_pos hQ)]
    have h := (div_le_iff₀ hε).1 hlog
    linarith
  have hcard : 0 < Fintype.card ι := by omega
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr hcard
  have h := hD c hQ hp hkp σ hjump
  apply (le_div_iff₀ (mul_pos (by norm_num) (pow_pos hN 2))).2
  nlinarith only [h, hc, hlogb]

variable [LinearOrder ι]

/-- For fixed forms, exterior degree `p` and constant `C > 0`, the last successive minimum of the
wedge domain with jump index `k = card ι - p` is at least `c₀ · μ k / μ (k - 1)` whenever the
others are at most `1`, with `c₀ > 0` independent of the exponents, the level and the bijections.
-/
private theorem exists_pos_mul_div_le_successiveMinimum_wedge {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) {C : ℝ} (hC : 0 < C) (p : ℕ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k : ℕ, 0 < p → k + p = Fintype.card ι →
      ∀ (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}, 0 < Q → Q ≠ 1 →
      ∀ σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι,
      (∀ l < (Fintype.card ι).choose p - 1,
        (approxModule S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
            ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q).successiveMinimum
          (approxBody (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
            ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q) l ≤ 1) →
      c₀ * ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) k /
          (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) (k - 1)) ≤
        (approxModule S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
            ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q).successiveMinimum
          (approxBody (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
            ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q)
          ((Fintype.card ι).choose p - 1) := by
  set N := Fintype.card ι
  set d := finrank ℚ K
  by_cases hpN : 0 < p ∧ p ≤ N
  swap
  · exact ⟨1, one_pos, fun k hp hkp ↦ absurd ⟨hp, by omega⟩ hpN⟩
  have hd : d ≠ 0 := finrank_pos.ne'
  have hMcard : Fintype.card (Set.powersetCard ι p) = N.choose p := fintypeCard p
  -- Minkowski's lower bound for the wedge domain, and the upper bound on its weight.
  obtain ⟨A₁, hA₁, h₁⟩ := exists_pos_mul_rpow_le_successiveMinimum_pow (S₀ := S₀)
    (L := fun v ↦ wedgeForms (L v) p) (fun v ↦ linearIndependent_wedgeForms (hLinf v) p)
    (fun v hv ↦ linearIndependent_wedgeForms (hLfin v hv) p)
    (by rw [hMcard]; exact Nat.choose_pos hpN.2)
  obtain ⟨A₂, hA₂, h₂⟩ :=
    exists_pos_rpow_approxWeight_wedgeExponent_le (k := N - p) hLinf hLfin hpN.1 (by omega) hC
  refine ⟨(A₁ / A₂) ^ (d⁻¹ : ℝ), Real.rpow_pos_of_pos (div_pos hA₁ hA₂) _,
    fun k _ hkp c Q hQ hQ₁ σ hν ↦ ?_⟩
  obtain rfl : k = N - p := by omega
  set μ := (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)
  set L' : AbsoluteValue K ℝ → Set.powersetCard ι p → Dual K (Set.powersetCard ι p → K) :=
    fun v ↦ wedgeForms (L v) p
  set c' := wedgeExponent c p (N - p) σ μ C Q
  set ν := (approxModule S₀ L' c' Q).successiveMinimum (approxBody L' c' Q)
  have hμ₀ : 0 < μ (N - p) := successiveMinimum_approx_pos hLinf hLfin c hQ (by omega)
  have hμ₁ : 0 < μ (N - p - 1) := successiveMinimum_approx_pos hLinf hLfin c hQ (by omega)
  have hr : 0 < μ (N - p) / μ (N - p - 1) := div_pos hμ₀ hμ₁
  have hQw : 0 < Q ^ approxWeight S₀ c' := Real.rpow_pos_of_pos hQ _
  have h₁' : A₁ * Q ^ (-approxWeight S₀ c') ≤ ν (N.choose p - 1) ^ d := by
    have h := h₁ c' hQ fun l hl ↦ hν l (by rwa [hMcard] at hl)
    rwa [hMcard] at h
  have h₂' : Q ^ approxWeight S₀ c' ≤ A₂ * (μ (N - p - 1) / μ (N - p)) ^ d := h₂ c hQ hQ₁ σ
  refine (pow_le_pow_iff_left₀ (mul_pos (Real.rpow_pos_of_pos (div_pos hA₁ hA₂) _) hr).le
    (Submodule.successiveMinimum_nonneg _ _ _) hd).1 ?_
  calc ((A₁ / A₂) ^ (d⁻¹ : ℝ) * (μ (N - p) / μ (N - p - 1))) ^ d
      = A₁ / (A₂ * (μ (N - p - 1) / μ (N - p)) ^ d) := by
        rw [mul_pow, Real.rpow_inv_natCast_pow (div_pos hA₁ hA₂).le hd, div_pow, div_pow]
        field_simp
    _ ≤ A₁ / Q ^ approxWeight S₀ c' := div_le_div_of_nonneg_left hA₁.le hQw h₂'
    _ = A₁ * Q ^ (-approxWeight S₀ c') := by rw [Real.rpow_neg hQ.le, div_eq_mul_inv]
    _ ≤ ν (N.choose p - 1) ^ d := h₁'

/-- The constant of `exists_pos_mul_div_le_successiveMinimum_wedge` can be chosen uniformly in the
exterior degree `p`. -/
private theorem exists_pos_forall_mul_div_le_successiveMinimum_wedge
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) {C : ℝ} (hC : 0 < C) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k p : ℕ, 0 < p → k + p = Fintype.card ι →
      ∀ (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}, 0 < Q → Q ≠ 1 →
      ∀ σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι,
      (∀ l < (Fintype.card ι).choose p - 1,
        (approxModule S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
            ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q).successiveMinimum
          (approxBody (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
            ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q) l ≤ 1) →
      c₀ * ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) k /
          (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) (k - 1)) ≤
        (approxModule S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
            ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q).successiveMinimum
          (approxBody (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
            ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q)
          ((Fintype.card ι).choose p - 1) := by
  set N := Fintype.card ι
  have hc := exists_pos_mul_div_le_successiveMinimum_wedge hLinf hLfin hC
  choose c₀ hc₀ hc₀' using hc
  -- One constant for all exterior degrees `p ≤ N`; the bound is monotone in the constant.
  refine ⟨(range (N + 1)).inf' nonempty_range_add_one c₀, (lt_inf'_iff _).2 fun p _ ↦ hc₀ p,
    fun k p hp hkp c Q hQ hQ₁ σ hν ↦ le_trans ?_ (hc₀' p k hp hkp c hQ hQ₁ σ hν)⟩
  exact mul_le_mul_of_nonneg_right (inf'_le _ (mem_range.2 (by omega)))
    (div_pos (successiveMinimum_approx_pos hLinf hLfin c hQ (by omega))
      (successiveMinimum_approx_pos hLinf hLfin c hQ (by omega))).le

/-- **The successive minima of the wedge domain** (Bombieri–Gubler, Lemma 7.5.31). There is
`C > 0`, depending only on `K` and `ι`, with the following property. For forms `L` linearly
independent at the infinite places and at `S₀` there is `c₀ > 0` such that for all exponents `c`,
levels `0 < Q ≠ 1`, `k` and `0 < p` with `k + p = card ι`, and linearly independent vectors `x l` of
`approxModule S₀ L c Q` realizing its successive minima `μ` over `K`, there are triangular
corrections `y` of `x` and bijections `σ v` such that
* the Plücker vectors of the `p`-subfamilies of `y` meeting `{0, …, k - 1}` lie in the wedge
  domain `S(Q)`, the approximation domain of the wedge forms `wedgeForms (L v) p` with the
  exponents `wedgeExponent c p k σ μ C Q`;
* every successive minimum over `K` of `S(Q)` but the last, of index `(card ι).choose p - 1`, is
  at most `1`;
* the last is at least `c₀ · μ k / μ (k - 1)`. -/
theorem exists_successiveMinimum_wedge :
    ∃ C : ℝ, 0 < C ∧ ∀ {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)},
      (∀ v : InfinitePlace K, LinearIndependent K (L v.val)) →
      (∀ v ∈ S₀, LinearIndependent K (L v.val)) →
      ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} {k p : ℕ}
        {x : Fin (Fintype.card ι) → ι → K}, 0 < Q → Q ≠ 1 → 0 < p →
        k + p = Fintype.card ι → LinearIndependent K x →
        (∀ l, x l ∈ approxModule S₀ L c Q) →
        (∀ l : Fin (Fintype.card ι), (fun j ↦ mixedEmbedding K (x l j)) ∈
          (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l • approxBody L c Q) →
        ∃ (y : Fin (Fintype.card ι) → ι → K) (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι),
          (∀ j, y j - x j ∈ Submodule.span K (x '' Set.Iio j)) ∧
          (∀ J : Set.powersetCard (Fin (Fintype.card ι)) p, (∃ j ∈ J, (j : ℕ) < k) →
            plucker (y ∘ ofFinEmbEquiv.symm J) ∈ approxDomain S₀ (fun v ↦ wedgeForms (L v) p)
              (wedgeExponent c p k σ
                ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q) ∧
          (∀ l < (Fintype.card ι).choose p - 1,
            (approxModule S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
                ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q)
                Q).successiveMinimum
              (approxBody (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
                ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q) l ≤ 1) ∧
          c₀ * ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) k /
              (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) (k - 1)) ≤
            (approxModule S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
                ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q)
                Q).successiveMinimum
              (approxBody (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
                ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q)
              ((Fintype.card ι).choose p - 1) := by
  obtain ⟨C, hC, hE⟩ := exists_plucker_mem_approxDomain_wedgeForms (K := K) (ι := ι)
  refine ⟨C, hC, fun {S₀ L} hLinf hLfin ↦ ?_⟩
  obtain ⟨c₀, hc₀, hlast⟩ := exists_pos_forall_mul_div_le_successiveMinimum_wedge hLinf hLfin hC
  set N := Fintype.card ι
  refine ⟨c₀, hc₀, fun c Q k p x hQ hQ₁ hp hkp hx hxΛ hxB ↦ ?_⟩
  set μ := (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)
  have hμ (l : ℕ) (hl : l < N) : 0 < μ l := successiveMinimum_approx_pos hLinf hLfin c hQ hl
  obtain ⟨y, σ, hspan, hmem⟩ := hE S₀ L c Q x μ hLinf hLfin hQ hQ₁ hx
    (monotoneOn_successiveMinimum_approx hLinf hLfin c hQ) hμ hxΛ
    fun v i l ↦ (mixedEmbedding_mem_smul_approxBody_iff (hμ l l.isLt)).1 (hxB l) v i
  set L' : AbsoluteValue K ℝ → Set.powersetCard ι p → Dual K (Set.powersetCard ι p → K) :=
    fun v ↦ wedgeForms (L v) p
  set c' := wedgeExponent c p k σ μ C Q
  have hL'inf (v : InfinitePlace K) : LinearIndependent K (L' v.val) :=
    linearIndependent_wedgeForms (hLinf v) p
  have hL'fin (v : FinitePlace K) (hv : v ∈ S₀) : LinearIndependent K (L' v.val) :=
    linearIndependent_wedgeForms (hLfin v hv) p
  have hMc : Fintype.card (Set.powersetCard ι p) = N.choose p := fintypeCard p
  -- The Plücker vectors meeting the first `k` indices span a hyperplane inside the span of `S(Q)`.
  have hrank : N.choose p - 1 ≤ finrank K (approxSpan S₀ L' c' Q) := by
    have hy := hx.of_sub_mem_span hspan
    have h₁ := finrank_wedgeSpan_add_one hy hkp
    have h₂ := Submodule.finrank_mono (wedgeSpan_le_iff.2 fun J hJ ↦
      mem_approxSpan_of_mem (hmem k p J hJ) : wedgeSpan k p y ≤ approxSpan S₀ L' c' Q)
    rw [hMc] at h₁
    omega
  have hν (l : ℕ) (hl : l < N.choose p - 1) :
      (approxModule S₀ L' c' Q).successiveMinimum (approxBody L' c' Q) l ≤ 1 :=
    (successiveMinimum_approx_le_one_iff hL'inf hL'fin c' hQ
      (by rw [hMc]; omega)).2 (by omega)
  exact ⟨y, σ, hspan, hmem k p, hν, hlast k p hp hkp c hQ hQ₁ σ hν⟩

/-- **The successive minima of the wedge domain after a large jump** (Bombieri–Gubler, (7.41) and
Lemma 7.5.31). There is `C > 0`, depending only on `K` and `ι`, with the following property. For
forms `L` linearly independent at the infinite places and at `S₀` there is `c₀ > 0` such that for
all exponents `c`, levels `0 < Q ≠ 1` and linearly independent vectors `x l` of
`approxModule S₀ L c Q` realizing its successive minima `μ` over `K`, if the rank
`R = finrank K (approxSpan S₀ L c Q)` satisfies `1 ≤ R < card ι`, then for some `k` with
`R ≤ k < card ι`, and `p = card ι - k`, there are triangular corrections `y` of `x` and bijections
`σ v` such that the Plücker vectors of the `p`-subfamilies of `y` meeting `{0, …, k - 1}` lie in
the wedge domain `S(Q)`, every successive minimum over `K` of `S(Q)` but the last is at most `1`,
and the last, raised to the power `card ι - R`, is at least `c₀ · μ (card ι - 1)`. -/
theorem exists_successiveMinimum_wedge_pow :
    ∃ C : ℝ, 0 < C ∧ ∀ {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)},
      (∀ v : InfinitePlace K, LinearIndependent K (L v.val)) →
      (∀ v ∈ S₀, LinearIndependent K (L v.val)) →
      ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
        {x : Fin (Fintype.card ι) → ι → K}, 0 < Q → Q ≠ 1 →
        0 < finrank K (approxSpan S₀ L c Q) →
        finrank K (approxSpan S₀ L c Q) < Fintype.card ι → LinearIndependent K x →
        (∀ l, x l ∈ approxModule S₀ L c Q) →
        (∀ l : Fin (Fintype.card ι), (fun j ↦ mixedEmbedding K (x l j)) ∈
          (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l • approxBody L c Q) →
        ∃ k, finrank K (approxSpan S₀ L c Q) ≤ k ∧ k < Fintype.card ι ∧
        ∃ (y : Fin (Fintype.card ι) → ι → K) (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι),
          (∀ j, y j - x j ∈ Submodule.span K (x '' Set.Iio j)) ∧
          (∀ J : Set.powersetCard (Fin (Fintype.card ι)) (Fintype.card ι - k),
            (∃ j ∈ J, (j : ℕ) < k) →
            plucker (y ∘ ofFinEmbEquiv.symm J) ∈
              approxDomain S₀ (fun v ↦ wedgeForms (L v) (Fintype.card ι - k))
                (wedgeExponent c (Fintype.card ι - k) k σ
                  ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q) ∧
          (∀ l < (Fintype.card ι).choose (Fintype.card ι - k) - 1,
            (approxModule S₀ (fun v ↦ wedgeForms (L v) (Fintype.card ι - k))
                (wedgeExponent c (Fintype.card ι - k) k σ
                  ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q)
                Q).successiveMinimum
              (approxBody (fun v ↦ wedgeForms (L v) (Fintype.card ι - k))
                (wedgeExponent c (Fintype.card ι - k) k σ
                  ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q) l ≤ 1) ∧
          c₀ * (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)
              (Fintype.card ι - 1) ≤
            (approxModule S₀ (fun v ↦ wedgeForms (L v) (Fintype.card ι - k))
                (wedgeExponent c (Fintype.card ι - k) k σ
                  ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q)
                Q).successiveMinimum
              (approxBody (fun v ↦ wedgeForms (L v) (Fintype.card ι - k))
                (wedgeExponent c (Fintype.card ι - k) k σ
                  ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q)
              ((Fintype.card ι).choose (Fintype.card ι - k) - 1) ^
              (Fintype.card ι - finrank K (approxSpan S₀ L c Q)) := by
  obtain ⟨C, hC, hW⟩ := exists_successiveMinimum_wedge (K := K) (ι := ι)
  refine ⟨C, hC, fun {S₀ L} hLinf hLfin ↦ ?_⟩
  obtain ⟨c₀, hc₀, h⟩ := hW hLinf hLfin
  set N := Fintype.card ι
  -- Shrinking `c₀` to at most `1` makes `c₀ ^ N` a constant for every exponent `N - R ≤ N`.
  refine ⟨min c₀ 1 ^ N, pow_pos (lt_min hc₀ one_pos) _,
    fun c Q x hQ hQ₁ hR hRN hx hxΛ hxB ↦ ?_⟩
  set μ := (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)
  set R := finrank K (approxSpan S₀ L c Q)
  have hbot : approxSpan S₀ L c Q ≠ ⊥ := fun h ↦ hR.ne' (Submodule.finrank_eq_zero.2 h)
  have htop : approxSpan S₀ L c Q ≠ ⊤ := fun h ↦ hRN.ne <| by
    rw [← Module.finrank_fintype_fun_eq_card K, ← finrank_top K (ι → K), ← h]
  obtain ⟨k, hk, hjump⟩ := exists_div_pow_le_inv hLinf hLfin c hQ hbot htop
  obtain ⟨hRk, hkN⟩ := Finset.mem_Ico.1 hk
  obtain ⟨y, σ, hspan, hmem, hν, hlast⟩ :=
    h c (k := k) (p := N - k) hQ hQ₁ (by omega) (by omega) hx hxΛ hxB
  refine ⟨k, hRk, hkN, y, σ, hspan, hmem, hν, ?_⟩
  have hμ (l : ℕ) (hl : l < N) : 0 < μ l := successiveMinimum_approx_pos hLinf hLfin c hQ hl
  have hr : 0 < μ k / μ (k - 1) := div_pos (hμ k hkN) (hμ (k - 1) (by omega))
  have hm : 0 < min c₀ 1 := lt_min hc₀ one_pos
  -- `μ (N - 1) ≤ (μ k / μ (k - 1)) ^ (N - R)` is the jump, inverted.
  have hjump' : μ (N - 1) ≤ (μ k / μ (k - 1)) ^ (N - R) := by
    have h := (le_inv_comm₀ (pow_pos (div_pos (hμ (k - 1) (by omega)) (hμ k hkN)) _)
      (hμ _ (by omega))).1 hjump
    rwa [← inv_pow, inv_div] at h
  calc min c₀ 1 ^ N * μ (N - 1)
      ≤ min c₀ 1 ^ (N - R) * (μ k / μ (k - 1)) ^ (N - R) :=
        mul_le_mul (pow_le_pow_of_le_one hm.le (min_le_right _ _) (by omega)) hjump'
          (hμ _ (by omega)).le (pow_nonneg hm.le _)
    _ = (min c₀ 1 * (μ k / μ (k - 1))) ^ (N - R) := (mul_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity)
        ((mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le).trans hlast) _

end TauCeti.NumberField
