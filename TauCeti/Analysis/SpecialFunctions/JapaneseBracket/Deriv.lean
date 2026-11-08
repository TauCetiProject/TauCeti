/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Derivatives of powers of the Japanese bracket

On a real inner product space `E`, write `⟨x⟩ = (1 + ‖x‖ ^ 2) ^ (1 / 2)` for the Japanese bracket.
For every real `r` and every `k`, the `k`-th derivative of `⟨x⟩ ^ (2r) = (1 + ‖x‖ ^ 2) ^ r` decays
like the bracket power of order `2r - k`:

`‖D^k (1 + ‖x‖ ^ 2) ^ r‖ ≤ C (1 + ‖x‖ ^ 2) ^ (r - k / 2)`.

Each derivative gains one power of `⟨x⟩⁻¹`; this is the statement that `⟨x⟩ ^ (2r)` is a symbol of
order `2r` in Hörmander's sense. The same holds for `⟪x, v⟫ (1 + ‖x‖ ^ 2) ^ r`, of order `2r + 1`.
For `r ≤ 0`, and for `r ≤ -1 / 2` in the case of `⟪x, v⟫ (1 + ‖x‖ ^ 2) ^ r`, these symbols have
nonpositive order. Those are the estimates that make the symbols of the Bessel potentials of
nonpositive order, and of first derivatives composed with the Bessel potential of order `-1`,
multipliers of Mihlin type, and so bounded on `Lᵖ` for `1 < p < ∞`.

The derivative of `(1 + ‖x‖ ^ 2) ^ r` is `(1 + ‖x‖ ^ 2) ^ (r - 1)` times the linear map
`2r ⟪x, ·⟫`, and a smooth function times a continuous linear map gains half a power of
`1 + ‖x‖ ^ 2` in its derivative bounds
(`ContinuousLinearMap.exists_norm_iteratedFDeriv_smul_le_one_add_norm_sq_rpow`). The bounds follow
by induction on `k`.

## Main declarations

* `TauCeti.exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_le`: the derivative bounds for
  `(1 + ‖x‖ ^ 2) ^ r`.
* `TauCeti.exists_norm_iteratedFDeriv_inner_mul_one_add_norm_sq_rpow_le`: the derivative bounds
  for `⟪x, v⟫ (1 + ‖x‖ ^ 2) ^ r`.
* `TauCeti.exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_mul_le`: the derivative bounds for a
  bracket power times a smooth cutoff `χ` localized where `1 + ‖x‖ ^ 2 ≍ R ^ 2` and adapted to the
  scale `R`: the product is `O(R ^ s / R ^ k)` in its `k`-th derivative.

## References

* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Section 1.3 (Bessel potentials).
* M. Taylor, *Partial Differential Equations I*, Chapter 4, §1.
-/

public section

open scoped ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace ContinuousLinearMap

variable [NormedSpace ℝ E]

/-- A continuous linear map grows like `(1 + ‖x‖ ^ 2) ^ (1 / 2)`, its derivative is constant, and
its higher derivatives vanish: `‖D^j L x‖ ≤ ‖L‖ (1 + ‖x‖ ^ 2) ^ ((1 - j) / 2)` for every `j`. -/
theorem norm_iteratedFDeriv_le_one_add_norm_sq_rpow (L : E →L[ℝ] G) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j L x‖ ≤ ‖L‖ * (1 + ‖x‖ ^ 2) ^ ((1 - j : ℝ) / 2) := by
  rcases j with _ | _ | j
  · rw [norm_iteratedFDeriv_zero]
    refine (L.le_opNorm x).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg L))
    rw [Nat.cast_zero, sub_zero, ← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by linarith)
  · rw [norm_iteratedFDeriv_one, L.fderiv]
    simp
  · -- The derivative of `L` is the constant map `L`, whose derivatives of positive order vanish.
    have hL : fderiv ℝ L = fun _ ↦ L := funext fun _ ↦ L.fderiv
    have h : iteratedFDeriv ℝ (j + 2) L x = 0 := by
      rw [← norm_eq_zero, ← norm_iteratedFDeriv_fderiv, hL,
        iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]
      simp
    rw [h, norm_zero]
    positivity

/-- If the first `k` derivatives of a smooth function `g` satisfy the bracket bounds
`‖D^i g x‖ ≤ C (1 + ‖x‖ ^ 2) ^ (ρ - i / 2)`, then the `k`-th derivative of `g x • L x`, for a
continuous linear map `L`, satisfies the bracket bound of order `ρ + 1 / 2`. -/
theorem exists_norm_iteratedFDeriv_smul_le_one_add_norm_sq_rpow (L : E →L[ℝ] G) {g : E → ℝ}
    {k : ℕ} (hg : ContDiff ℝ k g) {ρ : ℝ}
    (hgk : ∀ i ≤ k, ∃ C, ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ (ρ - i / 2)) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ k (fun x ↦ g x • L x) x‖ ≤
      C * (1 + ‖x‖ ^ 2) ^ (ρ + 1 / 2 - k / 2) := by
  choose! C hC using hgk
  refine ⟨∑ i ∈ Finset.range (k + 1), k.choose i * C i * ‖L‖, fun x ↦ ?_⟩
  refine (norm_iteratedFDeriv_smul_le hg L.contDiff x le_rfl).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  -- In the Leibniz expansion, the `i`-th term carries `D^i g` and `D^(k - i) L`, whose bracket
  -- exponents add up to `ρ + 1 / 2 - k / 2`.
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hw : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have h₁ := hC i hik x
  have h₀ : 0 ≤ C i * (1 + ‖x‖ ^ 2) ^ (ρ - i / 2) := (norm_nonneg _).trans h₁
  have h₂ := L.norm_iteratedFDeriv_le_one_add_norm_sq_rpow (k - i) x
  have hexp : (1 + ‖x‖ ^ 2) ^ (ρ - i / 2) * (1 + ‖x‖ ^ 2) ^ ((1 - (k - i : ℕ) : ℝ) / 2) =
      (1 + ‖x‖ ^ 2) ^ (ρ + 1 / 2 - k / 2) := by
    rw [← Real.rpow_add hw, Nat.cast_sub hik]
    ring_nf
  calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i g x‖ * ‖iteratedFDeriv ℝ (k - i) L x‖
      ≤ k.choose i * (C i * (1 + ‖x‖ ^ 2) ^ (ρ - i / 2)) *
          (‖L‖ * (1 + ‖x‖ ^ 2) ^ ((1 - (k - i : ℕ) : ℝ) / 2)) := by
        gcongr
    _ = k.choose i * C i * ‖L‖ * (1 + ‖x‖ ^ 2) ^ (ρ + 1 / 2 - k / 2) := by
        rw [← hexp]
        ring

end ContinuousLinearMap

namespace TauCeti

/-- Where `a R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ≤ b R ^ 2`, every power `(1 + ‖ξ‖ ^ 2) ^ (u / 2)` of the Japanese
bracket is at most `max (a ^ (u / 2)) (b ^ (u / 2)) R ^ u`. -/
theorem one_add_norm_sq_rpow_half_le {a b R : ℝ} (ha : 0 < a) (hR : 0 < R) {ξ : E}
    (hξ : a * R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ∧ 1 + ‖ξ‖ ^ 2 ≤ b * R ^ 2) (u : ℝ) :
    (1 + ‖ξ‖ ^ 2) ^ (u / 2) ≤ max (a ^ (u / 2)) (b ^ (u / 2)) * R ^ u := by
  have hb : 0 < b := pos_of_mul_pos_left ((mul_pos ha (by positivity)).trans_le
    (hξ.1.trans hξ.2)) (by positivity)
  have hRu (c : ℝ) (hc : 0 < c) : (c * R ^ 2) ^ (u / 2) = c ^ (u / 2) * R ^ u := by
    rw [Real.mul_rpow hc.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    congr 2
    push_cast
    ring
  rcases le_total 0 u with hu | hu
  · calc (1 + ‖ξ‖ ^ 2) ^ (u / 2) ≤ (b * R ^ 2) ^ (u / 2) :=
          Real.rpow_le_rpow (by positivity) hξ.2 (by positivity)
      _ ≤ _ := by
          rw [hRu b hb]
          gcongr
          exact le_max_right _ _
  · calc (1 + ‖ξ‖ ^ 2) ^ (u / 2) ≤ (a * R ^ 2) ^ (u / 2) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hξ.1 (by linarith)
      _ ≤ _ := by
          rw [hRu a ha]
          gcongr
          exact le_max_left _ _

variable [InnerProductSpace ℝ E]

/-- The derivative of `(1 + ‖x‖ ^ 2) ^ r` is `(1 + ‖x‖ ^ 2) ^ (r - 1)` times `2r ⟪x, ·⟫`. -/
theorem hasFDerivAt_one_add_norm_sq_rpow (r : ℝ) (x : E) :
    HasFDerivAt (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ r)
      ((1 + ‖x‖ ^ 2) ^ (r - 1) • ((2 * r) • innerSL ℝ x)) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add 1).rpow_const (p := r)
    (Or.inl (by positivity))
  convert h using 1
  ext v
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  ring

/-- **Derivative bounds for powers of the Japanese bracket.** For every real `r` and every `k`,
`‖D^k (1 + ‖x‖ ^ 2) ^ r‖ ≤ C (1 + ‖x‖ ^ 2) ^ (r - k / 2)`: each derivative of
`(1 + ‖x‖ ^ 2) ^ r` gains a factor `(1 + ‖x‖ ^ 2) ^ (-1 / 2)`. -/
theorem exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_le (r : ℝ) (k : ℕ) :
    ∃ C, ∀ x : E, ‖iteratedFDeriv ℝ k (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ r) x‖ ≤
      C * (1 + ‖x‖ ^ 2) ^ (r - k / 2) := by
  induction k using Nat.strong_induction_on generalizing r with
  | _ k ih =>
  rcases k with _ | k
  · refine ⟨1, fun x ↦ ?_⟩
    rw [norm_iteratedFDeriv_zero, Real.norm_of_nonneg (by positivity)]
    simp
  · -- The derivative is a lower bracket power times a continuous linear map.
    have hderiv : fderiv ℝ (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ r) =
        fun x ↦ (1 + ‖x‖ ^ 2) ^ (r - 1) • ((2 * r) • innerSL ℝ) x :=
      funext fun x ↦ (hasFDerivAt_one_add_norm_sq_rpow r x).fderiv
    have hcont : ContDiff ℝ k (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (r - 1)) :=
      (contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne fun x ↦ by positivity
    obtain ⟨C, hC⟩ :=
      ((2 * r) • innerSL ℝ).exists_norm_iteratedFDeriv_smul_le_one_add_norm_sq_rpow hcont
        (ρ := r - 1) fun i hi ↦ ih i (Nat.lt_succ_of_le hi) (r - 1)
    refine ⟨C, fun x ↦ ?_⟩
    rw [← norm_iteratedFDeriv_fderiv, hderiv]
    convert hC x using 3
    push_cast
    ring

/-- **Derivative bounds for a linear function times a bracket power.** For every `v`, every real
`r` and every `k`, `‖D^k (⟪x, v⟫ (1 + ‖x‖ ^ 2) ^ r)‖ ≤ C (1 + ‖x‖ ^ 2) ^ (r + 1 / 2 - k / 2)`. -/
theorem exists_norm_iteratedFDeriv_inner_mul_one_add_norm_sq_rpow_le (v : E) (r : ℝ) (k : ℕ) :
    ∃ C, ∀ x : E, ‖iteratedFDeriv ℝ k (fun x : E ↦ inner ℝ x v * (1 + ‖x‖ ^ 2) ^ r) x‖ ≤
      C * (1 + ‖x‖ ^ 2) ^ (r + 1 / 2 - k / 2) := by
  have hfun : (fun x : E ↦ inner ℝ x v * (1 + ‖x‖ ^ 2) ^ r) =
      fun x ↦ (1 + ‖x‖ ^ 2) ^ r • innerSL ℝ v x := by
    ext x
    rw [innerSL_apply_apply, real_inner_comm, smul_eq_mul, mul_comm]
  rw [hfun]
  exact (innerSL ℝ v).exists_norm_iteratedFDeriv_smul_le_one_add_norm_sq_rpow
    ((contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne fun x ↦ by positivity)
    fun i _ ↦ exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_le r i

/-- **Bessel-weighted dyadic cutoffs are symbols of order `s` at scale `R`.** Let `a > 0`, `b`,
`N` and `B : ℕ → ℝ`. There is a constant `K ≥ 0` with the following property. Let `R > 0` and let
`χ` be a smooth real function such that `a R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ≤ b R ^ 2` on the support of `χ` and
`‖D^k χ‖ ≤ B k / R ^ k` for `k ≤ N`. Then `‖D^k ((1 + ‖·‖ ^ 2) ^ (s / 2) χ)‖ ≤ K R ^ s / R ^ k` for
`k ≤ N`. -/
theorem exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_mul_le (s : ℝ) {a b : ℝ}
    (ha : 0 < a) (N : ℕ) (B : ℕ → ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ (R : ℝ) (χ : E → ℝ), 0 < R → ContDiff ℝ ∞ χ →
      (∀ ξ ∈ tsupport χ, a * R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ∧ 1 + ‖ξ‖ ^ 2 ≤ b * R ^ 2) →
      (∀ k ≤ N, ∀ ξ, ‖iteratedFDeriv ℝ k χ ξ‖ ≤ B k / R ^ k) → ∀ k ≤ N, ∀ ξ,
        ‖iteratedFDeriv ℝ k (fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2) * χ ξ) ξ‖ ≤ K * R ^ s / R ^ k := by
  -- Derivative bounds for the weight `w ξ = (1 + ‖ξ‖ ^ 2) ^ (s / 2)`, a symbol of order `s`.
  choose W hW using fun i : ℕ ↦ exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_le (E := E)
    (s / 2) i
  have hW0 (i : ℕ) : 0 ≤ W i := by simpa using (norm_nonneg _).trans (hW i 0)
  set P : ℕ → ℝ := fun i ↦ max (a ^ ((s - i) / 2)) (b ^ ((s - i) / 2))
  have hP0 (i : ℕ) : 0 ≤ P i := le_max_of_le_left (by positivity)
  -- The Leibniz constant of order `k`, and their sum over `k ≤ N`.
  set S : ℕ → ℝ := fun k ↦
    ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (W i * P i) * max (B (k - i)) 0
  have hS0 (k : ℕ) : 0 ≤ S k := Finset.sum_nonneg fun i _ ↦ by
    have := hW0 i; have := hP0 i; positivity
  refine ⟨∑ k ∈ Finset.range (N + 1), S k, Finset.sum_nonneg fun k _ ↦ hS0 k,
    fun R χ hR hχ hsupp hB k hk ξ ↦ ?_⟩
  set w : E → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (s / 2)
  have hw : ContDiff ℝ ∞ w :=
    (contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne fun ξ ↦ by positivity
  -- By the Leibniz rule, each term `D^i w D^(k-i) χ` is `O(R ^ (s - i) R ^ (-(k - i)))`, which is
  -- `O(R ^ s / R ^ k)`; it vanishes off the support of `χ`.
  have hterm (i : ℕ) (hi : i ∈ Finset.range (k + 1)) :
      (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i w ξ‖ * ‖iteratedFDeriv ℝ (k - i) χ ξ‖ ≤
        (k.choose i : ℝ) * (W i * P i) * max (B (k - i)) 0 * (R ^ s / R ^ k) := by
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have := hW0 i
    have := hP0 i
    by_cases hξ : ξ ∈ tsupport χ
    · have hwi : ‖iteratedFDeriv ℝ i w ξ‖ ≤ W i * (P i * R ^ (s - i)) := by
        refine (hW i ξ).trans ?_
        rw [← sub_div]
        exact mul_le_mul_of_nonneg_left (one_add_norm_sq_rpow_half_le ha hR (hsupp ξ hξ) (s - i))
          (hW0 i)
      have hχi : ‖iteratedFDeriv ℝ (k - i) χ ξ‖ ≤ max (B (k - i)) 0 / R ^ (k - i) :=
        (hB (k - i) ((Nat.sub_le k i).trans hk) ξ).trans (by gcongr; exact le_max_left _ _)
      have hpow : R ^ (s - i) * (1 / R ^ (k - i)) = R ^ s / R ^ k := by
        rw [Real.rpow_sub hR, Real.rpow_natCast, ← pow_sub_mul_pow R hik]
        field_simp
      calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i w ξ‖ * ‖iteratedFDeriv ℝ (k - i) χ ξ‖
          ≤ (k.choose i : ℝ) * (W i * (P i * R ^ (s - i))) *
              (max (B (k - i)) 0 / R ^ (k - i)) := by
            gcongr
        _ = (k.choose i : ℝ) * (W i * P i) * max (B (k - i)) 0 *
              (R ^ (s - i) * (1 / R ^ (k - i))) := by
            ring
        _ = _ := by rw [hpow]
    · rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hξ (tsupport_iteratedFDeriv_subset _ h)),
        norm_zero, mul_zero]
      positivity
  refine (norm_iteratedFDeriv_mul_le hw hχ ξ (by exact_mod_cast le_top)).trans
    ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.sum_mul, mul_div_assoc]
  gcongr
  exact Finset.single_le_sum (fun k _ ↦ hS0 k) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

end TauCeti
