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

## References

* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Section 1.3 (Bessel potentials).
* M. Taylor, *Partial Differential Equations I*, Chapter 4, §1.
-/

public section

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

end TauCeti
