/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

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
`2r ⟪x, ·⟫`, and a `C^k` function times a continuous linear map gains half a power of
`1 + ‖x‖ ^ 2` in its derivative bounds
(`ContinuousLinearMap.exists_norm_iteratedFDeriv_smul_le_one_add_norm_sq_rpow`). The bounds follow
by induction on `k`. Rescaling the argument by `c ≠ 0` changes `1 + ‖x‖ ^ 2` by at most a constant
factor, so `(1 + ‖c x‖ ^ 2) ^ r` satisfies the same bounds.

## Main declarations

* `TauCeti.exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_le`: the derivative bounds for
  `(1 + ‖x‖ ^ 2) ^ r`.
* `TauCeti.contDiff_one_add_norm_sq_rpow`, `TauCeti.contDiff_ofReal_one_add_norm_sq_rpow`: the
  bracket power `(1 + ‖x‖ ^ 2) ^ r` and its complex version are smooth.
* `TauCeti.exists_norm_iteratedFDeriv_ofReal_one_add_norm_sq_rpow_half_le`: the bounds for the
  complex Bessel weight `(1 + ‖x‖ ^ 2) ^ (s / 2)`, in the form of symbol estimates of order `s`.
* `TauCeti.exists_norm_iteratedFDeriv_inner_mul_one_add_norm_sq_rpow_le`: the derivative bounds
  for `⟪x, v⟫ (1 + ‖x‖ ^ 2) ^ r`.
* `TauCeti.exists_norm_iteratedFDeriv_cutoff_smul_le`: the derivative bounds for a `C^N` symbol
  of order `m`, such as a bracket power, times a `C^N` cutoff `χ` localized where
  `1 + ‖x‖ ^ 2 ≍ R ^ 2` and adapted to the scale `R`: for `k ≤ N`, the product is
  `O(R ^ m / R ^ k)` in its `k`-th derivative.
* `TauCeti.exists_one_add_norm_smul_sq_rpow_le`,
  `TauCeti.exists_norm_iteratedFDeriv_one_add_norm_smul_sq_rpow_le`: the bracket power of a
  rescaled argument `c x` and its derivative bounds.
* `TauCeti.one_add_norm_smul_sq_rpow_half_le`: on an annulus `0 < c ≤ ‖ζ‖ ≤ d`, the bracket power
  `(1 + ‖t ζ‖ ^ 2) ^ (u / 2)` is `O(t ^ u)` for `t ≥ 1`.
* `ContinuousLinearMap.exists_norm_iteratedFDeriv_comp_left_le_one_add_norm_sq_rpow`: composing
  on the left with a continuous linear map preserves bracket bounds on derivatives.

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
  · rw [L.iteratedFDeriv_add_two, norm_zero]
    positivity

/-- If the derivatives of order `i ≤ k` of a `C^k` function `g` satisfy the bracket bounds
`‖D^i g x‖ ≤ C_i (1 + ‖x‖ ^ 2) ^ (ρ - i / 2)`, then the `k`-th derivative of `g x • L x`, for a
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

/-- Composing on the left with a continuous linear map `L` preserves a bracket bound
`‖D^k g x‖ ≤ C (1 + ‖x‖ ^ 2) ^ ρ` on the `k`-th derivative of a `C^k` function `g`. -/
theorem exists_norm_iteratedFDeriv_comp_left_le_one_add_norm_sq_rpow {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : F →L[ℝ] G) {g : E → F} {k : ℕ}
    (hg : ContDiff ℝ k g) {ρ : ℝ}
    (hgk : ∃ C, ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ ρ) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ k (fun x ↦ L (g x)) x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ ρ := by
  obtain ⟨C, hC⟩ := hgk
  refine ⟨‖L‖ * C, fun x ↦ ?_⟩
  calc ‖iteratedFDeriv ℝ k (fun x ↦ L (g x)) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ k g x‖ :=
        L.norm_iteratedFDeriv_comp_left hg.contDiffAt le_rfl
    _ ≤ ‖L‖ * (C * (1 + ‖x‖ ^ 2) ^ ρ) := mul_le_mul_of_nonneg_left (hC x) (norm_nonneg L)
    _ = ‖L‖ * C * (1 + ‖x‖ ^ 2) ^ ρ := (mul_assoc _ _ _).symm

end ContinuousLinearMap

namespace TauCeti

section NormedSpace

variable [NormedSpace ℝ E]

/-- **Dyadic cutoffs of a symbol of order `m` are symbols at scale `R`.** Let `w` be a `C^N`
function with the symbol estimates `‖D^i w ξ‖ ≤ C_i (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2)` of order `m` for
`i ≤ N`, and let `a > 0`, `b` and `B : ℕ → ℝ`. There is a constant `K ≥ 0` with the following
property. Let `R > 0` and let `χ` be a `C^N` real function such that
`a R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ≤ b R ^ 2` on the support of `χ` and `‖D^k χ‖ ≤ B k / R ^ k` for `k ≤ N`.
Then
`‖D^k (χ • w)‖ ≤ K R ^ m / R ^ k` for `k ≤ N`: on the support of `χ` the symbol `w` behaves like
the constant `R ^ m`. -/
theorem exists_norm_iteratedFDeriv_cutoff_smul_le {w : E → G} {N : ℕ} (hw : ContDiff ℝ N w)
    {m : ℝ} (hwm : ∀ i ≤ N, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ i w ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m - i) / 2))
    {a b : ℝ} (ha : 0 < a) (B : ℕ → ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ (R : ℝ) (χ : E → ℝ), 0 < R → ContDiff ℝ N χ →
      (∀ ξ ∈ tsupport χ, a * R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 ∧ 1 + ‖ξ‖ ^ 2 ≤ b * R ^ 2) →
      (∀ k ≤ N, ∀ ξ, ‖iteratedFDeriv ℝ k χ ξ‖ ≤ B k / R ^ k) → ∀ k ≤ N, ∀ ξ,
        ‖iteratedFDeriv ℝ k (fun ξ ↦ χ ξ • w ξ) ξ‖ ≤ K * R ^ m / R ^ k := by
  choose! W hW using hwm
  have hW0 {i : ℕ} (hi : i ≤ N) : 0 ≤ W i := by simpa using (norm_nonneg _).trans (hW i hi 0)
  set P : ℕ → ℝ := fun i ↦ max (a ^ ((m - i) / 2)) (b ^ ((m - i) / 2))
  have hP0 (i : ℕ) : 0 ≤ P i := le_max_of_le_left (by positivity)
  -- The Leibniz constant of order `k`, and their sum over `k ≤ N`.
  set S : ℕ → ℝ := fun k ↦
    ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * max (B i) 0 * (W (k - i) * P (k - i))
  have hS0 {k : ℕ} (hk : k ∈ Finset.range (N + 1)) : 0 ≤ S k := Finset.sum_nonneg fun i _ ↦ by
    have := hW0 ((k.sub_le i).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)))
    have := hP0 (k - i); positivity
  refine ⟨∑ k ∈ Finset.range (N + 1), S k, Finset.sum_nonneg fun k hk ↦ hS0 hk,
    fun R χ hR hχ hsupp hB k hk ξ ↦ ?_⟩
  -- By the Leibniz rule, each term `D^i χ D^(k-i) w` is `O(R ^ (-i) R ^ (m - (k - i)))`, which is
  -- `O(R ^ m / R ^ k)`; it vanishes off the support of `χ`.
  have hterm (i : ℕ) (hi : i ∈ Finset.range (k + 1)) :
      (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ ξ‖ * ‖iteratedFDeriv ℝ (k - i) w ξ‖ ≤
        (k.choose i : ℝ) * max (B i) 0 * (W (k - i) * P (k - i)) * (R ^ m / R ^ k) := by
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hkiN : k - i ≤ N := (k.sub_le i).trans hk
    have := hW0 hkiN
    have := hP0 (k - i)
    by_cases hξ : ξ ∈ tsupport χ
    · have hwi : ‖iteratedFDeriv ℝ (k - i) w ξ‖ ≤ W (k - i) * (P (k - i) * R ^ (m - (k - i : ℕ))) :=
        (hW (k - i) hkiN ξ).trans (mul_le_mul_of_nonneg_left
          (one_add_norm_sq_rpow_half_le ha hR (hsupp ξ hξ) _) (hW0 hkiN))
      have hχi : ‖iteratedFDeriv ℝ i χ ξ‖ ≤ max (B i) 0 / R ^ i :=
        (hB i (hik.trans hk) ξ).trans (by gcongr; exact le_max_left _ _)
      have hpow : 1 / R ^ i * R ^ (m - (k - i : ℕ)) = R ^ m / R ^ k := by
        rw [Real.rpow_sub hR, Real.rpow_natCast, ← pow_sub_mul_pow R hik]
        field_simp
      calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ ξ‖ * ‖iteratedFDeriv ℝ (k - i) w ξ‖
          ≤ (k.choose i : ℝ) * (max (B i) 0 / R ^ i) *
              (W (k - i) * (P (k - i) * R ^ (m - (k - i : ℕ)))) := by
            gcongr
        _ = (k.choose i : ℝ) * max (B i) 0 * (W (k - i) * P (k - i)) *
              (1 / R ^ i * R ^ (m - (k - i : ℕ))) := by
            ring
        _ = _ := by rw [hpow]
    · rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hξ (tsupport_iteratedFDeriv_subset _ h)),
        norm_zero, mul_zero, zero_mul]
      positivity
  refine (norm_iteratedFDeriv_smul_le hχ hw ξ (by exact_mod_cast hk)).trans
    ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.sum_mul, mul_div_assoc]
  gcongr
  exact Finset.single_le_sum (fun k hk ↦ hS0 hk) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

/-- Rescaling the argument by `c ≠ 0` changes `(1 + ‖x‖ ^ 2) ^ r` by at most a constant factor. -/
theorem exists_one_add_norm_smul_sq_rpow_le {c : ℝ} (hc : c ≠ 0) (r : ℝ) :
    ∃ C, ∀ x : E, (1 + ‖c • x‖ ^ 2) ^ r ≤ C * (1 + ‖x‖ ^ 2) ^ r := by
  have hc2 : 0 < c ^ 2 := by positivity
  refine ⟨max (max 1 (c ^ 2) ^ r) (min 1 (c ^ 2) ^ r), fun x ↦ ?_⟩
  have hx : 0 < 1 + ‖x‖ ^ 2 := by positivity
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rcases le_total 0 r with hr | hr
  · calc (1 + c ^ 2 * ‖x‖ ^ 2) ^ r ≤ (max 1 (c ^ 2) * (1 + ‖x‖ ^ 2)) ^ r :=
          Real.rpow_le_rpow (by positivity)
            (by nlinarith [le_max_left 1 (c ^ 2), le_max_right 1 (c ^ 2), sq_nonneg ‖x‖]) hr
      _ = max 1 (c ^ 2) ^ r * (1 + ‖x‖ ^ 2) ^ r := Real.mul_rpow (by positivity) hx.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · calc (1 + c ^ 2 * ‖x‖ ^ 2) ^ r ≤ (min 1 (c ^ 2) * (1 + ‖x‖ ^ 2)) ^ r :=
          Real.rpow_le_rpow_of_nonpos (mul_pos (lt_min one_pos hc2) hx)
            (by nlinarith [min_le_left 1 (c ^ 2), min_le_right 1 (c ^ 2), sq_nonneg ‖x‖]) hr
      _ = min 1 (c ^ 2) ^ r * (1 + ‖x‖ ^ 2) ^ r :=
          Real.mul_rpow (lt_min one_pos hc2).le hx.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- On the annulus `0 < c ≤ ‖ζ‖ ≤ d`, every power of the Japanese bracket of `t ζ` with `t ≥ 1` is
at most a multiple of `t ^ u`: `(1 + ‖t ζ‖ ^ 2) ^ (u / 2) ≤ max ((c ^ 2) ^ (u / 2))
((1 + d ^ 2) ^ (u / 2)) t ^ u`. -/
theorem one_add_norm_smul_sq_rpow_half_le {c d t : ℝ} (hc : 0 < c) (ht : 1 ≤ t) {ζ : E}
    (hζ : c ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ d) (u : ℝ) :
    (1 + ‖t • ζ‖ ^ 2) ^ (u / 2) ≤ max ((c ^ 2) ^ (u / 2)) ((1 + d ^ 2) ^ (u / 2)) * t ^ u := by
  have ht0 : 0 < t := one_pos.trans_le ht
  have htζ : ‖t • ζ‖ = t * ‖ζ‖ := by rw [norm_smul, Real.norm_of_nonneg ht0.le]
  have hlo := mul_self_le_mul_self (by positivity) (mul_le_mul_of_nonneg_left hζ.1 ht0.le)
  have hhi := mul_self_le_mul_self (by positivity) (mul_le_mul_of_nonneg_left hζ.2 ht0.le)
  exact one_add_norm_sq_rpow_half_le (by positivity) ht0
    ⟨by rw [htζ]; nlinarith, by rw [htζ]; nlinarith [one_le_pow₀ (n := 2) ht]⟩ u

end NormedSpace

variable [InnerProductSpace ℝ E]

/-- The bracket power `(1 + ‖x‖ ^ 2) ^ r` is smooth. -/
theorem contDiff_one_add_norm_sq_rpow (r : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun x : E ↦ (1 + ‖x‖ ^ 2) ^ r :=
  (contDiff_const.add (contDiff_norm_sq ℝ)).rpow_const_of_ne fun x ↦ by positivity

/-- The complex-valued bracket power `(1 + ‖x‖ ^ 2) ^ r` is smooth. -/
theorem contDiff_ofReal_one_add_norm_sq_rpow (r : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ r : ℝ) : ℂ) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_one_add_norm_sq_rpow r)

/-- The derivative of `(1 + ‖x‖ ^ 2) ^ r` is `(1 + ‖x‖ ^ 2) ^ (r - 1)` times `2r ⟪x, ·⟫`, in the
strict sense. -/
theorem hasStrictFDerivAt_one_add_norm_sq_rpow (r : ℝ) (x : E) :
    HasStrictFDerivAt (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ r)
      ((1 + ‖x‖ ^ 2) ^ (r - 1) • ((2 * r) • innerSL ℝ x)) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).const_add 1).rpow_const (p := r)
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
      funext fun x ↦ (hasStrictFDerivAt_one_add_norm_sq_rpow r x).hasFDerivAt.fderiv
    obtain ⟨C, hC⟩ := ((2 * r) • innerSL ℝ).exists_norm_iteratedFDeriv_smul_le_one_add_norm_sq_rpow
        (contDiff_one_add_norm_sq_rpow (r - 1))
        (ρ := r - 1) fun i hi ↦ ih i (Nat.lt_succ_of_le hi) (r - 1)
    refine ⟨C, fun x ↦ ?_⟩
    rw [← norm_iteratedFDeriv_fderiv, hderiv]
    convert hC x using 3
    push_cast
    ring

/-- **The complex Bessel weight is a symbol.** The complex-valued bracket power
`(1 + ‖x‖ ^ 2) ^ (s / 2)` satisfies the symbol estimates of order `s`:
`‖D^k (1 + ‖x‖ ^ 2) ^ (s / 2)‖ ≤ C (1 + ‖x‖ ^ 2) ^ ((s - k) / 2)`. It is the symbol of the Bessel
potential of order `s`. -/
theorem exists_norm_iteratedFDeriv_ofReal_one_add_norm_sq_rpow_half_le (s : ℝ) (k : ℕ) :
    ∃ C, ∀ x : E, ‖iteratedFDeriv ℝ k (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) x‖ ≤
      C * (1 + ‖x‖ ^ 2) ^ ((s - k) / 2) := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_le (E := E) (s / 2) k
  refine ⟨C, fun x ↦ ?_⟩
  calc _ = ‖iteratedFDeriv ℝ k (fun x : E ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)) x‖ :=
        Complex.ofRealLI.norm_iteratedFDeriv_comp_left
          (contDiff_one_add_norm_sq_rpow (s / 2)).contDiffAt le_rfl
    _ ≤ _ := (hC x).trans_eq (by rw [sub_div])

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
    (contDiff_one_add_norm_sq_rpow r)
    fun i _ ↦ exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_le r i

/-- **Derivative bounds for a rescaled bracket power.** For `c ≠ 0`, every real `r` and every
`k`, `‖D^k (1 + ‖c x‖ ^ 2) ^ r‖ ≤ C (1 + ‖x‖ ^ 2) ^ (r - k / 2)`. -/
theorem exists_norm_iteratedFDeriv_one_add_norm_smul_sq_rpow_le {c : ℝ} (hc : c ≠ 0) (r : ℝ)
    (k : ℕ) :
    ∃ C, ∀ x : E, ‖iteratedFDeriv ℝ k (fun x : E ↦ (1 + ‖c • x‖ ^ 2) ^ r) x‖ ≤
      C * (1 + ‖x‖ ^ 2) ^ (r - k / 2) := by
  set f : E → ℝ := fun x ↦ (1 + ‖x‖ ^ 2) ^ r
  have hf : ContDiff ℝ k f := contDiff_one_add_norm_sq_rpow r
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_one_add_norm_sq_rpow_le (E := E) r k
  obtain ⟨K, hK⟩ := exists_one_add_norm_smul_sq_rpow_le (E := E) hc (r - k / 2)
  refine ⟨|c| ^ k * max C 0 * K, fun x ↦ ?_⟩
  -- The `k`-th derivative of `x ↦ f (c • x)` is `c ^ k` times that of `f` at `c • x`.
  rw [iteratedFDeriv_comp_const_smul c hf, norm_smul, norm_pow, Real.norm_eq_abs]
  calc |c| ^ k * ‖iteratedFDeriv ℝ k f (c • x)‖
      ≤ |c| ^ k * (max C 0 * (1 + ‖c • x‖ ^ 2) ^ (r - k / 2)) := by
        gcongr
        exact (hC (c • x)).trans (by gcongr; exact le_max_left _ _)
    _ ≤ |c| ^ k * (max C 0 * (K * (1 + ‖x‖ ^ 2) ^ (r - k / 2))) := by
        gcongr
        exact hK x
    _ = |c| ^ k * max C 0 * K * (1 + ‖x‖ ^ 2) ^ (r - k / 2) := by ring

end TauCeti
