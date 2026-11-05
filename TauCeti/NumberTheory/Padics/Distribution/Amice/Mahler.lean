/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Amice.Isometry
public import TauCeti.NumberTheory.Padics.Distribution.Amice.Norm

/-!
# Analytic stages in Mahler coordinates

Let `E` be a complete ultrametric normed `ℤ_p`-module with contractive action, and put
`m_h(n) = ⌊n / pʰ⌋!`. By Amice's theorem (`TauCeti.AnalyticStage.amiceEquiv`) every coefficient
vector `c` in the analytic stage `LA_h(E)` is `∑ₙ e_{h,n} • dₙ` for a unique null sequence `d`
with `‖c‖ = supₙ ‖dₙ‖`, where `e_{h,n}(x) = m_h(n) (x choose n)`. Evaluating, the function
defined by `c` has Mahler coefficients

`aₙ = m_h(n) • dₙ`   (`TauCeti.AnalyticStage.mahlerEquiv_eval`),

so evaluation followed by Mahler's isometry `PadicInt.mahlerEquiv` is diagonal in Amice
coordinates. No torsion-freeness of `E` is needed for this.

When `E` is moreover a `ℚ_p`-module, the factorials can be inverted, and the Amice coordinates are
recovered from the Mahler coefficients as `dₙ = m_h(n)⁻¹ • aₙ`. This describes the functions in the
image of `LA_h(E)` and their norms entirely in terms of Mahler coefficients: a continuous function
`f : ℤ_p → E` with Mahler coefficients `aₙ` is analytic on the discs of level `h` exactly when
`m_h(n)⁻¹ • aₙ → 0`, that is, `‖aₙ‖ / ‖m_h(n)‖ → 0` when the norm is compatible with the
`ℚ_p`-action. The vector representing it then has norm `supₙ ‖aₙ‖ / ‖m_h(n)‖`.

Comparing the weights `‖m_h(n)‖` with the powers of the radii
`r_h = p ^ (-1 / ((p - 1) pʰ))`, which increase to `1`, gives Amice's characterisation of
locally analytic functions: `f` is analytic on the discs of some level exactly when its Mahler
coefficients decay exponentially, `‖aₙ‖ ≤ C ρⁿ` for some `C` and `0 ≤ ρ < 1`. The forward
direction holds for every `E`: at level `h` the Mahler coefficients are bounded by
`p ‖c‖ r_{h+1}ⁿ`.

## Main results

* `TauCeti.AnalyticStage.mahlerEquiv_eval`: the Mahler coefficients of an evaluated coefficient
  vector are `⌊n / pʰ⌋!` times its Amice coordinates.
* `TauCeti.AnalyticStage.norm_mahlerEquiv_eval_le`: the Mahler coefficients of an evaluated
  coefficient vector at level `h` are bounded by `p ‖c‖ r_{h+1}ⁿ`.
* `TauCeti.AnalyticStage.amiceEquiv_symm_apply`: over `ℚ_p`, the Amice coordinates are the Mahler
  coefficients divided by `⌊n / pʰ⌋!`.
* `TauCeti.AnalyticStage.mem_range_eval_iff`,
  `TauCeti.AnalyticStage.mem_range_eval_iff_tendsto_norm_div`: a continuous function is analytic on
  the discs of level `h` exactly when its Mahler coefficients divided by `⌊n / pʰ⌋!` tend to zero.
* `TauCeti.AnalyticStage.norm_eq_iSup_norm_mahlerEquiv_div`: the norm of a coefficient vector is
  `supₙ ‖aₙ‖ / ‖⌊n / pʰ⌋!‖`, where `aₙ` are the Mahler coefficients of its evaluation.
* `TauCeti.AnalyticStage.exists_mem_range_eval_iff`: a continuous function is analytic at some level
  exactly when its Mahler coefficients decay exponentially.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

open Filter Topology Nat PadicInt
open scoped ZeroAtInfty

variable {p : ℕ} [hp : Fact p.Prime]

namespace TauCeti.AnalyticStage

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-! ### Mahler coefficients of evaluated coefficient vectors -/

section Diagonal

variable {h : ℕ}

/-- The Mahler coefficients of the evaluation of Amice's series `∑ₙ e_{h,n} • cₙ` are
`⌊n / pʰ⌋! • cₙ`. -/
@[simp]
theorem mahlerEquiv_eval_amiceMap (c : C₀(ℕ, E)) (n : ℕ) :
    mahlerEquiv E (eval S (amiceMap p h S c)) n = (n / p ^ h)! • c n := by
  have hc : Tendsto (fun n ↦ (n / p ^ h)! • c n) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n ↦ ?_) (tendsto_zero_iff_norm_tendsto_zero.mp
      (by simpa [Nat.cofinite_eq_atTop] using c.tendsto_cofinite))
    rw [← Nat.cast_smul_eq_nsmul ℤ_[p]]
    exact (norm_smul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one _))
  rw [eval_amiceMap, mahlerEquiv_apply]
  exact fwdDiff_mahlerSeries hc n

/-- **Evaluation is diagonal in Amice and Mahler coordinates.** The `n`-th Mahler coefficient of
the function defined by `c ∈ LA_h(E)` is `⌊n / pʰ⌋!` times the `n`-th Amice coordinate of `c`. -/
theorem mahlerEquiv_eval (c : AnalyticStage p h E) (n : ℕ) :
    mahlerEquiv E (eval S c) n = (n / p ^ h)! • (amiceEquiv p h S).symm c n := by
  conv_lhs => rw [← (amiceEquiv p h S).apply_symm_apply c, amiceEquiv_apply]
  exact mahlerEquiv_eval_amiceMap S _ n

/-- At level `h`, the Mahler coefficients of the function defined by `c ∈ LA_h(E)` are bounded by
`p ‖c‖ r_{h+1}ⁿ`. -/
theorem norm_mahlerEquiv_eval_le (c : AnalyticStage p h E) (n : ℕ) :
    ‖mahlerEquiv E (eval S c) n‖ ≤ p * ‖c‖ * amiceRadius p (h + 1) ^ n := by
  rw [mahlerEquiv_eval, ← Nat.cast_smul_eq_nsmul ℤ_[p], mul_right_comm]
  refine (norm_smul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _)
    (by have := (amiceRadius_pos (p := p) (h + 1)).le; positivity))
  · simpa [PadicInt.norm_def] using norm_factorial_le_mul_amiceRadius_succ_pow (p := p) h n
  · exact (((amiceEquiv p h S).symm c).norm_coe_le_norm n).trans_eq
      ((amiceEquiv p h S).symm.norm_map c)

end Diagonal

/-! ### Coefficients in a `ℚ_p`-module -/

section Rational

variable {h : ℕ} [Module ℚ_[p] E]

/-- Over `ℚ_p`, the Amice coordinates of `c ∈ LA_h(E)` are the Mahler coefficients of its
evaluation divided by `⌊n / pʰ⌋!`. -/
theorem amiceEquiv_symm_apply (c : AnalyticStage p h E) (n : ℕ) :
    (amiceEquiv p h S).symm c n = ((n / p ^ h)! : ℚ_[p])⁻¹ • mahlerEquiv E (eval S c) n := by
  rw [mahlerEquiv_eval, ← Nat.cast_smul_eq_nsmul ℚ_[p], smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast factorial_ne_zero _), one_smul]

/-- **The Mahler-coefficient criterion for analyticity.** A continuous function `f : ℤ_p → E` with
Mahler coefficients `aₙ` is the evaluation of a coefficient vector in `LA_h(E)` exactly when
`⌊n / pʰ⌋!⁻¹ • aₙ → 0`. -/
theorem mem_range_eval_iff {f : C(ℤ_[p], E)} :
    f ∈ Set.range (eval (p := p) (h := h) S) ↔
      Tendsto (fun n ↦ ((n / p ^ h)! : ℚ_[p])⁻¹ • mahlerEquiv E f n) atTop (𝓝 0) := by
  constructor
  · rintro ⟨c, rfl⟩
    simpa [← amiceEquiv_symm_apply, Nat.cofinite_eq_atTop] using
      ((amiceEquiv p h S).symm c).tendsto_cofinite
  · intro hf
    let d : C₀(ℕ, E) :=
      ZeroAtInftyContinuousMap.mkOfDiscrete _ (by rwa [Nat.cofinite_eq_atTop])
    refine ⟨amiceMap p h S d, (mahlerEquiv E).injective (ZeroAtInftyContinuousMap.ext fun n ↦ ?_)⟩
    rw [mahlerEquiv_eval_amiceMap, ZeroAtInftyContinuousMap.coe_mkOfDiscrete,
      ← Nat.cast_smul_eq_nsmul ℚ_[p], smul_smul,
      mul_inv_cancel₀ (by exact_mod_cast factorial_ne_zero _), one_smul]

variable [NormSMulClass ℚ_[p] E]

/-- **The Mahler-coefficient criterion for analyticity**, with norms: a continuous function
`f : ℤ_p → E` with Mahler coefficients `aₙ` is the evaluation of a coefficient vector in `LA_h(E)`
exactly when `‖aₙ‖ / ‖⌊n / pʰ⌋!‖ → 0`. -/
theorem mem_range_eval_iff_tendsto_norm_div {f : C(ℤ_[p], E)} :
    f ∈ Set.range (eval (p := p) (h := h) S) ↔
      Tendsto (fun n ↦ ‖mahlerEquiv E f n‖ / ‖((n / p ^ h)! : ℚ_[p])‖) atTop (𝓝 0) := by
  rw [mem_range_eval_iff, tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_smul, norm_inv, div_eq_inv_mul]

/-- **The norm of an analytic stage in Mahler coordinates.** The norm of `c ∈ LA_h(E)` is
`supₙ ‖aₙ‖ / ‖⌊n / pʰ⌋!‖`, where `aₙ` are the Mahler coefficients of the function it defines. -/
theorem norm_eq_iSup_norm_mahlerEquiv_div (c : AnalyticStage p h E) :
    ‖c‖ = ⨆ n, ‖mahlerEquiv E (eval S c) n‖ / ‖((n / p ^ h)! : ℚ_[p])‖ := by
  rw [← (amiceEquiv p h S).symm.norm_map, ZeroAtInftyContinuousMap.norm_eq_iSup_norm]
  simp [amiceEquiv_symm_apply, norm_smul, div_eq_inv_mul]

end Rational

/-! ### Exponential decay of Mahler coefficients -/

section Decay

variable [Module ℚ_[p] E] [IsBoundedSMul ℚ_[p] E]

/-- **Amice's characterisation of locally analytic functions.** A continuous function
`f : ℤ_p → E` is analytic on the discs of some level `h` exactly when its Mahler coefficients decay
exponentially: `‖aₙ‖ ≤ C ρⁿ` for some `C` and some `0 ≤ ρ < 1`. -/
theorem exists_mem_range_eval_iff {f : C(ℤ_[p], E)} :
    (∃ h, f ∈ Set.range (eval (p := p) (h := h) S)) ↔
      ∃ C ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ n, ‖mahlerEquiv E f n‖ ≤ C * ρ ^ n := by
  constructor
  · rintro ⟨h, c, rfl⟩
    exact ⟨p * ‖c‖, amiceRadius p (h + 1), (amiceRadius_pos _).le, amiceRadius_lt_one _,
      norm_mahlerEquiv_eval_le S c⟩
  · rintro ⟨C, ρ, hρ₀, hρ₁, hC⟩
    obtain ⟨h, hh⟩ := (tendsto_amiceRadius (p := p)).eventually (lt_mem_nhds hρ₁) |>.exists
    have hr := amiceRadius_pos (p := p) h
    refine ⟨h, (mem_range_eval_iff S).mpr <| squeeze_zero_norm (fun n ↦ ?_) <| by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hρ₀ hr.le)
        ((div_lt_one hr).mpr hh)).const_mul C⟩
    have hm := amiceRadius_pow_le_norm_factorial (p := p) h n
    rw [div_pow, mul_div_assoc', div_eq_inv_mul]
    refine (norm_smul_le _ _).trans (mul_le_mul ?_ (hC n) (norm_nonneg _) (by positivity))
    rw [norm_inv]
    exact inv_anti₀ (pow_pos hr n) hm

end Decay

end TauCeti.AnalyticStage
