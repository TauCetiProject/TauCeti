/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Amice.Character
public import TauCeti.NumberTheory.Padics.Distribution.Amice.Isometry
public import TauCeti.NumberTheory.Padics.Distribution.LocallyAnalytic

/-!
# Mahler coefficients of locally analytic functions

Let `E` be a complete ultrametric normed `ℤ_p`-module with contractive action, and put
`m_h(n) = ⌊n / pʰ⌋!`. By Amice's theorem every coefficient vector `v` of the analytic stage
`LA_h(E)` is `∑ₙ e_{h,n} • cₙ` for a unique null sequence `c = (amiceEquiv p h S).symm v`, where
`e_{h,n}(x) = m_h(n) (x choose n)`. Hence the function `eval S v` has Mahler coefficients

`aₙ = m_h(n) • cₙ`   (`TauCeti.AnalyticStage.mahlerEquiv_eval_apply`):

evaluation followed by Mathlib's Mahler isometry `PadicInt.mahlerEquiv` is the diagonal map
`cₙ ↦ m_h(n) • cₙ` in Amice coordinates. This holds for every such `E`, including torsion modules.

When `E` is moreover a normed `ℚ_p`-vector space with `‖x • e‖ = ‖x‖ ‖e‖`, a Banach `ℚ_p`-space,
the diagonal can be inverted, `cₙ = m_h(n)⁻¹ • aₙ`. This determines the analytic stage inside
`C(ℤ_p, E)` through the Mahler coefficients `aₙ` of a continuous function `f`:

* `f` is the evaluation of a vector of `LA_h(E)` exactly when `‖aₙ‖ / ‖m_h(n)‖ → 0`
  (`TauCeti.AnalyticStage.mem_range_eval_iff`);
* the norm of that vector is `‖v‖ = supₙ ‖aₙ‖ / ‖m_h(n)‖`
  (`TauCeti.AnalyticStage.norm_eq_iSup_norm_mahlerEquiv_eval_div`).

Since `r_hⁿ ≤ ‖m_h(n)‖ ≤ p r_{h+1}ⁿ` with `r_h = p ^ (-1 / ((p - 1) pʰ))` increasing to `1`,
`f` is locally analytic, that is, analytic at some level, exactly when its Mahler coefficients
decay exponentially: `‖aₙ‖ ≤ ρⁿ` for all large `n` and some `0 < ρ < 1`
(`TauCeti.LocallyAnalytic.mem_range_eval_iff`). Informally, this is the condition
`liminfₙ (-log_p ‖aₙ‖) / n > 0`, with the value `+∞` for vanishing coefficients; the statement
here uses the explicit exponential bound instead.

The character `χ_t(x) = (1 + t) ^ x` has Mahler coefficients `tⁿ`. For a multiplicative norm the
criterion therefore gives the converse of the analyticity of `χ_t` for `‖t‖ < r_h`: the character
is analytic on the discs of level `h` *only* when `‖t‖ < r_h`
(`TauCeti.AnalyticStage.exists_eval_eq_addChar_iff`); the boundary `‖t‖ = r_h` is excluded.

## Main results

* `TauCeti.AnalyticStage.mahlerEquiv_eval_amiceMap`: the Mahler coefficients of `∑ₙ e_{h,n} • cₙ`
  are `m_h(n) • cₙ`.
* `TauCeti.AnalyticStage.mahlerEquiv_eval_apply`: evaluation followed by Mahler coefficients is
  diagonal in Amice coordinates.
* `TauCeti.AnalyticStage.amiceEquiv_symm_apply`: over `ℚ_p`, the Amice coordinates of `v` are
  `m_h(n)⁻¹ • aₙ`.
* `TauCeti.AnalyticStage.mem_range_eval_iff`: the image of `LA_h(E)` in `C(ℤ_p, E)`.
* `TauCeti.AnalyticStage.norm_eq_iSup_norm_mahlerEquiv_eval_div`: the norm of `LA_h(E)` in Mahler
  coefficients.
* `TauCeti.LocallyAnalytic.mem_range_eval_iff`: locally analytic functions are those with
  exponentially decaying Mahler coefficients.
* `TauCeti.AnalyticStage.exists_eval_eq_addChar_iff`: `χ_t` is analytic at level `h` exactly when
  `‖t‖ < r_h`.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

open Filter Topology Nat
open scoped ZeroAtInfty

variable {p : ℕ} [hp : Fact p.Prime]

namespace TauCeti

namespace AnalyticStage

variable {h : ℕ} {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- **The Mahler coefficients of Amice's series.** The function `∑ₙ e_{h,n} • cₙ`, where
`e_{h,n}(x) = ⌊n / pʰ⌋! (x choose n)`, has `n`-th Mahler coefficient `⌊n / pʰ⌋! • cₙ`. -/
@[simp]
theorem mahlerEquiv_eval_amiceMap (c : C₀(ℕ, E)) (n : ℕ) :
    PadicInt.mahlerEquiv E (eval S (amiceMap p h S c)) n = (n / p ^ h)! • c n := by
  have hc : Tendsto c atTop (𝓝 0) := Nat.cofinite_eq_atTop ▸ c.tendsto_cofinite
  have hmc : Tendsto (fun n ↦ (n / p ^ h)! • c n) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n ↦ IsUltrametricDist.norm_nsmul_le (c n) _)
      (tendsto_zero_iff_norm_tendsto_zero.mp hc)
  rw [eval_amiceMap, PadicInt.mahlerEquiv_apply]
  exact PadicInt.fwdDiff_mahlerSeries hmc n

/-- **Evaluation followed by Mahler coefficients is diagonal in Amice coordinates.** The `n`-th
Mahler coefficient of the function defined by `v ∈ LA_h(E)` is `⌊n / pʰ⌋!` times the `n`-th
Amice coordinate of `v`. -/
theorem mahlerEquiv_eval_apply (v : AnalyticStage p h E) (n : ℕ) :
    PadicInt.mahlerEquiv E (eval S v) n = (n / p ^ h)! • (amiceEquiv p h S).symm v n := by
  conv_lhs => rw [← (amiceEquiv p h S).apply_symm_apply v, amiceEquiv_apply]
  exact mahlerEquiv_eval_amiceMap S _ n

section Rational

variable [Module ℚ_[p] E]

/-- Over a `ℚ_p`-vector space, the `n`-th Amice coordinate of `v ∈ LA_h(E)` is the `n`-th Mahler
coefficient of its evaluation divided by `⌊n / pʰ⌋!`. -/
theorem amiceEquiv_symm_apply (v : AnalyticStage p h E) (n : ℕ) :
    (amiceEquiv p h S).symm v n =
      ((n / p ^ h)! : ℚ_[p])⁻¹ • PadicInt.mahlerEquiv E (eval S v) n := by
  rw [mahlerEquiv_eval_apply, ← Nat.cast_smul_eq_nsmul ℚ_[p], smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast factorial_ne_zero _), one_smul]

variable [NormSMulClass ℚ_[p] E]

/-- The norm of the `n`-th Amice coordinate of `v ∈ LA_h(E)` is `‖aₙ‖ / ‖⌊n / pʰ⌋!‖`, where `aₙ`
is the `n`-th Mahler coefficient of its evaluation. -/
theorem norm_amiceEquiv_symm_apply (v : AnalyticStage p h E) (n : ℕ) :
    ‖(amiceEquiv p h S).symm v n‖ =
      ‖PadicInt.mahlerEquiv E (eval S v) n‖ / ‖((n / p ^ h)! : ℚ_[p])‖ := by
  rw [amiceEquiv_symm_apply, norm_smul, norm_inv, inv_mul_eq_div]

/-- **The norm of `LA_h(E)` in Mahler coefficients.** Over a Banach `ℚ_p`-space, the norm of
`v ∈ LA_h(E)` is `supₙ ‖aₙ‖ / ‖⌊n / pʰ⌋!‖`, where `aₙ` are the Mahler coefficients of its
evaluation. -/
theorem norm_eq_iSup_norm_mahlerEquiv_eval_div (v : AnalyticStage p h E) :
    ‖v‖ = ⨆ n, ‖PadicInt.mahlerEquiv E (eval S v) n‖ / ‖((n / p ^ h)! : ℚ_[p])‖ := by
  simp_rw [← (amiceEquiv p h S).symm.norm_map v, ZeroAtInftyContinuousMap.norm_eq_iSup_norm,
    norm_amiceEquiv_symm_apply]

/-- **The image of the analytic stage in the continuous functions.** Over a Banach `ℚ_p`-space, a
continuous function `f` is the evaluation of a coefficient vector of `LA_h(E)` exactly when its
Mahler coefficients satisfy `‖aₙ‖ / ‖⌊n / pʰ⌋!‖ → 0`. -/
theorem mem_range_eval_iff {f : C(ℤ_[p], E)} :
    f ∈ Set.range (eval (p := p) (h := h) S) ↔
      Tendsto (fun n ↦ ‖PadicInt.mahlerEquiv E f n‖ / ‖((n / p ^ h)! : ℚ_[p])‖) atTop (𝓝 0) := by
  constructor
  · rintro ⟨v, rfl⟩
    simp_rw [← norm_amiceEquiv_symm_apply]
    exact tendsto_zero_iff_norm_tendsto_zero.mp
      (Nat.cofinite_eq_atTop ▸ ((amiceEquiv p h S).symm v).tendsto_cofinite)
  · intro hf
    have hc : Tendsto (fun n ↦ ((n / p ^ h)! : ℚ_[p])⁻¹ • PadicInt.mahlerEquiv E f n) cofinite
        (𝓝 0) := by
      rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
      simpa only [norm_smul, norm_inv, inv_mul_eq_div] using hf
    refine ⟨amiceMap p h S (ZeroAtInftyContinuousMap.mkOfDiscrete _ hc), ?_⟩
    refine (PadicInt.mahlerEquiv E).injective (ZeroAtInftyContinuousMap.ext fun n ↦ ?_)
    rw [mahlerEquiv_eval_amiceMap, ZeroAtInftyContinuousMap.coe_mkOfDiscrete,
      ← Nat.cast_smul_eq_nsmul ℚ_[p], smul_smul,
      mul_inv_cancel₀ (by exact_mod_cast factorial_ne_zero _), one_smul]

end Rational

end AnalyticStage

namespace LocallyAnalytic

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  [IsUltrametricDist E] [CompleteSpace E] [Module ℚ_[p] E] [NormSMulClass ℚ_[p] E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- A function analytic at level `h` has Mahler coefficients bounded by `ρⁿ` for every
`r_{h+1} < ρ`, for all large `n`. -/
private theorem eventually_norm_mahlerEquiv_le_pow {h : ℕ} {f : C(ℤ_[p], E)}
    (hf : f ∈ Set.range (AnalyticStage.eval (p := p) (h := h) S)) {ρ : ℝ}
    (hρ : amiceRadius p (h + 1) < ρ) :
    ∀ᶠ n in atTop, ‖PadicInt.mahlerEquiv E f n‖ ≤ ρ ^ n := by
  set r := amiceRadius p (h + 1)
  have hr := amiceRadius_pos (p := p) (h + 1)
  have hρ0 : 0 < ρ := hr.trans hρ
  -- Eventually `‖aₙ‖ ≤ ‖⌊n / pʰ⌋!‖ ≤ p rⁿ`, and `p (r / ρ)ⁿ ≤ 1`.
  have hsmall : Tendsto (fun n : ℕ ↦ (p : ℝ) * (r / ρ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_pos hr hρ0).le
      ((div_lt_one hρ0).mpr hρ)).const_mul (p : ℝ)
  filter_upwards [(AnalyticStage.mem_range_eval_iff S).mp hf |>.eventually (ge_mem_nhds one_pos),
    hsmall.eventually (ge_mem_nhds one_pos)] with n hn hpn
  have hm : 0 < ‖((n / p ^ h)! : ℚ_[p])‖ :=
    norm_pos_iff.mpr (by exact_mod_cast factorial_ne_zero _)
  calc ‖PadicInt.mahlerEquiv E f n‖ ≤ ‖((n / p ^ h)! : ℚ_[p])‖ := by
        rwa [div_le_one hm] at hn
    _ ≤ p * r ^ n := norm_factorial_le_mul_amiceRadius_succ_pow h n
    _ = (p * (r / ρ) ^ n) * ρ ^ n := by
        rw [div_pow, mul_assoc, div_mul_cancel₀ _ (pow_pos hρ0 n).ne']
    _ ≤ ρ ^ n := mul_le_of_le_one_left (pow_pos hρ0 n).le hpn

/-- **Locally analytic functions have exponentially decaying Mahler coefficients.** Over a Banach
`ℚ_p`-space, a continuous function on `ℤ_p` is locally analytic, the evaluation of an element of
the algebraic union of the analytic stages, exactly when its Mahler coefficients satisfy
`‖aₙ‖ ≤ ρⁿ` for all large `n`, for some `0 < ρ < 1`. -/
theorem mem_range_eval_iff {f : C(ℤ_[p], E)} :
    f ∈ Set.range (eval (p := p) (E := E) S) ↔
      ∃ ρ ∈ Set.Ioo (0 : ℝ) 1, ∀ᶠ n in atTop, ‖PadicInt.mahlerEquiv E f n‖ ≤ ρ ^ n := by
  rw [range_eval S, Set.mem_iUnion]
  constructor
  · rintro ⟨h, hf⟩
    obtain ⟨ρ, hrρ, hρ1⟩ := exists_between (amiceRadius_lt_one (p := p) (h + 1))
    exact ⟨ρ, ⟨(amiceRadius_pos (h + 1)).trans hrρ, hρ1⟩,
      eventually_norm_mahlerEquiv_le_pow S hf hrρ⟩
  · rintro ⟨ρ, ⟨hρ0, hρ1⟩, hf⟩
    obtain ⟨h, hh⟩ := (tendsto_amiceRadius (p := p)).eventually (lt_mem_nhds hρ1) |>.exists
    have hr := amiceRadius_pos (p := p) h
    refine ⟨h, (AnalyticStage.mem_range_eval_iff S).mpr ?_⟩
    -- `‖aₙ‖ / ‖⌊n / pʰ⌋!‖ ≤ ρⁿ / r_hⁿ = (ρ / r_h)ⁿ → 0`.
    refine squeeze_zero' (Eventually.of_forall fun n ↦ by positivity) ?_
      (tendsto_pow_atTop_nhds_zero_of_lt_one (div_pos hρ0 hr).le ((div_lt_one hr).mpr hh))
    filter_upwards [hf] with n hn
    rw [div_pow]
    exact div_le_div₀ (pow_pos hρ0 n).le hn (pow_pos hr n) (amiceRadius_pow_le_norm_factorial h n)

end LocallyAnalytic

namespace AnalyticStage

variable {K : Type*} [NormedRing K] [NormMulClass K] [NormOneClass K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [Module ℚ_[p] K] [NormSMulClass ℚ_[p] K] [IsUltrametricDist K]
  [CompleteSpace K]
  (S : Type*) [Semiring S] [Module S K] [ContinuousConstSMul S K] [SMulCommClass ℤ_[p] S K]

/-- **The analyticity criterion for additive characters.** For a multiplicative norm, as over a
complete normed field over `ℚ_p`, the character `χ_t(x) = (1 + t) ^ x` is the evaluation of a
coefficient vector of `LA_h(K)` exactly when `‖t‖ < r_h = p ^ (-1 / ((p - 1) pʰ))`. In particular
it is not analytic on the discs of level `h` when `‖t‖ = r_h`. -/
theorem exists_eval_eq_addChar_iff {h : ℕ} {t : K} (hr : Tendsto (t ^ ·) atTop (𝓝 0)) :
    (∃ v : AnalyticStage p h K, ⇑(eval S v) = PadicInt.addChar_of_value_at_one t hr) ↔
      ‖t‖ < amiceRadius p h := by
  refine ⟨fun ⟨v, hv⟩ ↦ ?_, fun ht ↦ ⟨addCharExpansion p h t ht, eval_addCharExpansion S ht hr⟩⟩
  rw [PadicInt.coe_addChar_of_value_at_one] at hv
  have hmahler (n : ℕ) : PadicInt.mahlerEquiv K (eval S v) n = t ^ n := by
    rw [ContinuousMap.coe_injective hv, PadicInt.mahlerEquiv_apply]
    exact PadicInt.fwdDiff_mahlerSeries hr n
  have hlim := (mem_range_eval_iff S).mp (Set.mem_range_self (f := eval (p := p) (h := h) S) v)
  simp_rw [hmahler, norm_pow, ← norm_amiceCharCoeff] at hlim
  exact tendsto_amiceCharCoeff_iff.mp (tendsto_zero_iff_norm_tendsto_zero.mpr hlim)

end AnalyticStage

end TauCeti
