/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.AddChar
public import TauCeti.NumberTheory.Padics.Distribution.Amice.Basis
public import TauCeti.NumberTheory.Padics.Distribution.Amice.Norm

/-!
# Analyticity of the additive characters of `ℤ_p`

For `t` with `tⁿ → 0` in a complete ultrametric normed `ℤ_p`-algebra `R`, Mathlib's
`PadicInt.addChar_of_value_at_one t` is the continuous character `χ_t(x) = (1 + t) ^ x`, the
Mahler series `∑ₙ tⁿ (x choose n)`. This file expands `χ_t` on the discs of level `h`.

When `R` is moreover a normed `ℚ_p`-module, the Mahler coefficient `tⁿ` is `⌊n / pʰ⌋! cₙ` with
Amice coordinate

`cₙ = tⁿ / ⌊n / pʰ⌋!`   (`TauCeti.amiceCharCoeff`).

The weight bound `r_hⁿ ≤ ‖⌊n / pʰ⌋!‖`, with `r_h = p ^ (-1 / ((p - 1) pʰ))`, shows that these
coordinates tend to zero, and have norm at most one, when `‖t‖ < r_h`. Amice's map then sends them
to a coefficient vector in the analytic stage `LA_h(R)` whose evaluation is `χ_t`
(`TauCeti.AnalyticStage.eval_addCharExpansion`): the character is analytic on every disc
`a + pʰℤ_p`. When the norm of `R` is multiplicative, as over a normed field, the expansion on each
disc has Gauss norm exactly one, its constant term being `χ_t(a)`, of norm one.

For a multiplicative norm the Amice coordinates tend to zero *exactly* when `‖t‖ < r_h`
(`TauCeti.tendsto_amiceCharCoeff_iff`): on the boundary and beyond, along `n = p^(h + k)` they keep
norm at least `p ^ (-1 / (p - 1))`, the weight bound being sharp there. Since `r_h → 1`, every
continuous character of `ℤ_p` with values in a complete normed field over `ℚ_p`, or more generally
in such an algebra with multiplicative norm, is analytic at some level
(`TauCeti.AnalyticStage.exists_eval_eq_addChar`). For a general Banach algebra, `‖t‖ < r_h` remains
a sufficient condition, and the expansion has norm at most one.

The converse, that `χ_t` lies in the image of `LA_h(K)` only when `‖t‖ < r_h`, needs Amice's basis
theorem identifying the image of the evaluation with the functions whose Amice coordinates tend to
zero; it is not proved here. The coordinate statement `TauCeti.tendsto_amiceCharCoeff_iff` is the
coefficient form of that criterion.

## Main definitions

* `TauCeti.amiceCharCoeff p h t n`: the Amice coordinate `tⁿ / ⌊n / pʰ⌋!` of `χ_t` at level `h`.
* `TauCeti.AnalyticStage.addCharExpansion p h t ht`: the expansion of `χ_t` in `LA_h(R)`, for
  `‖t‖ < r_h`.

## Main results

* `TauCeti.tendsto_amiceCharCoeff`: the Amice coordinates tend to zero when `‖t‖ < r_h`.
* `TauCeti.tendsto_amiceCharCoeff_iff`: for a multiplicative norm, they tend to zero exactly when
  `‖t‖ < r_h`; `TauCeti.le_norm_amiceCharCoeff_pow` is the subsequence detecting the failure.
* `TauCeti.not_tendsto_amiceCharCoeff_one_and_tendsto_amiceCharCoeff_two`: at `p = 2`, a parameter
  of norm `2 ^ (-1 / 2)` fails the criterion at level one and satisfies it at level two.
* `TauCeti.AnalyticStage.eval_addCharExpansion`: the expansion evaluates to `χ_t`.
* `TauCeti.AnalyticStage.norm_addCharExpansion_le`: the expansion has norm at most one.
* `TauCeti.AnalyticStage.isGreatest_norm_addCharExpansion`: for a multiplicative norm, the
  expansion has Gauss norm exactly one on each disc.
* `TauCeti.AnalyticStage.exists_eval_eq_addChar`: every continuous character of `ℤ_p` with values
  in a complete normed field over `ℚ_p` is analytic at some level.

## References

* Y. Amice, *Interpolation p-adique*, Bull. Soc. Math. France 92 (1964), 117–180.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

open Filter Topology Nat
open scoped ZeroAtInfty

variable {p : ℕ} [hp : Fact p.Prime]

namespace TauCeti

/-! ### The Amice coordinates of a character -/

section Coordinates

variable {R : Type*} [NormedRing R] [Module ℚ_[p] R]

variable (p) in
/-- The Amice coordinate `tⁿ / ⌊n / pʰ⌋!` at level `h` of the character `x ↦ (1 + t) ^ x`, whose
Mahler coefficients are the powers `tⁿ`. The factorial is inverted in `ℚ_p`. -/
noncomputable def amiceCharCoeff (h : ℕ) (t : R) (n : ℕ) : R :=
  ((n / p ^ h)! : ℚ_[p])⁻¹ • t ^ n

/-- The defining formula of the Amice coordinate. -/
theorem amiceCharCoeff_def (h : ℕ) (t : R) (n : ℕ) :
    amiceCharCoeff p h t n = ((n / p ^ h)! : ℚ_[p])⁻¹ • t ^ n :=
  (rfl)

/-- Multiplying the Amice coordinate by `⌊n / pʰ⌋!` recovers the Mahler coefficient `tⁿ`. -/
theorem factorial_smul_amiceCharCoeff (h : ℕ) (t : R) (n : ℕ) :
    (n / p ^ h)! • amiceCharCoeff p h t n = t ^ n := by
  rw [amiceCharCoeff_def, ← Nat.cast_smul_eq_nsmul ℚ_[p], smul_smul,
    mul_inv_cancel₀ (by exact_mod_cast factorial_ne_zero _), one_smul]

variable [IsBoundedSMul ℚ_[p] R]

/-- The Amice coordinate has norm at most `‖tⁿ‖ / ‖⌊n / pʰ⌋!‖`. -/
theorem norm_amiceCharCoeff_le (h : ℕ) (t : R) (n : ℕ) :
    ‖amiceCharCoeff p h t n‖ ≤ ‖t ^ n‖ / ‖((n / p ^ h)! : ℚ_[p])‖ := by
  rw [amiceCharCoeff_def, div_eq_inv_mul, ← norm_inv]
  exact norm_smul_le _ _

/-- For `n ≥ 1` the Amice coordinate has norm at most `(‖t‖ / r_h)ⁿ`. -/
private theorem norm_amiceCharCoeff_le_div_pow {h n : ℕ} (t : R) (hn : n ≠ 0) :
    ‖amiceCharCoeff p h t n‖ ≤ (‖t‖ / amiceRadius p h) ^ n := by
  have hr := (pow_pos (amiceRadius_pos (p := p) h) n)
  refine (norm_amiceCharCoeff_le h t n).trans ?_
  rw [div_pow]
  exact div_le_div₀ (by positivity) (norm_pow_le' t (Nat.pos_of_ne_zero hn)) hr
    (amiceRadius_pow_le_norm_factorial h n)

/-- **The Amice coordinates of `χ_t` tend to zero** when `‖t‖ < r_h`. -/
theorem tendsto_amiceCharCoeff {h : ℕ} {t : R} (ht : ‖t‖ < amiceRadius p h) :
    Tendsto (amiceCharCoeff p h t) atTop (𝓝 0) := by
  have hr := amiceRadius_pos (p := p) h
  refine squeeze_zero_norm' (eventually_atTop.mpr ⟨1, fun n hn ↦
    norm_amiceCharCoeff_le_div_pow t (Nat.one_le_iff_ne_zero.mp hn)⟩) ?_
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ((div_lt_one hr).mpr ht)

/-- When `‖t‖ ≤ r_h`, every Amice coordinate of `χ_t` has norm at most one. -/
theorem norm_amiceCharCoeff_le_one [NormOneClass R] {h : ℕ} {t : R}
    (ht : ‖t‖ ≤ amiceRadius p h) (n : ℕ) : ‖amiceCharCoeff p h t n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [amiceCharCoeff_def]
  · have hr := amiceRadius_pos (p := p) h
    exact (norm_amiceCharCoeff_le_div_pow t hn).trans
      (pow_le_one₀ (by positivity) ((div_le_one hr).mpr ht))

end Coordinates

section NormMulClass

variable {K : Type*} [NormedRing K] [NormMulClass K] [NormOneClass K] [Module ℚ_[p] K]
  [NormSMulClass ℚ_[p] K]

/-- For a multiplicative norm, the Amice coordinate has norm exactly `‖t‖ⁿ / ‖⌊n / pʰ⌋!‖`. -/
theorem norm_amiceCharCoeff (h : ℕ) (t : K) (n : ℕ) :
    ‖amiceCharCoeff p h t n‖ = ‖t‖ ^ n / ‖((n / p ^ h)! : ℚ_[p])‖ := by
  rw [amiceCharCoeff_def, norm_smul, norm_inv, norm_pow, inv_mul_eq_div]

/-- **The Amice coordinates do not tend to zero on and beyond the boundary.** If `r_h ≤ ‖t‖`, then
along `n = p^(h + k)` the Amice coordinate of `χ_t` has norm at least `p ^ (-1 / (p - 1))`. -/
theorem le_norm_amiceCharCoeff_pow {h : ℕ} {t : K} (ht : amiceRadius p h ≤ ‖t‖) (k : ℕ) :
    (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) ≤ ‖amiceCharCoeff p h t (p ^ (h + k))‖ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hr := pow_pos (amiceRadius_pos (p := p) h) (p ^ (h + k))
  rw [norm_amiceCharCoeff, pow_add, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos h),
    norm_factorial_pow_eq_mul_amiceRadius_pow h k, le_div_iff₀ (by positivity), ← mul_assoc,
    Real.rpow_neg hp0.le, inv_mul_cancel₀ (by positivity), one_mul, ← pow_add]
  exact pow_le_pow_left₀ (amiceRadius_pos h).le ht _

/-- **The coefficient criterion for analyticity of `χ_t`.** For a multiplicative norm, the Amice
coordinates `tⁿ / ⌊n / pʰ⌋!` tend to zero exactly when `‖t‖ < r_h = p ^ (-1 / ((p - 1) pʰ))`. -/
theorem tendsto_amiceCharCoeff_iff {h : ℕ} {t : K} :
    Tendsto (amiceCharCoeff p h t) atTop (𝓝 0) ↔ ‖t‖ < amiceRadius p h := by
  refine ⟨fun hlim ↦ ?_, tendsto_amiceCharCoeff⟩
  by_contra! ht
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hp.out.pos) _
  have hsub : Tendsto (fun k ↦ p ^ (h + k)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hp.out.one_lt).comp
      (tendsto_atTop_mono (fun k ↦ Nat.le_add_left k h) tendsto_id)
  obtain ⟨k, hk⟩ := ((tendsto_zero_iff_norm_tendsto_zero.mp (hlim.comp hsub)).eventually
    (gt_mem_nhds hpos)).exists
  exact (le_norm_amiceCharCoeff_pow ht k).not_gt hk

/-- **A parameter on the level-one boundary at `p = 2`.** If `‖t‖ = 2 ^ (-1 / 2)`, then the Amice
coordinates of `χ_t` do not tend to zero at level one, where `r_1 = 2 ^ (-1 / 2)`, but do at level
two, where `r_2 = 2 ^ (-1 / 4)`. -/
theorem not_tendsto_amiceCharCoeff_one_and_tendsto_amiceCharCoeff_two [Module ℚ_[2] K]
    [NormSMulClass ℚ_[2] K] {t : K} (ht : ‖t‖ = (2 : ℝ) ^ (-(1 / 2 : ℝ))) :
    ¬ Tendsto (amiceCharCoeff 2 1 t) atTop (𝓝 0) ∧ Tendsto (amiceCharCoeff 2 2 t) atTop (𝓝 0) := by
  rw [tendsto_amiceCharCoeff_iff, tendsto_amiceCharCoeff_iff, ht, amiceRadius_def,
    amiceRadius_def]
  norm_num

end NormMulClass

/-! ### The expansion of a character on the discs of level `h` -/

namespace AnalyticStage

variable {R : Type*} [NormedRing R] [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R] [Module ℚ_[p] R]
  [IsBoundedSMul ℚ_[p] R] [IsUltrametricDist R] [CompleteSpace R]

variable (p) in
/-- **The expansion of the character `x ↦ (1 + t) ^ x` on the discs of level `h`**, for
`‖t‖ < r_h`: the image under Amice's map of the Amice coordinates `tⁿ / ⌊n / pʰ⌋!`. -/
noncomputable def addCharExpansion (h : ℕ) (t : R) (ht : ‖t‖ < amiceRadius p h) :
    AnalyticStage p h R :=
  amiceMap p h ℤ_[p] <| ZeroAtInftyContinuousMap.mkOfDiscrete (amiceCharCoeff p h t) <| by
    rw [Nat.cofinite_eq_atTop]
    exact tendsto_amiceCharCoeff ht

/-- The coefficients of the expansion of `χ_t`: on the disc of `a`, the coefficient of `wᵏ` is the
sum over `n` of the `k`-th coefficient of Amice's polynomial `amicePolynomial p h n a.val`, times
the Amice coordinate `tⁿ / ⌊n / pʰ⌋!`. -/
theorem addCharExpansion_apply {h : ℕ} {t : R} (ht : ‖t‖ < amiceRadius p h)
    (i : ZMod (p ^ h) × ℕ) :
    addCharExpansion p h t ht i =
      ∑' n, (amicePolynomial p h n (i.1.val : ℤ_[p])).coeff i.2 • amiceCharCoeff p h t n := by
  rw [addCharExpansion, amiceMap_apply, ZeroAtInftyContinuousMap.coe_mkOfDiscrete]

variable (S : Type*) [Semiring S] [Module S R] [ContinuousConstSMul S R] [SMulCommClass ℤ_[p] S R]

/-- **The character `χ_t` is analytic on the discs of level `h`** when `‖t‖ < r_h`: its expansion
evaluates to `x ↦ (1 + t) ^ x`. (The hypothesis `hr`, needed to name the character, follows from
`ht`.) -/
theorem eval_addCharExpansion {h : ℕ} {t : R} (ht : ‖t‖ < amiceRadius p h)
    (hr : Tendsto (t ^ ·) atTop (𝓝 0)) :
    ⇑(eval S (addCharExpansion p h t ht)) = PadicInt.addChar_of_value_at_one t hr := by
  -- `addCharExpansion` uses Amice's map over `ℤ_p`; both maps sum the same vectors.
  rw [PadicInt.coe_addChar_of_value_at_one, addCharExpansion,
    (hasSum_amiceMap ℤ_[p] _).unique (hasSum_amiceMap S _), eval_amiceMap]
  simp only [ZeroAtInftyContinuousMap.coe_mkOfDiscrete, factorial_smul_amiceCharCoeff]

/-- The expansion of `χ_t` has norm at most one. -/
theorem norm_addCharExpansion_le [NormOneClass R] {h : ℕ} {t : R}
    (ht : ‖t‖ < amiceRadius p h) : ‖addCharExpansion p h t ht‖ ≤ 1 :=
  (norm_amiceMap_le ℤ_[p] _).trans <| (ZeroAtInftyContinuousMap.norm_le zero_le_one).mpr fun n ↦ by
    simpa using norm_amiceCharCoeff_le_one ht.le n

/-- The constant term of the expansion of `χ_t` on the disc of `a` is `χ_t(a)`, the value at its
centre `a.val`. -/
theorem addCharExpansion_apply_zero {h : ℕ} {t : R} (ht : ‖t‖ < amiceRadius p h)
    (a : ZMod (p ^ h)) :
    addCharExpansion p h t ht (a, 0) = (1 + t) ^ a.val := by
  have hval := eval_natCast_val_add_mul ℤ_[p] (addCharExpansion p h t ht) a 0
  rw [mul_zero, add_zero, tsum_eq_single 0 fun n hn ↦ by simp [zero_pow hn], pow_zero,
    one_smul] at hval
  rw [← hval, eval_addCharExpansion ℤ_[p] ht
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (ht.trans (amiceRadius_lt_one h))),
    ← nsmul_one, AddChar.map_nsmul_eq_pow, PadicInt.addChar_of_value_at_one_def]

/-! ### Characters with values in a ring with multiplicative norm -/

section NormMulClass

variable {K : Type*} [NormedRing K] [NormMulClass K] [NormOneClass K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [Module ℚ_[p] K] [NormSMulClass ℚ_[p] K] [IsUltrametricDist K]
  [CompleteSpace K]

/-- **The expansion of `χ_t` has Gauss norm one on every disc.** For a multiplicative norm, on the
disc of `a` the largest coefficient norm of the expansion is one, attained by the constant term
`χ_t(a)`. -/
theorem isGreatest_norm_addCharExpansion {h : ℕ} {t : K} (ht : ‖t‖ < amiceRadius p h)
    (a : ZMod (p ^ h)) :
    IsGreatest (Set.range fun k ↦ ‖addCharExpansion p h t ht (a, k)‖) 1 := by
  refine ⟨⟨0, ?_⟩, ?_⟩
  · have ht1 : ‖t‖ < 1 := ht.trans (amiceRadius_lt_one h)
    have h1 : ‖1 + t‖ = 1 := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact ht1.ne'),
        norm_one, max_eq_left ht1.le]
    simp [addCharExpansion_apply_zero, h1]
  · rintro _ ⟨k, rfl⟩
    exact ((addCharExpansion p h t ht).norm_coe_le_norm _).trans (norm_addCharExpansion_le ht)

/-- The expansion of `χ_t` has norm exactly one. -/
theorem norm_addCharExpansion {h : ℕ} {t : K} (ht : ‖t‖ < amiceRadius p h) :
    ‖addCharExpansion p h t ht‖ = 1 := by
  obtain ⟨k, hk⟩ := (isGreatest_norm_addCharExpansion ht 0).1
  exact (norm_addCharExpansion_le ht).antisymm
    (hk.symm.le.trans ((addCharExpansion p h t ht).norm_coe_le_norm _))

variable (S : Type*) [Semiring S] [Module S K] [ContinuousConstSMul S K] [SMulCommClass ℤ_[p] S K]

/-- **Every continuous character of `ℤ_p` is analytic at some level**, when its values lie in a
complete ultrametric normed `ℚ_p`-algebra with multiplicative norm, such as a complete normed field
over `ℚ_p`: it is the evaluation of a coefficient vector of norm one in some analytic stage
`LA_h(K)`. -/
theorem exists_eval_eq_addChar {κ : AddChar ℤ_[p] K} (hκ : Continuous κ) :
    ∃ h, ∃ f : AnalyticStage p h K, ‖f‖ = 1 ∧ ⇑(eval S f) = κ := by
  have hlim := AddChar.tendsto_eval_one_sub_pow hκ
  have hnorm := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp hlim
  obtain ⟨h, ht⟩ := (tendsto_amiceRadius (p := p)).eventually (lt_mem_nhds hnorm) |>.exists
  refine ⟨h, addCharExpansion p h _ ht, norm_addCharExpansion ht, ?_⟩
  rw [eval_addCharExpansion S ht hlim,
    ← PadicInt.eq_addChar_of_value_at_one hlim hκ (by abel)]

end NormMulClass

end AnalyticStage

end TauCeti
