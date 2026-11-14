/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
public import TauCeti.NumberTheory.ModularForms.LFunction.Basic
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.NumberTheory.ModularForms.Bounds
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Bounds
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Dimension
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.Bounds
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightOne.Dimension
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Bounds
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.WeightTwo.Dimension
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# The sharp non-cuspidal abscissa of convergence

Let `Γ` be a subgroup of `GL₂(ℝ)` containing the image of `Γ₁(N)`, such as `Γ₁(N)` or `Γ₀(N)`.
For every modular form of weight `k` on `Γ`, the L-series `∑ aₙ n^(-s)` of its `q`-expansion
coefficients converges absolutely for `Re s > k` (Diamond–Shurman, Proposition 5.9.1), and for
`k > 0` coincides on `Re s > k` with Mathlib's `ModularForm.L`. This sharpens the bound `k + 1`
that `aₙ = O(nᵏ)` gives for every arithmetic subgroup
(`ModularForm.abscissaOfAbsConv_qExpansion_coeff_le`).

A form on `Γ` restricts to a form on `Γ₁(N)` with the same `q`-expansion and (when `Γ` is
arithmetic) the same `ModularForm.L` (`ModularForm.L_congr`), and `Γ₁(N)` has strict cusp width `1`
at `∞`. On `Γ₁(N)` the proof splits by weight:

* In weight `k ≤ 0` every positive `q`-expansion coefficient vanishes
  (`ModularForm.abscissaOfAbsConv_qExpansion_coeff_eq_bot_of_weight_nonpos`), so the abscissa is
  `⊥`.
* In weight `k ≥ 3` the form splits into its Eisenstein and cuspidal parts
  (Diamond–Shurman, Theorem 4.5.2;
  `TauCeti.EisensteinSeries.span_range_form_eq_congruenceEisensteinSubspace`). The normalized raised
  Eisenstein series with character have twisted divisor-sum coefficients `O(n^(k-1))`
  (`TauCeti.EisensteinSeries.CharIndex.isBigO_qExpansion_form_coeff`), and the cuspidal part obeys
  Hecke's bound `O(n^(k/2))`, giving `aₙ = O(n^(k-1))`.
* In weight two the Eisenstein part is spanned by the series `E₂^{ψ,φ,t}` and `E₂(z) - t E₂(tz)`
  (Diamond–Shurman, Theorem 4.6.2;
  `TauCeti.EisensteinSeries.span_range_weightTwoForm_eq_congruenceG2Subspace`), whose coefficients
  are bounded by `σ₁(n)` and hence are `O(n^(1+ε))` for every `ε > 0`
  (`TauCeti.EisensteinSeries.isBigO_qExpansion_coeff_of_mem_span_weightTwoForm`).
* In weight one the form splits into the span of the weight-one Eisenstein series `E₁^{ψ,φ,t}` and
  the cusp-form submodule (Diamond–Shurman, Theorem 4.8.1;
  `TauCeti.EisensteinSeries.isCompl_span_range_weightOneForm_cuspFormSubmodule`). On the Eisenstein
  span the coefficients are bounded by `σ₀(n) = O(n^ε)`, giving abscissa at most `1`
  (`TauCeti.EisensteinSeries.abscissaOfAbsConv_qExpansion_coeff_le_of_mem_span_weightOneForm`); on
  the cuspidal part Hecke's pointwise estimate `O(n^(1/2))` would only give `3/2`, whereas the
  mean-square bound `∑_{n ≤ X} |aₙ|² = O(X)` and Cauchy–Schwarz give abscissa at most
  `(1 + 1)/2 = 1` (`CuspForm.abscissaOfAbsConv_qExpansion_coeff_le`).

In weights one and two the estimate `aₙ = O(n^(k-1))` is false (the divisor sum `σ₁(n)` is not
`O(n)`), so the hypothesis `3 ≤ k` cannot be dropped from that coefficient bound.

## Main results

* `TauCeti.isBigO_qExpansion_coeff_of_mem_cuspFormSubmodule`: cusp forms on `Γ₁(N)` of weight
  `m ≥ 2` have coefficients `O(n^(m-1))`.
* `TauCeti.ModularFormClass.qExpansion_isBigO_of_Gamma1_le`: the coefficient bound
  `aₙ = O(n^(k-1))` in weight `k ≥ 3`.
* `TauCeti.ModularFormClass.qExpansion_isBigO_rpow_of_Gamma1_le`: the coefficient bound
  `aₙ = O(n^(k-1+ε))` for every `ε > 0`, in weight `k ≥ 2`.
* `TauCeti.ModularFormClass.abscissaOfAbsConv_qExpansion_coeff_le_of_Gamma1_le`: in every weight
  `k`, the abscissa of absolute convergence of the coefficient L-series is at most `k`, giving
  absolute convergence on `Re s > k`
  (`TauCeti.ModularFormClass.LSeriesSummable_qExpansion_coeff_of_Gamma1_le`).
* `TauCeti.ModularFormClass.LSeries_qExpansion_coeff_eq_of_Gamma1_le` and
  `TauCeti.ModularFormClass.hasSum_L_of_Gamma1_le`: in positive weight `k > 0`, the coefficient
  L-series and plain Dirichlet series on `Re s > k` equal `ModularForm.L hk f s`.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Theorems 4.5.2, 4.6.2, and 4.8.1,
  and Proposition 5.9.1.
-/

public section

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup Filter Asymptotics
open TauCeti.EisensteinSeries
open scoped MatrixGroups

namespace TauCeti

variable {N m : ℕ} [NeZero N]

/-- **Coefficient bound for cusp forms of weight at least two**: a modular form of weight
`m ≥ 2` on `Γ₁(N)` lying in the cusp-form submodule has `q`-expansion coefficients
`O(n^(m-1))`. This follows from Hecke's bound `O(n^(m/2))` (`CuspFormClass.qExpansion_isBigO`)
and, unlike `ModularFormClass.qExpansion_isBigO_of_Gamma1_le`, already holds in weight two. -/
theorem isBigO_qExpansion_coeff_of_mem_cuspFormSubmodule (hm : 2 ≤ m)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) m}
    (hf : f ∈ ModularForm.cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) m) :
    (fun n ↦ (qExpansion 1 f).coeff n) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (m - 1) := by
  obtain ⟨c, rfl⟩ := hf
  have hc := CuspFormClass.qExpansion_isBigO c
  rw [strictWidthInfty_Gamma1] at hc
  refine hc.trans (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := mod_cast hn
  have hexp : ((m : ℤ) : ℝ) / 2 ≤ ((m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    have : (2 : ℝ) ≤ m := mod_cast hm
    linarith
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul,
    ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hn' hexp

/-- In weight `m ≥ 3`, every modular form on `Γ₁(N)` has `q`-expansion coefficients
`O(n^(m-1))`: its Eisenstein part is a combination of the normalized raised series with
character, and its cuspidal part obeys Hecke's bound. -/
private lemma isBigO_qExpansion_coeff_Gamma1 (hm : 3 ≤ (m : ℤ))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) m) :
    (fun n ↦ (qExpansion 1 f).coeff n) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (m - 1) := by
  let Q := ModularForm.qExpansionLinearMap one_pos (one_mem_strictPeriods_Gamma1_map N) (m : ℤ)
  have hQ (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) m) : Q g = qExpansion 1 g :=
    ModularForm.qExpansionLinearMap_apply _ _ g
  have hf : f ∈ congruenceEisensteinSubspace (Gamma_le_Gamma1 N) hm ⊔
      ModularForm.cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) m := by
    rw [sup_congruenceEisensteinSubspace_cuspFormSubmodule_eq_top]
    exact Submodule.mem_top
  obtain ⟨e, he, c, hc, rfl⟩ := Submodule.mem_sup.mp hf
  clear hf
  rw [← span_range_form_eq_congruenceEisensteinSubspace hm] at he
  have hE : (fun n ↦ (Q e).coeff n) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (m - 1) := by
    induction he using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨a, rfl⟩ := hg
        simpa only [hQ] using a.isBigO_qExpansion_form_coeff hm
    | zero => simpa using isBigO_zero (fun n : ℕ ↦ (n : ℝ) ^ (m - 1)) atTop
    | add g h _ _ hg hh => simpa using hg.add hh
    | smul a g _ hg => simpa using hg.const_mul_left a
  have hC := isBigO_qExpansion_coeff_of_mem_cuspFormSubmodule (by omega) hc
  rw [← hQ] at hC ⊢
  simpa using hE.add hC

/-- In weight two, every modular form on `Γ₁(N)` has `q`-expansion coefficients `O(n^(1+ε))`
for every `ε > 0`: its Eisenstein part is a combination of the series `E₂^{ψ,φ,t}` and
`E₂(z) - t E₂(tz)`, and its cuspidal part obeys Hecke's bound. -/
private lemma isBigO_qExpansion_coeff_Gamma1_two {ε : ℝ} (hε : 0 < ε)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) 2) :
    (fun n ↦ (qExpansion 1 f).coeff n) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 + ε) := by
  let Q := ModularForm.qExpansionLinearMap one_pos (one_mem_strictPeriods_Gamma1_map N) 2
  have hQ (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) 2) : Q g = qExpansion 1 g :=
    ModularForm.qExpansionLinearMap_apply _ _ g
  have hf : f ∈ Submodule.span ℂ (Set.range (CharIndex.weightTwoForm (N := N))) ⊔
      ModularForm.cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) 2 := by
    rw [span_range_weightTwoForm_eq_congruenceG2Subspace,
      (isCompl_congruenceG2Subspace_cuspFormSubmodule (Gamma_le_Gamma1 N)).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨e, he, c, hc, rfl⟩ := Submodule.mem_sup.mp hf
  clear hf
  have hE := isBigO_qExpansion_coeff_of_mem_span_weightTwoForm hε he
  -- Hecke's bound `O(n)` for the cuspidal part is weaker than `O(n^(1+ε))`
  have hC : (fun n ↦ (qExpansion 1 c).coeff n) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 + ε) := by
    refine (isBigO_qExpansion_coeff_of_mem_cuspFormSubmodule (m := 2) le_rfl hc).trans
      (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := mod_cast hn
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul,
      ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hn' (by norm_num; linarith)
  rw [← hQ] at hE hC ⊢
  simpa using hE.add hC

/-- In weight one, every modular form on `Γ₁(N)` has coefficient L-series abscissa at most `1`:
its Eisenstein part lies in the span of the series `E₁^{ψ,φ,t}` (abscissa at most `1` from
`σ₀(n) = O(n^ε)`), and its cuspidal part has abscissa at most `(1 + 1) / 2 = 1` by the mean-square
estimate and Cauchy–Schwarz. -/
private lemma abscissaOfAbsConv_qExpansion_coeff_Gamma1_one
    (f : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) 1) :
    LSeries.abscissaOfAbsConv (fun n ↦ (qExpansion 1 f).coeff n) ≤ (1 : EReal) := by
  let Q := ModularForm.qExpansionLinearMap one_pos (one_mem_strictPeriods_Gamma1_map N) 1
  have hQ (g : _root_.ModularForm ((Gamma1 N).map (mapGL ℝ)) 1) : Q g = qExpansion 1 g :=
    ModularForm.qExpansionLinearMap_apply _ _ g
  have hf : f ∈ Submodule.span ℂ (Set.range (CharIndex.weightOneForm (N := N))) ⊔
      _root_.ModularForm.cuspFormSubmodule ((Gamma1 N).map (mapGL ℝ)) 1 := by
    rw [(isCompl_span_range_weightOneForm_cuspFormSubmodule (N := N)).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨e, he, c, hc, rfl⟩ := Submodule.mem_sup.mp hf
  have hE : LSeries.abscissaOfAbsConv (fun n ↦ (qExpansion 1 e).coeff n) ≤ 1 :=
    abscissaOfAbsConv_qExpansion_coeff_le_of_mem_span_weightOneForm he
  have hC : LSeries.abscissaOfAbsConv (fun n ↦ (qExpansion 1 c).coeff n) ≤ 1 := by
    obtain ⟨c₀, rfl⟩ := hc
    have hc₀ := CuspForm.abscissaOfAbsConv_qExpansion_coeff_le c₀
    rw [strictWidthInfty_Gamma1] at hc₀
    have hcoe : (⇑(CuspForm.toModularFormₗ c₀) : ℍ → ℂ) = ⇑c₀ :=
      funext (CuspForm.toModularFormₗ_apply c₀)
    have h1 : ((((1 : ℤ) : ℝ) + 1) / 2 : ℝ) = 1 := by norm_num
    simpa only [hcoe, h1, EReal.coe_one] using hc₀
  have hadd : (fun n ↦ (qExpansion 1 ⇑(e + c)).coeff n) =
      (fun n ↦ (qExpansion 1 e).coeff n) + (fun n ↦ (qExpansion 1 c).coeff n) := by
    ext n
    rw [← hQ (e + c), map_add, hQ e, hQ c, map_add, Pi.add_apply]
  rw [hadd]
  exact (LSeries.abscissaOfAbsConv_add_le _ _).trans (max_le hE hC)

namespace ModularFormClass

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]

/-- **Coefficient bound for modular forms of weight at least three**: if `Γ` contains `Γ₁(N)`,
then a modular form of weight `k ≥ 3` on `Γ` has `q`-expansion coefficients `O(n^(k-1))`. This
sharpens Mathlib's `ModularFormClass.qExpansion_isBigO`, which gives `O(nᵏ)` for every
arithmetic subgroup. -/
theorem qExpansion_isBigO_of_Gamma1_le (hΓ : (Gamma1 N).map (mapGL ℝ) ≤ Γ) (hk : 3 ≤ k)
    [ModularFormClass F Γ k] (f : F) :
    (fun n ↦ (qExpansion 1 f).coeff n) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (k - 1) := by
  lift k to ℕ using (by omega)
  have h := isBigO_qExpansion_coeff_Gamma1 hk
    (_root_.ModularForm.restrict hΓ (ModularFormClass.modularForm f))
  have hexp : (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) := by omega
  have hcoe : ⇑(_root_.ModularForm.restrict hΓ (ModularFormClass.modularForm f)) = ⇑f := by
    ext; simp
  simpa only [hcoe, hexp, zpow_natCast] using h

/-- **Coefficient bound for modular forms of weight at least two**: if `Γ` contains `Γ₁(N)`,
then for every `ε > 0` a modular form of weight `k ≥ 2` on `Γ` has `q`-expansion coefficients
`O(n^(k-1+ε))`. In weight `k ≥ 3` this follows from the sharper `qExpansion_isBigO_of_Gamma1_le`;
in weight two the factor `n^ε` absorbs the divisor sums `σ₁(n)` of the Eisenstein series. -/
theorem qExpansion_isBigO_rpow_of_Gamma1_le (hΓ : (Gamma1 N).map (mapGL ℝ) ≤ Γ) (hk : 2 ≤ k)
    {ε : ℝ} (hε : 0 < ε) [ModularFormClass F Γ k] (f : F) :
    (fun n ↦ (qExpansion 1 f).coeff n) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ ((k : ℝ) - 1 + ε) := by
  have hcases : k = 2 ∨ 3 ≤ k := by omega
  obtain rfl | hk3 := hcases
  · have h := isBigO_qExpansion_coeff_Gamma1_two hε
      (_root_.ModularForm.restrict hΓ (ModularFormClass.modularForm f))
    have hcoe : ⇑(_root_.ModularForm.restrict hΓ (ModularFormClass.modularForm f)) = ⇑f := by
      ext; simp
    have hexp : ((2 : ℤ) : ℝ) - 1 + ε = 1 + ε := by norm_num
    simpa only [hcoe, hexp] using h
  · refine (qExpansion_isBigO_of_Gamma1_le hΓ hk3 f).trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := mod_cast hn
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul,
      ← Real.rpow_intCast, Int.cast_sub, Int.cast_one]
    exact Real.rpow_le_rpow_of_exponent_le hn' (by linarith)

/-- **The sharp non-cuspidal abscissa** (Diamond–Shurman, Proposition 5.9.1): if `Γ` contains
`Γ₁(N)`, then for every modular form of weight `k` on `Γ` the L-series of its `q`-expansion
coefficients has abscissa of absolute convergence at most `k` (in nonpositive weight `k ≤ 0`, the
abscissa is `⊥`). -/
theorem abscissaOfAbsConv_qExpansion_coeff_le_of_Gamma1_le
    (hΓ : (Gamma1 N).map (mapGL ℝ) ≤ Γ) [ModularFormClass F Γ k] (f : F) :
    LSeries.abscissaOfAbsConv (fun n ↦ (qExpansion 1 f).coeff n) ≤ ((k : ℝ) : EReal) := by
  have hcases : k ≤ 0 ∨ k = 1 ∨ 2 ≤ k := by omega
  rcases hcases with hk0 | rfl | hk2
  · let f₁ := _root_.ModularForm.restrict hΓ (ModularFormClass.modularForm f)
    have hcoe : ⇑f₁ = ⇑f := by ext; simp [f₁]
    rw [← hcoe, _root_.ModularForm.abscissaOfAbsConv_qExpansion_coeff_eq_bot_of_weight_nonpos hk0
      f₁]
    exact bot_le
  · let f₁ := _root_.ModularForm.restrict hΓ (ModularFormClass.modularForm f)
    have hcoe : ⇑f₁ = ⇑f := by ext; simp [f₁]
    rw [← hcoe]
    simpa using abscissaOfAbsConv_qExpansion_coeff_Gamma1_one f₁
  · refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦ ?_
    have hε : 0 < (y - k) / 2 := by linarith
    refine LSeriesSummable_of_isBigO_rpow (x := k + (y - k) / 2)
      (by simp only [Complex.ofReal_re]; linarith) ?_
    have hexp : (k : ℝ) + (y - k) / 2 - 1 = k - 1 + (y - k) / 2 := by ring
    simpa only [hexp] using qExpansion_isBigO_rpow_of_Gamma1_le hΓ hk2 hε f

/-- If `Γ` contains `Γ₁(N)`, the L-series of the `q`-expansion coefficients of a modular form of
weight `k` on `Γ` converges absolutely on the half-plane `Re s > k`. -/
theorem LSeriesSummable_qExpansion_coeff_of_Gamma1_le
    (hΓ : (Gamma1 N).map (mapGL ℝ) ≤ Γ) [ModularFormClass F Γ k] (f : F) {s : ℂ}
    (hs : k < s.re) :
    LSeriesSummable (fun n ↦ (qExpansion 1 f).coeff n) s :=
  LSeriesSummable_of_abscissaOfAbsConv_lt_re
    ((abscissaOfAbsConv_qExpansion_coeff_le_of_Gamma1_le hΓ f).trans_lt (mod_cast hs))

/-- On the half-plane `Re s > k`, for any arithmetic subgroup `Γ` containing `Γ₁(N)` and positive
weight `k > 0`, the `q`-expansion coefficient L-series of `f` equals `ModularForm.L hk f s`. -/
theorem LSeries_qExpansion_coeff_eq_of_Gamma1_le [Γ.IsArithmetic]
    (hΓ : (Gamma1 N).map (mapGL ℝ) ≤ Γ) (hk : 0 < k) [ModularFormClass F Γ k] (f : F) {s : ℂ}
    (hs : k < s.re) :
    LSeries (fun n ↦ (qExpansion 1 f).coeff n) s = _root_.ModularForm.L hk f s := by
  let f₁ := _root_.ModularForm.restrict hΓ (ModularFormClass.modularForm f)
  have hcoe : (f₁ : ℍ → ℂ) = f := by ext; simp [f₁]
  have hsk : s ≠ k := fun h ↦ hs.ne' (by simpa using congrArg Complex.re h)
  have habs : LSeries.abscissaOfAbsConv
      (fun n ↦ (qExpansion (((Gamma1 N).map (mapGL ℝ)).strictWidthInfty) f₁).coeff n) < s.re := by
    rw [strictWidthInfty_Gamma1]
    exact (abscissaOfAbsConv_qExpansion_coeff_le_of_Gamma1_le le_rfl f₁).trans_lt (mod_cast hs)
  have h := _root_.ModularForm.LSeries_qExpansion_coeff_eq_of_abscissaOfAbsConv_lt_re hk f₁
    (Or.inl hsk) habs
  rwa [strictWidthInfty_Gamma1, Complex.ofReal_one, Complex.one_cpow, one_mul, hcoe,
    _root_.ModularForm.L_congr hk hcoe] at h

/-- On the half-plane `Re s > k`, for any arithmetic subgroup `Γ` containing `Γ₁(N)` and positive
weight `k > 0`, the plain Dirichlet series `∑ aₙ / n ^ s` converges to `ModularForm.L hk f s`. -/
theorem hasSum_L_of_Gamma1_le [Γ.IsArithmetic]
    (hΓ : (Gamma1 N).map (mapGL ℝ) ≤ Γ) (hk : 0 < k) [ModularFormClass F Γ k] (f : F) {s : ℂ}
    (hs : k < s.re) :
    HasSum (fun n : ℕ ↦ (qExpansion 1 f).coeff n / (n : ℂ) ^ s) (_root_.ModularForm.L hk f s) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp only [Complex.zero_re] at hs
    have : (0 : ℝ) < k := mod_cast hk
    linarith
  have hsum := (LSeriesSummable_qExpansion_coeff_of_Gamma1_le hΓ f hs).LSeriesHasSum
  rw [LSeries_qExpansion_coeff_eq_of_Gamma1_le hΓ hk f hs] at hsum
  rwa [LSeriesHasSum, funext (LSeries.term_of_ne_zero' hs0 _)] at hsum

end ModularFormClass

end TauCeti
