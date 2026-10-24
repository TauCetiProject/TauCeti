/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.ModularForms.Bounds
import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Bounds
import TauCeti.NumberTheory.ModularForms.EisensteinSeries.Dimension
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# The sharp non-cuspidal abscissa of convergence

Let `Γ` be a subgroup of `GL₂(ℝ)` containing the image of `Γ₁(N)`, such as `Γ₁(N)` or `Γ₀(N)`.
In weight `k ≥ 3`, the `q`-expansion coefficients of every modular form on `Γ` are `O(n^(k-1))`,
so its L-series `∑ aₙ n^(-s)` converges absolutely for `Re s > k` (Diamond–Shurman,
Proposition 5.9.1). This sharpens the bound `k + 1` that `aₙ = O(nᵏ)` gives for every arithmetic
subgroup (`ModularForm.abscissaOfAbsConv_qExpansion_coeff_le`).

The proof splits a form on `Γ₁(N)` into its Eisenstein and cuspidal parts. The Eisenstein part is
a linear combination of the normalized raised Eisenstein series with character, whose
coefficients are twisted divisor sums and hence `O(n^(k-1))`
(`TauCeti.EisensteinSeries.CharIndex.isBigO_qExpansion_form_coeff`); that these series span the
Eisenstein part is Diamond–Shurman, Theorem 4.5.2
(`TauCeti.EisensteinSeries.span_range_form_eq_congruenceEisensteinSubspace`). The cuspidal part
has coefficients `O(n^(k/2))` by Hecke's bound, and `k/2 ≤ k - 1`. Spanning is known at levels
`N ∉ {1, 2, 4}`; a form on `Γ` is in particular a form on `Γ₁(3N)`, with the same `q`-expansion,
which removes the exceptional levels.

In weights one and two the estimate `aₙ = O(n^(k-1))` is false (the divisor sum `σ₁(n)` is not
`O(n)`), so the hypothesis `3 ≤ k` cannot be dropped from the coefficient bound.

## Main results

* `TauCeti.isBigO_qExpansion_coeff_of_mem_cuspFormSubmodule`: cusp forms on `Γ₁(N)` of weight
  `m ≥ 2` have coefficients `O(n^(m-1))`.
* `TauCeti.ModularFormClass.qExpansion_isBigO_of_Gamma1_le`: the coefficient bound
  `aₙ = O(n^(k-1))`.
* `TauCeti.ModularFormClass.abscissaOfAbsConv_qExpansion_coeff_le_of_Gamma1_le`: the abscissa
  of absolute convergence of the coefficient L-series is at most `k`.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Theorem 4.5.2 and
  Proposition 5.9.1.
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

/-- In weight `m ≥ 3` and at a level `N ∉ {1, 2, 4}`, every modular form on `Γ₁(N)` has
`q`-expansion coefficients `O(n^(m-1))`: its Eisenstein part is a combination of the normalized
raised series with character, and its cuspidal part obeys Hecke's bound. -/
private lemma isBigO_qExpansion_coeff_Gamma1 (hN : 2 < N) (hN4 : N ≠ 4) (hm : 3 ≤ (m : ℤ))
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
  rw [← span_range_form_eq_congruenceEisensteinSubspace hN hN4 hm] at he
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
  have : NeZero (3 * N) := ⟨mul_ne_zero three_ne_zero (NeZero.ne N)⟩
  have hle : (Gamma1 (3 * N)).map (mapGL ℝ) ≤ Γ :=
    (Gamma1_map_le_Gamma1_map_of_dvd (dvd_mul_left N 3)).trans hΓ
  have hN : 2 < 3 * N := by have := NeZero.ne N; omega
  have h := isBigO_qExpansion_coeff_Gamma1 hN (by omega) hk
    (ModularForm.restrict hle (ModularFormClass.modularForm f))
  have hexp : (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) := by omega
  have hcoe : ⇑(ModularForm.restrict hle (ModularFormClass.modularForm f)) = ⇑f := by
    ext; simp
  simpa only [hcoe, hexp, zpow_natCast] using h

/-- **The sharp non-cuspidal abscissa** (Diamond–Shurman, Proposition 5.9.1): if `Γ` contains
`Γ₁(N)`, then the L-series of the `q`-expansion coefficients of a modular form of weight
`k ≥ 3` on `Γ` converges absolutely for `Re s > k`. -/
theorem abscissaOfAbsConv_qExpansion_coeff_le_of_Gamma1_le
    (hΓ : (Gamma1 N).map (mapGL ℝ) ≤ Γ) (hk : 3 ≤ k) [ModularFormClass F Γ k] (f : F) :
    LSeries.abscissaOfAbsConv (fun n ↦ (qExpansion 1 f).coeff n) ≤ ((k : ℝ) : EReal) := by
  have h := LSeries.abscissaOfAbsConv_le_of_isBigO_rpow (x := (k : ℝ) - 1) <|
    (qExpansion_isBigO_of_Gamma1_le hΓ hk f).congr_right fun n ↦ by
      rw [← Real.rpow_intCast, Int.cast_sub, Int.cast_one]
  refine h.trans_eq ?_
  rw [← EReal.coe_one, ← EReal.coe_add, sub_add_cancel]

end ModularFormClass

end TauCeti
