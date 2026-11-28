/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.MvPowerSeries.Substitution
import TauCeti.RingTheory.MvPowerSeries.ImplicitFunction
import TauCeti.RingTheory.MvPowerSeries.NormCoeff
import TauCeti.RingTheory.MvPowerSeries.Order

/-!
# Inverse of a twisted system of Lubin–Tate logarithms

For a self-map `ς` of the variables, the twisted logarithm at `x` has terms
`p⁻ᵉ X_(ς^[e] x)^(q^e)`. Its linear part is the identity. After formal inversion,
the equation for each coefficient of the inverse involves only lower-degree coefficients.

This is §3.1 of the Tau Ceti roadmap *Hodge–Tate lattices and Lubin–Tate logarithms*.
The twisted power notation follows §4.1 of *Lubin–Tate formal modules and quasi-canonical lifts*.

## References

Levent Alpöge's Riemann-hypothesis formalization proves the case `q = p²` in
`Formalism/GaussJetBounds/GenLogInverse.lean`, where the twisted system is
`Formalism.DworkPowerSeriesWeights.genLog`. The proof here follows the degree induction route
given for general `q` in §3.1.
-/

public section

namespace TauCeti

open Finset MvPowerSeries

open scoped Classical in
/-- The twisted logarithm at `x`, with summands `p⁻ᵉ X_(ς^[e] x)^(q^e)`.
For `q ≥ 2`, only indices `e` smaller than the total degree can contribute. -/
noncomputable def twistedLog (K : Type*) [Field K] (p : ℕ) {S : Type*} (ς : S → S) (q : ℕ)
    (x : S) : MvPowerSeries S K :=
  fun n => ∑ e ∈ range (Finsupp.degree n + 1),
    if n = Finsupp.single (ς^[e] x) (q ^ e) then ((p : K) ^ e)⁻¹ else 0

section Formal

variable {K S : Type*} [Field K] {p q : ℕ} {ς : S → S}

/-- The first `m` terms determine the logarithm below degree `q^m`. -/
private theorem le_order_twistedLog_sub_sum (hq : 2 ≤ q) (x : S) (m : ℕ) :
    ((q ^ m : ℕ) : ℕ∞) ≤
      (twistedLog K p ς q x -
        ∑ e ∈ range m, ((p : K) ^ e)⁻¹ • (X (ς^[e] x) : MvPowerSeries S K) ^ q ^ e).order := by
  classical
  refine nat_le_order fun n hn ↦ ?_
  rw [map_sub, sub_eq_zero, coeff_apply (twistedLog K p ς q x), twistedLog, map_sum]
  simp only [coeff_smul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  have hzero (e : ℕ) (he : n.degree < q ^ e) :
      (if n = Finsupp.single (ς^[e] x) (q ^ e) then ((p : K) ^ e)⁻¹ else 0) = 0 :=
    ite_eq_right fun h ↦ he.ne (by
      simpa only [Finsupp.degree_single] using congrArg Finsupp.degree h)
  rcases le_total (n.degree + 1) m with hm | hm
  · refine sum_subset (range_mono hm) fun e _ he ↦ hzero e ?_
    exact (show n.degree < e by simpa only [mem_range, not_lt, Nat.succ_le_iff] using he).trans
      (Nat.lt_pow_self (by omega : 1 < q))
  · symm
    refine sum_subset (range_mono hm) fun e _ he ↦ hzero e ?_
    exact hn.trans_le (Nat.pow_le_pow_right (by omega) (by simpa only [mem_range, not_lt] using he))

private theorem two_le_order_twistedLog_sub_X (hq : 2 ≤ q) (x : S) :
    (2 : ℕ∞) ≤ (twistedLog K p ς q x - X x).order := by
  have h := le_order_twistedLog_sub_sum (K := K) (p := p) (ς := ς) hq x 1
  exact (show (2 : ℕ∞) ≤ (q : ℕ∞) by exact_mod_cast hq).trans (by simpa using h)

private theorem coeff_subst_twistedLog {g : S → MvPowerSeries S K} (hg : HasSubst g)
    (hg₀ : ∀ x, constantCoeff (g x) = 0) (hq : 2 ≤ q) (x : S) (n : S →₀ ℕ) :
    coeff n (subst g (twistedLog K p ς q x)) =
      coeff n (g x) +
        ∑ e ∈ range n.degree, ((p : K) ^ (e + 1))⁻¹ *
          coeff n (g (ς^[e + 1] x) ^ q ^ (e + 1)) := by
  let m := n.degree + 1
  let F : MvPowerSeries S K :=
    ∑ e ∈ range m, ((p : K) ^ e)⁻¹ • (X (ς^[e] x) : MvPowerSeries S K) ^ q ^ e
  have horder := (le_order_twistedLog_sub_sum (K := K) (p := p) (ς := ς) hq x m).trans
    (order_le_order_subst hg hg₀ (twistedLog K p ς q x - F))
  have hlt : n.degree < q ^ m :=
    n.degree.lt_succ_self.trans (Nat.lt_pow_self (by omega : 1 < q))
  have h := coeff_of_lt_order (d := n) ((Nat.cast_lt.mpr hlt).trans_le horder)
  rw [subst_sub hg, map_sub, sub_eq_zero] at h
  rw [h, ← coe_substAlgHom hg]
  simp only [F, map_sum, map_smul, map_pow, substAlgHom_X, m]
  rw [Finset.sum_range_succ']
  simp [add_comm]

end Formal

section Norm

variable {K S : Type*} [NormedField K] [IsUltrametricDist K] [Finite S]

/-- In a power of exponent at least two, only terms of smaller degree than `n` contribute to
the coefficient at `n`. Their geometric bounds multiply under convolution. -/
private theorem norm_coeff_pow_le_rpow_sub {f : MvPowerSeries S K} (hf₀ : constantCoeff f = 0)
    {r : ℝ} (hr : 0 < r) (n : S →₀ ℕ) {k : ℕ} (hk : 2 ≤ k)
    (hf : ∀ t : S →₀ ℕ, t.degree < n.degree → t ≠ 0 →
      ‖coeff t f‖ ≤ r ^ ((t.degree : ℝ) - 1)) :
    ‖coeff n (f ^ k)‖ ≤ r ^ ((n.degree : ℝ) - k) := by
  let f' : MvPowerSeries S K := ↑(truncTotal n.degree f)
  have hcoeff (t : S →₀ ℕ) : coeff t f' = if t.degree < n.degree then coeff t f else 0 := by
    rw [MvPolynomial.coeff_coe, coeff_truncTotal_eq_ite]
  have hf'₀ : constantCoeff f' = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hcoeff]
    simp [hf₀]
  have hdiff : (n.degree : ℕ∞) ≤ (f - f').order := by
    refine nat_le_order fun t ht ↦ ?_
    rw [map_sub, hcoeff, ite_eq_left ht, sub_self]
  have hlt : (n.degree : ℕ∞) < ((n.degree + k - 1 : ℕ) : ℕ∞) := by
    exact_mod_cast (show n.degree < n.degree + k - 1 by omega)
  have h := coeff_of_lt_order (d := n) (hlt.trans_le (le_order_pow_sub_pow hf₀ hf'₀ hdiff))
  rw [map_sub, sub_eq_zero] at h
  have hweight (t : S →₀ ℕ) : t.prod (fun _ j ↦ r ^ j) = r ^ t.degree := by
    simp only [Finsupp.prod, Finsupp.degree_apply, Finset.prod_pow_eq_pow_sum]
  have hf' (t : S →₀ ℕ) : ‖coeff t f'‖ ≤ r⁻¹ * t.prod (fun _ j ↦ r ^ j) := by
    rw [hweight]
    by_cases ht : t = 0
    · simp [ht, hf'₀, hr.le]
    rw [hcoeff]
    split_ifs with hlt
    · simpa only [Real.rpow_sub_one hr.ne', Real.rpow_natCast, div_eq_mul_inv, mul_comm] using
        hf t hlt ht
    · exact (norm_zero.trans_le (mul_nonneg (inv_nonneg.mpr hr.le) (pow_nonneg hr.le _)))
  rw [h, Real.rpow_sub_natCast hr.ne', Real.rpow_natCast, div_eq_mul_inv, ← inv_pow, mul_comm,
    ← hweight]
  exact norm_coeff_pow_le_pow_mul_prod_pow (s := fun _ ↦ r) (fun _ ↦ hr.le) hf' k n

private theorem norm_coeff_le_of_subst_twistedLog {p : ℕ} (hp : p.Prime)
    (hpK : ‖(p : K)‖ = (p : ℝ)⁻¹) {ς : S → S} {q : ℕ} (hq : 2 ≤ q)
    {g : S → MvPowerSeries S K} (hg₀ : ∀ x, constantCoeff (g x) = 0)
    (hg : ∀ x, subst g (twistedLog K p ς q x) = X x) (x : S) (n : S →₀ ℕ) (hn : n ≠ 0) :
    ‖coeff n (g x)‖ ≤ (p : ℝ) ^ (((n.degree : ℝ) - 1) / ((q : ℝ) - 1)) := by
  have hp₁ : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hpR : 0 < (p : ℝ) := zero_lt_one.trans_le hp₁
  have hqR : 0 < (q : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast (show 1 < q by omega))
  let r : ℝ := (p : ℝ) ^ ((q : ℝ) - 1)⁻¹
  have hr : 0 < r := Real.rpow_pos_of_pos hpR _
  have hrpow (d : ℕ) (k : ℝ) : r ^ ((d : ℝ) - k) =
      (p : ℝ) ^ (((d : ℝ) - k) / ((q : ℝ) - 1)) := by
    dsimp only [r]
    rw [← Real.rpow_mul hpR.le, div_eq_mul_inv, mul_comm]
  induction hN : n.degree using Nat.strong_induction_on generalizing x n with
  | ind N ih =>
    rw [← hN]
    have hnR : 1 ≤ (n.degree : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h ↦ hn ((Finsupp.degree_eq_zero_iff n).mp h))
    have heq := congrArg (coeff n) (hg x)
    rw [coeff_subst_twistedLog (hasSubst_of_constantCoeff_zero hg₀) hg₀ hq] at heq
    rw [eq_sub_of_add_eq heq, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · refine (norm_coeff_X_le_one x n).trans ?_
      calc
        1 = (p : ℝ) ^ (0 : ℝ) := (Real.rpow_zero _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hp₁ (div_nonneg (sub_nonneg.mpr hnR) hqR.le)
    rw [norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hpR.le _) ?_
    intro e _
    let k := q ^ (e + 1)
    have hk : 2 ≤ k := hq.trans (by
      simpa only [pow_one, k] using
        (Nat.pow_le_pow_right (by omega : 0 < q) (Nat.succ_pos e) : q ^ 1 ≤ q ^ (e + 1)))
    have hpow := norm_coeff_pow_le_rpow_sub (hg₀ (ς^[e + 1] x)) hr n hk fun t ht ht₀ ↦ by
      rw [hrpow]
      simpa using ih t.degree (ht.trans_le hN.le) (ς^[e + 1] x) t ht₀ rfl
    -- Write the power using `k` to match the bound in `hpow`.
    change ‖((p : K) ^ (e + 1))⁻¹ * coeff n (g (ς^[e + 1] x) ^ k)‖ ≤ _
    rw [norm_mul, norm_inv, norm_pow, hpK, inv_pow, inv_inv]
    calc
      _ ≤ (p : ℝ) ^ (e + 1) * (p : ℝ) ^ (((n.degree : ℝ) - k) / ((q : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left (by simpa only [hrpow] using hpow) (pow_nonneg hpR.le _)
      _ = (p : ℝ) ^ (((e + 1 : ℕ) : ℝ) + ((n.degree : ℝ) - k) / ((q : ℝ) - 1)) := by
        rw [Real.rpow_add hpR, Real.rpow_natCast]
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hp₁
        have hgeom : 1 + ((e + 1 : ℕ) : ℝ) * ((q : ℝ) - 1) ≤ (k : ℝ) := by
          simpa only [k, Nat.cast_pow] using
            one_add_mul_sub_le_pow (by linarith : (-1 : ℝ) ≤ q) (e + 1)
        apply (le_div_iff₀ hqR).mpr
        rw [add_mul, div_mul_cancel₀ _ hqR.ne']
        linarith

end Norm

/-- A twisted logarithm system has a unique zero-constant inverse for substitution. It is
two-sided, and the coefficient of degree `d > 0` has norm at most `p ^ ((d - 1) / (q - 1))`
when `‖(p : K)‖ = p⁻¹`. -/
theorem exists_twistedLog_inverse_norm_coeff_le (K : Type*) [NormedField K] [IsUltrametricDist K]
    (p : ℕ) (hp : p.Prime) (hpK : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {S : Type*} [Finite S] (ς : S → S) (q : ℕ) (hq : 2 ≤ q) :
    ∃ g : S → MvPowerSeries S K,
      (∀ x, constantCoeff (g x) = 0) ∧
      (∀ x, subst g (twistedLog K p ς q x) = X x) ∧
      (∀ g' : S → MvPowerSeries S K, (∀ x, constantCoeff (g' x) = 0) →
        (∀ x, subst g' (twistedLog K p ς q x) = X x) → g' = g) ∧
      (∀ x, subst (twistedLog K p ς q) (g x) = X x) ∧
      ∀ x (n : S →₀ ℕ), n ≠ 0 →
        ‖coeff n (g x)‖ ≤ (p : ℝ) ^ (((n.degree : ℝ) - 1) / ((q : ℝ) - 1)) := by
  let L := twistedLog K p ς q
  have hL₂ : ∀ x, (2 : ℕ∞) ≤ (L x - X x).order := two_le_order_twistedLog_sub_X hq
  have hL₀ (x : S) : constantCoeff (L x) = 0 := by
    simpa using constantCoeff_eq_zero_of_le_order (by decide) (hL₂ x)
  obtain ⟨⟨g, hg₀⟩, hg, huniq⟩ :=
    existsUnique_subst_eq_of_two_le_order_sub_X L hL₂ X constantCoeff_X
  have hright (x : S) : subst g (L x) = X x := by
    simpa only [substAlgHom_apply] using hg x
  have hleft (x : S) : subst L (g x) = X x := by
    let gL : {a : S → MvPowerSeries S K // ∀ y, constantCoeff (a y) = 0} :=
      ⟨fun y ↦ subst L (g y), fun y ↦
        constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hL₀) hL₀ (hg₀ y)⟩
    let vars : {a : S → MvPowerSeries S K // ∀ y, constantCoeff (a y) = 0} :=
      ⟨X, constantCoeff_X⟩
    have heq : gL = vars := (existsUnique_subst_eq_of_two_le_order_sub_X L hL₂ L hL₀).unique
      (by
        intro y
        rw [substAlgHom_apply]
        dsimp only [gL]
        have hs := hasSubst_of_constantCoeff_zero hL₀
        rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hg₀) hs, hright y, subst_X hs])
      (by
        intro y
        rw [substAlgHom_apply]
        exact congrFun subst_self (L y))
    exact congrArg (fun a ↦ a.val x) heq
  refine ⟨g, hg₀, hright, ?_, hleft, norm_coeff_le_of_subst_twistedLog hp hpK hq hg₀ hright⟩
  intro g' hg'₀ hg'
  exact congrArg Subtype.val (huniq ⟨g', hg'₀⟩ fun x ↦ by
    simpa only [substAlgHom_apply] using hg' x)

end TauCeti
