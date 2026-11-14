/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Asymptotics.Arith
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Group.Order

/-!
# Uniform-grid increment bounds from one-sided Lipschitz oscillation

If a curve `f : ℝ → E` satisfies the right-sided pointwise Lipschitz bound
`(f · - f t) =O[𝓝[>] t] (· - t)` at `t : ℝ` (in particular, if `f` is right-differentiable at `t`),
then for every window length `p : ℕ` and every sufficiently small mesh `h > 0`, the `p` consecutive
uniform-grid increments immediately to the right of `t` (starting at integer index `⌊t / h⌋ + 1`)
all have norm `O(h)`. By reflection `s ↦ f (-s)`, a dual statement holds for left-sided oscillation
`(f · - f t) =O[𝓝[<] t] (· - t)` using the `p` consecutive grid increments immediately to the left
of `t` (starting at integer index `⌈t / h⌉ - (p + 1)`).

Contrapositively, if inside a one-sided neighborhood `s ∈ 𝓝[>] t` (resp. `s ∈ 𝓝[<] t`) every block
of `p` consecutive dyadic `2⁻ⁿ`-increments contained in `s` eventually has an increment exceeding
`M / 2ⁿ`, then `f` fails the corresponding one-sided pointwise Lipschitz bound at `t`, and in
particular fails one-sided and two-sided differentiability at `t`.

## Main statements

* `Asymptotics.IsBigO.exists_forall_norm_sub_mul_le_of_nhdsGT` — right-sided uniform-mesh window
  bound from `(f · - f t) =O[𝓝[>] t] (· - t)`.
* `Asymptotics.IsBigO.exists_forall_norm_sub_mul_le_of_nhdsLT` — left-sided uniform-mesh window
  bound from `(f · - f t) =O[𝓝[<] t] (· - t)`.
* `TauCeti.not_isBigO_sub_nhdsGT_of_dyadic` and `TauCeti.not_isBigO_sub_nhdsLT_of_dyadic` —
  obstruction to one-sided pointwise Lipschitz oscillation from local dyadic rough-path oscillation.
* `TauCeti.not_differentiableWithinAt_Ici_of_dyadic`,
  `TauCeti.not_differentiableWithinAt_Iic_of_dyadic`, and `TauCeti.not_differentiableAt_of_dyadic` —
  resulting non-existence of one-sided and two-sided derivatives.

## References

* P. Mörters, Y. Peres, *Brownian Motion*, Cambridge University Press, 2010, Theorem 1.30.
* A. Dvoretzky, P. Erdős, S. Kakutani, *Nonincrease everywhere of the Brownian motion process*,
  Proc. Fourth Berkeley Symp. Math. Statist. Probab., Vol. II (1961), 103–116.
-/

public section

open Filter Set
open scoped Topology

namespace Asymptotics.IsBigO

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] {f : ℝ → E} {t : ℝ}

/-- If `f` has bounded right-sided linear oscillation `(f · - f t) =O[𝓝[>] t] (· - t)` at `t : ℝ`,
then for every window length `p : ℕ` there exist `K > 0` and `δ > 0` such that for every mesh
`0 < h` with `(p + 1) * h < δ`, all `p` consecutive integer-grid increments immediately to the right
of `t` have norm at most `K * h`. -/
theorem exists_forall_norm_sub_mul_le_of_nhdsGT
    (h : (f · - f t) =O[𝓝[>] t] (· - t)) (p : ℕ) :
    ∃ K > 0, ∃ δ > 0, ∀ {h₀ : ℝ}, 0 < h₀ → ((p + 1 : ℕ) : ℝ) * h₀ < δ →
      ∀ j < p,
        ‖f (((⌊t / h₀⌋ + 1 + j + 1 : ℤ) : ℝ) * h₀) -
            f (((⌊t / h₀⌋ + 1 + j : ℤ) : ℝ) * h₀)‖ ≤ K * h₀ := by
  obtain ⟨C, hC, hbound⟩ := h.exists_pos
  obtain ⟨b, htb, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hbound.bound
  refine ⟨2 * ((p + 1 : ℕ) : ℝ) * C, by positivity, b - t, sub_pos.mpr htb, ?_⟩
  intro h₀ hh₀ hmesh j hj
  have hpt (k : ℕ) (hk : k ≤ p) :
      ‖f (((⌊t / h₀⌋ + 1 + k : ℤ) : ℝ) * h₀) - f t‖ ≤ C * (((p + 1 : ℕ) : ℝ) * h₀) := by
    set s : ℝ := ((⌊t / h₀⌋ + 1 + k : ℤ) : ℝ) * h₀
    have hts : t < s := (div_lt_iff₀ hh₀).mp <|
      (Int.lt_floor_add_one _).trans_le (by push_cast; linarith)
    have hst : s ≤ t + ((p + 1 : ℕ) : ℝ) * h₀ := by
      have hle : ((⌊t / h₀⌋ + 1 + k : ℤ) : ℝ) ≤ t / h₀ + ((p + 1 : ℕ) : ℝ) := by
        have hfl : (⌊t / h₀⌋ : ℝ) ≤ t / h₀ := Int.floor_le _
        have hkp : (k : ℝ) ≤ p := Nat.cast_le.mpr hk
        push_cast
        linarith
      calc
        s ≤ (t / h₀ + ((p + 1 : ℕ) : ℝ)) * h₀ := mul_le_mul_of_nonneg_right hle hh₀.le
        _ = t + ((p + 1 : ℕ) : ℝ) * h₀ := by rw [add_mul, div_mul_cancel₀ _ hh₀.ne']
    calc
      ‖f s - f t‖ ≤ C * ‖s - t‖ := hb ⟨hts, by linarith⟩
      _ = C * (s - t) := by rw [Real.norm_of_nonneg (sub_pos.mpr hts).le]
      _ ≤ C * (((p + 1 : ℕ) : ℝ) * h₀) := by gcongr; linarith
  calc
    ‖f (((⌊t / h₀⌋ + 1 + j + 1 : ℤ) : ℝ) * h₀) - f (((⌊t / h₀⌋ + 1 + j : ℤ) : ℝ) * h₀)‖
      ≤ ‖f (((⌊t / h₀⌋ + 1 + (j + 1 : ℕ) : ℤ) : ℝ) * h₀) - f t‖ +
          ‖f t - f (((⌊t / h₀⌋ + 1 + j : ℤ) : ℝ) * h₀)‖ := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
          norm_sub_le_norm_sub_add_norm_sub _ (f t) _
    _ = ‖f (((⌊t / h₀⌋ + 1 + (j + 1 : ℕ) : ℤ) : ℝ) * h₀) - f t‖ +
          ‖f (((⌊t / h₀⌋ + 1 + j : ℤ) : ℝ) * h₀) - f t‖ := by
        rw [norm_sub_rev (f t)]
    _ ≤ C * (((p + 1 : ℕ) : ℝ) * h₀) + C * (((p + 1 : ℕ) : ℝ) * h₀) :=
        add_le_add (hpt (j + 1) hj) (hpt j hj.le)
    _ = 2 * ((p + 1 : ℕ) : ℝ) * C * h₀ := by ring

/-- If `f` has bounded left-sided linear oscillation `(f · - f t) =O[𝓝[<] t] (· - t)` at `t : ℝ`,
then for every window length `p : ℕ` there exist `K > 0` and `δ > 0` such that for every mesh
`0 < h` with `(p + 1) * h < δ`, all `p` consecutive integer-grid increments from
`(⌈t / h⌉ - (p + 1)) * h` to `(⌈t / h⌉ - 1) * h` (strictly to the left of `t`) have norm at most
`K * h`. -/
theorem exists_forall_norm_sub_mul_le_of_nhdsLT
    (h : (f · - f t) =O[𝓝[<] t] (· - t)) (p : ℕ) :
    ∃ K > 0, ∃ δ > 0, ∀ {h₀ : ℝ}, 0 < h₀ → ((p + 1 : ℕ) : ℝ) * h₀ < δ →
      ∀ j < p,
        ‖f (((⌈t / h₀⌉ - (p + 1) + j + 1 : ℤ) : ℝ) * h₀) -
            f (((⌈t / h₀⌉ - (p + 1) + j : ℤ) : ℝ) * h₀)‖ ≤ K * h₀ := by
  have hneg : (fun s : ℝ ↦ f (-s) - f (- -t)) =O[𝓝[>] (-t)] (· - (-t)) :=
    ((h.comp_tendsto tendsto_neg_nhdsGT_neg).congr (fun s ↦ by simp)
      fun s ↦ by simp only [Function.comp_apply]; ring).of_neg_right
  obtain ⟨K, hK, δ, hδ, hwin⟩ := hneg.exists_forall_norm_sub_mul_le_of_nhdsGT p
  refine ⟨K, hK, δ, hδ, fun {h₀} hh₀ hmesh j hj ↦ ?_⟩
  have hj' : p - 1 - j < p := by omega
  have hstep := hwin hh₀ hmesh (p - 1 - j) hj'
  have hfl : ⌊(-t) / h₀⌋ = -⌈t / h₀⌉ := by rw [neg_div, Int.floor_neg]
  have ha : -(((⌊(-t) / h₀⌋ + 1 + (p - 1 - j : ℕ) + 1 : ℤ) : ℝ) * h₀) =
      ((⌈t / h₀⌉ - (p + 1) + j : ℤ) : ℝ) * h₀ := by
    rw [hfl, ← neg_mul, ← Int.cast_neg]
    congr 2
    omega
  have hb : -(((⌊(-t) / h₀⌋ + 1 + (p - 1 - j : ℕ) : ℤ) : ℝ) * h₀) =
      ((⌈t / h₀⌉ - (p + 1) + j + 1 : ℤ) : ℝ) * h₀ := by
    rw [hfl, ← neg_mul, ← Int.cast_neg]
    congr 2
    omega
  rwa [ha, hb, norm_sub_rev] at hstep

end Seminormed

end Asymptotics.IsBigO

namespace TauCeti

section Dyadic

variable {E : Type*}

/-- If inside a right-sided neighborhood `s ∈ 𝓝[>] t` every window of `p` consecutive dyadic
`2⁻ⁿ`-increments eventually contains an increment exceeding `M / 2ⁿ`, then `f` fails the
right-sided Lipschitz bound `(f · - f t) =O[𝓝[>] t] (· - t)`. -/
theorem not_isBigO_sub_nhdsGT_of_dyadic [SeminormedAddCommGroup E] {f : ℝ → E} {p : ℕ}
    {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝[>] t)
    (hosc : ∀ M : ℕ, ∀ᶠ n in atTop, ∀ m : ℤ,
      (∀ k ≤ p, ((m + k : ℤ) : ℝ) / 2 ^ n ∈ s) →
      ∃ j : Fin p,
        (M : ℝ) / 2 ^ n < ‖f (((m + j + 1 : ℤ) : ℝ) / 2 ^ n) - f (((m + j : ℤ) : ℝ) / 2 ^ n)‖) :
    ¬ (f · - f t) =O[𝓝[>] t] (· - t) := by
  intro hO
  obtain ⟨K, _, δ, hδ, hwin⟩ := hO.exists_forall_norm_sub_mul_le_of_nhdsGT p
  obtain ⟨b, htb, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hs
  have hδ' : 0 < min δ (b - t) := lt_min hδ (sub_pos.mpr htb)
  have hlim : Tendsto (fun n : ℕ ↦ ((p + 1 : ℕ) : ℝ) * (2⁻¹ : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)).const_mul
        ((p + 1 : ℕ) : ℝ)
  obtain ⟨n, hn_osc, hn_mesh⟩ :=
    ((hosc ⌈K⌉₊).and (hlim.eventually (gt_mem_nhds hδ'))).exists
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hh₀ : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := inv_pos.mpr hpow_pos
  have hmesh' : ((p + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ n)⁻¹ < min δ (b - t) := by
    simpa only [inv_pow] using hn_mesh
  set m : ℤ := ⌊t / ((2 : ℝ) ^ n)⁻¹⌋ + 1
  have hm_mem (k : ℕ) (hk : k ≤ p) : ((m + k : ℤ) : ℝ) / 2 ^ n ∈ s := by
    apply hb
    refine ⟨(lt_div_iff₀ hpow_pos).mpr ?_, (div_lt_iff₀ hpow_pos).mpr ?_⟩
    · have h1 : t * (2 : ℝ) ^ n < (⌊t / ((2 : ℝ) ^ n)⁻¹⌋ : ℝ) + 1 := by
        simpa only [div_inv_eq_mul] using Int.lt_floor_add_one (t / ((2 : ℝ) ^ n)⁻¹)
      exact h1.trans_le (by push_cast [m]; linarith)
    · have hfl : (⌊t / ((2 : ℝ) ^ n)⁻¹⌋ : ℝ) ≤ t * (2 : ℝ) ^ n := by
        simpa only [div_inv_eq_mul] using Int.floor_le (t / ((2 : ℝ) ^ n)⁻¹)
      have hbt : ((p + 1 : ℕ) : ℝ) < (b - t) * (2 : ℝ) ^ n :=
        (div_lt_iff₀ hpow_pos).mp
          (by simpa only [div_eq_mul_inv] using hmesh'.trans_le (min_le_right _ _))
      have hkp : (k : ℝ) ≤ p := Nat.cast_le.mpr hk
      push_cast [m] at hbt ⊢
      linarith
  obtain ⟨j, hj_gt⟩ := hn_osc m hm_mem
  have hj_le := hwin hh₀ (hmesh'.trans_le (min_le_left _ _)) j j.isLt
  have hKM : K * ((2 : ℝ) ^ n)⁻¹ ≤ (⌈K⌉₊ : ℝ) * ((2 : ℝ) ^ n)⁻¹ :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil K) hh₀.le
  simp only [div_eq_mul_inv] at hj_gt
  linarith

/-- If inside a left-sided neighborhood `s ∈ 𝓝[<] t` every window of `p` consecutive dyadic
`2⁻ⁿ`-increments eventually contains an increment exceeding `M / 2ⁿ`, then `f` fails the
left-sided Lipschitz bound `(f · - f t) =O[𝓝[<] t] (· - t)`. -/
theorem not_isBigO_sub_nhdsLT_of_dyadic [SeminormedAddCommGroup E] {f : ℝ → E} {p : ℕ}
    {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝[<] t)
    (hosc : ∀ M : ℕ, ∀ᶠ n in atTop, ∀ m : ℤ,
      (∀ k ≤ p, ((m + k : ℤ) : ℝ) / 2 ^ n ∈ s) →
      ∃ j : Fin p,
        (M : ℝ) / 2 ^ n < ‖f (((m + j + 1 : ℤ) : ℝ) / 2 ^ n) - f (((m + j : ℤ) : ℝ) / 2 ^ n)‖) :
    ¬ (f · - f t) =O[𝓝[<] t] (· - t) := by
  intro hO
  have hneg : (fun u : ℝ ↦ f (-u) - f (- -t)) =O[𝓝[>] (-t)] (· - (-t)) :=
    ((hO.comp_tendsto tendsto_neg_nhdsGT_neg).congr (fun u ↦ by simp)
      fun u ↦ by simp only [Function.comp_apply]; ring).of_neg_right
  refine not_isBigO_sub_nhdsGT_of_dyadic (p := p) (s := Neg.neg ⁻¹' s)
    (tendsto_neg_nhdsGT_neg hs) (fun M ↦ (hosc M).mono fun n hn m' hm' ↦ ?_) hneg
  have hm_mem (k : ℕ) (hk : k ≤ p) : ((-(m' + p) + k : ℤ) : ℝ) / 2 ^ n ∈ s := by
    have hk' : p - k ≤ p := Nat.sub_le p k
    have hmem : -(((m' + (p - k : ℕ) : ℤ) : ℝ) / 2 ^ n) ∈ s := hm' (p - k) hk'
    convert hmem using 1
    rw [← neg_div, ← Int.cast_neg]
    congr 2
    omega
  obtain ⟨j, hj⟩ := hn (-(m' + p)) hm_mem
  refine ⟨j.rev, ?_⟩
  have ha : ((-(m' + p) + j + 1 : ℤ) : ℝ) / 2 ^ n = -(((m' + j.rev : ℤ) : ℝ) / 2 ^ n) := by
    rw [← neg_div, ← Int.cast_neg]
    congr 2
    have := j.isLt
    simp only [Fin.val_rev]
    omega
  have hb : ((-(m' + p) + j : ℤ) : ℝ) / 2 ^ n = -(((m' + j.rev + 1 : ℤ) : ℝ) / 2 ^ n) := by
    rw [← neg_div, ← Int.cast_neg]
    congr 2
    have := j.isLt
    simp only [Fin.val_rev]
    omega
  rwa [ha, hb, norm_sub_rev] at hj

/-- Under the dyadic rough-path oscillation property inside a right-sided neighborhood `s ∈ 𝓝[>] t`,
`f` has no right derivative at `t`. -/
theorem not_differentiableWithinAt_Ici_of_dyadic [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {p : ℕ} {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝[>] t)
    (hosc : ∀ M : ℕ, ∀ᶠ n in atTop, ∀ m : ℤ,
      (∀ k ≤ p, ((m + k : ℤ) : ℝ) / 2 ^ n ∈ s) →
      ∃ j : Fin p,
        (M : ℝ) / 2 ^ n < ‖f (((m + j + 1 : ℤ) : ℝ) / 2 ^ n) - f (((m + j : ℤ) : ℝ) / 2 ^ n)‖) :
    ¬ DifferentiableWithinAt ℝ f (Ici t) t := fun hd ↦
  not_isBigO_sub_nhdsGT_of_dyadic hs hosc
    (hd.isBigO_sub.mono (nhdsWithin_mono _ Ioi_subset_Ici_self))

/-- Under the dyadic rough-path oscillation property inside a left-sided neighborhood `s ∈ 𝓝[<] t`,
`f` has no left derivative at `t`. -/
theorem not_differentiableWithinAt_Iic_of_dyadic [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {p : ℕ} {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝[<] t)
    (hosc : ∀ M : ℕ, ∀ᶠ n in atTop, ∀ m : ℤ,
      (∀ k ≤ p, ((m + k : ℤ) : ℝ) / 2 ^ n ∈ s) →
      ∃ j : Fin p,
        (M : ℝ) / 2 ^ n < ‖f (((m + j + 1 : ℤ) : ℝ) / 2 ^ n) - f (((m + j : ℤ) : ℝ) / 2 ^ n)‖) :
    ¬ DifferentiableWithinAt ℝ f (Iic t) t := fun hd ↦
  not_isBigO_sub_nhdsLT_of_dyadic hs hosc
    (hd.isBigO_sub.mono (nhdsWithin_mono _ Iio_subset_Iic_self))

/-- Under the dyadic rough-path oscillation property inside a right-sided neighborhood `s ∈ 𝓝[>] t`,
`f` is not differentiable at `t`. -/
theorem not_differentiableAt_of_dyadic [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {p : ℕ} {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝[>] t)
    (hosc : ∀ M : ℕ, ∀ᶠ n in atTop, ∀ m : ℤ,
      (∀ k ≤ p, ((m + k : ℤ) : ℝ) / 2 ^ n ∈ s) →
      ∃ j : Fin p,
        (M : ℝ) / 2 ^ n < ‖f (((m + j + 1 : ℤ) : ℝ) / 2 ^ n) - f (((m + j : ℤ) : ℝ) / 2 ^ n)‖) :
    ¬ DifferentiableAt ℝ f t := fun hd ↦
  not_differentiableWithinAt_Ici_of_dyadic hs hosc hd.differentiableWithinAt

end Dyadic

end TauCeti
