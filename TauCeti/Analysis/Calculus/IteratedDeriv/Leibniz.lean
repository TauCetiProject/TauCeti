/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Leibniz's rule at a zero of a power, and for continuous bilinear maps

The `n`-th derivative of `z ↦ (z - a) ^ n • h z` at `a` is `n! • h a`: in Leibniz's rule every
other term differentiates `(z - a) ^ n` fewer than `n` times and so vanishes at `a`. If an
analytic function `f` factors as `f z = (z - a) ^ n • h z` (for instance through
`AnalyticOnNhd.exists_eq_prod_pow_smul`), this recovers its first possibly nonzero derivative at
`a` from the value of the quotient `h`.

More generally, multiplying by `(z - a) ^ p` shifts the Taylor coefficients at `a` up by `p`
without changing them.

For a continuous bilinear map `B` and functions `f` and `g` that are `Cⁿ` at a point (within a
set with unique derivatives), Leibniz's rule
`(B (f ·) (g ·))⁽ⁿ⁾ = ∑ᵢ (n choose i) B f⁽ⁱ⁾ g⁽ⁿ⁻ⁱ⁾` holds there. Taking `B` to be
`ContinuousLinearMap.compL` gives the rule for pointwise compositions of continuous linear maps.

## Main results

* `TauCeti.iteratedDeriv_pow_sub_smul`: the `n`-th derivative of `z ↦ (z - a) ^ p • h z` at `a`
  equals `n.descFactorial p • iteratedDeriv (n - p) h a`, unconditionally for all `n p : ℕ`
  (vanishing automatically when `n < p`).
* `TauCeti.iteratedDeriv_pow_sub_smul_iteratedDeriv`: the `k`-th derivative of
  `z ↦ (z - a) ^ p • iteratedDeriv q h z` at `a` equals
  `k.descFactorial p • iteratedDeriv (k + q - p) h a`, unconditionally for all `k p q : ℕ`.
* `TauCeti.iteratedDeriv_pow_sub_smul_self`: the `n = p` specialization.
* `TauCeti.inv_factorial_smul_iteratedDeriv_pow_sub_smul`: the `(p + i)`-th Taylor coefficient of
  `z ↦ (z - a) ^ p • h z` at `a` is the `i`-th Taylor coefficient of `h`.
* `TauCeti.iteratedDeriv_pow_sub_smul_eq_zero` and
  `TauCeti.iteratedDeriv_prod_pow_sub_smul_eq_zero`: derivatives of order `< m a` at `a` vanish
  when a `C^k` function is multiplied by `(z - a) ^ n` or `∏ b ∈ S, (z - b) ^ m b`.
* `ContinuousLinearMap.iteratedDerivWithin_of_bilinear`: Leibniz's rule within a set for a
  continuous bilinear map.
* `ContinuousLinearMap.iteratedDeriv_of_bilinear`: the same rule for the plain iterated
  derivative.
-/

public section

namespace TauCeti

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {a : 𝕜}

/-- The `n`-th derivative of `z ↦ (z - a) ^ p • h z` at `a` is
`n.descFactorial p • iteratedDeriv (n - p) h a`: in Leibniz's rule every term other than `j = p`
differentiates `(z - a) ^ p` the wrong number of times and vanishes at `a`. When `n < p`,
`n.descFactorial p = 0`, so both sides vanish with no `p ≤ n` hypothesis. -/
theorem iteratedDeriv_pow_sub_smul (n p : ℕ) {h : 𝕜 → E} (hh : ContDiffAt 𝕜 n h a) :
    iteratedDeriv n (fun z ↦ (z - a) ^ p • h z) a =
      n.descFactorial p • iteratedDeriv (n - p) h a := by
  have hpow (j : ℕ) : iteratedDeriv j (fun z : 𝕜 ↦ (z - a) ^ p) a =
      if j = p then (p.factorial : 𝕜) else 0 := by
    simpa only [sub_self, iteratedDeriv_fun_pow_zero, Nat.cast_ite, Nat.cast_zero] using
      congrFun (iteratedDeriv_comp_sub_const j (fun w : 𝕜 ↦ w ^ p) a) a
  have hL := iteratedDerivWithin_smul (Set.mem_univ a) uniqueDiffOn_univ (n := n)
    (f := fun z : 𝕜 ↦ (z - a) ^ p) (by fun_prop) hh.contDiffWithinAt
  simp only [iteratedDerivWithin_univ] at hL
  have hfun : (fun z ↦ (z - a) ^ p • h z) = (fun z : 𝕜 ↦ (z - a) ^ p) • h := by
    ext z
    simp only [Pi.smul_apply']
  rw [hfun, hL]
  rcases lt_or_ge n p with hnp | hpn
  · rw [Nat.descFactorial_of_lt hnp, zero_smul]
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hjp : j ≠ p := by
      have := Finset.mem_range.mp hj
      omega
    simp [hpow j, hjp]
  · rw [Finset.sum_eq_single_of_mem p (Finset.mem_range.mpr (by omega))
      fun j _ hj ↦ by simp [hpow j, hj]]
    simp only [hpow, ↓reduceIte, Nat.cast_smul_eq_nsmul, smul_smul,
      Nat.descFactorial_eq_factorial_mul_choose, mul_comm (n.choose p)]

/-- The `k`-th derivative of `z ↦ (z - a) ^ p • iteratedDeriv q h z` at `a` equals
`k.descFactorial p • iteratedDeriv (k + q - p) h a`, unconditionally for all `k p q : ℕ`.
When `k < p`, `k.descFactorial p = 0`, so both sides vanish automatically. -/
theorem iteratedDeriv_pow_sub_smul_iteratedDeriv (k p q : ℕ) {h : 𝕜 → E}
    (hh : ContDiffAt 𝕜 k (iteratedDeriv q h) a) :
    iteratedDeriv k (fun z ↦ (z - a) ^ p • iteratedDeriv q h z) a =
      k.descFactorial p • iteratedDeriv (k + q - p) h a := by
  rw [iteratedDeriv_pow_sub_smul k p hh]
  rcases lt_or_ge k p with hkp | hpk
  · simp [Nat.descFactorial_of_lt hkp]
  · congr 1
    simp only [iteratedDeriv_eq_iterate, ← Function.iterate_add_apply]
    rw [Nat.sub_add_comm hpk]

/-- The `n`-th derivative of `z ↦ (z - a) ^ n • h z` at `a` is `n! • h a`: in Leibniz's rule
every other term differentiates `(z - a) ^ n` fewer than `n` times and so vanishes at `a`. -/
theorem iteratedDeriv_pow_sub_smul_self {h : 𝕜 → E} {n : ℕ} (hh : ContDiffAt 𝕜 n h a) :
    iteratedDeriv n (fun z ↦ (z - a) ^ n • h z) a = n.factorial • h a := by
  simpa [Nat.descFactorial_self] using iteratedDeriv_pow_sub_smul n n hh

/-- **Taylor-shift invariance.** Multiplying `h` by `(z - a) ^ p` shifts its Taylor coefficients at
`a` up by `p` without changing them: the `(p + i)`-th Taylor coefficient at `a` of
`z ↦ (z - a) ^ p • h z` is the `i`-th Taylor coefficient of `h`. In Leibniz's rule only the term
that differentiates `(z - a) ^ p` exactly `p` times survives at `a`. -/
theorem inv_factorial_smul_iteratedDeriv_pow_sub_smul [CharZero 𝕜] (p i : ℕ) {h : 𝕜 → E}
    (hh : ContDiffAt 𝕜 (p + i) h a) :
    ((p + i).factorial : 𝕜)⁻¹ • iteratedDeriv (p + i) (fun z ↦ (z - a) ^ p • h z) a =
      (i.factorial : 𝕜)⁻¹ • iteratedDeriv i h a := by
  rw [iteratedDeriv_pow_sub_smul (p + i) p hh, Nat.add_sub_cancel_left,
    ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul]
  congr 1
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right p i)
  rw [Nat.add_sub_cancel_left, mul_comm ((p + i).choose p),
    ← Nat.descFactorial_eq_factorial_mul_choose] at h
  have hd : ((p + i).descFactorial p : 𝕜) ≠ 0 := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero p.factorial_ne_zero
      (Nat.choose_pos (Nat.le_add_right p i)).ne')
  rw [← h]
  push_cast
  field_simp

/-- All derivatives of order `k < n` of `z ↦ (z - a) ^ n • h z` vanish at `a` whenever `h` is
`C^k` at `a`. -/
theorem iteratedDeriv_pow_sub_smul_eq_zero {h : 𝕜 → E} {n k : ℕ} (hh : ContDiffAt 𝕜 k h a)
    (hk : k < n) : iteratedDeriv k (fun z ↦ (z - a) ^ n • h z) a = 0 := by
  have hpow (i : ℕ) (hi : i ≤ k) : iteratedDeriv i (fun z : 𝕜 ↦ (z - a) ^ n) a = 0 := by
    rw [iteratedDeriv_comp_sub_const i (· ^ n) a]
    dsimp only
    rw [sub_self, iteratedDeriv_fun_pow_zero, ite_eq_right (by omega), Nat.cast_zero]
  have hL := iteratedDerivWithin_smul (Set.mem_univ a) uniqueDiffOn_univ (n := k)
    (f := fun z : 𝕜 ↦ (z - a) ^ n) (by fun_prop) hh.contDiffWithinAt
  simp only [iteratedDerivWithin_univ] at hL
  have hfun : (fun z ↦ (z - a) ^ n • h z) = (fun z : 𝕜 ↦ (z - a) ^ n) • h := by
    ext z
    simp only [Pi.smul_apply']
  rw [hfun, hL]
  exact Finset.sum_eq_zero fun i hi ↦ by
    rw [hpow i (Finset.mem_range_succ_iff.mp hi), zero_smul, smul_zero]

/-- Multiplying a function `C^k` at `a ∈ S` by `∏ b ∈ S, (z - b) ^ m b` annihilates all
derivatives of order `k < m a` at `a`. -/
theorem iteratedDeriv_prod_pow_sub_smul_eq_zero (S : Finset 𝕜) (m : 𝕜 → ℕ) {r : 𝕜 → E}
    {a : 𝕜} (ha : a ∈ S) {k : ℕ} (hra : ContDiffAt 𝕜 k r a) (hk : k < m a) :
    iteratedDeriv k (fun z ↦ (∏ b ∈ S, (z - b) ^ m b) • r z) a = 0 := by
  classical
  have hfactor : (fun z ↦ (∏ b ∈ S, (z - b) ^ m b) • r z) =
      fun z ↦ (z - a) ^ m a • ((∏ b ∈ S.erase a, (z - b) ^ m b) • r z) := by
    ext z
    rw [← Finset.mul_prod_erase S (fun b ↦ (z - b) ^ m b) ha, mul_smul]
  rw [hfactor]
  have hr' : ContDiffAt 𝕜 k (fun z ↦ (∏ b ∈ S.erase a, (z - b) ^ m b) • r z) a :=
    (by fun_prop : ContDiffAt 𝕜 k (fun z : 𝕜 ↦ ∏ b ∈ S.erase a, (z - b) ^ m b) a).smul hra
  exact iteratedDeriv_pow_sub_smul_eq_zero hr' hk

end TauCeti

namespace ContinuousLinearMap

section Bilinear

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- **Leibniz's rule for a continuous bilinear map** within a set. If `f` and `g` are `Cⁿ` at `x`
within a set `s` with unique derivatives, the `n`-th derivative within `s` at `x` of
`y ↦ B (f y) (g y)` is `∑ᵢ (n choose i) B (f⁽ⁱ⁾ x) (g⁽ⁿ⁻ⁱ⁾ x)`. -/
theorem iteratedDerivWithin_of_bilinear (B : E →L[𝕜] F →L[𝕜] G) {s : Set 𝕜} {f : 𝕜 → E}
    {g : 𝕜 → F} {n : ℕ} {x : 𝕜} (hx : x ∈ s) (h : UniqueDiffOn 𝕜 s)
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    iteratedDerivWithin n (fun y ↦ B (f y) (g y)) s x =
      ∑ i ∈ Finset.range (n + 1),
        n.choose i • B (iteratedDerivWithin i f s x) (iteratedDerivWithin (n - i) g s x) := by
  induction n generalizing f g with
  | zero => simp
  | succ n ih =>
    have hf' : ContDiffWithinAt 𝕜 n (derivWithin f s) s x := hf.derivWithin h le_rfl hx
    have hg' : ContDiffWithinAt 𝕜 n (derivWithin g s) s x := hg.derivWithin h le_rfl hx
    have hle : (n : WithTop ℕ∞) ≤ (n + 1 : ℕ) := by norm_cast; omega
    -- Near `x` within `s`, the derivative of `y ↦ B (f y) (g y)` is given by the product rule.
    rw [iteratedDerivWithin_succ', Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert
        (g := (fun y ↦ B (derivWithin f s y) (g y)) + fun y ↦ B (f y) (derivWithin g s y))]
    · have hB {u : 𝕜 → E} {v : 𝕜 → F} (hu : ContDiffWithinAt 𝕜 n u s x)
          (hv : ContDiffWithinAt 𝕜 n v s x) : ContDiffWithinAt 𝕜 n (fun y ↦ B (u y) (v y)) s x :=
        (B.contDiff.comp_contDiffWithinAt hu).clm_apply hv
      rw [iteratedDerivWithin_add hx h (hB hf' (hg.of_le hle)) (hB (hf.of_le hle) hg'),
        ih hf' (hg.of_le hle), ih (hf.of_le hle) hg']
      simp only [← iteratedDerivWithin_succ']
      refine Eq.trans ?_ (Finset.sum_choose_succ_nsmul
        (fun i k ↦ B (iteratedDerivWithin i f s x) (iteratedDerivWithin k g s x)) n).symm
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [Finset.mem_range] at hi
      rw [show n - i + 1 = n + 1 - i by omega]
    · filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hfy hgy
      rw [Pi.add_apply, derivWithin_of_bilinear (hfy.differentiableWithinAt (by simp))
        (hgy.differentiableWithinAt (by simp)), add_comm]

/-- **Leibniz's rule for a continuous bilinear map.** If `f` and `g` are `Cⁿ` at `x`, the `n`-th
derivative at `x` of `y ↦ B (f y) (g y)` is `∑ᵢ (n choose i) B (f⁽ⁱ⁾ x) (g⁽ⁿ⁻ⁱ⁾ x)`. -/
theorem iteratedDeriv_of_bilinear (B : E →L[𝕜] F →L[𝕜] G) {f : 𝕜 → E} {g : 𝕜 → F} {n : ℕ}
    {x : 𝕜} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) :
    iteratedDeriv n (fun y ↦ B (f y) (g y)) x =
      ∑ i ∈ Finset.range (n + 1),
        n.choose i • B (iteratedDeriv i f x) (iteratedDeriv (n - i) g x) := by
  simpa only [iteratedDerivWithin_univ] using B.iteratedDerivWithin_of_bilinear (Set.mem_univ x)
    uniqueDiffOn_univ hf.contDiffWithinAt hg.contDiffWithinAt

end Bilinear

end ContinuousLinearMap
