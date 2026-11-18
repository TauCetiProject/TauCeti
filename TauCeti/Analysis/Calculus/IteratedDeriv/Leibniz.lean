/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Leibniz's rule at a zero of a power, and for compositions of linear maps

The `n`-th derivative of `z ↦ (z - a) ^ n • h z` at `a` is `n! • h a`: in Leibniz's rule every
other term differentiates `(z - a) ^ n` fewer than `n` times and so vanishes at `a`. If an
analytic function `f` factors as `f z = (z - a) ^ n • h z` (for instance through
`AnalyticOnNhd.exists_eq_prod_pow_smul`), this recovers its first possibly nonzero derivative at
`a` from the value of the quotient `h`.

More generally, multiplying by `(z - a) ^ p` shifts the Taylor coefficients at `a` up by `p`
without changing them.

For functions `c` and `d` with values in continuous linear maps, `Cⁿ` at a point (within a set
with unique derivatives), Leibniz's rule `(c ∘ d)⁽ⁿ⁾ = ∑ᵢ (n choose i) c⁽ⁱ⁾ ∘ d⁽ⁿ⁻ⁱ⁾` holds there
for their pointwise composition.

## Main results

* `TauCeti.iteratedDeriv_pow_sub_smul_self`: the identity above.
* `TauCeti.inv_factorial_smul_iteratedDeriv_pow_sub_smul`: the `(p + i)`-th Taylor coefficient of
  `z ↦ (z - a) ^ p • h z` at `a` is the `i`-th Taylor coefficient of `h`.
* `TauCeti.iteratedDerivWithin_clm_comp`: Leibniz's rule within a set for the pointwise
  composition of functions with values in continuous linear maps.
* `TauCeti.iteratedDeriv_clm_comp`: the same rule for the plain iterated derivative.
-/

public section

namespace TauCeti

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {a : 𝕜}

/-- The `n`-th derivative of `z ↦ (z - a) ^ n • h z` at `a` is `n! • h a`: in Leibniz's rule
every other term differentiates `(z - a) ^ n` fewer than `n` times and so vanishes at `a`. -/
theorem iteratedDeriv_pow_sub_smul_self {h : 𝕜 → E} {n : ℕ} (hh : ContDiffAt 𝕜 n h a) :
    iteratedDeriv n (fun z ↦ (z - a) ^ n • h z) a = n.factorial • h a := by
  have hp (i : ℕ) : iteratedDeriv i (fun z : 𝕜 ↦ (z - a) ^ n) a =
      if i = n then (n.factorial : 𝕜) else 0 := by
    rw [iteratedDeriv_comp_sub_const i (· ^ n) a]
    dsimp only
    rw [sub_self, iteratedDeriv_fun_pow_zero]
    split_ifs <;> simp
  have hL := iteratedDerivWithin_smul (Set.mem_univ a) uniqueDiffOn_univ
    (f := fun z : 𝕜 ↦ (z - a) ^ n) (by fun_prop) hh.contDiffWithinAt
  simp only [iteratedDerivWithin_univ] at hL
  have hfun : (fun z ↦ (z - a) ^ n • h z) = (fun z : 𝕜 ↦ (z - a) ^ n) • h := by
    ext z
    simp only [Pi.smul_apply']
  rw [hfun, hL,
    Finset.sum_eq_single_of_mem n (Finset.self_mem_range_succ n) fun i _ hi ↦ by simp [hp, hi]]
  simp [hp, Nat.cast_smul_eq_nsmul]

/-- **Taylor-shift invariance.** Multiplying `h` by `(z - a) ^ p` shifts its Taylor coefficients at
`a` up by `p` without changing them: the `(p + i)`-th Taylor coefficient at `a` of
`z ↦ (z - a) ^ p • h z` is the `i`-th Taylor coefficient of `h`. In Leibniz's rule only the term
that differentiates `(z - a) ^ p` exactly `p` times survives at `a`. -/
theorem inv_factorial_smul_iteratedDeriv_pow_sub_smul [CharZero 𝕜] (p i : ℕ) {h : 𝕜 → E}
    (hh : ContDiffAt 𝕜 (p + i) h a) :
    ((p + i).factorial : 𝕜)⁻¹ • iteratedDeriv (p + i) (fun z ↦ (z - a) ^ p • h z) a =
      (i.factorial : 𝕜)⁻¹ • iteratedDeriv i h a := by
  have hpow (j : ℕ) : iteratedDeriv j (fun z : 𝕜 ↦ (z - a) ^ p) a =
      if j = p then (p.factorial : 𝕜) else 0 := by
    simpa only [sub_self, iteratedDeriv_fun_pow_zero, Nat.cast_ite, Nat.cast_zero] using
      congrFun (iteratedDeriv_comp_sub_const j (fun w : 𝕜 ↦ w ^ p) a) a
  have hleib := iteratedDerivWithin_smul (Set.mem_univ a) uniqueDiffOn_univ (n := p + i)
    (f := fun z : 𝕜 ↦ (z - a) ^ p) (by fun_prop) hh.contDiffWithinAt
  simp only [iteratedDerivWithin_univ] at hleib
  have hfun : (fun z ↦ (z - a) ^ p • h z) = (fun z : 𝕜 ↦ (z - a) ^ p) • h := by
    ext z
    simp only [Pi.smul_apply']
  rw [hfun, hleib,
    Finset.sum_eq_single p (fun j _ hj ↦ by rw [hpow, ite_eq_right hj, zero_smul, smul_zero])
      (fun hp ↦ absurd (Finset.mem_range.2 (by omega)) hp),
    hpow, ite_eq_left rfl, Nat.add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul,
    smul_smul]
  congr 1
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right p i)
  rw [Nat.add_sub_cancel_left] at h
  have hC : ((p + i).choose p : 𝕜) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_add_right p i)).ne'
  have hP : (p.factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr p.factorial_ne_zero
  rw [← h]
  push_cast
  field_simp

section CLMComp

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G]

/-- **Leibniz's rule for compositions of continuous linear maps** within a set. If `c` and `d`
are `Cⁿ` at `x` within a set `s` with unique derivatives, the `n`-th derivative within `s` at `x`
of their pointwise composition is `∑ᵢ (n choose i) c⁽ⁱ⁾(x) ∘ d⁽ⁿ⁻ⁱ⁾(x)`. -/
theorem iteratedDerivWithin_clm_comp {s : Set 𝕜} {c : 𝕜 → F →L[𝕜] G} {d : 𝕜 → E →L[𝕜] F}
    {n : ℕ} {x : 𝕜} (hx : x ∈ s) (h : UniqueDiffOn 𝕜 s) (hc : ContDiffWithinAt 𝕜 n c s x)
    (hd : ContDiffWithinAt 𝕜 n d s x) :
    iteratedDerivWithin n (fun y ↦ (c y).comp (d y)) s x =
      ∑ i ∈ Finset.range (n + 1),
        n.choose i • (iteratedDerivWithin i c s x).comp (iteratedDerivWithin (n - i) d s x) := by
  induction n generalizing c d with
  | zero => simp
  | succ n ih =>
    have hc' : ContDiffWithinAt 𝕜 n (derivWithin c s) s x := hc.derivWithin h le_rfl hx
    have hd' : ContDiffWithinAt 𝕜 n (derivWithin d s) s x := hd.derivWithin h le_rfl hx
    have hle : (n : WithTop ℕ∞) ≤ (n + 1 : ℕ) := by norm_cast; omega
    -- Near `x` within `s`, the derivative of the composition is given by the product rule.
    rw [iteratedDerivWithin_succ', Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert
        (g := (fun y ↦ (derivWithin c s y).comp (d y)) + fun y ↦ (c y).comp (derivWithin d s y))]
    · rw [iteratedDerivWithin_add hx h (hc'.clm_comp (hd.of_le hle))
          ((hc.of_le hle).clm_comp hd'), ih hc' (hd.of_le hle), ih (hc.of_le hle) hd']
      simp only [← iteratedDerivWithin_succ']
      refine Eq.trans ?_ (Finset.sum_choose_succ_nsmul
        (fun i k ↦ (iteratedDerivWithin i c s x).comp (iteratedDerivWithin k d s x)) n).symm
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [Finset.mem_range] at hi
      rw [show n - i + 1 = n + 1 - i by omega]
    · filter_upwards [hc.eventually (by simp), hd.eventually (by simp)] with y hcy hdy
      exact derivWithin_clm_comp (hcy.differentiableWithinAt (by simp))
        (hdy.differentiableWithinAt (by simp))

/-- **Leibniz's rule for compositions of continuous linear maps.** If `c` and `d` are `Cⁿ` at `x`,
the `n`-th derivative at `x` of their pointwise composition is
`∑ᵢ (n choose i) c⁽ⁱ⁾(x) ∘ d⁽ⁿ⁻ⁱ⁾(x)`. -/
theorem iteratedDeriv_clm_comp {c : 𝕜 → F →L[𝕜] G} {d : 𝕜 → E →L[𝕜] F} {n : ℕ} {x : 𝕜}
    (hc : ContDiffAt 𝕜 n c x) (hd : ContDiffAt 𝕜 n d x) :
    iteratedDeriv n (fun y ↦ (c y).comp (d y)) x =
      ∑ i ∈ Finset.range (n + 1),
        n.choose i • (iteratedDeriv i c x).comp (iteratedDeriv (n - i) d x) := by
  simpa only [iteratedDerivWithin_univ] using iteratedDerivWithin_clm_comp (Set.mem_univ x)
    uniqueDiffOn_univ hc.contDiffWithinAt hd.contDiffWithinAt

end CLMComp

end TauCeti
