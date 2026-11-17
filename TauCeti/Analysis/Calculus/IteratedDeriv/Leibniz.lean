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

For functions `c` and `d` with values in continuous linear maps, `Cⁿ` at a point, Leibniz's
rule `(c ∘ d)⁽ⁿ⁾ = ∑ᵢ (n choose i) c⁽ⁱ⁾ ∘ d⁽ⁿ⁻ⁱ⁾` holds there for their pointwise composition.

## Main results

* `TauCeti.iteratedDeriv_pow_sub_smul_self`: the identity above.
* `TauCeti.inv_factorial_smul_iteratedDeriv_pow_sub_smul`: the `(p + i)`-th Taylor coefficient of
  `z ↦ (z - a) ^ p • h z` at `a` is the `i`-th Taylor coefficient of `h`.
* `TauCeti.iteratedDeriv_clm_comp`: Leibniz's rule for the pointwise composition of functions
  with values in continuous linear maps.
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

/-- Leibniz's rule for compositions of continuous linear maps, on an open set where both factors
are `Cⁿ`. -/
private theorem iteratedDeriv_clm_comp_of_isOpen {s : Set 𝕜} (hs : IsOpen s)
    {c : 𝕜 → F →L[𝕜] G} {d : 𝕜 → E →L[𝕜] F} {n : ℕ} (hc : ContDiffOn 𝕜 n c s)
    (hd : ContDiffOn 𝕜 n d s) {x : 𝕜} (hx : x ∈ s) :
    iteratedDeriv n (fun y ↦ (c y).comp (d y)) x =
      ∑ i ∈ Finset.range (n + 1),
        n.choose i • (iteratedDeriv i c x).comp (iteratedDeriv (n - i) d x) := by
  induction n generalizing c d with
  | zero => simp
  | succ n ih =>
    have hc' : ContDiffOn 𝕜 n (deriv c) s := hc.deriv_of_isOpen hs (by norm_cast)
    have hd' : ContDiffOn 𝕜 n (deriv d) s := hd.deriv_of_isOpen hs (by norm_cast)
    -- On `s` the derivative of the composition is given by the product rule.
    have heq : Set.EqOn (deriv fun y ↦ (c y).comp (d y))
        ((fun y ↦ (deriv c y).comp (d y)) + fun y ↦ (c y).comp (deriv d y)) s := fun y hy ↦ by
      have hm := hs.mem_nhds hy
      exact deriv_clm_comp ((hc.differentiableOn (by simp)).differentiableAt hm)
        ((hd.differentiableOn (by simp)).differentiableAt hm)
    have hm := hs.mem_nhds hx
    have hle : (n : WithTop ℕ∞) ≤ (n + 1 : ℕ) := by norm_cast; omega
    rw [iteratedDeriv_succ', heq.iteratedDeriv_of_isOpen hs n hx,
      iteratedDeriv_add ((hc'.clm_comp (hd.of_le hle)).contDiffAt hm)
        (((hc.of_le hle).clm_comp hd').contDiffAt hm), ih hc' (hd.of_le hle),
      ih (hc.of_le hle) hd']
    simp only [← iteratedDeriv_succ']
    refine Eq.trans ?_ (Finset.sum_choose_succ_nsmul
      (fun i k ↦ (iteratedDeriv i c x).comp (iteratedDeriv k d x)) n).symm
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    rw [show n - i + 1 = n + 1 - i by omega]

/-- **Leibniz's rule for compositions of continuous linear maps.** If `c` and `d` are `Cⁿ` at `x`,
the `n`-th derivative at `x` of their pointwise composition is
`∑ᵢ (n choose i) c⁽ⁱ⁾(x) ∘ d⁽ⁿ⁻ⁱ⁾(x)`. -/
theorem iteratedDeriv_clm_comp {c : 𝕜 → F →L[𝕜] G} {d : 𝕜 → E →L[𝕜] F} {n : ℕ} {x : 𝕜}
    (hc : ContDiffAt 𝕜 n c x) (hd : ContDiffAt 𝕜 n d x) :
    iteratedDeriv n (fun y ↦ (c y).comp (d y)) x =
      ∑ i ∈ Finset.range (n + 1),
        n.choose i • (iteratedDeriv i c x).comp (iteratedDeriv (n - i) d x) := by
  obtain ⟨u, hu, hcu⟩ := hc.contDiffOn le_rfl (by simp)
  obtain ⟨v, hv, hdv⟩ := hd.contDiffOn le_rfl (by simp)
  obtain ⟨s, hsuv, hs, hx⟩ := mem_nhds_iff.1 (Filter.inter_mem hu hv)
  exact iteratedDeriv_clm_comp_of_isOpen hs (hcu.mono fun y hy ↦ (hsuv hy).1)
    (hdv.mono fun y hy ↦ (hsuv hy).2) hx

end CLMComp

end TauCeti
