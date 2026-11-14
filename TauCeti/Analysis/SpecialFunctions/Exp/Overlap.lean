/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Pointwise overlap of exponentially decaying functions

If `‖f z‖ ≤ K exp (-(c ‖z‖))` and `‖g z‖ ≤ L exp (-(c ‖z‖))`, then `f` decays about `0` and the
translate `g (· + a)` decays about `-a`. Since `‖a‖ ≤ ‖z‖ + ‖z + a‖`, their product is
exponentially small in the separation `‖a‖`. Any part `b ≤ c` of the rate can be spent on the
separation, and the rest `c - b` kept as decay in `z`.

## Main results

* `TauCeti.norm_mul_norm_le_mul_exp_mul_exp`: the overlap is at most
  `K L exp (-(b ‖a‖)) exp (-((c - b) ‖z‖))` for every `0 ≤ b ≤ c`.
* `TauCeti.norm_mul_norm_le_mul_exp_neg_mul_norm`: the case `b = c`, a bound `K L exp (-(c ‖a‖))`
  uniform in `z`.
* `TauCeti.exists_mul_le_mul_exp_neg_mul_norm_of_forall_lt`: the same for nonnegative functions
  decaying at every rate below a threshold.
-/

public section

namespace TauCeti

variable {E F G : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [SeminormedAddCommGroup G] {f : E → F} {g : E → G} {K L c : ℝ}

/-- **Overlap of exponentially decaying functions, splitting the rate.** If
`‖f z‖ ≤ K exp (-(c ‖z‖))` and `‖g z‖ ≤ L exp (-(c ‖z‖))`, then for every `0 ≤ b ≤ c` the product
of `f` and of the translate `g (· + a)` is at most `K L exp (-(b ‖a‖)) exp (-((c - b) ‖z‖))`:
part `b` of the rate is spent on the separation `‖a‖` and the rest is kept as decay in `z`. -/
theorem norm_mul_norm_le_mul_exp_mul_exp {b : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c)
    (hf : ∀ z, ‖f z‖ ≤ K * Real.exp (-(c * ‖z‖)))
    (hg : ∀ z, ‖g z‖ ≤ L * Real.exp (-(c * ‖z‖))) (z a : E) :
    ‖f z‖ * ‖g (z + a)‖ ≤ K * L * Real.exp (-(b * ‖a‖)) * Real.exp (-((c - b) * ‖z‖)) := by
  have hK : 0 ≤ K * Real.exp (-(c * ‖z‖)) := (norm_nonneg _).trans (hf z)
  -- `‖a‖ ≤ ‖z‖ + ‖z + a‖`, so the two decay factors together beat `exp (-(b ‖a‖))`.
  have ha : ‖a‖ ≤ ‖z‖ + ‖z + a‖ := by
    simpa [add_comm ‖z‖] using norm_sub_le (z + a) z
  have hexp : Real.exp (-(c * ‖z‖)) * Real.exp (-(c * ‖z + a‖)) ≤
      Real.exp (-(b * ‖a‖)) * Real.exp (-((c - b) * ‖z‖)) := by
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    nlinarith [norm_nonneg (z + a), mul_le_mul_of_nonneg_left ha hb]
  have hKL : 0 ≤ K * L := by
    have hK' : 0 ≤ K := nonneg_of_mul_nonneg_left hK (Real.exp_pos _)
    have hL' : 0 ≤ L :=
      nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hg z)) (Real.exp_pos _)
    positivity
  calc ‖f z‖ * ‖g (z + a)‖
      ≤ K * Real.exp (-(c * ‖z‖)) * (L * Real.exp (-(c * ‖z + a‖))) :=
        mul_le_mul (hf z) (hg _) (norm_nonneg _) hK
    _ = K * L * (Real.exp (-(c * ‖z‖)) * Real.exp (-(c * ‖z + a‖))) := by ring
    _ ≤ K * L * (Real.exp (-(b * ‖a‖)) * Real.exp (-((c - b) * ‖z‖))) :=
        mul_le_mul_of_nonneg_left hexp hKL
    _ = _ := by ring

/-- **Overlap of exponentially decaying functions, pointwise.** If `‖f z‖ ≤ K exp (-(c ‖z‖))`
and `‖g z‖ ≤ L exp (-(c ‖z‖))` with `0 ≤ c`, then the product of `f` and of the translate
`g (· + a)`, which decays about `-a`, is at most `K L exp (-(c ‖a‖))` everywhere. -/
theorem norm_mul_norm_le_mul_exp_neg_mul_norm (hc : 0 ≤ c)
    (hf : ∀ z, ‖f z‖ ≤ K * Real.exp (-(c * ‖z‖)))
    (hg : ∀ z, ‖g z‖ ≤ L * Real.exp (-(c * ‖z‖))) (z a : E) :
    ‖f z‖ * ‖g (z + a)‖ ≤ K * L * Real.exp (-(c * ‖a‖)) := by
  simpa using norm_mul_norm_le_mul_exp_mul_exp hc le_rfl hf hg z a

/-- **Overlap of nonnegative functions decaying at every rate below `r`, pointwise.** If
`0 ≤ f`, `0 ≤ g` and both are at most `K exp (-(c ‖z‖))` for every rate `c < r`, with `K`
depending on `c`, then `f z g (z + a) ≤ K exp (-(c ‖a‖))` for every rate `c < r`. -/
theorem exists_mul_le_mul_exp_neg_mul_norm_of_forall_lt {f g : E → ℝ} {r : ℝ}
    (hf₀ : ∀ z, 0 ≤ f z) (hg₀ : ∀ z, 0 ≤ g z)
    (hf : ∀ c < r, ∃ K, ∀ z, f z ≤ K * Real.exp (-(c * ‖z‖)))
    (hg : ∀ c < r, ∃ K, ∀ z, g z ≤ K * Real.exp (-(c * ‖z‖))) (hr : 0 < r) (hc : c < r) :
    ∃ K, ∀ z a, f z * g (z + a) ≤ K * Real.exp (-(c * ‖a‖)) := by
  obtain ⟨Kf, hKf⟩ := hf (max c 0) (max_lt hc hr)
  obtain ⟨Kg, hKg⟩ := hg (max c 0) (max_lt hc hr)
  refine ⟨Kf * Kg, fun z a ↦ ?_⟩
  have h := norm_mul_norm_le_mul_exp_neg_mul_norm (le_max_right c 0) (f := f) (g := g)
    (fun w ↦ (Real.norm_of_nonneg (hf₀ w)).trans_le (hKf w))
    (fun w ↦ (Real.norm_of_nonneg (hg₀ w)).trans_le (hKg w)) z a
  rw [Real.norm_of_nonneg (hf₀ z), Real.norm_of_nonneg (hg₀ _)] at h
  have hKfg : 0 ≤ Kf * Kg :=
    nonneg_of_mul_nonneg_left ((mul_nonneg (hf₀ z) (hg₀ (z + a))).trans h) (Real.exp_pos _)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hKfg)
  exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (norm_nonneg a)))

end TauCeti
