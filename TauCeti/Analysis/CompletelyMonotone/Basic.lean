/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Completely monotone functions

A function `f : ℝ → ℝ` is *completely monotone* if it is smooth on the closed half-line
`[0, ∞)` and its iterated derivatives there alternate in sign:
`(-1)ⁿ f⁽ⁿ⁾(t) ≥ 0` for every `n` and every `t ≥ 0`. Equivalently `f` is nonnegative,
nonincreasing, convex, and so on through every order. These are the functions that, by
Bernstein's theorem, are exactly the Laplace transforms of positive measures on `[0, ∞)`;
the prototypes `t ↦ e^{-x t}` (`x ≥ 0`) are the extreme rays out of which Bernstein's
theorem builds the general member.

The smoothness clause is essential and is not folded into the sign condition: an iterated
derivative defaults to a junk value where the function fails to be differentiable, so
without it a badly behaved `f` could satisfy `0 ≤ 0` vacuously. We phrase the sign condition
through `iteratedDerivWithin _ (Set.Ici 0)`, the derivative *within* the closed half-line,
which is the object that pairs cleanly with `ContDiffOn` (in particular at the boundary
point `0`); on the open half-line it agrees with the ordinary iterated derivative.

## Main declarations

* `TauCeti.IsCompletelyMonotone`: the predicate that `f` is smooth and sign-alternating on
  `[0, ∞)`.
* `TauCeti.IsCompletelyMonotone.nonneg`, `TauCeti.IsCompletelyMonotone.derivWithin_nonpos`,
  `TauCeti.IsCompletelyMonotone.antitoneOn`: a completely monotone function is nonnegative
  and nonincreasing on `[0, ∞)`.
* `TauCeti.IsCompletelyMonotone.add`, `TauCeti.IsCompletelyMonotone.const_mul`: closure under
  sums and nonnegative scalar multiples.
* `TauCeti.isCompletelyMonotone_const`: a nonnegative constant is completely monotone.
* `TauCeti.isCompletelyMonotone_exp_neg_mul`: the building block `t ↦ e^{-x t}` for `x ≥ 0`.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012).
-/

open Set Filter
open scoped ContDiff Topology

namespace TauCeti

/-- A function `f : ℝ → ℝ` is **completely monotone** if it is `C^∞` on the closed half-line
`[0, ∞)` and its iterated derivatives within `[0, ∞)` alternate in sign:
`0 ≤ (-1)ⁿ f⁽ⁿ⁾(t)` for every `n` and every `t ≥ 0`. The smoothness clause prevents the sign
condition from being satisfied vacuously by a junk iterated derivative. -/
def IsCompletelyMonotone (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (Ici 0) ∧
    ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → 0 ≤ (-1) ^ n * iteratedDerivWithin n f (Ici 0) t

namespace IsCompletelyMonotone

variable {f g : ℝ → ℝ}

/-- A completely monotone function is `C^∞` on `[0, ∞)`. -/
lemma contDiffOn (hf : IsCompletelyMonotone f) : ContDiffOn ℝ ∞ f (Ici 0) := hf.1

/-- The sign-alternation property of the iterated derivatives of a completely monotone
function. -/
lemma sign (hf : IsCompletelyMonotone f) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (-1) ^ n * iteratedDerivWithin n f (Ici 0) t := hf.2 n t ht

/-- A completely monotone function is nonnegative on `[0, ∞)`. -/
lemma nonneg (hf : IsCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  simpa [iteratedDerivWithin_zero] using hf.sign 0 ht

/-- The derivative within `[0, ∞)` of a completely monotone function is nonpositive: it is
nonincreasing. -/
lemma derivWithin_nonpos (hf : IsCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) :
    derivWithin f (Ici 0) t ≤ 0 := by
  have h := hf.sign 1 ht
  rw [pow_one, iteratedDerivWithin_one] at h
  linarith

/-- A completely monotone function is nonincreasing on `[0, ∞)`. -/
lemma antitoneOn (hf : IsCompletelyMonotone f) : AntitoneOn f (Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hf.contDiffOn.continuousOn
    ((hf.contDiffOn.differentiableOn (by simp)).mono interior_subset) (fun x hx => ?_)
  rw [interior_Ici] at hx
  have hmem : Ici (0 : ℝ) ∈ 𝓝 x := mem_of_superset (isOpen_Ioi.mem_nhds hx) Ioi_subset_Ici_self
  rw [← derivWithin_of_mem_nhds hmem]
  exact hf.derivWithin_nonpos (le_of_lt hx)

/-- Completely monotone functions are closed under addition. -/
lemma add (hf : IsCompletelyMonotone f) (hg : IsCompletelyMonotone g) :
    IsCompletelyMonotone (f + g) := by
  refine ⟨hf.contDiffOn.add hg.contDiffOn, fun n t ht => ?_⟩
  have hle : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hcf : ContDiffWithinAt ℝ n f (Ici 0) t :=
    (hf.contDiffOn.contDiffWithinAt (mem_Ici.mpr ht)).of_le hle
  have hcg : ContDiffWithinAt ℝ n g (Ici 0) t :=
    (hg.contDiffOn.contDiffWithinAt (mem_Ici.mpr ht)).of_le hle
  rw [iteratedDerivWithin_add (mem_Ici.mpr ht) (uniqueDiffOn_Ici 0) hcf hcg, mul_add]
  exact add_nonneg (hf.sign n ht) (hg.sign n ht)

/-- Completely monotone functions are closed under multiplication by a nonnegative constant. -/
lemma const_mul (hf : IsCompletelyMonotone f) {c : ℝ} (hc : 0 ≤ c) :
    IsCompletelyMonotone (fun t => c * f t) := by
  refine ⟨contDiffOn_const.mul hf.contDiffOn, fun n t ht => ?_⟩
  rw [iteratedDerivWithin_const_mul_field, mul_left_comm]
  exact mul_nonneg hc (hf.sign n ht)

end IsCompletelyMonotone

/-- A nonnegative constant function is completely monotone. -/
lemma isCompletelyMonotone_const {c : ℝ} (hc : 0 ≤ c) :
    IsCompletelyMonotone (fun _ : ℝ => c) := by
  refine ⟨contDiffOn_const, fun n t _ => ?_⟩
  rcases n with _ | n
  · simpa [iteratedDerivWithin_const] using hc
  · simp [iteratedDerivWithin_const]

/-- The prototype completely monotone function `t ↦ e^{-x t}` for `x ≥ 0`, the extreme ray of
the cone of completely monotone functions. Its `n`-th derivative is `(-x)ⁿ e^{-x t}`, so
`(-1)ⁿ` times it is `xⁿ e^{-x t} ≥ 0`. -/
lemma isCompletelyMonotone_exp_neg_mul {x : ℝ} (hx : 0 ≤ x) :
    IsCompletelyMonotone (fun t => Real.exp (-x * t)) := by
  have hcd : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (-x * t)) := by fun_prop
  refine ⟨hcd.contDiffOn, fun n t ht => ?_⟩
  have hcat : ContDiffAt ℝ (n : WithTop ℕ∞) (fun t : ℝ => Real.exp (-x * t)) t :=
    hcd.contDiffAt.of_le (by exact_mod_cast le_top)
  have hval : iteratedDerivWithin n (fun t : ℝ => Real.exp (-x * t)) (Ici 0) t
      = (-x) ^ n * Real.exp (-x * t) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcat (mem_Ici.mpr ht),
      iteratedDeriv_exp_const_mul]
  have hpow : (0 : ℝ) ≤ (-1) ^ n * (-x) ^ n := by
    rw [← mul_pow, show (-1 : ℝ) * -x = x from by ring]
    exact pow_nonneg hx n
  rw [hval, ← mul_assoc]
  exact mul_nonneg hpow (Real.exp_nonneg _)

end TauCeti
