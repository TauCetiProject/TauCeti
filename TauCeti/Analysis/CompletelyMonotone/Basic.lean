/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.AbsolutelyMonotone
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Completely monotone functions

A function `f : ℝ → ℝ` is *completely monotone* if it is smooth on the closed half-line
`[0, ∞)` and its iterated derivatives there alternate in sign:
`(-1)ⁿ f⁽ⁿ⁾(t) ≥ 0` for every `n` and every `t ≥ 0`. Equivalently `f` is nonnegative,
nonincreasing, convex, and so on through every order. Bernstein's theorem identifies the
completely monotone functions on the *open* half-line `(0, ∞)` with the Laplace transforms of
positive measures on `[0, ∞)`. Demanding smoothness up to the boundary point `0`, as we do
here, is a genuine strengthening: it carves out the subclass whose representing measure has
every moment finite. (It thereby excludes some Laplace transforms of finite measures, such as
`t ↦ ∫₀^∞ e^{-x t} (1 + x)⁻² dx`, which is finite at `0` yet has `f'(0⁺) = -∞`.) The
prototypes `t ↦ e^{-x t}` (`x ≥ 0`) are the extreme rays out of which Bernstein's theorem
builds the general member.

The smoothness clause is essential and is not folded into the sign condition: an iterated
derivative defaults to a junk value where the function fails to be differentiable, so
without it a badly behaved `f` could satisfy `0 ≤ 0` vacuously. We phrase the sign condition
through `iteratedDerivWithin _ (Set.Ici 0)`, the derivative *within* the closed half-line,
which is the object that pairs cleanly with `ContDiffOn` (in particular at the boundary
point `0`); on the open half-line it agrees with the ordinary iterated derivative.

## Main declarations

* `TauCeti.IsCompletelyMonotone`: the predicate that `f` is smooth and sign-alternating on
  `[0, ∞)`.
* `TauCeti.IsCompletelyMonotone.congr`: complete monotonicity only depends on the values of the
  function on `[0, ∞)`.
* `TauCeti.IsCompletelyMonotone.nonneg`, `TauCeti.IsCompletelyMonotone.derivWithin_nonpos`,
  `TauCeti.IsCompletelyMonotone.antitoneOn`: a completely monotone function is nonnegative
  and nonincreasing on `[0, ∞)`.
* `TauCeti.IsCompletelyMonotone.neg_one_pow_mul_iteratedDeriv_nonneg`: on the open half-line,
  the sign condition also holds for ordinary iterated derivatives.
* `TauCeti.IsCompletelyMonotone.add`, `TauCeti.IsCompletelyMonotone.smul`: closure under
  sums and nonnegative scalar multiples.
* `TauCeti.IsCompletelyMonotoneOnIoi`: the open-half-line analogue, using ordinary iterated
  derivatives on `(0, ∞)`.
* `TauCeti.isCompletelyMonotone_const`: a nonnegative constant is completely monotone.
* `TauCeti.isCompletelyMonotone_exp_neg_mul`: the building block `t ↦ e^{-x t}` for `x ≥ 0`.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012).
-/

public section

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

/-- `IsCompletelyMonotone f` unfolds to its defining conjunction: `f` is `C^∞` on `[0, ∞)`
and its iterated derivatives within `[0, ∞)` alternate in sign. -/
lemma isCompletelyMonotone_iff {f : ℝ → ℝ} :
    IsCompletelyMonotone f ↔
      ContDiffOn ℝ ∞ f (Ici 0) ∧
        ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → 0 ≤ (-1) ^ n * iteratedDerivWithin n f (Ici 0) t :=
  Iff.rfl

/-- Completely monotone functions are exactly absolutely monotone functions after reflecting the
closed half-line through zero. -/
lemma isCompletelyMonotone_iff_absolutelyMonotoneOn_comp_neg {f : ℝ → ℝ} :
    IsCompletelyMonotone f ↔ AbsolutelyMonotoneOn (fun u => f (-u)) (Iic 0) := by
  rw [isCompletelyMonotone_iff,
    AbsolutelyMonotoneOn.iff_iteratedDerivWithin_nonneg (uniqueDiffOn_Iic 0)]
  constructor
  · rintro ⟨hcont, hsign⟩
    refine ⟨?_, fun n u hu => ?_⟩
    · have hpre : ((-ContinuousLinearMap.id ℝ ℝ) ⁻¹' Ici 0) = Iic 0 := by
        ext x
        simp
      simpa [Function.comp_def, hpre] using
        (hcont.comp_continuousLinearMap (-ContinuousLinearMap.id ℝ ℝ) :
          ContDiffOn ℝ ∞ (fun u : ℝ => f (-u)) ((-ContinuousLinearMap.id ℝ ℝ) ⁻¹' Ici 0))
    · rw [iteratedDerivWithin_comp_neg (n := n) (f := f) (s := Iic 0) u]
      have hset : (-Iic (0 : ℝ) : Set ℝ) = Ici 0 := by
        ext x
        simp
      rw [hset]
      simpa [smul_eq_mul] using hsign n (-u) (neg_nonneg.mpr hu)
  · rintro ⟨hcont, hsign⟩
    refine ⟨?_, fun n t ht => ?_⟩
    · have hpre : ((-ContinuousLinearMap.id ℝ ℝ) ⁻¹' Iic 0) = Ici 0 := by
        ext x
        simp
      simpa [Function.comp_def, hpre] using
        (hcont.comp_continuousLinearMap (-ContinuousLinearMap.id ℝ ℝ) :
          ContDiffOn ℝ ∞ ((fun u : ℝ => f (-u)) ∘ (-ContinuousLinearMap.id ℝ ℝ))
            ((-ContinuousLinearMap.id ℝ ℝ) ⁻¹' Iic 0))
    · have hsign' := hsign n (-t) (mem_Iic.mpr (neg_nonpos.mpr ht))
      rw [iteratedDerivWithin_comp_neg (n := n) (f := f) (s := Iic 0) (-t)] at hsign'
      have hset : (-Iic (0 : ℝ) : Set ℝ) = Ici 0 := by
        ext x
        simp
      rw [hset] at hsign'
      simpa [smul_eq_mul] using hsign'

namespace IsCompletelyMonotone

variable {f g : ℝ → ℝ}

/-- A completely monotone function is `C^∞` on `[0, ∞)`. -/
@[grind →]
lemma contDiffOn (hf : IsCompletelyMonotone f) : ContDiffOn ℝ ∞ f (Ici 0) := hf.1

/-- The sign-alternation property of the iterated derivatives of a completely monotone
function: `0 ≤ (-1)ⁿ f⁽ⁿ⁾(t)` for every `n` and every `t ≥ 0`. -/
@[grind =>]
lemma neg_one_pow_mul_iteratedDerivWithin_nonneg (hf : IsCompletelyMonotone f) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ (-1) ^ n * iteratedDerivWithin n f (Ici 0) t := hf.2 n t ht

/-- On the open half-line, the completely monotone sign condition can be read using ordinary
iterated derivatives instead of derivatives within `[0, ∞)`. -/
lemma neg_one_pow_mul_iteratedDeriv_nonneg (hf : IsCompletelyMonotone f) (n : ℕ) {t : ℝ}
    (ht : 0 < t) : 0 ≤ (-1) ^ n * iteratedDeriv n f t := by
  have hnhds : Ici (0 : ℝ) ∈ 𝓝 t :=
    mem_of_superset (isOpen_Ioi.mem_nhds ht) Ioi_subset_Ici_self
  have hcont : ContDiffAt ℝ (n : WithTop ℕ∞) f t :=
    (hf.contDiffOn.contDiffAt hnhds).of_le (by exact_mod_cast le_top)
  rw [← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcont
    (mem_Ici.mpr ht.le)]
  exact hf.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht.le

/-- A completely monotone function is nonnegative on `[0, ∞)`. -/
@[grind =>]
lemma nonneg (hf : IsCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := by
  simpa [iteratedDerivWithin_zero] using hf.neg_one_pow_mul_iteratedDerivWithin_nonneg 0 ht

/-- The derivative within `[0, ∞)` of a completely monotone function is nonpositive: it is
nonincreasing. -/
@[grind =>]
lemma derivWithin_nonpos (hf : IsCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) :
    derivWithin f (Ici 0) t ≤ 0 := by
  have h := hf.neg_one_pow_mul_iteratedDerivWithin_nonneg 1 ht
  rw [pow_one, iteratedDerivWithin_one] at h
  linarith

/-- Complete monotonicity is determined by the values of the function on `[0, ∞)`: if `g` agrees
with a completely monotone `f` throughout `[0, ∞)`, then `g` is completely monotone too. Both the
smoothness clause and the sign condition only see the function within `[0, ∞)`. -/
lemma congr (hf : IsCompletelyMonotone f) (h : Set.EqOn g f (Ici 0)) :
    IsCompletelyMonotone g := by
  refine ⟨hf.contDiffOn.congr fun x hx => h hx, fun n t ht => ?_⟩
  rw [iteratedDerivWithin_congr h (mem_Ici.mpr ht)]
  exact hf.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht

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
  rw [isCompletelyMonotone_iff_absolutelyMonotoneOn_comp_neg]
  convert (isCompletelyMonotone_iff_absolutelyMonotoneOn_comp_neg.mp hf).add
    (isCompletelyMonotone_iff_absolutelyMonotoneOn_comp_neg.mp hg) using 1
  ext u
  simp [Pi.add_apply]

/-- Completely monotone functions are closed under multiplication by a nonnegative constant. -/
lemma smul (hf : IsCompletelyMonotone f) {c : ℝ} (hc : 0 ≤ c) :
    IsCompletelyMonotone (c • f) := by
  rw [isCompletelyMonotone_iff_absolutelyMonotoneOn_comp_neg]
  convert (isCompletelyMonotone_iff_absolutelyMonotoneOn_comp_neg.mp hf).smul hc using 1
  ext u
  simp [Pi.smul_apply, smul_eq_mul]

end IsCompletelyMonotone

/-- A nonnegative constant function is completely monotone. -/
lemma isCompletelyMonotone_const {c : ℝ} (hc : 0 ≤ c) :
    IsCompletelyMonotone (fun _ : ℝ => c) := by
  refine ⟨contDiffOn_const, fun n t _ => ?_⟩
  rcases n with _ | n
  · simpa [iteratedDerivWithin_const] using hc
  · simp [iteratedDerivWithin_const]

/-- The prototype completely monotone function `t ↦ e^{-x t}` for `x ≥ 0`. Its `n`-th
derivative is `(-x)ⁿ e^{-x t}`, so `(-1)ⁿ` times it is `xⁿ e^{-x t} ≥ 0`. -/
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
    rw [← mul_pow, neg_one_mul, neg_neg]
    exact pow_nonneg hx n
  rw [hval, ← mul_assoc]
  exact mul_nonneg hpow (Real.exp_nonneg _)

/-- Complete monotonicity on the open half-line `(0, ∞)`: the function is `C^∞` there and its
ordinary iterated derivatives alternate in sign. This is the version used for derivatives of
Bernstein functions, whose right derivatives need not be finite at `0`. -/
def IsCompletelyMonotoneOnIoi (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (Ioi 0) ∧
    ∀ n : ℕ, ∀ t : ℝ, 0 < t → 0 ≤ (-1) ^ n * iteratedDeriv n f t

namespace IsCompletelyMonotoneOnIoi

variable {f g : ℝ → ℝ}

/-- A completely monotone function on `(0, ∞)` is smooth there. -/
@[grind →]
lemma contDiffOn (hf : IsCompletelyMonotoneOnIoi f) : ContDiffOn ℝ ∞ f (Ioi 0) := hf.1

/-- The sign-alternation property on `(0, ∞)`. -/
@[grind =>]
lemma neg_one_pow_mul_iteratedDeriv_nonneg (hf : IsCompletelyMonotoneOnIoi f) (n : ℕ) {t : ℝ}
    (ht : 0 < t) : 0 ≤ (-1) ^ n * iteratedDeriv n f t := hf.2 n t ht

/-- A completely monotone function on `(0, ∞)` is nonnegative there. -/
@[grind =>]
lemma nonneg (hf : IsCompletelyMonotoneOnIoi f) {t : ℝ} (ht : 0 < t) : 0 ≤ f t := by
  simpa [iteratedDeriv_zero] using hf.neg_one_pow_mul_iteratedDeriv_nonneg 0 ht

/-- The derivative of a completely monotone function on `(0, ∞)` is nonpositive there. -/
@[grind =>]
lemma deriv_nonpos (hf : IsCompletelyMonotoneOnIoi f) {t : ℝ} (ht : 0 < t) :
    deriv f t ≤ 0 := by
  have h := hf.neg_one_pow_mul_iteratedDeriv_nonneg 1 ht
  rw [pow_one, iteratedDeriv_one] at h
  linarith

/-- Complete monotonicity on `(0, ∞)` is preserved by pointwise equality there. -/
lemma congr (hf : IsCompletelyMonotoneOnIoi f) (h : Set.EqOn g f (Ioi 0)) :
    IsCompletelyMonotoneOnIoi g := by
  refine ⟨hf.contDiffOn.congr fun x hx => h hx, fun n t ht => ?_⟩
  rw [Filter.EventuallyEq.iteratedDeriv_eq n (h.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds ht))]
  exact hf.neg_one_pow_mul_iteratedDeriv_nonneg n ht

/-- Complete monotonicity on `(0, ∞)` is closed under addition. -/
lemma add (hf : IsCompletelyMonotoneOnIoi f) (hg : IsCompletelyMonotoneOnIoi g) :
    IsCompletelyMonotoneOnIoi (f + g) := by
  refine ⟨hf.contDiffOn.add hg.contDiffOn, fun n t ht => ?_⟩
  rw [iteratedDeriv_add
    ((hf.contDiffOn.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_top))
    ((hg.contDiffOn.contDiffAt (isOpen_Ioi.mem_nhds ht)).of_le (by exact_mod_cast le_top))]
  simpa [mul_add] using add_nonneg (hf.neg_one_pow_mul_iteratedDeriv_nonneg n ht)
    (hg.neg_one_pow_mul_iteratedDeriv_nonneg n ht)

/-- Complete monotonicity on `(0, ∞)` is closed under multiplication by a nonnegative constant. -/
lemma smul (hf : IsCompletelyMonotoneOnIoi f) {c : ℝ} (hc : 0 ≤ c) :
    IsCompletelyMonotoneOnIoi (c • f) := by
  refine ⟨hf.contDiffOn.const_smul c, fun n t ht => ?_⟩
  rw [iteratedDeriv_const_smul_field]
  simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    mul_nonneg hc (hf.neg_one_pow_mul_iteratedDeriv_nonneg n ht)

/-- The closed-half-line Tau Ceti predicate restricts to complete monotonicity on `(0, ∞)`. -/
lemma _root_.TauCeti.IsCompletelyMonotone.isCompletelyMonotoneOnIoi
    (hf : IsCompletelyMonotone f) : IsCompletelyMonotoneOnIoi f :=
  ⟨hf.contDiffOn.mono Ioi_subset_Ici_self,
    fun n _ ht => hf.neg_one_pow_mul_iteratedDeriv_nonneg n ht⟩

end IsCompletelyMonotoneOnIoi

end TauCeti
