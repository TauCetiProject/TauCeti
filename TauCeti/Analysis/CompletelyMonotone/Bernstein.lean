/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Analysis.CompletelyMonotone.Closure
import Mathlib.Analysis.Convex.Deriv

/-!
# Bernstein functions

A *Bernstein function* is a nonnegative function `f : ℝ → ℝ`, smooth on the closed half-line
`[0, ∞)`, whose derivative is completely monotone. Equivalently `f ≥ 0` and `f'` alternates in
sign through every order: `0 ≤ f'`, `0 ≥ f''`, `0 ≤ f'''`, and so on. These are exactly the
functions `f` for which `t ↦ e^{-s f(t)}` is completely monotone for every `s ≥ 0`; in
probability they are the Laplace exponents of subordinators, and the
completely-monotone ↔ Bernstein correspondence (a Bernstein function has completely monotone
derivative, and a completely monotone function composed with a Bernstein function stays
completely monotone) is the backbone of the Lévy–Khinchine theory.

The smoothness clause is essential, exactly as for `TauCeti.IsCompletelyMonotone`: an iterated
derivative defaults to a junk value where the function fails to be differentiable, so without
demanding `ContDiffOn ℝ ∞ f [0, ∞)` a badly behaved `f` could be declared "Bernstein" because its
junk derivative `0` is (vacuously) completely monotone. We therefore bundle smoothness of `f`
directly into the predicate; the smoothness of `f'` then follows, so the completely-monotone
clause on `f'` is never satisfied vacuously.

A Bernstein function is nondecreasing (its derivative is nonnegative) and concave (its derivative
is nonincreasing) on `[0, ∞)`; both are recorded below. The class is closed under sums and
nonnegative scalar multiples, and the basic catalogue — constants, the identity, affine functions
`t ↦ c + d t` with `c, d ≥ 0`, and the prototype `t ↦ 1 - e^{-x t}` — is built from these.

## Main declarations

* `TauCeti.IsCompletelyMonotone.congr`: complete monotonicity only depends on the values of the
  function on `[0, ∞)` (a workhorse for computing derivatives in closed form).
* `TauCeti.IsBernsteinFunction`: the predicate that `f` is smooth, nonnegative, and has completely
  monotone derivative on `[0, ∞)`.
* `TauCeti.IsBernsteinFunction.nonneg`, `TauCeti.IsBernsteinFunction.derivWithin_nonneg`,
  `TauCeti.IsBernsteinFunction.monotoneOn`, `TauCeti.IsBernsteinFunction.concaveOn`: a Bernstein
  function is nonnegative, has nonnegative derivative, is nondecreasing, and is concave on
  `[0, ∞)`.
* `TauCeti.IsBernsteinFunction.add`, `TauCeti.IsBernsteinFunction.const_smul`,
  `TauCeti.IsBernsteinFunction.sum`: closure under sums, nonnegative scalar multiples, and finite
  sums.
* `TauCeti.isBernsteinFunction_const`, `TauCeti.isBernsteinFunction_id`,
  `TauCeti.isBernsteinFunction_affine`, `TauCeti.isBernsteinFunction_one_sub_exp_neg_mul`: the
  basic examples.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012).
-/

open Set Filter
open scoped ContDiff Topology

namespace TauCeti

/-- Complete monotonicity is determined by the values of the function on `[0, ∞)`: if `g` agrees
with a completely monotone `f` throughout `[0, ∞)`, then `g` is completely monotone too. Both the
smoothness clause and the sign condition only see the function within `[0, ∞)`. -/
lemma IsCompletelyMonotone.congr {f g : ℝ → ℝ} (hf : IsCompletelyMonotone f)
    (h : Set.EqOn g f (Ici 0)) : IsCompletelyMonotone g := by
  refine ⟨hf.contDiffOn.congr fun x hx => h hx, fun n t ht => ?_⟩
  rw [iteratedDerivWithin_congr h (mem_Ici.mpr ht)]
  exact hf.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht

/-- A function `f : ℝ → ℝ` is a **Bernstein function** if it is `C^∞` on the closed half-line
`[0, ∞)`, nonnegative there, and its derivative within `[0, ∞)` is completely monotone. The
smoothness clause prevents the derivative condition from being satisfied vacuously by a junk
derivative. -/
def IsBernsteinFunction (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (Ici 0) ∧ (∀ t : ℝ, 0 ≤ t → 0 ≤ f t) ∧
    IsCompletelyMonotone (derivWithin f (Ici 0))

/-- For a function differentiable at a point `x ≥ 0`, the derivative within `[0, ∞)` agrees with
the ordinary derivative. -/
private lemma derivWithin_Ici_eq_deriv {f : ℝ → ℝ} {x : ℝ} (hx : x ∈ Ici (0 : ℝ))
    (hf : DifferentiableAt ℝ f x) : derivWithin f (Ici 0) x = deriv f x :=
  hf.derivWithin (uniqueDiffOn_Ici 0 x hx)

namespace IsBernsteinFunction

variable {f g : ℝ → ℝ}

/-- A Bernstein function is `C^∞` on `[0, ∞)`. -/
lemma contDiffOn (hf : IsBernsteinFunction f) : ContDiffOn ℝ ∞ f (Ici 0) := hf.1

/-- A Bernstein function is nonnegative on `[0, ∞)`. -/
lemma nonneg (hf : IsBernsteinFunction f) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ f t := hf.2.1 t ht

/-- The derivative within `[0, ∞)` of a Bernstein function is completely monotone. -/
lemma derivWithin_isCompletelyMonotone (hf : IsBernsteinFunction f) :
    IsCompletelyMonotone (derivWithin f (Ici 0)) := hf.2.2

/-- A Bernstein function is differentiable on `[0, ∞)`. -/
lemma differentiableOn (hf : IsBernsteinFunction f) : DifferentiableOn ℝ f (Ici 0) :=
  hf.contDiffOn.differentiableOn (by simp)

/-- The derivative within `[0, ∞)` of a Bernstein function is nonnegative: a Bernstein function is
nondecreasing. -/
lemma derivWithin_nonneg (hf : IsBernsteinFunction f) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ derivWithin f (Ici 0) t :=
  hf.derivWithin_isCompletelyMonotone.nonneg ht

/-- A Bernstein function is nondecreasing on `[0, ∞)`. -/
lemma monotoneOn (hf : IsBernsteinFunction f) : MonotoneOn f (Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hf.contDiffOn.continuousOn
    (hf.differentiableOn.mono interior_subset) fun x hx => ?_
  rw [interior_Ici] at hx
  have hmem : Ici (0 : ℝ) ∈ 𝓝 x := mem_of_superset (isOpen_Ioi.mem_nhds hx) Ioi_subset_Ici_self
  rw [← derivWithin_of_mem_nhds hmem]
  exact hf.derivWithin_nonneg hx.le

/-- A Bernstein function is concave on `[0, ∞)`: its derivative is nonincreasing. -/
lemma concaveOn (hf : IsBernsteinFunction f) : ConcaveOn ℝ (Ici 0) f := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici 0) hf.contDiffOn.continuousOn
    (hf.differentiableOn.mono interior_subset) fun a ha b hb hab => ?_
  rw [interior_Ici] at ha hb
  have hma : Ici (0 : ℝ) ∈ 𝓝 a := mem_of_superset (isOpen_Ioi.mem_nhds ha) Ioi_subset_Ici_self
  have hmb : Ici (0 : ℝ) ∈ 𝓝 b := mem_of_superset (isOpen_Ioi.mem_nhds hb) Ioi_subset_Ici_self
  rw [← derivWithin_of_mem_nhds hma, ← derivWithin_of_mem_nhds hmb]
  exact hf.derivWithin_isCompletelyMonotone.antitoneOn (mem_Ici.mpr ha.le) (mem_Ici.mpr hb.le) hab

/-- Bernstein functions are closed under addition. -/
theorem add (hf : IsBernsteinFunction f) (hg : IsBernsteinFunction g) :
    IsBernsteinFunction (f + g) := by
  refine ⟨hf.contDiffOn.add hg.contDiffOn, fun t ht => add_nonneg (hf.nonneg ht) (hg.nonneg ht), ?_⟩
  have hd : Set.EqOn (derivWithin (f + g) (Ici 0))
      (derivWithin f (Ici 0) + derivWithin g (Ici 0)) (Ici 0) := by
    intro x hx
    rw [Pi.add_apply, derivWithin_add (hf.differentiableOn x hx) (hg.differentiableOn x hx)]
  exact (hf.derivWithin_isCompletelyMonotone.add hg.derivWithin_isCompletelyMonotone).congr hd

/-- Bernstein functions are closed under multiplication by a nonnegative constant. -/
theorem const_smul (hf : IsBernsteinFunction f) {c : ℝ} (hc : 0 ≤ c) :
    IsBernsteinFunction (c • f) := by
  refine ⟨hf.contDiffOn.const_smul c, fun t ht => ?_, ?_⟩
  · simpa [Pi.smul_apply, smul_eq_mul] using mul_nonneg hc (hf.nonneg ht)
  have hd : Set.EqOn (derivWithin (c • f) (Ici 0)) (c • derivWithin f (Ici 0)) (Ici 0) := by
    intro x hx
    rw [Pi.smul_apply, derivWithin_const_smul c (hf.differentiableOn x hx)]
  exact (hf.derivWithin_isCompletelyMonotone.smul hc).congr hd

end IsBernsteinFunction

/-- A nonnegative constant function is a Bernstein function. -/
theorem isBernsteinFunction_const {c : ℝ} (hc : 0 ≤ c) :
    IsBernsteinFunction (fun _ : ℝ => c) := by
  refine ⟨contDiffOn_const, fun _ _ => hc, ?_⟩
  have hd : Set.EqOn (derivWithin (fun _ : ℝ => c) (Ici 0)) (fun _ => (0 : ℝ)) (Ici 0) := by
    intro x hx
    rw [derivWithin_Ici_eq_deriv hx (differentiableAt_const c)]
    simp
  exact (isCompletelyMonotone_const le_rfl).congr hd

/-- The zero function is a Bernstein function. -/
theorem isBernsteinFunction_zero : IsBernsteinFunction (fun _ : ℝ => (0 : ℝ)) :=
  isBernsteinFunction_const le_rfl

namespace IsBernsteinFunction

/-- Bernstein functions are closed under finite sums. -/
theorem sum {ι : Type*} {s : Finset ι} {f : ι → ℝ → ℝ}
    (hf : ∀ i ∈ s, IsBernsteinFunction (f i)) :
    IsBernsteinFunction (fun t => ∑ i ∈ s, f i t) := by
  have h := Finset.sum_induction f IsBernsteinFunction (fun _ _ => IsBernsteinFunction.add)
    isBernsteinFunction_zero hf
  have heq : (∑ i ∈ s, f i) = fun t => ∑ i ∈ s, f i t := funext fun t => Finset.sum_apply t s f
  rwa [heq] at h

end IsBernsteinFunction

/-- The identity function is a Bernstein function: it is nonnegative on `[0, ∞)` with constant
derivative `1`. -/
theorem isBernsteinFunction_id : IsBernsteinFunction (fun t : ℝ => t) := by
  refine ⟨contDiffOn_id, fun t ht => ht, ?_⟩
  have hd : Set.EqOn (derivWithin (fun t : ℝ => t) (Ici 0)) (fun _ => (1 : ℝ)) (Ici 0) := by
    intro x hx
    rw [derivWithin_Ici_eq_deriv hx differentiableAt_fun_id]
    simp
  exact (isCompletelyMonotone_const zero_le_one).congr hd

/-- An affine function `t ↦ c + d t` with nonnegative coefficients is a Bernstein function. -/
theorem isBernsteinFunction_affine {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) :
    IsBernsteinFunction (fun t : ℝ => c + d * t) := by
  have h := (isBernsteinFunction_const hc).add (isBernsteinFunction_id.const_smul hd)
  have heq : ((fun _ : ℝ => c) + (d • fun t : ℝ => t)) = fun t : ℝ => c + d * t := by
    funext t; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rwa [heq] at h

/-- The prototype Bernstein function `t ↦ 1 - e^{-x t}` for `x ≥ 0`: it is nonnegative on
`[0, ∞)` and its derivative `t ↦ x e^{-x t}` is completely monotone. -/
theorem isBernsteinFunction_one_sub_exp_neg_mul {x : ℝ} (hx : 0 ≤ x) :
    IsBernsteinFunction (fun t : ℝ => 1 - Real.exp (-x * t)) := by
  -- The derivative is `t ↦ x e^{-x t}`, computed once and for all.
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => 1 - Real.exp (-x * t))
      (x * Real.exp (-x * t)) t := by
    intro t
    have hb : HasDerivAt (fun t : ℝ => -x * t) (-x) t := by
      simpa using (hasDerivAt_id t).const_mul (-x)
    have he := (hb.exp).const_sub 1
    have key : x * Real.exp (-x * t) = -(Real.exp (-x * t) * -x) := by ring
    rw [key]; exact he
  refine ⟨?_, fun t ht => ?_, ?_⟩
  · fun_prop
  · -- `e^{-x t} ≤ 1` because `-x t ≤ 0`.
    have hle : Real.exp (-x * t) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith)
    linarith
  · have hcm : IsCompletelyMonotone (x • fun t : ℝ => Real.exp (-x * t)) :=
      (isCompletelyMonotone_exp_neg_mul hx).smul hx
    have hd : Set.EqOn (derivWithin (fun t : ℝ => 1 - Real.exp (-x * t)) (Ici 0))
        (x • fun t : ℝ => Real.exp (-x * t)) (Ici 0) := by
      intro t ht
      rw [derivWithin_Ici_eq_deriv ht (hderiv t).differentiableAt, (hderiv t).deriv]
      simp [Pi.smul_apply, smul_eq_mul]
    exact hcm.congr hd

end TauCeti
