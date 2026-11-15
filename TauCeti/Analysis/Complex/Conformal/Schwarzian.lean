/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import TauCeti.Analysis.Complex.Conformal.PreSchwarzian

/-!
# The Schwarzian derivative

The **Schwarzian derivative** of a holomorphic function `f` is
`S(f) = f''' / f' - (3 / 2) * (f'' / f') ^ 2`.  In terms of the pre-Schwarzian derivative
`P(f) = f'' / f'` it is `S(f) = P(f)' - P(f) ^ 2 / 2`.  Unlike the pre-Schwarzian, which is
invariant only under postcomposition with affine maps, the Schwarzian is invariant under
postcomposition with every Möbius transformation `w ↦ (a * w + b) / (c * w + d)` with
`a * d - b * c ≠ 0`.  Consequently the Schwarzian of a local inverse of a holomorphic covering
does not depend on the chosen branch whenever two branches differ by a Möbius map, which is how it
enters the differential equations satisfied by inverses of universal coverings of punctured
spheres.

The definition `TauCeti.schwarzian` is totalized: at a critical point of `f`, Lean's division
by zero makes it zero.  The analytic identities below therefore carry nonvanishing hypotheses on
the relevant first derivatives where they are needed.

## Main results

* `TauCeti.schwarzian_eq_div_sub_sq` -- the classical formula
  `S(f) = f''' / f' - (3 / 2) * (f'' / f') ^ 2`, valid everywhere for the totalized definition.
* `TauCeti.schwarzian_eq_deriv_logDeriv_deriv_sub` -- the Schwarzian in terms of the
  pre-Schwarzian derivative `logDeriv (deriv f)`.
* `TauCeti.schwarzian_comp` -- the chain rule
  `S(f ∘ g) = (S(f) ∘ g) * (g') ^ 2 + S(g)`.
* `TauCeti.schwarzian_const_mul_add`, `TauCeti.schwarzian_fun_inv` and
  `TauCeti.schwarzian_moebius` -- invariance under postcomposition with affine maps, inversion and
  Möbius maps.
* `TauCeti.schwarzian_affine`, `TauCeti.schwarzian_zpow`, `TauCeti.schwarzian_pow` and
  `TauCeti.schwarzian_inv` -- the Schwarzians of affine maps and of integer powers; in
  particular `S(x ↦ x ^ 2) = -3 / (2 * x ^ 2)` and `S(x ↦ 1 / x) = 0`.

## References

* O. Lehto, *Univalent Functions and Teichmüller Spaces*, Chapter II, Section 1.
* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), Remark 5.1.10.
-/

public section

namespace TauCeti

open Filter Topology

variable {f g : ℂ → ℂ} {x : ℂ}

/-- The **Schwarzian derivative** `S(f) = f''' / f' - (3 / 2) * (f'' / f') ^ 2`, written over the
common denominator `2 * f' ^ 2`.  It is totalized: at a point where `f' = 0` it is zero, and it
carries no geometric meaning there. -/
noncomputable def schwarzian (f : ℂ → ℂ) (x : ℂ) : ℂ :=
  (2 * iteratedDeriv 3 f x * deriv f x - 3 * iteratedDeriv 2 f x ^ 2) / (2 * deriv f x ^ 2)

/-- The defining formula of `TauCeti.schwarzian`. -/
theorem schwarzian_def (f : ℂ → ℂ) (x : ℂ) :
    schwarzian f x =
      (2 * iteratedDeriv 3 f x * deriv f x - 3 * iteratedDeriv 2 f x ^ 2) /
        (2 * deriv f x ^ 2) :=
  (rfl)

/-- The classical form of the Schwarzian derivative,
`S(f) = f''' / f' - (3 / 2) * (f'' / f') ^ 2`.  Both sides vanish at a critical point, so the
identity holds everywhere. -/
theorem schwarzian_eq_div_sub_sq (f : ℂ → ℂ) (x : ℂ) :
    schwarzian f x =
      iteratedDeriv 3 f x / deriv f x - 3 / 2 * (iteratedDeriv 2 f x / deriv f x) ^ 2 := by
  rw [schwarzian_def]
  by_cases h : deriv f x = 0
  · simp [h]
  · field_simp

/-- The Schwarzian derivative vanishes at a critical point, by totalization. -/
theorem schwarzian_of_deriv_eq_zero (h : deriv f x = 0) : schwarzian f x = 0 := by
  simp [schwarzian_def, h]

/-- The Schwarzian derivative at `x` depends only on the germ of the function at `x`. -/
theorem _root_.Filter.EventuallyEq.schwarzian_eq (h : f =ᶠ[𝓝 x] g) :
    schwarzian f x = schwarzian g x := by
  simp only [schwarzian_def, h.deriv_eq, h.iteratedDeriv_eq]

/-- **The Schwarzian derivative through the pre-Schwarzian derivative.**  For `f` holomorphic at
`x` with `f' x ≠ 0`, `S(f) = P(f)' - P(f) ^ 2 / 2`, where `P(f) = logDeriv (deriv f)`. -/
theorem schwarzian_eq_deriv_logDeriv_deriv_sub (hf : AnalyticAt ℂ f x) (hfx : deriv f x ≠ 0) :
    schwarzian f x = deriv (logDeriv (deriv f)) x - logDeriv (deriv f) x ^ 2 / 2 := by
  have hP : logDeriv (deriv f) = deriv (deriv f) / deriv f :=
    funext fun y => logDeriv_apply _ y
  rw [hP, Pi.div_apply, deriv_div hf.deriv.deriv.differentiableAt hf.deriv.differentiableAt hfx,
    schwarzian_def, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
  field_simp
  ring

/-- **The chain rule for the Schwarzian derivative.**  If `g` is holomorphic at `x` and `f` is
holomorphic at `g x` with `f' (g x) ≠ 0`, then `S(f ∘ g) = (S(f) ∘ g) * (g') ^ 2 + S(g)` at
`x`.  No hypothesis on `g' x` is needed: if it vanishes, both sides vanish. -/
theorem schwarzian_comp (hf : AnalyticAt ℂ f (g x)) (hg : AnalyticAt ℂ g x)
    (hfn : deriv f (g x) ≠ 0) :
    schwarzian (f ∘ g) x = schwarzian f (g x) * deriv g x ^ 2 + schwarzian g x := by
  have hdcomp : deriv (f ∘ g) x = deriv f (g x) * deriv g x :=
    deriv_comp x hf.differentiableAt hg.differentiableAt
  by_cases hgn : deriv g x = 0
  · rw [schwarzian_of_deriv_eq_zero (by rw [hdcomp, hgn, mul_zero]),
      schwarzian_of_deriv_eq_zero hgn, hgn]
    ring
  -- Near `x`, the pre-Schwarzian of `f ∘ g` is given by its chain rule.
  have hev : logDeriv (deriv (f ∘ g)) =ᶠ[𝓝 x]
      fun y => logDeriv (deriv f) (g y) * deriv g y + logDeriv (deriv g) y := by
    filter_upwards [hg.continuousAt.preimage_mem_nhds hf.eventually_analyticAt,
      hg.eventually_analyticAt,
      hg.continuousAt.preimage_mem_nhds (hf.deriv.continuousAt.eventually_ne hfn)]
      with y hfy hgy hny
    exact logDeriv_deriv_comp hfy hgy hny
  have hPf : DifferentiableAt ℂ (logDeriv (deriv f)) (g x) :=
    hf.deriv.deriv.differentiableAt.div hf.deriv.differentiableAt hfn
  have hPg : DifferentiableAt ℂ (logDeriv (deriv g)) x :=
    hg.deriv.deriv.differentiableAt.div hg.deriv.differentiableAt hgn
  have hderiv : deriv (logDeriv (deriv (f ∘ g))) x =
      deriv (logDeriv (deriv f)) (g x) * deriv g x * deriv g x +
        logDeriv (deriv f) (g x) * deriv (deriv g) x + deriv (logDeriv (deriv g)) x := by
    rw [hev.deriv_eq]
    exact (((hPf.hasDerivAt.comp x hg.differentiableAt.hasDerivAt).mul
      hg.deriv.differentiableAt.hasDerivAt).add hPg.hasDerivAt).deriv
  have hg2 : deriv (deriv g) x = logDeriv (deriv g) x * deriv g x := by
    rw [logDeriv_apply]
    field_simp
  have hfgn : deriv (f ∘ g) x ≠ 0 := by
    rw [hdcomp]
    exact mul_ne_zero hfn hgn
  rw [schwarzian_eq_deriv_logDeriv_deriv_sub (hf.comp hg) hfgn,
    hderiv, hev.eq_of_nhds, schwarzian_eq_deriv_logDeriv_deriv_sub hf hfn,
    schwarzian_eq_deriv_logDeriv_deriv_sub hg hgn, hg2]
  ring

/-- **Invariance of the Schwarzian derivative under affine postcomposition.**  For `a ≠ 0`,
`S(a * f + b) = S(f)`; no regularity of `f` is needed. -/
theorem schwarzian_const_mul_add {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    schwarzian (fun y => a * f y + b) x = schwarzian f x := by
  have hd : deriv (fun y => a * f y + b) = fun y => a * deriv f y := by
    funext y
    rw [deriv_add_const, deriv_const_mul_field']
  have hn (n : ℕ) :
      iteratedDeriv (n + 1) (fun y => a * f y + b) x = a * iteratedDeriv (n + 1) f x := by
    rw [iteratedDeriv_succ', hd, iteratedDeriv_const_mul_field, iteratedDeriv_succ']
  rw [schwarzian_def, schwarzian_def, hn 2, hn 1, hd]
  by_cases h : deriv f x = 0
  · simp [h]
  · field_simp

/-- The Schwarzian derivative of an affine map vanishes. -/
@[simp]
theorem schwarzian_affine (a b x : ℂ) : schwarzian (fun y => a * y + b) x = 0 := by
  have hd : deriv (fun y => a * y + b) = fun _ => a := by
    funext y
    simp
  have h2 : iteratedDeriv 2 (fun y => a * y + b) x = 0 := by
    rw [iteratedDeriv_succ', hd]
    simp
  have h3 : iteratedDeriv 3 (fun y => a * y + b) x = 0 := by
    rw [iteratedDeriv_succ', hd, iteratedDeriv_succ']
    simp
  simp [schwarzian_def, h2, h3]

/-- The Schwarzian derivative of a nonzero integer power:
`S(x ↦ x ^ m) = (1 - m ^ 2) / (2 * x ^ 2)`.  At `x = 0` both sides vanish. -/
theorem schwarzian_zpow {m : ℤ} (hm : m ≠ 0) (x : ℂ) :
    schwarzian (fun y => y ^ m) x = (1 - (m : ℂ) ^ 2) / (2 * x ^ 2) := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  rw [schwarzian_def, ← iteratedDeriv_one, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    iteratedDeriv_eq_iterate, iter_deriv_zpow, iter_deriv_zpow, iter_deriv_zpow]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, sub_zero, one_mul]
  rcases eq_or_ne x 0 with rfl | hx
  · rcases eq_or_ne m 1 with rfl | hm1
    · simp
    · have h0 : (0 : ℂ) ^ (m - 1) = 0 := zero_zpow _ (by omega)
      simp [h0]
  · have hxm : x ^ m ≠ 0 := zpow_ne_zero m hx
    simp only [zpow_sub₀ hx, zpow_ofNat]
    field_simp
    ring

/-- The Schwarzian derivative of a nonzero natural power:
`S(x ↦ x ^ n) = (1 - n ^ 2) / (2 * x ^ 2)`.  For `n = 2` this is `-3 / (2 * x ^ 2)`. -/
theorem schwarzian_pow {n : ℕ} (hn : n ≠ 0) (x : ℂ) :
    schwarzian (fun y => y ^ n) x = (1 - (n : ℂ) ^ 2) / (2 * x ^ 2) := by
  simpa using schwarzian_zpow (m := n) (by exact_mod_cast hn) x

/-- The Schwarzian derivative of inversion vanishes. -/
@[simp]
theorem schwarzian_inv (x : ℂ) : schwarzian (fun y => y⁻¹) x = 0 := by
  simpa using schwarzian_zpow (m := -1) (by norm_num) x

/-- **Invariance of the Schwarzian derivative under inversion.**  If `f` is holomorphic at `x`
and `f x ≠ 0`, then `S(1 / f) = S(f)` at `x`. -/
theorem schwarzian_fun_inv (hf : AnalyticAt ℂ f x) (hx : f x ≠ 0) :
    schwarzian (fun y => (f y)⁻¹) x = schwarzian f x := by
  have h := schwarzian_comp (f := fun w : ℂ => w⁻¹) (analyticAt_inv hx) hf (by simp [hx])
  simpa [Function.comp_def] using h

/-- **Möbius invariance of the Schwarzian derivative.**  If `a * d - b * c ≠ 0`, `f` is
holomorphic at `x` and `c * f x + d ≠ 0`, then postcomposing `f` with the Möbius map
`w ↦ (a * w + b) / (c * w + d)` does not change its Schwarzian derivative at `x`. -/
theorem schwarzian_moebius {a b c d : ℂ} (hD : a * d - b * c ≠ 0) (hf : AnalyticAt ℂ f x)
    (hx : c * f x + d ≠ 0) :
    schwarzian (fun y => (a * f y + b) / (c * f y + d)) x = schwarzian f x := by
  rcases eq_or_ne c 0 with rfl | hc
  · have hd : d ≠ 0 := by simpa using hx
    have ha : a ≠ 0 := by rintro rfl; simp at hD
    have h : (fun y => (a * f y + b) / (0 * f y + d)) = fun y => a / d * f y + b / d := by
      funext y
      rw [zero_mul, zero_add]
      ring
    rw [h, schwarzian_const_mul_add (div_ne_zero ha hd)]
  · -- Near `x`, the Möbius map is an affine function of `(c * f + d)⁻¹`.
    have hev : (fun y => (a * f y + b) / (c * f y + d)) =ᶠ[𝓝 x]
        fun y => (b * c - a * d) / c * (c * f y + d)⁻¹ + a / c := by
      filter_upwards [((hf.continuousAt.const_mul c).add_const d).eventually_ne hx] with y hy
      rw [div_eq_iff hy, add_mul, mul_assoc, inv_mul_cancel₀ hy, mul_one]
      field_simp
      ring
    have hK : (b * c - a * d) / c ≠ 0 :=
      div_ne_zero (fun h => hD (by linear_combination -h)) hc
    rw [hev.schwarzian_eq, schwarzian_const_mul_add hK,
      schwarzian_fun_inv (f := fun y => c * f y + d)
        ((analyticAt_const.mul hf).add analyticAt_const) hx,
      schwarzian_const_mul_add hc]

end TauCeti
