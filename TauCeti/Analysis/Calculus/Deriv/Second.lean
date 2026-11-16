/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.CompMul
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv
import TauCeti.Analysis.SpecialFunctions.Log.Deriv

/-!
# Second derivatives of functions of one variable

Computations of the second derivative `deriv (deriv f)` of a function of one variable.

The `n`-th iterated derivative of `fun x ↦ f (c * x)` is `c ^ n` times the `n`-th iterated
derivative of `f` at `c * x`; in particular its second derivative is `c ^ 2` times the second
derivative of `f` at `c * x`. As for `deriv_comp_mul_left`, no differentiability of `f` is needed,
since Mathlib's derivative is `0` wherever it is undefined. Mathlib's
`iteratedDeriv_comp_const_smul` states the same formula under a `ContDiff` hypothesis.

The second derivative of a quadratic polynomial `a + b s + c s ^ 2` is the constant `2 c`, and
the affine line `t ↦ a + t • b` has constant derivative `b` and vanishing second derivative.

The second derivative of `√(g s)` at a point where `g` is positive is
`g'' / (2 √g) - g' ^ 2 / (4 g √g)`. Specializing to a quadratic polynomial
`Q s = a + b s + c s ^ 2`, since `2 Q Q'' - Q' ^ 2` is the constant `4 a c - b ^ 2`, gives
`(4 a c - b ^ 2) / (4 Q √Q)`; at `0` this is `(4 a c - b ^ 2) / (4 a √a)`.

Under the change of variables `x = e^y` the operators `x d/dx` and `x² d²/dx²` become `d/dy` and
`d²/dy² - d/dy`: for `v` twice differentiable at `log x`, `x (v ∘ log)'(x) = v'(log x)` and
`x² (v ∘ log)''(x) = v''(log x) - v'(log x)`, and conversely
`(f ∘ exp)''(y) = e^y f'(e^y) + e^{2y} f''(e^y)`. These turn equations of Euler type, whose
coefficients `x` and `x²` degenerate at `0`, into equations with constant coefficients.

## Main results

* `TauCeti.iteratedDeriv_comp_mul_left`: the iterated derivatives of `fun x ↦ f (c * x)`, and
  `TauCeti.deriv_deriv_comp_mul_left` its second derivative.
* `TauCeti.deriv_deriv_quadratic`: the second derivative of `s ↦ a + b s + c s ^ 2`.
* `TauCeti.deriv_const_add_smul`, `TauCeti.iteratedDeriv_two_const_add_smul`: the first and
  second derivatives of the affine line `t ↦ a + t • b`.
* `TauCeti.hasDerivAt_deriv_sqrt`, `TauCeti.deriv_deriv_sqrt`: the second derivative of
  `s ↦ √(g s)` where `g` is positive.
* `TauCeti.deriv_deriv_sqrt_quadratic`: the second derivative of `s ↦ √(a + b s + c s ^ 2)`, and
  `TauCeti.deriv_deriv_sqrt_quadratic_zero` its value at `0`.
* `TauCeti.sq_mul_deriv_deriv_comp_log`, `TauCeti.deriv_deriv_comp_exp`: the second derivatives
  under the change of variables `x = e^y`.
-/

public section

open Filter Real Topology

namespace TauCeti

section CompMul

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The `n`-th iterated derivative of `fun x ↦ f (c * x)` is
`fun x ↦ c ^ n • iteratedDeriv n f (c * x)`, with no differentiability assumption on `f`. -/
theorem iteratedDeriv_comp_mul_left (n : ℕ) (c : 𝕜) (f : 𝕜 → F) :
    iteratedDeriv n (f <| c * ·) = fun x ↦ c ^ n • iteratedDeriv n f (c * x) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_smul]
  | succ n ih =>
    funext x
    rw [iteratedDeriv_succ, ih, deriv_fun_const_smul_field, deriv_comp_mul_left,
      iteratedDeriv_succ, smul_smul, pow_succ]

/-- The second derivative of `fun x ↦ f (c * x)` at `x` is `c ^ 2 • deriv (deriv f) (c * x)`,
with no differentiability assumption on `f`. -/
theorem deriv_deriv_comp_mul_left (c : 𝕜) (f : 𝕜 → F) (x : 𝕜) :
    deriv (deriv (f <| c * ·)) x = c ^ 2 • deriv (deriv f) (c * x) := by
  simpa only [iteratedDeriv_succ (n := 1), iteratedDeriv_one] using
    congrFun (iteratedDeriv_comp_mul_left 2 c f) x

end CompMul

section Quadratic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The derivative of a quadratic polynomial `a + b * s + c * s ^ 2` at `t` is `b + 2 * c * t`. -/
theorem hasDerivAt_quadratic (a b c t : 𝕜) :
    HasDerivAt (fun s ↦ a + b * s + c * s ^ 2) (b + 2 * c * t) t := by
  have h := HasDerivAt.add (HasDerivAt.const_add a (HasDerivAt.const_mul b (hasDerivAt_id t)))
    (HasDerivAt.const_mul c (hasDerivAt_pow 2 t))
  convert h using 1
  · ext u
    simp only [id, Pi.add_apply]
  · simp only [mul_one, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring

/-- The second derivative of a quadratic polynomial `a + b * s + c * s ^ 2` is `2 * c`. -/
theorem deriv_deriv_quadratic (a b c t : 𝕜) :
    deriv (deriv fun s ↦ a + b * s + c * s ^ 2) t = 2 * c := by
  have h : deriv (fun s ↦ a + b * s + c * s ^ 2) = fun s ↦ b + 2 * c * s :=
    funext fun s ↦ (hasDerivAt_quadratic a b c s).deriv
  rw [h]
  simp

end Quadratic

section AffineLine

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of the affine line `t ↦ a + t • b` is constantly `b`. -/
theorem deriv_const_add_smul (a b : F) : deriv (fun t : 𝕜 ↦ a + t • b) = fun _ ↦ b :=
  funext fun t ↦ by simpa using (((hasDerivAt_id t).smul_const b).const_add a).deriv

/-- The second derivative of the affine line `t ↦ a + t • b` vanishes. -/
@[simp]
theorem iteratedDeriv_two_const_add_smul (a b : F) :
    iteratedDeriv 2 (fun t : 𝕜 ↦ a + t • b) = 0 := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, deriv_const_add_smul, deriv_const',
    Pi.zero_def]

end AffineLine

/-- The second derivative of `s ↦ √(g s)` at a point `t` where `0 < g t`, `g` has derivative
`g'` at `t`, and `deriv g` has derivative `g''` at `t`, is
`g'' / (2 * √(g t)) - g' ^ 2 / (4 * g t * √(g t))`. -/
theorem hasDerivAt_deriv_sqrt {g : ℝ → ℝ} {g' g'' t : ℝ} (ht : 0 < g t)
    (hg' : HasDerivAt g g' t) (hg'' : HasDerivAt (deriv g) g'' t) :
    HasDerivAt (deriv fun s ↦ √(g s))
      (g'' / (2 * √(g t)) - g' ^ 2 / (4 * g t * √(g t))) t := by
  have hpos : ∀ᶠ s in 𝓝 t, 0 < g s :=
    continuousAt_const.eventually_lt hg'.continuousAt ht
  have hderiv : deriv (fun s ↦ √(g s)) =ᶠ[𝓝 t] fun s ↦ deriv g s / (2 * √(g s)) := by
    filter_upwards [eventually_eventually_nhds.mpr hpos] with s hspos
    by_cases hds : DifferentiableAt ℝ g s
    · exact (hds.hasDerivAt.sqrt hspos.self_of_nhds.ne').deriv
    · have hds_sqrt : ¬ DifferentiableAt ℝ (fun u ↦ √(g u)) s := fun hd ↦
        hds ((hd.pow 2).congr_of_eventuallyEq (hspos.mono fun u hu ↦ (Real.sq_sqrt hu.le).symm))
      rw [deriv_zero_of_not_differentiableAt hds_sqrt, deriv_zero_of_not_differentiableAt hds,
        zero_div]
  have hden : HasDerivAt (fun s ↦ 2 * √(g s)) (2 * (g' / (2 * √(g t)))) t :=
    (hg'.sqrt ht.ne').const_mul 2
  refine ((HasDerivAt.fun_div hg'' hden (by positivity)).congr_of_eventuallyEq hderiv).congr_deriv
    ?_
  have hsq := Real.sq_sqrt ht.le
  rw [hg'.deriv]
  field_simp
  rw [hsq]
  ring

/-- Evaluating `hasDerivAt_deriv_sqrt` as `deriv (deriv fun s ↦ √(g s)) t`. -/
theorem deriv_deriv_sqrt {g : ℝ → ℝ} {t : ℝ} (ht : 0 < g t)
    (hg : DifferentiableAt ℝ g t) (hg'' : DifferentiableAt ℝ (deriv g) t) :
    deriv (deriv fun s ↦ √(g s)) t =
      deriv (deriv g) t / (2 * √(g t)) - deriv g t ^ 2 / (4 * g t * √(g t)) :=
  (hasDerivAt_deriv_sqrt ht hg.hasDerivAt hg''.hasDerivAt).deriv

/-- The second derivative of the square root of a quadratic polynomial
`Q s = a + b * s + c * s ^ 2` at a point `t` where `Q` is positive is
`(4 * a * c - b ^ 2) / (4 * Q t * √(Q t))`. -/
theorem deriv_deriv_sqrt_quadratic {a b c t : ℝ} (ht : 0 < a + b * t + c * t ^ 2) :
    deriv (deriv fun s ↦ √(a + b * s + c * s ^ 2)) t =
      (4 * a * c - b ^ 2) / (4 * (a + b * t + c * t ^ 2) * √(a + b * t + c * t ^ 2)) := by
  have hd : deriv (fun s ↦ a + b * s + c * s ^ 2) = fun s ↦ b + 2 * c * s :=
    funext fun s ↦ (hasDerivAt_quadratic a b c s).deriv
  have hdd : HasDerivAt (deriv fun s ↦ a + b * s + c * s ^ 2) (2 * c) t := by
    rw [hd]
    simpa using ((hasDerivAt_id t).const_mul (2 * c)).const_add b
  rw [(hasDerivAt_deriv_sqrt (g := fun s ↦ a + b * s + c * s ^ 2) ht
    (hasDerivAt_quadratic a b c t) hdd).deriv]
  field_simp
  ring

/-- The second derivative at `0` of the square root of a quadratic polynomial
`a + b * s + c * s ^ 2` with `0 < a` is `(4 * a * c - b ^ 2) / (4 * a * √a)`. -/
theorem deriv_deriv_sqrt_quadratic_zero {a b c : ℝ} (ha : 0 < a) :
    deriv (deriv fun s ↦ √(a + b * s + c * s ^ 2)) 0 = (4 * a * c - b ^ 2) / (4 * a * √a) := by
  simpa using deriv_deriv_sqrt_quadratic (b := b) (c := c) (t := 0) (by simpa using ha)

section LogExp

variable {f v : ℝ → ℝ} {x y : ℝ}

/-- Under the change of variables `x = e^y` the operator `x² d²/dx²` is `d²/dy² - d/dy`:
`x² (v ∘ log)''(x) = v''(log x) - v'(log x)` for `x ≠ 0`. -/
theorem sq_mul_deriv_deriv_comp_log (hv' : DifferentiableAt ℝ (deriv v) (log x)) (hx : x ≠ 0) :
    x ^ 2 * deriv (deriv fun x ↦ v (log x)) x = deriv (deriv v) (log x) - deriv v (log x) := by
  have hev : deriv (fun x ↦ v (log x)) =ᶠ[𝓝 x] fun x ↦ deriv v (log x) / x := by
    filter_upwards [eventually_ne_nhds hx] with z hz0
    rw [← mul_deriv_comp_log hz0]
    field_simp
  have h : HasDerivAt (fun x ↦ deriv v (log x) / x)
      ((deriv (deriv v) (log x) * x⁻¹ * x - deriv v (log x) * 1) / x ^ 2) x :=
    (hv'.hasDerivAt.comp x (hasDerivAt_log hx)).div (hasDerivAt_id x) hx
  rw [hev.deriv_eq, h.deriv]
  field_simp

/-- The second derivative of `f ∘ exp`: `(f ∘ exp)''(y) = e^y f'(e^y) + e^{2y} f''(e^y)`. -/
theorem deriv_deriv_comp_exp (hf' : DifferentiableAt ℝ (deriv f) (exp y)) :
    deriv (deriv fun y ↦ f (exp y)) y =
      exp y * deriv f (exp y) + exp y ^ 2 * deriv (deriv f) (exp y) := by
  have hd : deriv (fun y ↦ f (exp y)) = fun y ↦ exp y * deriv f (exp y) :=
    funext fun _ ↦ deriv_comp_exp
  have h : HasDerivAt (fun y ↦ exp y * deriv f (exp y))
      (exp y * deriv f (exp y) + exp y * (deriv (deriv f) (exp y) * exp y)) y :=
    (hasDerivAt_exp y).mul (hf'.hasDerivAt.comp y (hasDerivAt_exp y))
  rw [hd, h.deriv]
  ring

end LogExp

end TauCeti
