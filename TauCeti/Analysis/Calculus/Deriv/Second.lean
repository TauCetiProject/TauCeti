/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.CompMul
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Second derivatives of functions of one variable

Computations of the second derivative `deriv (deriv f)` of a function of one variable.

The `n`-th iterated derivative of `fun x ↦ f (c * x)` is `c ^ n` times the `n`-th iterated
derivative of `f` at `c * x`; in particular its second derivative is `c ^ 2` times the second
derivative of `f` at `c * x`. As for `deriv_comp_mul_left`, no differentiability of `f` is needed,
since Mathlib's derivative is `0` wherever it is undefined. Mathlib's
`iteratedDeriv_comp_const_smul` states the same formula under a `ContDiff` hypothesis.

The second derivative of a quadratic polynomial `a + b s + c s ^ 2` is the constant `2 c`.

The second derivative of the square root of a quadratic polynomial `Q s = a + b s + c s ^ 2` is
computed where `Q` is positive. Since `2 Q Q'' - Q' ^ 2` is the constant `4 a c - b ^ 2`, it is
`(4 a c - b ^ 2) / (4 Q √Q)`; at `0` this is `(4 a c - b ^ 2) / (4 a √a)`.

## Main results

* `TauCeti.iteratedDeriv_comp_mul_left`: the iterated derivatives of `fun x ↦ f (c * x)`, and
  `TauCeti.deriv_deriv_comp_mul_left` its second derivative.
* `TauCeti.deriv_deriv_quadratic`: the second derivative of `s ↦ a + b s + c s ^ 2`.
* `TauCeti.deriv_deriv_sqrt_quadratic`: the second derivative of `s ↦ √(a + b s + c s ^ 2)`, and
  `TauCeti.deriv_deriv_sqrt_quadratic_zero` its value at `0`.
-/

public section

open Filter Topology

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

/-- The second derivative of the square root of a quadratic polynomial
`Q s = a + b * s + c * s ^ 2` at a point `t` where `Q` is positive is
`(4 * a * c - b ^ 2) / (4 * Q t * √(Q t))`. -/
theorem deriv_deriv_sqrt_quadratic {a b c t : ℝ} (ht : 0 < a + b * t + c * t ^ 2) :
    deriv (deriv fun s ↦ √(a + b * s + c * s ^ 2)) t =
      (4 * a * c - b ^ 2) / (4 * (a + b * t + c * t ^ 2) * √(a + b * t + c * t ^ 2)) := by
  have hQ (s : ℝ) := hasDerivAt_quadratic a b c s
  have hpos : ∀ᶠ s in 𝓝 t, 0 < a + b * s + c * s ^ 2 :=
    continuousAt_const.eventually_lt (HasDerivAt.continuousAt (hQ t)) ht
  have hderiv : deriv (fun s ↦ √(a + b * s + c * s ^ 2)) =ᶠ[𝓝 t]
      fun s ↦ (b + 2 * c * s) / (2 * √(a + b * s + c * s ^ 2)) :=
    hpos.mono fun s hs ↦ (HasDerivAt.sqrt (hQ s) hs.ne').deriv
  have hnum : HasDerivAt (fun s ↦ b + 2 * c * s) (2 * c) t := by
    simpa using HasDerivAt.const_add b (HasDerivAt.const_mul (2 * c) (hasDerivAt_id t))
  have hsqrt := Real.sqrt_pos.2 ht
  have hden : HasDerivAt (fun s ↦ 2 * √(a + b * s + c * s ^ 2))
      (2 * ((b + 2 * c * t) / (2 * √(a + b * t + c * t ^ 2)))) t :=
    HasDerivAt.const_mul 2 (HasDerivAt.sqrt (hQ t) ht.ne')
  rw [hderiv.deriv_eq, (HasDerivAt.fun_div hnum hden (by positivity)).deriv]
  have hsq := Real.sq_sqrt ht.le
  field_simp
  rw [hsq]
  ring

/-- The second derivative at `0` of the square root of a quadratic polynomial
`a + b * s + c * s ^ 2` with `0 < a` is `(4 * a * c - b ^ 2) / (4 * a * √a)`. -/
theorem deriv_deriv_sqrt_quadratic_zero {a b c : ℝ} (ha : 0 < a) :
    deriv (deriv fun s ↦ √(a + b * s + c * s ^ 2)) 0 = (4 * a * c - b ^ 2) / (4 * a * √a) := by
  simpa using deriv_deriv_sqrt_quadratic (b := b) (c := c) (t := 0) (by simpa using ha)

end TauCeti
