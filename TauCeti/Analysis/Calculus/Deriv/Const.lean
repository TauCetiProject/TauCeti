/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Vanishing derivatives of locally constant functions

A function from `ℝ` to a normed space that is constant on `(-∞, a]` and on `[b, ∞)` has vanishing
(total) derivative at every point outside `(a, b)`, with no regularity assumption. Similarly, a
function on `X × 𝕜` that is independent of the last coordinate near a point has zero derivative in
that coordinate there.

## Main results

* `TauCeti.deriv_eq_zero_of_not_mem_Ioo`: a function `ℝ → E` constant on `(-∞, a]` and on `[b, ∞)`
  has zero derivative outside `(a, b)`.
* `TauCeti.deriv_prodMk_eq_zero_of_eventually_eq`: a function on `X × 𝕜` locally independent of
  the last coordinate has zero derivative in that coordinate.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function `ℝ → E` that is constant on `(-∞, a]` and on `[b, ∞)` has vanishing derivative
outside `(a, b)`. This is a statement about Lean's total `deriv`, which is zero wherever the
function is not differentiable; it does not assert that the function is differentiable at the
endpoints `a` and `b`. -/
theorem deriv_eq_zero_of_not_mem_Ioo {μ : ℝ → E} {a b : ℝ} {c : E}
    (hlow : ∀ r ≤ a, μ r = μ a) (hhigh : ∀ r, b ≤ r → μ r = c) :
    ∀ r ∉ Ioo a b, deriv μ r = 0 := by
  intro r hr
  rcases not_and_or.1 (by simpa only [mem_Ioo] using hr) with h | h
  · have hr' : r ≤ a := not_lt.1 h
    exact ((hasDerivWithinAt_const r (Iic a) (μ a)).congr (fun x hx ↦ hlow x hx)
      (hlow r hr')).deriv_eq_zero (uniqueDiffOn_Iic a r hr')
  · have hr' : b ≤ r := not_lt.1 h
    exact ((hasDerivWithinAt_const r (Ici b) c).congr (fun x hx ↦ hhigh x hx)
      (hhigh r hr')).deriv_eq_zero (uniqueDiffOn_Ici b r hr')

/-- A function on `X × 𝕜` independent of the last coordinate near `(x, t₀)` has zero derivative
in that coordinate at `(x, t₀)`. -/
theorem deriv_prodMk_eq_zero_of_eventually_eq {𝕜 F X : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace X] {f : X × 𝕜 → F} {x : X}
    {t₀ : 𝕜} (hf : ∀ᶠ z in 𝓝 (x, t₀), f z = f (z.1, t₀)) : deriv (fun s ↦ f (x, s)) t₀ = 0 := by
  have h : (fun s ↦ f (x, s)) =ᶠ[𝓝 t₀] fun _ ↦ f (x, t₀) :=
    ((continuous_const.prodMk continuous_id).tendsto t₀).eventually hf
  rw [h.deriv_eq, deriv_const]

end TauCeti
