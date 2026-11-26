/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic

/-!
# Derivatives of functions that are odd or even near a point

The derivative of a function that is odd near `x` takes the same value at `-x` and `x`, and the
derivative of a function that is even near `x` takes opposite values there. Consequently the
second derivative at `0` of a function that is odd near `0` vanishes, provided the codomain has no
additive torsion. Along a curve that is odd near `0`, the third derivative of a composition at `0`
reduces to the third derivative of the outer map in the direction of the velocity, once the first
derivative of the outer map has been projected away. A family of maps that is odd near `(t, 0)`
vanishes at `0` for all parameters near `t`.

## Main results

* `TauCeti.deriv_neg_eq_of_eventually_odd`: `f'(-x) = f'(x)` for `f` odd near `x`.
* `TauCeti.deriv_neg_eq_neg_of_eventually_even`: `f'(-x) = -f'(x)` for `f` even near `x`.
* `TauCeti.iteratedDeriv_two_eq_zero_of_eventually_odd`: `f''(0) = 0` for `f` odd near `0`.
* `TauCeti.iteratedDeriv_three_comp_of_eventually_odd`: `(L ∘ g ∘ f)'''(0) = L (D³g(0) (v, v, v))`
  for `f` odd near `0` with `f'(0) = v`, when `L` vanishes on the range of `Dg(0)`.
* `TauCeti.eventually_apply_zero_eq_zero_of_eventually_odd`: a family odd near `(t, 0)` vanishes
  at `0` for parameters near `t`.
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : 𝕜 → F}

/-- If `f` is odd near `x`, then `f'(-x) = f'(x)`. -/
theorem deriv_neg_eq_of_eventually_odd {x : 𝕜} (h : ∀ᶠ y in 𝓝 x, f (-y) = -f y) :
    deriv f (-x) = deriv f x := by
  have h' : f =ᶠ[𝓝 x] fun y => -f (-y) := h.mono fun y hy => by beta_reduce; rw [hy, neg_neg]
  rw [h'.deriv_eq, deriv.fun_neg, deriv_comp_neg, neg_neg]

/-- If `f` is even near `x`, then `f'(-x) = -f'(x)`. -/
theorem deriv_neg_eq_neg_of_eventually_even {x : 𝕜} (h : ∀ᶠ y in 𝓝 x, f (-y) = f y) :
    deriv f (-x) = -deriv f x := by
  have h' : f =ᶠ[𝓝 x] fun y => f (-y) := h.mono fun y hy => hy.symm
  rw [h'.deriv_eq, deriv_comp_neg, neg_neg]

/-- The second derivative at `0` of a function that is odd near `0` vanishes. -/
theorem iteratedDeriv_two_eq_zero_of_eventually_odd [IsAddTorsionFree F]
    (h : ∀ᶠ y in 𝓝 0, f (-y) = -f y) : iteratedDeriv 2 f 0 = 0 := by
  have h₁ : ∀ᶠ y in 𝓝 (0 : 𝕜), deriv f (-y) = deriv f y :=
    h.eventually_nhds.mono fun y hy => deriv_neg_eq_of_eventually_odd hy
  have h₂ := deriv_neg_eq_neg_of_eventually_even h₁
  rw [neg_zero] at h₂
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  exact self_eq_neg.1 h₂

/-- **The third derivative along an odd curve.** If `f` is a `C³` curve through `0`, odd near `0`,
with velocity `v`, and `L` vanishes on the range of `Dg(0)`, then the third derivative of
`x ↦ L (g (f x))` at `0` is `L (D³g(0) (v, v, v))`. -/
theorem iteratedDeriv_three_comp_of_eventually_odd {G H : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H] [IsAddTorsionFree F] {g : F → G}
    {L : G →L[𝕜] H} {v : F} (hg : ContDiffAt 𝕜 3 g 0) (hf : ContDiffAt 𝕜 3 f 0) (hf0 : f 0 = 0)
    (hfv : deriv f 0 = v) (h : ∀ᶠ y in 𝓝 0, f (-y) = -f y) (hL : ∀ y, L (fderiv 𝕜 g 0 y) = 0) :
    iteratedDeriv 3 (fun x ↦ L (g (f x))) 0 = L (fderiv 𝕜 (fderiv 𝕜 (fderiv 𝕜 g)) 0 v v v) := by
  -- Faà di Bruno's formula for `(L ∘ g) ∘ f` has four terms. An odd curve has no acceleration
  -- at `0`, which kills the two middle terms, and `L ∘ Dg(0) = 0` kills the last one.
  have hf₂0 : iteratedDeriv 2 f 0 = 0 := iteratedDeriv_two_eq_zero_of_eventually_odd h
  rw [← hf0] at hg
  have hLg : fderiv 𝕜 (L ∘ g) (f 0) = L.comp (fderiv 𝕜 g (f 0)) :=
    (L.hasFDerivAt.comp (f 0) (hg.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have h₀ (M : F [×2]→L[𝕜] H) : M ![0, v] = 0 := M.map_coord_zero 0 (by simp)
  have h₁ (M : F [×2]→L[𝕜] H) : M ![v, 0] = 0 := M.map_coord_zero 1 (by simp)
  have h₃ := iteratedDeriv_vcomp_three (L.contDiff.contDiffAt.comp (f 0) hg) hf
  rw [L.iteratedFDeriv_comp_left hg le_rfl, hLg] at h₃
  simpa [Function.comp_def, hf₂0, hfv, hf0, hL, h₀, h₁, iteratedFDeriv_three_apply] using h₃

/-- A family that is odd near `(t, 0)` vanishes at `0` for all parameters near `t`. -/
theorem eventually_apply_zero_eq_zero_of_eventually_odd {S V W : Type*} [TopologicalSpace S]
    [TopologicalSpace V] [NegZeroClass V] [AddGroup W] [IsAddTorsionFree W] {g : S → V → W}
    {t : S} (h : ∀ᶠ p in 𝓝 (t, (0 : V)), g p.1 (-p.2) = -g p.1 p.2) :
    ∀ᶠ s in 𝓝 t, g s 0 = 0 := by
  filter_upwards [(continuous_id.prodMk continuous_const).continuousAt.eventually h] with s hs
  rw [id, neg_zero] at hs
  exact self_eq_neg.1 hs

end TauCeti
