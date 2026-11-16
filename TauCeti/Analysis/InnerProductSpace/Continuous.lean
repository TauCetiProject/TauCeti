/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Norm convergence from inner-product and norm convergence

In a real or complex inner product space `E`, expanding `‖f a - y‖ ^ 2` via `norm_sub_sq` shows
that if `‖f a‖ = ‖y‖` eventually along a filter `l` and `⟪y, f a⟫_𝕜` tends to `⟪y, y⟫_𝕜`, then
`f a` tends to `y` in norm. Completeness of `E` is not needed.

This upgrades weak operator convergence to strong operator convergence on families of isometric or
unitary operators.

## Main results

* `TauCeti.tendsto_of_tendsto_inner_of_norm_eq`: norm convergence from inner-product convergence
  against the limit and eventual norm equality.
-/

public section

open Filter Topology
open scoped InnerProductSpace

namespace TauCeti

/-- In a real or complex inner product space, if `‖f a‖ = ‖y‖` eventually along `l` and `⟪y, f a⟫_𝕜`
tends to `⟪y, y⟫_𝕜`, then `f a` tends to `y` in norm. -/
theorem tendsto_of_tendsto_inner_of_norm_eq {𝕜 E α : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {l : Filter α} {f : α → E} {y : E}
    (hnorm : ∀ᶠ a in l, ‖f a‖ = ‖y‖)
    (hinner : Tendsto (fun a => ⟪y, f a⟫_𝕜) l (𝓝 ⟪y, y⟫_𝕜)) :
    Tendsto f l (𝓝 y) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun a => ‖f a - y‖ ^ 2) l (𝓝 0) := by
    have hre : Tendsto (fun a => RCLike.re ⟪f a, y⟫_𝕜) l (𝓝 (‖y‖ ^ 2)) := by
      have h1 : Tendsto (fun a => RCLike.re ⟪y, f a⟫_𝕜) l (𝓝 (RCLike.re ⟪y, y⟫_𝕜)) :=
        (RCLike.continuous_re.tendsto _).comp hinner
      rw [inner_self_eq_norm_sq] at h1
      exact h1.congr fun a => by rw [← inner_conj_symm (f a) y, RCLike.conj_re]
    have hsub : Tendsto (fun a => 2 * ‖y‖ ^ 2 - 2 * RCLike.re ⟪f a, y⟫_𝕜) l
        (𝓝 (2 * ‖y‖ ^ 2 - 2 * ‖y‖ ^ 2)) :=
      tendsto_const_nhds.sub (hre.const_mul 2)
    rw [sub_self] at hsub
    refine hsub.congr' (hnorm.mono fun a ha => ?_)
    dsimp only
    rw [_root_.norm_sub_sq (𝕜 := 𝕜), ha]
    ring
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at hsqrt
  exact hsqrt.congr fun a => Real.sqrt_sq (norm_nonneg _)

end TauCeti
