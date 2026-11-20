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
that if `‖f a‖` tends to `‖y‖` and `RCLike.re ⟪y, f a⟫_𝕜` tends to `‖y‖ ^ 2` along a filter `l`
(in particular, if `⟪y, f a⟫_𝕜` tends to `⟪y, y⟫_𝕜`), then `f a` tends to `y` in norm. Neither
completeness nor definiteness of the seminorm on `E` is needed.

Specializing to eventual norm equality `‖f a‖ = ‖y‖` upgrades weak operator convergence to strong
operator convergence on families of isometric or unitary operators.

## Main results

* `TauCeti.tendsto_of_tendsto_re_inner_of_tendsto_norm`: norm convergence from convergence of norms
  and convergence of `RCLike.re ⟪y, f a⟫_𝕜` to `‖y‖ ^ 2`.
* `TauCeti.tendsto_of_tendsto_inner_of_tendsto_norm`: norm convergence from convergence of norms
  and inner-product convergence against the limit.
* `TauCeti.tendsto_of_tendsto_inner_of_norm_eq`: specialization to eventual norm equality.
-/

public section

open Filter Topology
open scoped InnerProductSpace

namespace TauCeti

/-- In a real or complex seminormed inner product space, if `‖f a‖` tends to `‖y‖` and
`RCLike.re ⟪y, f a⟫_𝕜` tends to `‖y‖ ^ 2` along `l`, then `f a` tends to `y` in norm. -/
theorem tendsto_of_tendsto_re_inner_of_tendsto_norm {𝕜 E α : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] {l : Filter α} {f : α → E} {y : E}
    (hnorm : Tendsto (fun a => ‖f a‖) l (𝓝 ‖y‖))
    (hinner : Tendsto (fun a => RCLike.re ⟪y, f a⟫_𝕜) l (𝓝 (‖y‖ ^ 2))) :
    Tendsto f l (𝓝 y) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun a => ‖f a - y‖ ^ 2) l (𝓝 0) := by
    have hre : Tendsto (fun a => RCLike.re ⟪f a, y⟫_𝕜) l (𝓝 (‖y‖ ^ 2)) :=
      hinner.congr fun a => by rw [← inner_conj_symm (f a) y, RCLike.conj_re]
    have hsub : Tendsto (fun a => ‖f a‖ ^ 2 - 2 * RCLike.re ⟪f a, y⟫_𝕜 + ‖y‖ ^ 2) l
        (𝓝 (‖y‖ ^ 2 - 2 * ‖y‖ ^ 2 + ‖y‖ ^ 2)) :=
      ((hnorm.pow 2).sub (hre.const_mul 2)).add tendsto_const_nhds
    have hzero : ‖y‖ ^ 2 - 2 * ‖y‖ ^ 2 + ‖y‖ ^ 2 = 0 := by ring
    rw [hzero] at hsub
    exact hsub.congr fun a => by rw [_root_.norm_sub_sq (𝕜 := 𝕜)]
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at hsqrt
  exact hsqrt.congr fun a => Real.sqrt_sq (norm_nonneg _)

/-- In a real or complex seminormed inner product space, if `‖f a‖` tends to `‖y‖` and `⟪y, f a⟫_𝕜`
tends to `⟪y, y⟫_𝕜` along `l`, then `f a` tends to `y` in norm. -/
theorem tendsto_of_tendsto_inner_of_tendsto_norm {𝕜 E α : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] {l : Filter α} {f : α → E} {y : E}
    (hnorm : Tendsto (fun a => ‖f a‖) l (𝓝 ‖y‖))
    (hinner : Tendsto (fun a => ⟪y, f a⟫_𝕜) l (𝓝 ⟪y, y⟫_𝕜)) :
    Tendsto f l (𝓝 y) :=
  tendsto_of_tendsto_re_inner_of_tendsto_norm hnorm <| by
    have h1 : Tendsto (fun a => RCLike.re ⟪y, f a⟫_𝕜) l (𝓝 (RCLike.re ⟪y, y⟫_𝕜)) :=
      (RCLike.continuous_re.tendsto _).comp hinner
    rwa [inner_self_eq_norm_sq] at h1

/-- In a real or complex seminormed inner product space, if `‖f a‖ = ‖y‖` eventually along `l` and
`⟪y, f a⟫_𝕜` tends to `⟪y, y⟫_𝕜`, then `f a` tends to `y` in norm. -/
theorem tendsto_of_tendsto_inner_of_norm_eq {𝕜 E α : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] {l : Filter α} {f : α → E} {y : E}
    (hnorm : ∀ᶠ a in l, ‖f a‖ = ‖y‖)
    (hinner : Tendsto (fun a => ⟪y, f a⟫_𝕜) l (𝓝 ⟪y, y⟫_𝕜)) :
    Tendsto f l (𝓝 y) :=
  tendsto_of_tendsto_inner_of_tendsto_norm ((tendsto_congr' hnorm).2 tendsto_const_nhds) hinner

end TauCeti
