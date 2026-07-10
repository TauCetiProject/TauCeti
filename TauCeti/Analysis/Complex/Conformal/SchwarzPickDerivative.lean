/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Set.Function
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import TauCeti.Analysis.Complex.Conformal.Moebius

/-!
# The infinitesimal Schwarz--Pick inequality

This file proves the differential (infinitesimal) form of the Schwarz--Pick lemma for
holomorphic self-maps of the complex unit disc: if `f` is holomorphic on `ball 0 1` and maps
it into itself, then at every point `z` of the disc
`‖deriv f z‖ / (1 - ‖f z‖ ^ 2) ≤ 1 / (1 - ‖z‖ ^ 2)`, i.e. `f` contracts the Poincaré
(hyperbolic) metric `|dz| / (1 - |z| ^ 2)`.

The proof conjugates `f` by the disc automorphisms `source` (sending `0 ↦ z`) and `target`
(sending `f z ↦ 0`), so that `g = target ∘ f ∘ source` is a self-map of the disc fixing `0`.
Mathlib's Schwarz lemma bounds `‖deriv g 0‖ ≤ 1`, and the chain rule evaluates `deriv g 0` in
terms of `deriv f z` together with the derivatives of the two Moebius factors
(`hasDerivAt_moebiusFactor`), which unwinds to the stated contraction.

This advances the conformal-mapping roadmap's **L2 Schwarz--Pick** target
(`TauCetiRoadmap/ConformalMapping/README.md`, the L2 hyperbolic/Poincaré-metric contraction),
complementing Tau Ceti's finite Schwarz--Pick estimate `pseudoHyperbolicExpr_map_le`.  It
reuses Mathlib's Schwarz lemma (`Complex.norm_deriv_le_one_of_mapsTo_ball`) and Tau Ceti's
unit-disc Moebius API.  As with the rest of the L0--L3 conformal-mapping material, it is
coordinated with the upstream Mathlib RMT effort leanprover-community/mathlib4#33505 and
should be refactored to upstream API if that work lands a human-curated Schwarz--Pick theorem.
-/

public section

namespace TauCeti

open Complex Metric Set
open scoped ComplexConjugate

/-- The complex derivative of the Moebius factor `ξ ↦ (ξ - a) / (1 - conj a * ξ)` at a point
`p` where the denominator is nonzero.  The value simplifies to `1 - ‖z‖ ^ 2` at `p = 0`
(with `a = -z`) and to `1 / (1 - ‖a‖ ^ 2)` at `p = a`. -/
private lemma hasDerivAt_moebiusFactor (a p : ℂ)
    (hp : 1 - (starRingEnd ℂ) a * p ≠ 0) :
    HasDerivAt (fun ξ : ℂ => (ξ - a) / (1 - (starRingEnd ℂ) a * ξ))
      ((1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * p) ^ 2) p := by
  have hn : HasDerivAt (fun ξ : ℂ => ξ - a) 1 p := (hasDerivAt_id p).sub_const a
  have hd : HasDerivAt (fun ξ : ℂ => 1 - (starRingEnd ℂ) a * ξ) (-(starRingEnd ℂ) a) p := by
    simpa using ((hasDerivAt_id p).const_mul ((starRingEnd ℂ) a)).const_sub 1
  have hq := hn.div hd hp
  have hval : (1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * p) ^ 2
      = (1 * (1 - (starRingEnd ℂ) a * p) - (p - a) * -(starRingEnd ℂ) a)
        / (1 - (starRingEnd ℂ) a * p) ^ 2 := by
    congr 1
    ring
  rw [hval]
  exact hq

/-- **The infinitesimal Schwarz--Pick inequality.** A holomorphic self-map `f` of the open
unit disc contracts the Poincaré metric: at every point `z` of the disc,
`‖deriv f z‖ / (1 - ‖f z‖ ^ 2) ≤ 1 / (1 - ‖z‖ ^ 2)`. -/
theorem norm_deriv_div_one_sub_norm_sq_le {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖deriv f z‖ / (1 - ‖f z‖ ^ 2) ≤ 1 / (1 - ‖z‖ ^ 2) := by
  have hz1 : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  have hfz_mem : f z ∈ ball (0 : ℂ) 1 := hmaps hz
  have hfz1 : ‖f z‖ < 1 := by simpa [mem_ball_zero_iff] using hfz_mem
  have hden_z : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hden_fz : (0 : ℝ) < 1 - ‖f z‖ ^ 2 := by nlinarith [norm_nonneg (f z)]
  -- The disc automorphisms conjugating `f` so that the conjugate fixes `0`.
  let source : ℂ → ℂ := fun ξ => (ξ - (-z)) / (1 - (starRingEnd ℂ) (-z) * ξ)
  let target : ℂ → ℂ := fun η => (η - f z) / (1 - (starRingEnd ℂ) (f z) * η)
  let g : ℂ → ℂ := target ∘ f ∘ source
  -- `source` and `target` map the disc into itself and are holomorphic there.
  have hsource_maps : MapsTo source (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    simpa [source] using mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one
      (a := -z) (by simpa using hz1)
  have htarget_maps : MapsTo target (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    simpa [target] using mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one (a := f z) hfz1
  have hsource_diff : DifferentiableOn ℂ source (ball (0 : ℂ) 1) := by
    simpa [source] using differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one
      (a := -z) (by simpa using hz1)
  have htarget_diff : DifferentiableOn ℂ target (ball (0 : ℂ) 1) := by
    simpa [target] using differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one (a := f z) hfz1
  have hg_maps : MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    fun ξ hξ => htarget_maps (hmaps (hsource_maps hξ))
  have hg_diff : DifferentiableOn ℂ g (ball (0 : ℂ) 1) :=
    htarget_diff.comp (hf.comp hsource_diff hsource_maps) (hmaps.comp hsource_maps)
  -- The conjugate `g` fixes the origin.
  have hsource_zero : source 0 = z := by
    change (0 - (-z)) / (1 - (starRingEnd ℂ) (-z) * 0) = z
    simp
  have hg_zero : g 0 = 0 := by
    change target (f (source 0)) = 0
    rw [hsource_zero]
    change (f z - f z) / (1 - (starRingEnd ℂ) (f z) * f z) = 0
    rw [sub_self, zero_div]
  -- Schwarz's lemma at `0` for `g`.
  have hg_maps_closed : MapsTo g (ball (0 : ℂ) 1) (closedBall (0 : ℂ) 1) :=
    fun ξ hξ => ball_subset_closedBall (hg_maps hξ)
  have hschwarz : ‖deriv g 0‖ ≤ 1 := by
    have hmaps' : MapsTo g (ball (0 : ℂ) 1) (closedBall (g 0) 1) := by
      rw [hg_zero]; exact hg_maps_closed
    exact Complex.norm_deriv_le_one_of_mapsTo_ball hg_diff hmaps' (by norm_num)
  -- The chain rule for `deriv g 0`.
  have hp_inner : (1 : ℂ) - (starRingEnd ℂ) (-z) * 0 ≠ 0 := by simp
  have hp_outer : (1 : ℂ) - (starRingEnd ℂ) (f z) * f z ≠ 0 :=
    one_sub_conj_mul_ne_zero_of_norm_lt_one hfz1 hfz1
  have hd_inner : HasDerivAt source (1 - (starRingEnd ℂ) z * z) 0 := by
    have h := hasDerivAt_moebiusFactor (-z) 0 hp_inner
    have hval : (1 - (starRingEnd ℂ) (-z) * (-z)) / (1 - (starRingEnd ℂ) (-z) * 0) ^ 2
        = 1 - (starRingEnd ℂ) z * z := by simp [map_neg]
    rw [hval] at h
    exact h
  have hd_outer : HasDerivAt target (1 / (1 - (starRingEnd ℂ) (f z) * f z)) (f z) := by
    have h := hasDerivAt_moebiusFactor (f z) (f z) hp_outer
    have hval : (1 - (starRingEnd ℂ) (f z) * f z) / (1 - (starRingEnd ℂ) (f z) * f z) ^ 2
        = 1 / (1 - (starRingEnd ℂ) (f z) * f z) := by
      rw [sq, ← div_div, div_self hp_outer]
    rw [hval] at h
    exact h
  have hf_at : HasDerivAt f (deriv f z) z :=
    (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hf_at' : HasDerivAt f (deriv f z) (source 0) := by rw [hsource_zero]; exact hf_at
  have hcomp1 : HasDerivAt (f ∘ source) (deriv f z * (1 - (starRingEnd ℂ) z * z)) 0 :=
    hf_at'.comp (0 : ℂ) hd_inner
  have hd_outer' : HasDerivAt target (1 / (1 - (starRingEnd ℂ) (f z) * f z)) ((f ∘ source) 0) := by
    rw [Function.comp_apply, hsource_zero]; exact hd_outer
  have hcompg : HasDerivAt g
      ((1 / (1 - (starRingEnd ℂ) (f z) * f z)) * (deriv f z * (1 - (starRingEnd ℂ) z * z))) 0 :=
    hd_outer'.comp (0 : ℂ) hcomp1
  have hderiv_g : deriv g 0
      = (1 / (1 - (starRingEnd ℂ) (f z) * f z)) * (deriv f z * (1 - (starRingEnd ℂ) z * z)) :=
    hcompg.deriv
  -- The norms of the two Moebius derivative factors.
  have hnorm : ∀ w : ℂ, ‖w‖ < 1 → ‖(1 : ℂ) - (starRingEnd ℂ) w * w‖ = 1 - ‖w‖ ^ 2 := by
    intro w hw
    have hconj : (starRingEnd ℂ) w * w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hconj, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith [norm_nonneg w])]
  have hnorm_z := hnorm z hz1
  have hnorm_fz := hnorm (f z) hfz1
  -- Assemble the norm of `deriv g 0` and conclude via Schwarz.
  have hnorm_dg : ‖deriv g 0‖ = ‖deriv f z‖ * (1 - ‖z‖ ^ 2) / (1 - ‖f z‖ ^ 2) := by
    rw [hderiv_g, norm_mul, norm_mul, norm_div, norm_one, hnorm_z, hnorm_fz]
    ring
  have hkey : ‖deriv f z‖ * (1 - ‖z‖ ^ 2) / (1 - ‖f z‖ ^ 2) ≤ 1 := hnorm_dg ▸ hschwarz
  rw [div_le_one hden_fz] at hkey
  rw [div_le_div_iff₀ hden_fz hden_z, one_mul]
  exact hkey

end TauCeti
