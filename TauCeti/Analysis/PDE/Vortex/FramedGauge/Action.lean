/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Regularity
import TauCeti.Analysis.PDE.Vortex.Multiplier

/-!
# The Sobolev gauge group acts on the affine field space

For an integer `k ≥ 2`, the framed degree-`m` plane vortex fields form the affine space
`A_m^k = x_m + H^k` (`TauCeti.Vortex.framedFieldSpace`), and its gauge group is the Sobolev
framed gauge group `G_(k+1) = {u = 1 + h : h ∈ H^(k+1), |u| = 1}`
(`TauCeti.Vortex.sobolevGaugeGroup`). This file shows that the charge-one action
`(a, α) ↦ (a - u⁻¹ du, u α)` (`TauCeti.Vortex.gaugeTransform`) of `G_(k+1)` preserves `A_m^k`
(`TauCeti.Vortex.gaugeTransform_mem_framedFieldSpace`), so that it is an action of the group
`G_(k+1)` on `A_m^k`.

Write `x = x_m + y` with `y ∈ H^k`, and `u = 1 + h`.

* Every `u ∈ G_(k+1)` is `C¹` (`TauCeti.Vortex.contDiff_of_mem_sobolevGaugeGroup`), and the
  connection increment `Im (u⁻¹ du)` has coefficients in `H^k`
  (`TauCeti.Vortex.gaugeForm_apply_mem_realSobolevFunctions`), so the connection stays in
  `a_m + H^k`.
* The section becomes `u α = α_m + y_α + h α`, and `h α` lies in `H^k`: multiplication by a
  coordinate of a field of `A_m^k`, a smooth reference coordinate with bounded derivatives plus an
  `H^k` tail, preserves `H^k`, since `H^k(ℂ)` is an algebra
  (`TauCeti.Vortex.mul_mem_realSobolevFunctions_of_mem_framedFieldSpace`).

Together with the converse `TauCeti.Vortex.mem_sobolevGaugeGroup_of_mem_framedFieldSpace`, this
characterizes `G_(k+1)` among `C²` gauges: a `C²` gauge maps one field of `A_m^k` into `A_m^k`
exactly when it lies in `G_(k+1)`
(`TauCeti.Vortex.gaugeTransform_mem_framedFieldSpace_iff`). Since the elements of `G_(k+1)` are
differentiable, the composition law `gaugeTransform_mul` applies to them, and the action is a
`MulAction` of `G_(k+1)` on the points of `A_m^k`, given by `gaugeTransform`
(`TauCeti.Vortex.coe_sobolevGaugeGroup_smul`).

These are membership statements: the Banach topology of `G_(k+1)` and the continuity and
smoothness of the action are not treated here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex TemperedDistribution

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)} {u : ℂ → Circle}

/-- **The Sobolev gauge group preserves the affine field space.** For an integer `k ≥ 2`, every
`u ∈ G_(k+1)` carries each field of `A_m^k` to a field of `A_m^k`. -/
theorem gaugeTransform_mem_framedFieldSpace (hk : 1 < k)
    (hu : u ∈ sobolevGaugeGroup (s := k + 1) (by norm_cast; omega))
    (hx : x ∈ framedFieldSpace f m k) : gaugeTransform u x ∈ framedFieldSpace f m k := by
  have hk' : (1 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨-, hu₁, hu₂⟩ := (mem_sobolevGaugeGroup _ u).1 hu
  have hmono := realSobolevFunctions_mono (E := ℂ) (p := 2) (by norm_num) (by norm_num)
    (lt_add_one (k : ℝ)).le
  have hω := gaugeForm_apply_mem_realSobolevFunctions hk' hu
  have hy := mem_sobolevFields.1 (mem_framedFieldSpace.1 hx)
  have hmul (i : Fin 4) {g : ℂ → ℝ} (hg : g ∈ realSobolevFunctions ℂ (k + 1) 2) :=
    mul_mem_realSobolevFunctions_of_mem_framedFieldSpace hk hx i (hmono hg)
  refine mem_framedFieldSpace.2 (mem_sobolevFields.2 fun i ↦ ?_)
  -- Connection coordinates `y_j - ω(e_j)`; section coordinates
  -- `(Re u - 1) x₂ + y₂ - Im u x₃` and `Im u x₂ + (Re u - 1) x₃ + y₃`.
  fin_cases i
  · convert sub_mem (hy 0) (hω 1) using 1
    ext z
    simp [gaugeTransform_apply]
    ring
  · convert sub_mem (hy 1) (hω I) using 1
    ext z
    simp [gaugeTransform_apply]
    ring
  · convert add_mem (add_mem (hmul 2 hu₁) (hy 2)) (neg_mem (hmul 3 hu₂)) using 1
    ext z
    simp [gaugeTransform_apply]
    ring
  · convert add_mem (add_mem (hmul 2 hu₂) (hmul 3 hu₁)) (hy 3) using 1
    ext z
    simp [gaugeTransform_apply]
    ring

/-- **The Sobolev gauges are the gauges of the affine field space.** For an integer `k ≥ 2`, a
`C²` gauge `u` carries a field `x` of `A_m^k` into `A_m^k` exactly when `u ∈ G_(k+1)`. -/
theorem gaugeTransform_mem_framedFieldSpace_iff (hk : 1 < k) (hx : x ∈ framedFieldSpace f m k)
    (hu : ContDiff ℝ 2 fun z ↦ (u z : ℂ)) :
    gaugeTransform u x ∈ framedFieldSpace f m k ↔
      u ∈ sobolevGaugeGroup (s := k + 1) (by norm_cast; omega) :=
  ⟨mem_sobolevGaugeGroup_of_mem_framedFieldSpace hk hx hu,
    fun h ↦ gaugeTransform_mem_framedFieldSpace hk h hx⟩

/-- **The action of `G_(k+1)` on `A_m^k`**, `k ≥ 2`, by `(a, α) ↦ (a - u⁻¹ du, u α)`. -/
instance [Fact (1 < k)] :
    MulAction (sobolevGaugeGroup (s := k + 1) (by have := (Fact.out : 1 < k); norm_cast; omega))
      (framedFieldSpace f m k) where
  smul u x := ⟨gaugeTransform u x, gaugeTransform_mem_framedFieldSpace Fact.out u.2 x.2⟩
  one_smul x := Subtype.ext (gaugeTransform_one x)
  mul_smul u v x := by
    -- Elements of `G_(k+1)`, `k ≥ 2`, are `C¹`, so the composition law applies.
    have hk : ((1 : ℕ) : ℝ) + 1 < k + 1 := by have := (Fact.out : 1 < k); norm_cast; omega
    exact Subtype.ext <| gaugeTransform_mul
      ((contDiff_of_mem_sobolevGaugeGroup hk u.2).differentiable one_ne_zero)
      ((contDiff_of_mem_sobolevGaugeGroup hk v.2).differentiable one_ne_zero) x

/-- The action of `G_(k+1)` on `A_m^k` is the gauge transformation of fields. -/
@[simp]
theorem coe_sobolevGaugeGroup_smul [Fact (1 < k)]
    (u : sobolevGaugeGroup (s := k + 1) (by have := (Fact.out : 1 < k); norm_cast; omega))
    (x : framedFieldSpace f m k) : ((u • x : framedFieldSpace f m k) : ℂ → _) =
      gaugeTransform u x :=
  (rfl)

end TauCeti.Vortex
