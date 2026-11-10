/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Sobolev
import TauCeti.Analysis.PDE.Vortex.FramedGauge.Regularity
import TauCeti.Analysis.PDE.Vortex.Multiplier

/-!
# The action of the Sobolev gauge group on framed vortex fields

For an integer `k ≥ 2`, the Sobolev framed gauge group `G_(k+1)`
(`TauCeti.Vortex.sobolevGaugeGroup`) acts on the affine space `A_m^k` of framed degree-`m` plane
vortex fields (`TauCeti.Vortex.framedFieldSpace`) by the charge-one gauge transformation
`(a, α) ↦ (a - u⁻¹ du, u α)` (`TauCeti.Vortex.gaugeTransform`). This is the group action whose
orbits are the gauge classes of the Sobolev completion of the plane vortex problem.

Write `u = 1 + h` with `h ∈ H^(k+1)`, `x = x_m + y` with `x_m` the reference field and
`y ∈ H^k`. Then

* the connection changes by the logarithmic derivative `Im (u⁻¹ du)`, whose coefficients lie in
  `H^k` (`TauCeti.Vortex.gaugeForm_apply_mem_realSobolevFunctions`);
* the section changes from `α` to `u α = α + h α`, and `h α` lies in `H^k` because `α` is a smooth
  reference coordinate with bounded derivatives plus an `H^k` tail, and `H^k(ℂ)` is an algebra
  (`TauCeti.Vortex.mul_mem_realSobolevFunctions_of_mem_framedFieldSpace`).

The elements of `G_(k+1)` are `C¹` by Sobolev embedding
(`TauCeti.Vortex.contDiff_coe_of_mem_sobolevGaugeGroup`), so `u⁻¹ du` is a classical
derivative and no regularity hypothesis on `u` is needed. Hence `G_(k+1)` preserves `A_m^k`
(`TauCeti.Vortex.gaugeTransform_mem_framedFieldSpace`). Conversely, a `C²` gauge carrying one field
of `A_m^k` into `A_m^k` lies in `G_(k+1)`
(`TauCeti.Vortex.mem_sobolevGaugeGroup_of_mem_framedFieldSpace`), so `G_(k+1)` is exactly the set of
`C²` gauges preserving `A_m^k` (`TauCeti.Vortex.gaugeTransform_mem_framedFieldSpace_iff`).

The resulting action of `G_(k+1)` on `A_m^k` is a `MulAction`, given under a `Fact (1 < k)`
instance, and it is free: an element fixing some field is the identity
(`TauCeti.Vortex.eq_one_of_gaugeTransform_eq_self`). No topology on `G_(k+1)`, continuity of the
action or slice for it is constructed here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter TemperedDistribution

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ} {x : ℂ → EuclideanSpace ℝ (Fin 4)} {u : ℂ → Circle}

/-- For `k ≥ 2` the elements of `G_(k+1)` are `C¹`. -/
private theorem contDiff_one_coe_of_mem_sobolevGaugeGroup (hk : 1 < k)
    (hu : u ∈ sobolevGaugeGroup (s := k + 1) (by norm_cast; omega)) :
    ContDiff ℝ 1 fun z ↦ (u z : ℂ) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  exact contDiff_coe_of_mem_sobolevGaugeGroup hu (by push_cast; linarith)

/-- **`G_(k+1)` preserves `A_m^k`.** For an integer `k ≥ 2`, the gauge transformation
`(a, α) ↦ (a - u⁻¹ du, u α)` by an element `u` of the Sobolev gauge group `G_(k+1)` maps the
affine space `A_m^k` of framed degree-`m` vortex fields to itself. -/
theorem gaugeTransform_mem_framedFieldSpace (hk : 1 < k)
    (hu : u ∈ sobolevGaugeGroup (s := k + 1) (by norm_cast; omega))
    (hx : x ∈ framedFieldSpace f m k) : gaugeTransform u x ∈ framedFieldSpace f m k := by
  have hk' : (1 : ℝ) < k := by exact_mod_cast hk
  have hC1 := contDiff_one_coe_of_mem_sobolevGaugeGroup hk hu
  obtain ⟨-, hre, him⟩ := (mem_sobolevGaugeGroup _ u).1 hu
  have hmono := realSobolevFunctions_mono (E := ℂ) (p := 2) (by norm_num) (by norm_num)
    (lt_add_one (k : ℝ)).le
  have hω (v : ℂ) := gaugeForm_apply_mem_realSobolevFunctions hk' hu hC1 v
  have hy := mem_sobolevFields.1 (mem_framedFieldSpace.1 hx)
  have hmul (i : Fin 4) {g : ℂ → ℝ} (hg : g ∈ realSobolevFunctions ℂ (k + 1) 2) :=
    mul_mem_realSobolevFunctions_of_mem_framedFieldSpace hk hx i (hmono hg)
  -- Coordinatewise: the connection gains `-Im (u⁻¹ du)`, and with `u = (1 + h₁) + i h₂` the
  -- section gains `(h₁ x₂ - h₂ x₃, h₂ x₂ + h₁ x₃)`.
  refine mem_framedFieldSpace.2 (mem_sobolevFields.2 fun i ↦ ?_)
  fin_cases i
  · convert sub_mem (hy 0) (hω 1) using 1
    ext z
    simp [gaugeTransform_apply]
    ring
  · convert sub_mem (hy 1) (hω I) using 1
    ext z
    simp [gaugeTransform_apply]
    ring
  · convert add_mem (sub_mem (hmul 2 hre) (hmul 3 him)) (hy 2) using 1
    ext z
    simp [gaugeTransform_apply]
    ring
  · convert add_mem (add_mem (hmul 2 him) (hmul 3 hre)) (hy 3) using 1
    ext z
    simp [gaugeTransform_apply]
    ring

/-- **`G_(k+1)` is the stabilizer of `A_m^k` among `C²` gauges.** For an integer `k ≥ 2` and a
field `x` of `A_m^k`, a `C²` gauge `u` carries `x` into `A_m^k` exactly when `u ∈ G_(k+1)`. -/
theorem gaugeTransform_mem_framedFieldSpace_iff (hk : 1 < k) (hx : x ∈ framedFieldSpace f m k)
    (hu : ContDiff ℝ 2 fun z ↦ (u z : ℂ)) :
    gaugeTransform u x ∈ framedFieldSpace f m k ↔
      u ∈ sobolevGaugeGroup (s := k + 1) (by norm_cast; omega) :=
  ⟨mem_sobolevGaugeGroup_of_mem_framedFieldSpace hk hx hu,
    fun h ↦ gaugeTransform_mem_framedFieldSpace hk h hx⟩

/-- Gauge transformations by elements of `G_(k+1)`, `k ≥ 2`, compose by multiplication of the
gauges. -/
theorem gaugeTransform_mul_of_mem_sobolevGaugeGroup (hk : 1 < k) {v : ℂ → Circle}
    (hu : u ∈ sobolevGaugeGroup (s := k + 1) (by norm_cast; omega))
    (hv : v ∈ sobolevGaugeGroup (s := k + 1) (by norm_cast; omega))
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    gaugeTransform (u * v) x = gaugeTransform u (gaugeTransform v x) :=
  gaugeTransform_mul ((contDiff_one_coe_of_mem_sobolevGaugeGroup hk hu).differentiable one_ne_zero)
    ((contDiff_one_coe_of_mem_sobolevGaugeGroup hk hv).differentiable one_ne_zero) x

/-- **The action of `G_(k+1)` on `A_m^k`**, for an integer `k ≥ 2`, by the charge-one gauge
transformation `(a, α) ↦ (a - u⁻¹ du, u α)`. -/
instance [hk : Fact (1 < k)] :
    MulAction (sobolevGaugeGroup (s := k + 1) (by have := hk.out; norm_cast; omega))
      (framedFieldSpace f m k) where
  smul u x := ⟨gaugeTransform u.val x, gaugeTransform_mem_framedFieldSpace hk.out u.property x.2⟩
  one_smul x := Subtype.ext (gaugeTransform_one x.1)
  mul_smul u v x :=
    Subtype.ext (gaugeTransform_mul_of_mem_sobolevGaugeGroup hk.out u.property v.property x.1)

/-- The action of `G_(k+1)` on `A_m^k` is the charge-one gauge transformation. -/
@[simp]
theorem coe_sobolevGaugeGroup_smul [hk : Fact (1 < k)]
    (u : sobolevGaugeGroup (s := k + 1) (by have := hk.out; norm_cast; omega))
    (x : framedFieldSpace f m k) :
    ((u • x : framedFieldSpace f m k) : ℂ → EuclideanSpace ℝ (Fin 4)) = gaugeTransform u.val x :=
  (rfl)

/-- **The action of `G_(k+1)` on `A_m^k` is free**: an element of `G_(k+1)` fixing one field is the
identity. -/
instance [hk : Fact (1 < k)] :
    IsCancelSMul (sobolevGaugeGroup (s := k + 1) (by have := hk.out; norm_cast; omega))
      (framedFieldSpace f m k) := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro u x hux
  refine Subtype.ext (eq_one_of_gaugeTransform_eq_self (x := x.1)
    ((contDiff_one_coe_of_mem_sobolevGaugeGroup hk.out u.property).differentiable one_ne_zero)
    (tendsto_cocompact_of_mem_sobolevGaugeGroup u.property) ?_)
  simpa only [coe_sobolevGaugeGroup_smul] using congrArg Subtype.val hux

end TauCeti.Vortex
