/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.PowerSeries
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.Series

/-!
# The exponential on `H^s`, `s > n / 2`, as a smooth map

Let `E` be a finite-dimensional real inner product space of dimension `n` and `s > n / 2`, so that
the Bessel-potential space `H^s(E)` is an algebra under pointwise multiplication
(`BesselPotentialSpace.mulCLM`). For `u ∈ H^s(E)` the function `exp u - 1` lies in `H^s(E)`
(`TemperedDistribution.exists_memSobolev_ae_eq_exp_sub_one`); this file bundles it as a map
`BesselPotentialSpace.expSubOne : H^s(E) → H^s(E)` and shows that it is smooth. Its derivative at
`u` is multiplication by `exp u`:

`D (exp · - 1)(u) v = v + (exp u - 1) v`

(`BesselPotentialSpace.hasFDerivAt_expSubOne`). The derivative is a continuous affine function of
the value `exp u - 1`, so the map is `C^∞`, indeed `C^∞` over `ℂ`
(`BesselPotentialSpace.contDiff_expSubOne`).

The two inputs are the addition law
`exp (u + v) - 1 = (exp u - 1) + (exp v - 1) + (exp u - 1)(exp v - 1)`
(`BesselPotentialSpace.expSubOne_add`), and the quadratic remainder estimate
`‖(exp v - 1) - v‖_{H^s} ≤ C ‖v‖_{H^s} ^ 2` for `‖v‖_{H^s} ≤ 1`
(`BesselPotentialSpace.exists_norm_expSubOne_sub_le`), which is the power-series action
`TemperedDistribution.exists_hasSum_mul_pow` applied to the series of `exp z - 1 - z`
(`Complex.hasSum_expRemainderCoeff`).

Nonlinear equations on the Sobolev scale, such as the reduced vortex equation
`Δw = (h exp (2w) - 1) / 8 + g`, contain such exponentials, and this is what makes them smooth
maps between Bessel-potential spaces, the setting of implicit-function-theorem arguments (which
also need the invertibility of the derivative, not proved here).

## Main declarations

* `BesselPotentialSpace.expSubOne`: the map `u ↦ exp u - 1` on `H^s(E)`.
* `BesselPotentialSpace.coeFn_toLp_inclusion_expSubOne`: its `L²` function is `exp u - 1`.
* `BesselPotentialSpace.expSubOne_add`: the addition law.
* `BesselPotentialSpace.hasFDerivAt_expSubOne`: the derivative `v ↦ v + (exp u - 1) v`.
* `BesselPotentialSpace.contDiff_expSubOne`: `expSubOne` is `C^∞` over `ℂ`.

## References

* M. E. Taylor, *Partial Differential Equations III: Nonlinear Equations*, 2nd ed., Applied
  Mathematical Sciences 117, Springer, 2011, Chapter 13, Section 3.
-/

public section

noncomputable section

open MeasureTheory Module Filter Asymptotics TemperedDistribution
open scoped Nat Topology ContDiff BesselPotentialSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

namespace BesselPotentialSpace

open TauCeti (nonneg_of_finrank_lt_two_mul)

variable {s : ℝ}

/-- **The exponential on `H^s(E)`, `s > dim E / 2`.** The element `exp u - 1` of `H^s(E)` for
`u ∈ H^s(E)`: its `L²` function is `x ↦ exp (u x) - 1`
(`BesselPotentialSpace.coeFn_toLp_inclusion_expSubOne`). -/
def expSubOne (hs : finrank ℝ E < 2 * s) (u : H^{s}(E)) : H^{s}(E) :=
  (exists_memSobolev_ae_eq_exp_sub_one hs
    (memSobolev_inclusionLp (nonneg_of_finrank_lt_two_mul hs)
      u)).choose_spec.2.toBesselPotentialSpace

/-- The `L²` function of `expSubOne hs u` is `x ↦ exp (u x) - 1`, for the `L²` function `u x` of
`u`. -/
theorem coeFn_toLp_inclusion_expSubOne (hs : finrank ℝ E < 2 * s) (h : 0 ≤ s) (u : H^{s}(E)) :
    ⇑(inclusion h (expSubOne hs u)).toLp =ᵐ[volume]
      fun x ↦ Complex.exp ((inclusion h u).toLp x) - 1 := by
  have hspec := (exists_memSobolev_ae_eq_exp_sub_one hs
    (memSobolev_inclusionLp (nonneg_of_finrank_lt_two_mul hs) u)).choose_spec
  rw [expSubOne, toLp_inclusion_toBesselPotentialSpace h _ rfl, toLp_inclusion]
  exact hspec.1

/-- An element of `H^s(E)` whose `L²` function is almost everywhere `exp u - 1` is
`expSubOne hs u`. -/
theorem eq_expSubOne_of_ae (hs : finrank ℝ E < 2 * s) (h : 0 ≤ s) {u w : H^{s}(E)}
    (hw : ⇑(inclusion h w).toLp =ᵐ[volume] fun x ↦ Complex.exp ((inclusion h u).toLp x) - 1) :
    w = expSubOne hs u :=
  toLp_inclusion_injective h <| Lp.ext <| hw.trans (coeFn_toLp_inclusion_expSubOne hs h u).symm

@[simp]
theorem expSubOne_zero (hs : finrank ℝ E < 2 * s) : expSubOne hs (0 : H^{s}(E)) = 0 := by
  have h := nonneg_of_finrank_lt_two_mul hs
  refine (eq_expSubOne_of_ae hs h ?_).symm
  have h0 : (inclusion h (0 : H^{s}(E))).toLp = 0 := by rw [map_zero, toLp_zero]
  rw [h0]
  filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure E)] with x hx
  rw [hx, Pi.zero_apply, Complex.exp_zero, sub_self]

/-- **The addition law of `exp - 1` on `H^s(E)`**:
`exp (u + v) - 1 = (exp u - 1) + (exp v - 1) + (exp u - 1)(exp v - 1)`. -/
theorem expSubOne_add (hs : finrank ℝ E < 2 * s) (u v : H^{s}(E)) :
    expSubOne hs (u + v) =
      expSubOne hs u + expSubOne hs v + mulCLM hs (expSubOne hs u) (expSubOne hs v) := by
  have h := nonneg_of_finrank_lt_two_mul hs
  refine (eq_expSubOne_of_ae hs h ?_).symm
  filter_upwards [coeFn_toLp_inclusion_add h (expSubOne hs u + expSubOne hs v)
      (mulCLM hs (expSubOne hs u) (expSubOne hs v)),
    coeFn_toLp_inclusion_add h (expSubOne hs u) (expSubOne hs v),
    coeFn_toLp_inclusion_mulCLM hs h (expSubOne hs u) (expSubOne hs v),
    coeFn_toLp_inclusion_expSubOne hs h u, coeFn_toLp_inclusion_expSubOne hs h v,
    coeFn_toLp_inclusion_add h u v] with x h₁ h₂ h₃ h₄ h₅ h₆
  rw [h₁, Pi.add_apply, h₂, Pi.add_apply, h₃, h₄, h₅, h₆, Pi.add_apply, Complex.exp_add]
  ring

/-- **The quadratic remainder of `exp - 1` on `H^s(E)`.** There is a constant `C` such that
`‖(exp v - 1) - v‖_{H^s} ≤ C ‖v‖_{H^s} ^ 2` for `‖v‖_{H^s} ≤ 1`. -/
theorem exists_norm_expSubOne_sub_le (hs : finrank ℝ E < 2 * s) :
    ∃ C, ∀ v : H^{s}(E), ‖v‖ ≤ 1 → ‖expSubOne hs v - v‖ ≤ C * ‖v‖ ^ 2 := by
  have h := nonneg_of_finrank_lt_two_mul hs
  obtain ⟨C, hC, hser⟩ := exists_hasSum_mul_pow (E := E) hs
  refine ⟨C * Real.exp C, fun v hv ↦ ?_⟩
  set r := ‖v‖
  have hr : 0 ≤ r := norm_nonneg _
  have hu := memSobolev_inclusionLp h v
  have hur : ‖hu.toBesselPotentialSpace‖ = r := by
    rw [toBesselPotentialSpace_memSobolev_inclusionLp]
  obtain ⟨hsum, hle⟩ := Complex.summable_and_tsum_norm_expRemainderCoeff_le (mul_nonneg hC hr)
  obtain ⟨w, hw, hws, hwn⟩ := hser hu (by rwa [hur])
  -- The element of `w` is `(exp v - 1) - v`.
  have hweq : hws.toBesselPotentialSpace = expSubOne hs v - v := by
    refine toLp_inclusion_injective h (Lp.ext ?_)
    -- `toLp_inclusion_injective` is stated for a `fun`, so beta-reduce its applications.
    beta_reduce
    rw [toLp_inclusion_toBesselPotentialSpace h hws rfl]
    filter_upwards [hw, coeFn_toLp_inclusion_sub h (expSubOne hs v) v,
      coeFn_toLp_inclusion_expSubOne hs h v] with x hx h₁ h₂
    rw [h₁, Pi.sub_apply, h₂, toLp_inclusion]
    exact hx.unique (Complex.hasSum_expRemainderCoeff _)
  rw [← hweq]
  calc ‖hws.toBesselPotentialSpace‖
      ≤ r * ∑' n, ‖Complex.expRemainderCoeff n‖ * (C * r) ^ n := by rw [← hur]; exact hwn
    _ ≤ r * ((C * r) * Real.exp (C * r)) := by gcongr
    _ ≤ r * ((C * r) * Real.exp C) := by gcongr; exact mul_le_of_le_one_right hC hv
    _ = C * Real.exp C * r ^ 2 := by ring

/-- **The derivative of `exp - 1` on `H^s(E)`**: at `u`, the derivative of `expSubOne hs` is
multiplication by `exp u`, `v ↦ v + (exp u - 1) v`. -/
theorem hasFDerivAt_expSubOne (hs : finrank ℝ E < 2 * s) (u : H^{s}(E)) :
    HasFDerivAt (expSubOne hs)
      (ContinuousLinearMap.id ℂ H^{s}(E) + mulCLM hs (expSubOne hs u)) u := by
  obtain ⟨C, hC⟩ := exists_norm_expSubOne_sub_le (E := E) hs
  set L : H^{s}(E) →L[ℂ] H^{s}(E) := ContinuousLinearMap.id ℂ H^{s}(E) + mulCLM hs (expSubOne hs u)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  -- The remainder is `(exp v - 1 - v) + (exp u - 1)(exp v - 1 - v)`, which is `O(‖v‖²)`.
  have hrem (v : H^{s}(E)) :
      expSubOne hs (u + v) - expSubOne hs u - L v = L (expSubOne hs v - v) := by
    simp only [L, expSubOne_add, map_sub, FunLike.coe_add, Pi.add_apply,
      ContinuousLinearMap.coe_id', id_eq]
    abel
  simp_rw [hrem]
  refine IsBigO.trans_isLittleO ?_ (isLittleO_norm_pow_id (E' := H^{s}(E)) one_lt_two)
  refine (L.isBigO_comp _ _).trans ?_
  refine IsBigO.of_bound C ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : H^{s}(E)) one_pos] with v hv
  rw [Metric.mem_closedBall, dist_zero_right] at hv
  rw [Real.norm_of_nonneg (by positivity)]
  exact hC v hv

/-- **`exp - 1` is smooth on `H^s(E)`**, `s > dim E / 2`: the map `u ↦ exp u - 1` is `C^∞` over
`ℂ`. -/
theorem contDiff_expSubOne (hs : finrank ℝ E < 2 * s) : ContDiff ℂ ∞ (expSubOne hs) := by
  -- The derivative `id + (exp u - 1) ·` is an affine function of the value, so each order of
  -- differentiability gives the next.
  have hd : Differentiable ℂ (expSubOne (E := E) hs) :=
    fun u ↦ (hasFDerivAt_expSubOne hs u).differentiableAt
  refine contDiff_infty.2 fun n ↦ ?_
  induction n with
  | zero => exact contDiff_zero.2 hd.continuous
  | succ n ih =>
    exact contDiff_succ_iff_hasFDerivAt.2 ⟨_, contDiff_const.add ((mulCLM hs).contDiff.comp ih),
      hasFDerivAt_expSubOne hs⟩

end BesselPotentialSpace
