/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.CircleContinuation.Rotation
public import TauCeti.Geometry.Manifold.Morse.Boundary.Continuation.Basic
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import TauCeti.Algebra.AddCircle
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# The mod-two continuation maps of the circle continuation examples

On the circle `S¹ = ℝ ⧸ 2πℤ`, a path `t ↦ r t` of rotations of `f_r(θ) = δ cos (2 (θ - r))`
(`TauCeti.circleCosTwo δ r`) has the positive parameter field

`W = 2 δ sin (2 (θ - r t)) ∂_θ + t (1 - t²) ∂_t`

on the cylinder `S¹ × ℝ` (`TauCeti.circleCylinderField δ r`), the field
`TauCeti.circleContinuationField δ r` of the universal cover `ℝ × ℝ` read on the cylinder. This
file computes the mod-two continuation map `TauCeti.morseContinuationMap` along `W`, which counts
the trajectories of `W` from `(p, 0)` to `(q, 1)` between critical points of equal index. It is
the step from the trajectory counts of
`TauCeti.Analysis.Calculus.Morse.CircleContinuation.Rotation`, made on the universal cover, to the
continuation map of Morse homology.

**Trajectories on the cylinder.** The time component of a trajectory of `W` through the open slab
`0 < t < 1` is a translate of the base trajectory `q = TauCeti.intervalBaseOrbit 1`, which runs
from `t = 0` to `t = 1`. A continuous lift of its angle to `ℝ`, which exists since `ℝ → S¹` is a
covering map, is then differentiable, with the velocity read in the circle
(`AddCircle.hasDerivAt_of_hasMFDerivAt_coe_comp`). Reparametrized by the time coordinate
`TauCeti.intervalBaseTimeCoordinate`, which inverts `q`, the lift is a solution `Θ` of
`Θ' = circleContinuationSlope δ r t (Θ t)` on `0 < t < 1`, and the trajectory is
`s ↦ ([Θ (q (s + c))], q (s + c))` for a shift `c`
(`TauCeti.exists_eq_of_isMIntegralCurve_circleCylinderField`); conversely every such curve is a
trajectory (`TauCeti.isMIntegralCurve_circleCylinderField`). So a point `x` lies in the
middle-level slice `TauCeti.morseContinuationSlice` from `p` to `q` exactly when some solution `Θ`
has `[Θ (1/2)] = x` and its image in the circle tends to `p` at `t = 0` and to `q` at `t = 1`
(`TauCeti.mem_morseContinuationSlice_circleCylinderField_iff`).

**The continuation map of a small rotation.** Let the path be `r₀` on `(0, a]` and `r₁` on
`[b, 1)`, continuous on `[a, b] ⊆ (0, 1)`, let `D = 2 δ ∫_a^b (t (1 - t²))⁻¹ dt` bound the drift of
the angle across `[a, b]`, and let `n` be an integer with `|r₁ - r₀ - n π| + D < π / 2`. With the
residual rotation `c = r₁ - r₀ - n π`, the trajectories from a source minimum `p` all end at the
target minimum `p + c`, those arriving at a target maximum `q` all start at the source maximum
`q - c`, and each of them is unique and exists. So the coefficient of `q` in the continuation of
`p` is `1` when `q = p + c` and `0` otherwise
(`TauCeti.morseContinuationCoeff_circleCylinderField`), and the continuation map sends each
critical point `p` of `f_{r₀}` to the critical point `p + c` of `f_{r₁}`
(`TauCeti.morseContinuationMap_circleCylinderField_single`).

**The examples.** Let `ρ` be continuous, `0` for `t ≤ 1/3` and `1` for `t ≥ 2/3`, and let `δ > 0`
satisfy `2 δ ∫_{1/6}^{5/6} (t (1 - t²))⁻¹ dt < π / 12`.

* For the half-turn `r = r₀ + π ρ`, from `f_{r₀}` to the same function `f_{r₀ + π}`
  (`TauCeti.circleCosTwo_add_pi`), the continuation map is the identity in the fixed spatial basis
  of critical points (`TauCeti.morseContinuationMap_circleCylinderField_add_pi_eq_id`). It sends
  `p_j(r₀)` to the critical point `p_{j + 1}(r₀ + π)` at the same angle, while tracking along the
  path gives `p_j(r₀ + π)`: in the tracked labels it is the exchange `S` of the two generators, in
  both degrees
  (`TauCeti.morseContinuationMap_single_circleCosTwoMaxCrit_add_pi`,
  `TauCeti.morseContinuationMap_single_circleCosTwoMinCrit_add_pi`).
* For the third-turns `Γ₁ = r₀ + (π / 3) ρ`, and `Γ₂` the same from `r₀ + π / 3`, the continuation
  map is the identity `I` in the tracked labels
  (`TauCeti.morseContinuationMap_single_circleCosTwoMaxCrit_add_pi_div_three`,
  `TauCeti.morseContinuationMap_single_circleCosTwoMinCrit_add_pi_div_three`), but
  for their concatenation `Γ₂ * Γ₁`, run at double speed on `[0, 1/2]` and `[1/2, 1]`, it is `S`
  (`TauCeti.morseContinuationMap_single_circleCosTwoMaxCrit_add_two_mul_pi_div_three`,
  `TauCeti.morseContinuationMap_single_circleCosTwoMinCrit_add_two_mul_pi_div_three`). So
  `Φ_{Γ₁} = Φ_{Γ₂} = I` but `Φ_{Γ₂ * Γ₁} = S`: continuation maps do not compose strictly.

The maps here are the mod-two continuation maps; the integral continuation maps, with their signs,
and the chain homotopy between `I` and `S` are not treated.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1–4.2 (continuation maps).
-/

public section

open AddCircle Filter Real Set Topology
open scoped Manifold

namespace TauCeti

local instance circleContinuationTwoPiPos : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

variable {δ : ℝ} {r : ℝ → ℝ}

/-! ### The parameter field on the cylinder -/

/-- The positive parameter field `2 δ sin (2 (θ - r t)) ∂_θ + t (1 - t²) ∂_t` of the continuation
family `δ cos (2 (θ - r t))` on the cylinder `S¹ × ℝ`, `S¹ = ℝ ⧸ 2πℤ`: the field
`TauCeti.circleContinuationField δ r` of the universal cover, evaluated at any lift of the angle
(`TauCeti.circleCylinderField_coe`). The tangent spaces of the cylinder are read in its charts,
which are local lifts of the angle. -/
noncomputable def circleCylinderField (δ : ℝ) (r : ℝ → ℝ) (z : AddCircle (2 * π) × ℝ) :
    TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) z :=
  circleContinuationField δ r ((equivIco (2 * π) 0 z.1 : ℝ), z.2)

/-- At the class of a lifted angle `θ`, the parameter field on the cylinder is the field
`circleContinuationField δ r` of the universal cover at `(θ, t)`. -/
@[simp]
theorem circleCylinderField_coe (δ : ℝ) (r : ℝ → ℝ) (θ t : ℝ) :
    circleCylinderField δ r ((θ : AddCircle (2 * π)), t) = circleContinuationField δ r (θ, t) := by
  -- The representative of `θ` in `[0, 2π)` differs from `θ` by a multiple of `2π`.
  have hθ : (equivIco (2 * π) 0 (θ : AddCircle (2 * π)) : ℝ) =
      θ - ⌊θ / (2 * π)⌋ * (2 * π) := by
    rw [coe_equivIco_mk_apply, Int.fract, sub_mul, div_mul_cancel₀ _ two_pi_pos.ne']
  rw [circleCylinderField, hθ, circleContinuationField_apply, circleContinuationField_apply,
    show 2 * (θ - ⌊θ / (2 * π)⌋ * (2 * π) - r t) =
      2 * (θ - r t) - ((2 * ⌊θ / (2 * π)⌋ : ℤ) : ℝ) * (2 * π) by push_cast; ring,
    sin_sub_int_mul_two_pi]

/-- The time component of the parameter field on the cylinder is `t (1 - t²)`. -/
@[simp]
theorem circleCylinderField_snd (δ : ℝ) (r : ℝ → ℝ) (z : AddCircle (2 * π) × ℝ) :
    (circleCylinderField δ r z : ℝ × ℝ).2 = z.2 * (1 - z.2 ^ 2) := by
  rw [circleCylinderField, circleContinuationField_apply]

/-! ### Trajectories on the cylinder -/

/-- **Graphs of slope solutions are trajectories on the cylinder.** If `Θ` solves
`Θ' = circleContinuationSlope δ r t (Θ t)` on `0 < t < 1`, then following its graph along the base
trajectory `q = TauCeti.intervalBaseOrbit 1`, shifted by `c`, gives the integral curve
`s ↦ ([Θ (q (s + c))], q (s + c))` of the parameter field on the cylinder. -/
theorem isMIntegralCurve_circleCylinderField {Θ : ℝ → ℝ}
    (hΘ : ∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) (c : ℝ) :
    IsMIntegralCurve (fun s ↦ ((Θ (intervalBaseOrbit 1 (s + c)) : AddCircle (2 * π)),
      intervalBaseOrbit 1 (s + c))) (circleCylinderField δ r) := by
  intro s
  set τ : ℝ → ℝ := fun s ↦ intervalBaseOrbit 1 (s + c)
  have hmem : τ s ∈ Ioo 0 1 := intervalBaseOrbit_mem_Ioo 1 (s + c)
  have hτ : HasDerivAt τ (τ s * (1 - τ s ^ 2)) s := by
    simpa only [one_mul] using (hasDerivAt_intervalBaseOrbit 1 (s + c)).comp_add_const s c
  -- Along the base trajectory the angle moves at the speed `2 δ sin (2 (Θ - r))` of the field.
  have hθ : HasDerivAt (fun s ↦ Θ (τ s)) (2 * δ * sin (2 * (Θ (τ s) - r (τ s)))) s := by
    have h := (hΘ (τ s) hmem).comp s hτ
    rwa [circleContinuationSlope_def,
      div_mul_cancel₀ _ (mul_one_sub_sq_pos_of_mem_Ioo hmem).ne'] at h
  have h₁ : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) (fun s ↦ (Θ (τ s) : AddCircle (2 * π))) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (2 * δ * sin (2 * (Θ (τ s) - r (τ s))))) :=
    ((hasMFDerivAt_coe (2 * π) (Θ (τ s))).comp s hθ.hasFDerivAt.hasMFDerivAt).congr_mfderiv
      (ContinuousLinearMap.id_comp _)
  have h₂ : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) τ s ((1 : ℝ →L[ℝ] ℝ).smulRight (τ s * (1 - τ s ^ 2))) :=
    hasMFDerivAt_iff_hasFDerivAt.2 hτ.hasFDerivAt
  beta_reduce
  rw [circleCylinderField_coe, circleContinuationField_apply]
  exact h₁.prodMk_curve h₂

/-- **Trajectories on the cylinder are graphs of slope solutions.** Let `γ` be an integral curve of
the parameter field on the cylinder meeting the open slab `0 < t < 1`. Then there are a solution
`Θ` of `Θ' = circleContinuationSlope δ r t (Θ t)` on `0 < t < 1` and a shift `c` with
`γ s = ([Θ (q (s + c))], q (s + c))` for the base trajectory `q = TauCeti.intervalBaseOrbit 1`. -/
theorem exists_eq_of_isMIntegralCurve_circleCylinderField {γ : ℝ → AddCircle (2 * π) × ℝ}
    (hγ : IsMIntegralCurve γ (circleCylinderField δ r)) {s₀ : ℝ} (h₀ : (γ s₀).2 ∈ Ioo 0 1) :
    ∃ Θ : ℝ → ℝ, (∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) ∧
      ∃ c, ∀ s, γ s = ((Θ (intervalBaseOrbit 1 (s + c)) : AddCircle (2 * π)),
        intervalBaseOrbit 1 (s + c)) := by
  -- The time component is a translate of the base trajectory.
  obtain ⟨c, hc⟩ := exists_snd_eq_intervalBaseOrbit (C := 1)
    (fun z _ ↦ by rw [circleCylinderField_snd, one_mul]) hγ h₀ one_ne_zero
  -- Lift the angle to a continuous real function, through the covering map `ℝ → S¹`.
  obtain ⟨e, he⟩ := QuotientAddGroup.mk_surjective (γ 0).1
  obtain ⟨θ, ⟨-, hθ⟩, -⟩ := (isCoveringMap_coe (2 * π)).existsUnique_continuousMap_lifts
    ⟨fun s ↦ (γ s).1, hγ.continuous.fst⟩ 0 e he
  have hγθ : ∀ s, γ s = ((θ s : AddCircle (2 * π)), intervalBaseOrbit 1 (s + c)) := fun s ↦
    Prod.ext (congrFun hθ s).symm (hc s)
  -- The lift moves at the speed `2 δ sin (2 (θ - r))` of the field.
  have hd : ∀ s, HasDerivAt θ (2 * δ * sin (2 * (θ s - r (intervalBaseOrbit 1 (s + c))))) s := by
    intro s
    refine hasDerivAt_of_hasMFDerivAt_coe_comp (p := 2 * π) θ.continuous.continuousAt ?_
    have h := (hγ s).fst_curve
    rw [show Prod.fst ∘ γ = fun u ↦ (θ u : AddCircle (2 * π)) from funext fun u ↦ by
      simp [hγθ u], hγθ s, circleCylinderField_coe] at h
    simpa using h
  -- Reparametrize the lift by the time coordinate, which inverts the base trajectory.
  refine ⟨fun t ↦ θ (intervalBaseTimeCoordinate t - c), fun t ht ↦ ?_, c, fun s ↦ ?_⟩
  · have h := (hd _).comp t ((hasDerivAt_intervalBaseTimeCoordinate ht).sub_const c)
    rw [sub_add_cancel, intervalBaseOrbit_one_intervalBaseTimeCoordinate ht] at h
    rw [circleContinuationSlope_def, div_eq_mul_inv]
    exact h
  · simp only [hγθ s, intervalBaseTimeCoordinate_intervalBaseOrbit, one_mul, add_sub_cancel_right]

/-- **The middle-level slice on the cylinder.** A point `x` of the circle lies in the slice
`TauCeti.morseContinuationSlice` of the trajectories of the parameter field from `(p, 0)` to
`(q, 1)` exactly when some solution `Θ` of `Θ' = circleContinuationSlope δ r t (Θ t)` on
`0 < t < 1` passes through a lift of `x` at `t = 1/2` and its image in the circle tends to `p` at
`t = 0` and to `q` at `t = 1`. -/
theorem mem_morseContinuationSlice_circleCylinderField_iff {p q x : AddCircle (2 * π)} :
    x ∈ morseContinuationSlice (circleCylinderField δ r) p q ↔
      ∃ Θ : ℝ → ℝ, (∀ t ∈ Ioo 0 1, HasDerivAt Θ (circleContinuationSlope δ r t (Θ t)) t) ∧
        (Θ (1 / 2) : AddCircle (2 * π)) = x ∧
        Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[>] 0) (𝓝 p) ∧
        Tendsto (fun t ↦ (Θ t : AddCircle (2 * π))) (𝓝[<] 1) (𝓝 q) := by
  have hhalf : (1 / 2 : ℝ) ∈ Ioo 0 1 := by norm_num
  rw [mem_morseContinuationSlice]
  constructor
  · rintro ⟨γ, hγ, hγ0, hp, hq⟩
    obtain ⟨Θ, hΘ, c, hγΘ⟩ := exists_eq_of_isMIntegralCurve_circleCylinderField hγ
      (s₀ := 0) (by rw [hγ0]; exact hhalf)
    have h0 := hγ0
    rw [hγΘ, zero_add, Prod.mk.injEq] at h0
    -- Read a time `t` of the slab as the time `U t - c` of the trajectory.
    have hU : ∀ t ∈ Ioo (0 : ℝ) 1,
        (γ (intervalBaseTimeCoordinate t - c)).1 = (Θ t : AddCircle (2 * π)) := fun t ht ↦ by
      rw [hγΘ, sub_add_cancel, intervalBaseOrbit_one_intervalBaseTimeCoordinate ht]
    refine ⟨Θ, hΘ, by rw [← h0.2, h0.1], ?_, ?_⟩
    · refine ((hp.fst_nhds).comp (tendsto_atBot_add_const_right _ (-c)
        tendsto_intervalBaseTimeCoordinate_nhdsGT_zero)).congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      rw [Function.comp_apply, ← sub_eq_add_neg, hU t ht]
    · refine ((hq.fst_nhds).comp (tendsto_atTop_add_const_right _ (-c)
        tendsto_intervalBaseTimeCoordinate_nhdsLT_one)).congr' ?_
      filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with t ht
      rw [Function.comp_apply, ← sub_eq_add_neg, hU t ht]
  · rintro ⟨Θ, hΘ, hx, hp, hq⟩
    set c := intervalBaseTimeCoordinate (1 / 2)
    have hτ₀ : Tendsto (fun s ↦ intervalBaseOrbit 1 (s + c)) atBot (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨(tendsto_intervalBaseOrbit_atBot one_pos).comp
        (tendsto_atBot_add_const_right _ c tendsto_id),
        .of_forall fun s ↦ (intervalBaseOrbit_mem_Ioo 1 (s + c)).1⟩
    have hτ₁ : Tendsto (fun s ↦ intervalBaseOrbit 1 (s + c)) atTop (𝓝[<] 1) :=
      tendsto_nhdsWithin_iff.2 ⟨(tendsto_intervalBaseOrbit_atTop one_pos).comp
        (tendsto_atTop_add_const_right _ c tendsto_id),
        .of_forall fun s ↦ (intervalBaseOrbit_mem_Ioo 1 (s + c)).2⟩
    refine ⟨_, isMIntegralCurve_circleCylinderField hΘ c, ?_,
      (hp.comp hτ₀).prodMk_nhds (tendsto_nhdsWithin_iff.1 hτ₀).1,
      (hq.comp hτ₁).prodMk_nhds (tendsto_nhdsWithin_iff.1 hτ₁).1⟩
    simp only [zero_add, c, intervalBaseOrbit_one_intervalBaseTimeCoordinate hhalf, hx]

/-! ### The continuation map of a small rotation -/

section Rotation

variable {a b r₀ r₁ : ℝ} {n : ℤ} (hδ : 0 < δ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
  (hr : ContinuousOn r (Icc a b)) (hr₀ : ∀ t ∈ Ioc 0 a, r t = r₀) (hr₁ : ∀ t ∈ Ico b 1, r t = r₁)
  (hn : |r₁ - r₀ - n * π| + 2 * δ * ∫ t in a..b, (t * (1 - t ^ 2))⁻¹ < π / 2)
include hδ ha hab hb hr hr₀ hr₁ hn

/-- The slice from a source point `p` to a target maximum `q`: it is a single point when
`q = p + (r₁ - r₀ - n π)`, and empty otherwise. -/
private theorem ncard_morseContinuationSlice_circleCylinderField_circleCosTwoMax
    (p : AddCircle (2 * π)) (k : Fin 2) :
    (morseContinuationSlice (circleCylinderField δ r) p (circleCosTwoMax r₁ k)).ncard =
      if circleCosTwoMax r₁ k = p + ((r₁ - r₀ - n * π : ℝ) : AddCircle (2 * π)) then 1 else 0 := by
  have hb₀ : 0 < b := ha.trans_le hab
  -- Every trajectory arriving at `q` starts at `q - c`.
  have hstart : ∀ x ∈ morseContinuationSlice (circleCylinderField δ r) p (circleCosTwoMax r₁ k),
      circleCosTwoMax r₁ k = p + ((r₁ - r₀ - n * π : ℝ) : AddCircle (2 * π)) := by
    intro x hx
    obtain ⟨Θ, hΘ, -, hp, hq⟩ := mem_morseContinuationSlice_circleCylinderField_iff.1 hx
    rw [tendsto_nhds_unique hp
      (tendsto_coe_circleCosTwoMax_sub_of_hasDerivAt_circleContinuationSlope hδ ha hab hb hr₀ hr₁
        hΘ hn hq), sub_add_cancel]
  split_ifs with hk
  · obtain ⟨Θ₀, hΘ₀, hq₀⟩ := exists_hasDerivAt_circleContinuationSlope_tendsto_coe_circleCosTwoMax
      hδ ha hab hb hr hr₀ hr₁ hn k
    have hp₀ := tendsto_coe_circleCosTwoMax_sub_of_hasDerivAt_circleContinuationSlope hδ ha hab hb
      hr₀ hr₁ hΘ₀ hn hq₀
    rw [hk, add_sub_cancel_right] at hp₀
    -- The slice is the single point `[Θ₀ (1/2)]`, by uniqueness of the trajectory arriving at `q`.
    convert ncard_singleton ((Θ₀ (1 / 2) : ℝ) : AddCircle (2 * π))
    ext x
    refine ⟨fun hx ↦ ?_, fun hx ↦ mem_morseContinuationSlice_circleCylinderField_iff.2
      ⟨Θ₀, hΘ₀, hx.symm, hp₀, hq₀⟩⟩
    obtain ⟨Θ, hΘ, hΘx, -, hq⟩ := mem_morseContinuationSlice_circleCylinderField_iff.1 hx
    rw [mem_singleton_iff, ← hΘx]
    exact eqOn_coe_of_tendsto_coe_circleCosTwoMax_of_hasDerivAt_circleContinuationSlope hδ.le hb₀
      hb hr₁ hΘ hΘ₀ hq hq₀ (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
  · rw [eq_empty_of_forall_notMem fun x hx ↦ hk (hstart x hx), ncard_empty]

/-- The slice from a source minimum `p` to a target point `q`: it is a single point when
`q = p + (r₁ - r₀ - n π)`, and empty otherwise. -/
private theorem ncard_morseContinuationSlice_circleCylinderField_circleCosTwoMin
    (j : Fin 2) (q : AddCircle (2 * π)) :
    (morseContinuationSlice (circleCylinderField δ r) (circleCosTwoMin r₀ j) q).ncard =
      if q = circleCosTwoMin r₀ j + ((r₁ - r₀ - n * π : ℝ) : AddCircle (2 * π)) then 1 else 0 := by
  -- Every trajectory leaving `p` ends at `p + c`.
  have hend : ∀ x ∈ morseContinuationSlice (circleCylinderField δ r) (circleCosTwoMin r₀ j) q,
      q = circleCosTwoMin r₀ j + ((r₁ - r₀ - n * π : ℝ) : AddCircle (2 * π)) := by
    intro x hx
    obtain ⟨Θ, hΘ, -, hp, hq⟩ := mem_morseContinuationSlice_circleCylinderField_iff.1 hx
    exact tendsto_nhds_unique hq
      (tendsto_coe_circleCosTwoMin_add_of_hasDerivAt_circleContinuationSlope hδ ha hab hb hr₀ hr₁
        hΘ hn hp)
  split_ifs with hq
  · obtain ⟨Θ₀, hΘ₀, hp₀⟩ := exists_hasDerivAt_circleContinuationSlope_tendsto_coe_circleCosTwoMin
      hδ ha hab hb hr hr₀ hr₁ hn j
    have hq₀ := tendsto_coe_circleCosTwoMin_add_of_hasDerivAt_circleContinuationSlope hδ ha hab hb
      hr₀ hr₁ hΘ₀ hn hp₀
    rw [← hq] at hq₀
    -- The slice is the single point `[Θ₀ (1/2)]`, by uniqueness of the trajectory leaving `p`.
    convert ncard_singleton ((Θ₀ (1 / 2) : ℝ) : AddCircle (2 * π))
    ext x
    refine ⟨fun hx ↦ ?_, fun hx ↦ mem_morseContinuationSlice_circleCylinderField_iff.2
      ⟨Θ₀, hΘ₀, hx.symm, hp₀, hq₀⟩⟩
    obtain ⟨Θ, hΘ, hΘx, hp, -⟩ := mem_morseContinuationSlice_circleCylinderField_iff.1 hx
    rw [mem_singleton_iff, ← hΘx]
    exact eqOn_coe_of_tendsto_coe_circleCosTwoMin_of_hasDerivAt_circleContinuationSlope hδ.le ha
      (hab.trans_lt hb) hr₀ hΘ hΘ₀ hp hp₀ (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
  · rw [eq_empty_of_forall_notMem fun x hx ↦ hq (hend x hx), ncard_empty]

/-- **The continuation coefficients of a small rotation.** Let the path `r` be `r₀` on `(0, a]` and
`r₁` on `[b, 1)`, continuous on `[a, b] ⊆ (0, 1)`, let `D = 2 δ ∫_a^b (t (1 - t²))⁻¹ dt` bound the
drift of the angle across `[a, b]`, and let `n` be an integer with `|r₁ - r₀ - n π| + D < π / 2`.
Then the coefficient of the critical point `q` of `f_{r₁}` in the continuation of the critical
point `p` of `f_{r₀}` along the parameter field on the cylinder is `1` when
`q = p + (r₁ - r₀ - n π)`, and `0` otherwise. -/
theorem morseContinuationCoeff_circleCylinderField (p : criticalPoints 𝓘(ℝ) (circleCosTwo δ r₀))
    (q : criticalPoints 𝓘(ℝ) (circleCosTwo δ r₁)) :
    morseContinuationCoeff (circleCosTwo δ r₀) (circleCosTwo δ r₁) (circleCylinderField δ r) p q =
      if (q : AddCircle (2 * π)) = p + ((r₁ - r₀ - n * π : ℝ) : AddCircle (2 * π)) then 1
      else 0 := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  obtain ⟨j, rfl | rfl⟩ := (mem_criticalPoints_circleCosTwo_iff_exists hδ.ne' r₀).1 hp <;>
    obtain ⟨k, rfl | rfl⟩ := (mem_criticalPoints_circleCosTwo_iff_exists hδ.ne' r₁).1 hq
  · rw [morseContinuationCoeff_eq_ncard (by simp only [manifoldMorseIndex_circleCosTwoMax hδ]),
      ncard_morseContinuationSlice_circleCylinderField_circleCosTwoMax hδ ha hab hb hr hr₀ hr₁ hn]
    split_ifs <;> simp
  · -- A maximum is carried to a maximum, never to the minimum `q`.
    obtain ⟨i, hi⟩ := exists_circleCosTwoMax_eq r₁ ((j : ℕ) - n)
    rw [morseContinuationCoeff_eq_zero_of_manifoldMorseIndex_ne (by
      simp only [manifoldMorseIndex_circleCosTwoMax hδ, manifoldMorseIndex_circleCosTwoMin hδ]
      exact one_ne_zero), eq_comm, ite_eq_right_iff]
    refine fun h ↦ absurd ?_ (circleCosTwoMin_ne_circleCosTwoMax r₁ k i)
    dsimp only at h
    rw [h, circleCosTwoMax_def, ← coe_add, hi]
    congr 1
    push_cast
    ring
  · -- A minimum is carried to a minimum, never to the maximum `q`.
    obtain ⟨i, hi⟩ := exists_circleCosTwoMin_eq r₁ ((j : ℕ) - n)
    rw [morseContinuationCoeff_eq_zero_of_manifoldMorseIndex_ne (by
      simp only [manifoldMorseIndex_circleCosTwoMax hδ, manifoldMorseIndex_circleCosTwoMin hδ]
      exact zero_ne_one), eq_comm, ite_eq_right_iff]
    refine fun h ↦ absurd ?_ (circleCosTwoMax_ne_circleCosTwoMin r₁ k i)
    dsimp only at h
    rw [h, circleCosTwoMin_def, ← coe_add, hi]
    congr 1
    push_cast
    ring
  · rw [morseContinuationCoeff_eq_ncard (by simp only [manifoldMorseIndex_circleCosTwoMin hδ]),
      ncard_morseContinuationSlice_circleCylinderField_circleCosTwoMin hδ ha hab hb hr hr₀ hr₁ hn]
    split_ifs <;> simp

/-- **The continuation map of a small rotation is the residual rotation.** Under the hypotheses of
`TauCeti.morseContinuationCoeff_circleCylinderField`, the mod-two continuation map along the
parameter field on the cylinder sends each critical point `p` of `f_{r₀}` to the critical point
`q = p + (r₁ - r₀ - n π)` of `f_{r₁}`. -/
theorem morseContinuationMap_circleCylinderField_single
    {p : criticalPoints 𝓘(ℝ) (circleCosTwo δ r₀)} {q : criticalPoints 𝓘(ℝ) (circleCosTwo δ r₁)}
    (hpq : (q : AddCircle (2 * π)) = p + ((r₁ - r₀ - n * π : ℝ) : AddCircle (2 * π))) :
    morseContinuationMap (circleCosTwo δ r₀) (isMorse_circleCosTwo hδ.ne' r₁)
      (circleCylinderField δ r) (Finsupp.single p 1) = Finsupp.single q 1 := by
  classical
  ext q'
  rw [morseContinuationMap_single_apply, one_mul,
    morseContinuationCoeff_circleCylinderField hδ ha hab hb hr hr₀ hr₁ hn, Finsupp.single_apply]
  exact if_congr (by rw [← hpq, Subtype.ext_iff, eq_comm]) rfl rfl

end Rotation

/-! ### The half-turn, the third-turns and their concatenation -/

section Examples

variable {ρ : ℝ → ℝ} {r₀ : ℝ} (hρ : Continuous ρ) (h0 : ∀ t ≤ 1 / 3, ρ t = 0)
  (h1 : ∀ t, 2 / 3 ≤ t → ρ t = 1) (hδ : 0 < δ)
  (hT : 2 * δ * ∫ t in (1 / 6 : ℝ)..(5 / 6), (t * (1 - t ^ 2))⁻¹ < π / 12)
include hρ h0 h1 hδ hT

/-- The coefficient of the rotation `r₀ + c ρ` of `δ cos (2 (θ - r₀))`, for a residual rotation
`c - n π` of size at most `π / 3`: the rotation is `r₀` on `(0, 1/6]`, `r₀ + c` on `[5/6, 1)` and
continuous, and the drift bound holds. -/
private theorem morseContinuationMap_circleCylinderField_add_mul_single {c : ℝ} {n : ℤ}
    (hc : |c - n * π| ≤ π / 3) {p : criticalPoints 𝓘(ℝ) (circleCosTwo δ r₀)}
    {q : criticalPoints 𝓘(ℝ) (circleCosTwo δ (r₀ + c))}
    (hpq : (q : AddCircle (2 * π)) = p + ((c - n * π : ℝ) : AddCircle (2 * π))) :
    morseContinuationMap (circleCosTwo δ r₀) (isMorse_circleCosTwo hδ.ne' (r₀ + c))
      (circleCylinderField δ fun t ↦ r₀ + c * ρ t) (Finsupp.single p 1) = Finsupp.single q 1 :=
  morseContinuationMap_circleCylinderField_single (r := fun t ↦ r₀ + c * ρ t) (a := 1 / 6)
    (b := 5 / 6) (n := n) hδ (by norm_num) (by norm_num) (by norm_num)
    (continuous_const.add (continuous_const.mul hρ)).continuousOn
    (fun t ht ↦ by rw [h0 t (by linarith [ht.2]), mul_zero, add_zero])
    (fun t ht ↦ by rw [h1 t (by linarith [ht.1]), mul_one])
    (by rw [add_sub_cancel_left]; linarith [pi_pos]) (by rw [add_sub_cancel_left]; exact hpq)

/-- The coefficient of the half-turn `r₀ + π ρ`, whose residual rotation is `0`: it carries each
critical point to the critical point of the end function at the same angle. -/
private theorem morseContinuationMap_circleCylinderField_add_pi_single
    {p : criticalPoints 𝓘(ℝ) (circleCosTwo δ r₀)}
    {q : criticalPoints 𝓘(ℝ) (circleCosTwo δ (r₀ + π))} (hpq : (q : AddCircle (2 * π)) = p) :
    morseContinuationMap (circleCosTwo δ r₀) (isMorse_circleCosTwo hδ.ne' (r₀ + π))
      (circleCylinderField δ fun t ↦ r₀ + π * ρ t) (Finsupp.single p 1) = Finsupp.single q 1 :=
  morseContinuationMap_circleCylinderField_add_mul_single hρ h0 h1 hδ hT (n := 1)
    (by simp [div_nonneg, pi_nonneg]) (by simpa using hpq)

/-- **The half-turn is the identity in fixed bases.** For the path `r = r₀ + π ρ`, from
`δ cos (2 (θ - r₀))` to the same function `δ cos (2 (θ - r₀ - π))` (`TauCeti.circleCosTwo_add_pi`),
the mod-two continuation map along the parameter field on the cylinder is the identity, in the
basis of critical points of the common end function. -/
theorem morseContinuationMap_circleCylinderField_add_pi_eq_id :
    morseContinuationMap (circleCosTwo δ r₀) (isMorse_circleCosTwo hδ.ne' r₀)
      (circleCylinderField δ fun t ↦ r₀ + π * ρ t) = LinearMap.id := by
  -- The rotation by `c = π` with `n = 1` has residual rotation `0`, and its end function is the
  -- source function itself.
  have h : ∀ (hf : IsMorse 𝓘(ℝ) (circleCosTwo δ (r₀ + π)))
      (p : criticalPoints 𝓘(ℝ) (circleCosTwo δ r₀))
      (q : criticalPoints 𝓘(ℝ) (circleCosTwo δ (r₀ + π))), (q : AddCircle (2 * π)) = p →
        morseContinuationMap (circleCosTwo δ r₀) hf (circleCylinderField δ fun t ↦ r₀ + π * ρ t)
          (Finsupp.single p 1) = Finsupp.single q 1 := fun _ _ _ hpq ↦
    morseContinuationMap_circleCylinderField_add_pi_single hρ h0 h1 hδ hT hpq
  rw [circleCosTwo_add_pi] at h
  exact Finsupp.lhom_ext' fun p ↦ LinearMap.ext_ring (h _ p p rfl)

/-- **The half-turn exchanges the tracked maxima.** For the path `r = r₀ + π ρ`, the mod-two
continuation map sends the maximum `p_j(r₀)` to the maximum `p_{j + 1}(r₀ + π)` at the same angle
(`TauCeti.circleCosTwoMax_add_pi`), not to the maximum `p_j(r₀ + π)` tracked from it along the
path: in the tracked labels it is the exchange of the two generators. -/
theorem morseContinuationMap_single_circleCosTwoMaxCrit_add_pi (j : Fin 2) :
    morseContinuationMap (circleCosTwo δ r₀) (isMorse_circleCosTwo hδ.ne' (r₀ + π))
      (circleCylinderField δ fun t ↦ r₀ + π * ρ t) (Finsupp.single (circleCosTwoMaxCrit δ r₀ j) 1) =
        Finsupp.single (circleCosTwoMaxCrit δ (r₀ + π) (j + 1)) 1 :=
  morseContinuationMap_circleCylinderField_add_pi_single hρ h0 h1 hδ hT
    (by simp [coe_circleCosTwoMaxCrit, circleCosTwoMax_add_pi, add_assoc])

/-- **The half-turn exchanges the tracked minima.** For the path `r = r₀ + π ρ`, the mod-two
continuation map sends the minimum `q_j(r₀)` to the minimum `q_{j + 1}(r₀ + π)` at the same angle
(`TauCeti.circleCosTwoMin_add_pi`), not to the minimum `q_j(r₀ + π)` tracked from it along the
path: in the tracked labels it is the exchange of the two generators. -/
theorem morseContinuationMap_single_circleCosTwoMinCrit_add_pi (j : Fin 2) :
    morseContinuationMap (circleCosTwo δ r₀) (isMorse_circleCosTwo hδ.ne' (r₀ + π))
      (circleCylinderField δ fun t ↦ r₀ + π * ρ t) (Finsupp.single (circleCosTwoMinCrit δ r₀ j) 1) =
        Finsupp.single (circleCosTwoMinCrit δ (r₀ + π) (j + 1)) 1 :=
  morseContinuationMap_circleCylinderField_add_pi_single hρ h0 h1 hδ hT
    (by simp [coe_circleCosTwoMinCrit, circleCosTwoMin_add_pi, add_assoc])

/-- **A third of a turn agrees with the tracked maxima.** For the path `r = r₀ + (π / 3) ρ`, the
mod-two continuation map sends the maximum `p_j(r₀)` to the maximum `p_j(r₀ + π / 3)` tracked from
it: in the tracked labels it is the identity. -/
theorem morseContinuationMap_single_circleCosTwoMaxCrit_add_pi_div_three
    (j : Fin 2) :
    morseContinuationMap (circleCosTwo δ r₀) (isMorse_circleCosTwo hδ.ne' (r₀ + π / 3))
      (circleCylinderField δ fun t ↦ r₀ + π / 3 * ρ t)
        (Finsupp.single (circleCosTwoMaxCrit δ r₀ j) 1) =
      Finsupp.single (circleCosTwoMaxCrit δ (r₀ + π / 3) j) 1 :=
  morseContinuationMap_circleCylinderField_add_mul_single hρ h0 h1 hδ hT (n := 0)
    (by simp [abs_of_pos, pi_pos]) (by simp [coe_circleCosTwoMaxCrit, circleCosTwoMax_add_coe])

/-- **A third of a turn agrees with the tracked minima.** For the path `r = r₀ + (π / 3) ρ`, the
mod-two continuation map sends the minimum `q_j(r₀)` to the minimum `q_j(r₀ + π / 3)` tracked from
it: in the tracked labels it is the identity. -/
theorem morseContinuationMap_single_circleCosTwoMinCrit_add_pi_div_three
    (j : Fin 2) :
    morseContinuationMap (circleCosTwo δ r₀) (isMorse_circleCosTwo hδ.ne' (r₀ + π / 3))
      (circleCylinderField δ fun t ↦ r₀ + π / 3 * ρ t)
        (Finsupp.single (circleCosTwoMinCrit δ r₀ j) 1) =
      Finsupp.single (circleCosTwoMinCrit δ (r₀ + π / 3) j) 1 :=
  morseContinuationMap_circleCylinderField_add_mul_single hρ h0 h1 hδ hT (n := 0)
    (by simp [abs_of_pos, pi_pos]) (by simp [coe_circleCosTwoMinCrit, circleCosTwoMin_add_coe])

/-- The concatenation of the third-turns `r₀ + (π / 3) ρ` and `r₀ + π / 3 + (π / 3) ρ`, run at
double speed on `[0, 1/2]` and `[1/2, 1]`, is `r₀` on `(0, 1/6]`, `r₀ + 2 π / 3` on `[5/6, 1)`, and
continuous: at `t = 1/2` both pieces equal `r₀ + π / 3`. Its residual rotation is
`2 π / 3 - π = -π / 3`. -/
private theorem morseContinuationMap_circleCylinderField_add_two_mul_pi_div_three_single
    {p : criticalPoints 𝓘(ℝ) (circleCosTwo δ r₀)}
    {q : criticalPoints 𝓘(ℝ) (circleCosTwo δ (r₀ + 2 * π / 3))}
    (hpq : (q : AddCircle (2 * π)) = p + ((2 * π / 3 - π : ℝ) : AddCircle (2 * π))) :
    morseContinuationMap (circleCosTwo δ r₀) (isMorse_circleCosTwo hδ.ne' (r₀ + 2 * π / 3))
      (circleCylinderField δ fun t ↦
        if t ≤ 1 / 2 then r₀ + π / 3 * ρ (2 * t) else r₀ + π / 3 + π / 3 * ρ (2 * t - 1))
      (Finsupp.single p 1) = Finsupp.single q 1 := by
  have hc : |2 * π / 3 - π| ≤ π / 3 := abs_le.2 ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hcont : Continuous fun t : ℝ ↦
      if t ≤ 1 / 2 then r₀ + π / 3 * ρ (2 * t) else r₀ + π / 3 + π / 3 * ρ (2 * t - 1) := by
    refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const ?_
    intro t ht
    rw [ht, h1 _ (by norm_num), h0 _ (by norm_num)]
    ring
  refine morseContinuationMap_circleCylinderField_single (a := 1 / 6) (b := 5 / 6) (n := 1) hδ
    (by norm_num) (by norm_num) (by norm_num) hcont.continuousOn (fun t ht ↦ ?_) (fun t ht ↦ ?_)
    (by rw [add_sub_cancel_left, Int.cast_one, one_mul]; linarith [pi_pos])
    (by rwa [add_sub_cancel_left, Int.cast_one, one_mul])
  · simp only [show t ≤ 1 / 2 by linarith [ht.2], ↓reduceIte,
      h0 _ (by linarith [ht.2] : 2 * t ≤ 1 / 3), mul_zero, add_zero]
  · simp only [show ¬t ≤ 1 / 2 by linarith [ht.1], ↓reduceIte,
      h1 _ (by linarith [ht.1] : 2 / 3 ≤ 2 * t - 1)]
    ring

/-- **The concatenation of two third-turns exchanges the tracked maxima.** For the concatenation of
the third-turns `Γ₁ = r₀ + (π / 3) ρ` and `Γ₂ = r₀ + π / 3 + (π / 3) ρ`, run at double speed on
`[0, 1/2]` and `[1/2, 1]`, the mod-two continuation map sends the maximum `p_j(r₀)` to the maximum
`p_{j + 1}(r₀ + 2 π / 3)`, not to the maximum `p_j(r₀ + 2 π / 3)` tracked from it. Each third-turn
agrees with the tracked labels
(`TauCeti.morseContinuationMap_single_circleCosTwoMaxCrit_add_pi_div_three`), but
their concatenation exchanges them: continuation maps do not compose strictly. -/
theorem morseContinuationMap_single_circleCosTwoMaxCrit_add_two_mul_pi_div_three (j : Fin 2) :
    morseContinuationMap (circleCosTwo δ r₀) (isMorse_circleCosTwo hδ.ne' (r₀ + 2 * π / 3))
      (circleCylinderField δ fun t ↦
        if t ≤ 1 / 2 then r₀ + π / 3 * ρ (2 * t) else r₀ + π / 3 + π / 3 * ρ (2 * t - 1))
      (Finsupp.single (circleCosTwoMaxCrit δ r₀ j) 1) =
      Finsupp.single (circleCosTwoMaxCrit δ (r₀ + 2 * π / 3) (j + 1)) 1 :=
  morseContinuationMap_circleCylinderField_add_two_mul_pi_div_three_single hρ h0 h1 hδ hT (by
    rw [coe_circleCosTwoMaxCrit, coe_circleCosTwoMaxCrit, circleCosTwoMax_add_coe,
      ← circleCosTwoMax_add_pi, circleCosTwoMax_def, circleCosTwoMax_def]
    exact coe_eq_coe_iff_exists_zsmul.2 ⟨1, by rw [one_zsmul]; ring⟩)

/-- **The concatenation of two third-turns exchanges the tracked minima.** For the concatenation of
the third-turns `Γ₁ = r₀ + (π / 3) ρ` and `Γ₂ = r₀ + π / 3 + (π / 3) ρ`, run at double speed on
`[0, 1/2]` and `[1/2, 1]`, the mod-two continuation map sends the minimum `q_j(r₀)` to the minimum
`q_{j + 1}(r₀ + 2 π / 3)`, not to the minimum `q_j(r₀ + 2 π / 3)` tracked from it. -/
theorem morseContinuationMap_single_circleCosTwoMinCrit_add_two_mul_pi_div_three (j : Fin 2) :
    morseContinuationMap (circleCosTwo δ r₀) (isMorse_circleCosTwo hδ.ne' (r₀ + 2 * π / 3))
      (circleCylinderField δ fun t ↦
        if t ≤ 1 / 2 then r₀ + π / 3 * ρ (2 * t) else r₀ + π / 3 + π / 3 * ρ (2 * t - 1))
      (Finsupp.single (circleCosTwoMinCrit δ r₀ j) 1) =
      Finsupp.single (circleCosTwoMinCrit δ (r₀ + 2 * π / 3) (j + 1)) 1 :=
  morseContinuationMap_circleCylinderField_add_two_mul_pi_div_three_single hρ h0 h1 hδ hT (by
    rw [coe_circleCosTwoMinCrit, coe_circleCosTwoMinCrit, circleCosTwoMin_add_coe,
      ← circleCosTwoMin_add_pi, circleCosTwoMin_def, circleCosTwoMin_def]
    exact coe_eq_coe_iff_exists_zsmul.2 ⟨1, by rw [one_zsmul]; ring⟩)

end Examples

end TauCeti
