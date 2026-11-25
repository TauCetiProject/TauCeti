/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.Eigenspace
public import TauCeti.Analysis.Semigroups.Group.Unitary
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.MeasureTheory.Integral.IntervalAverage
import TauCeti.Analysis.InnerProductSpace.Projection.RestrictScalars
import TauCeti.Analysis.Semigroups.Group.PhaseShift.Unitary
import TauCeti.MeasureTheory.Integral.Average

/-!
# Continuous-time mean ergodic theorem for C₀-groups

This file proves the continuous-time von Neumann mean ergodic theorem without separability:

* For any contractive C₀-group `U` (`∀ t, ‖U t‖ ≤ 1`) on a complete real Hilbert space `H`, the
  orbit averages `T⁻¹ • ∫ t in (0 : ℝ)..T, U t v` converge in norm as `T → ∞` to the orthogonal
  projection of `v` onto `U.fixedSpace` (`tendsto_average_orbit_starProjection_fixedSpace`).
* For a unitary C₀-group `U` on a complete complex Hilbert space `H`, restricting scalars recovers
  convergence to `(U.fixedSubmodule hU.isComplexLinear).starProjection v`
  (`IsUnitary.tendsto_average_starProjection`), and phase shifting yields convergence of the twisted
  averages `T⁻¹ • ∫ t in (0 : ℝ)..T, exp (-(ω * t * I)) • U t v` to
  `(U.eigenspace hU.isComplexLinear ω).starProjection v`
  (`IsUnitary.tendsto_twistedAverage_starProjection`).

The real-Hilbert proof reduces continuous-time averages to discrete Birkhoff averages of `U 1`
acting on `∫ t in (0 : ℝ)..1, U t v` via Mathlib's
`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`, bridges to real endpoints,
establishes shift invariance via the coboundary telescoping identity
`intervalIntegral_orbit_apply_sub`, and identifies the limit with the orthogonal projection onto
`U.fixedSpace`.

## Main results

* `TauCeti.Semigroups.StronglyContinuousGroup.map_intervalIntegral_orbit`: commuting a C₀-group
  operator past an orbit interval integral shifts the integration bounds.
* `TauCeti.Semigroups.StronglyContinuousGroup.average_orbit_of_mem_fixedSpace`: orbit averages
  preserve fixed vectors.
* `TauCeti.Semigroups.StronglyContinuousGroup.intervalIntegral_orbit_apply_sub`,
  `TauCeti.Semigroups.StronglyContinuousGroup.norm_average_orbit_apply_sub_le`, and
  `TauCeti.Semigroups.StronglyContinuousGroup.tendsto_average_orbit_apply_sub`: coboundary
  telescoping and quantitative `O(|T|⁻¹)` decay of orbit averages on `U s v - v`.
* `TauCeti.Semigroups.StronglyContinuousGroup.norm_intervalIntegral_orbit_le` and
  `TauCeti.Semigroups.StronglyContinuousGroup.norm_average_orbit_le`: norm bounds for contractive
  C₀-groups on a real normed space.
* `TauCeti.Semigroups.StronglyContinuousGroup.tendsto_average_orbit_starProjection_fixedSpace`:
  continuous-time von Neumann mean ergodic theorem for contractive C₀-groups on a real Hilbert
  space.
* `TauCeti.Semigroups.StronglyContinuousGroup.inner_intervalIntegral_orbit`: commuting an inner
  product past an orbit interval integral.
* `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.norm_intervalIntegral_orbit_le`: norm
  bound `‖∫ t in a..b, U t v‖ ≤ ‖v‖ * |b - a|` for unitary C₀-groups.
* `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.tendsto_average_starProjection`:
  continuous-time von Neumann mean ergodic theorem for unitary C₀-groups.
* `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.tendsto_twistedAverage_starProjection`:
  twisted continuous-time mean ergodic projection onto `eigenspace`.

## References

* J. von Neumann, *Proof of the quasi-ergodic hypothesis*, Proc. Natl. Acad. Sci. USA 18 (1932),
  70–82.
* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section V.4 (mean ergodic semigroups).
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped InnerProductSpace Topology

namespace TauCeti.Semigroups.StronglyContinuousGroup

/-! ## Orbit averages on real normed spaces -/

section RealNormed

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Commuting a C₀-group operator `U s` past an interval integral along an orbit shifts the
integration bounds by `s`. -/
theorem map_intervalIntegral_orbit [CompleteSpace X] (U : StronglyContinuousGroup X)
    (s a b : ℝ) (v : X) :
    U s (∫ t in a..b, U t v) = ∫ t in a + s..b + s, U t v := by
  have hint : IntervalIntegrable (fun t : ℝ ↦ U t v) volume a b :=
    (U.continuous_orbit v).intervalIntegrable a b
  rw [← (U s).intervalIntegral_comp_comm hint]
  have hcomp : (fun t : ℝ ↦ U s (U t v)) = fun t : ℝ ↦ U (t + s) v := by
    funext t
    rw [← U.map_add_apply, add_comm]
  rw [hcomp, intervalIntegral.integral_comp_add_right (a := a) (b := b) (f := fun t : ℝ ↦ U t v) s]

/-- Every nonzero time average of a fixed vector equals the vector itself. -/
theorem average_orbit_of_mem_fixedSpace [CompleteSpace X] (U : StronglyContinuousGroup X)
    {w : X} (hw : w ∈ U.fixedSpace) {T : ℝ} (hT : T ≠ 0) :
    T⁻¹ • ∫ t in (0 : ℝ)..T, U t w = w := by
  have hfun : (fun t : ℝ ↦ U t w) = fun _ ↦ w := funext fun t ↦ (U.mem_fixedSpace_iff w).mp hw t
  rw [hfun, intervalIntegral.integral_const, sub_zero, smul_smul, inv_mul_cancel₀ hT, one_smul]

/-- Telescoping identity for the interval integral of a coboundary `U s v - v`. -/
theorem intervalIntegral_orbit_apply_sub (U : StronglyContinuousGroup X)
    (s T : ℝ) (v : X) :
    (∫ t in (0 : ℝ)..T, U t (U s v - v)) =
      (∫ t in T..(T + s), U t v) - ∫ t in (0 : ℝ)..s, U t v := by
  have hcont : Continuous fun t : ℝ ↦ U t v := U.continuous_orbit v
  have hshift : Continuous fun t : ℝ ↦ U (t + s) v :=
    hcont.comp (continuous_id.add continuous_const)
  have hpoint : (fun t : ℝ ↦ U t (U s v - v)) = fun t : ℝ ↦ U (t + s) v - U t v := by
    funext t
    rw [(U t).map_sub, U.map_add_apply]
  rw [hpoint, intervalIntegral.integral_sub (hshift.intervalIntegrable 0 T)
    (hcont.intervalIntegrable 0 T),
    intervalIntegral.integral_comp_add_right (f := fun t : ℝ ↦ U t v) s, zero_add]
  exact intervalIntegral.integral_interval_sub_interval_comm'
    (hcont.intervalIntegrable s (T + s)) (hcont.intervalIntegrable 0 T)
    (hcont.intervalIntegrable s 0)

/-- The interval integral along an orbit of a contractive C₀-group grows at most linearly in the
interval length. -/
theorem norm_intervalIntegral_orbit_le (U : StronglyContinuousGroup X)
    (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1) (a b : ℝ) (v : X) :
    ‖∫ t in a..b, U t v‖ ≤ ‖v‖ * |b - a| :=
  intervalIntegral.norm_integral_le_of_norm_le_const fun t _ ↦ by
    rw [U.norm_map_apply_eq_of_norm_le_one t (hnorm t) (hnorm (-t))]

/-- The time average of an orbit of a contractive C₀-group is a contraction at every `T : ℝ`. -/
theorem norm_average_orbit_le (U : StronglyContinuousGroup X)
    (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1) (T : ℝ) (v : X) :
    ‖T⁻¹ • ∫ t in (0 : ℝ)..T, U t v‖ ≤ ‖v‖ := by
  simpa only [interval_average_eq, sub_zero] using
    TauCeti.norm_setAverage_le_of_norm_le_const (μ := volume) (s := Set.uIoc 0 T)
      (f := fun t : ℝ ↦ U t v) (norm_nonneg v) fun t _ ↦ by
        rw [U.norm_map_apply_eq_of_norm_le_one t (hnorm t) (hnorm (-t))]

/-- Quantitative decay of the time average on a coboundary `U s v - v`, for every `T : ℝ`. -/
theorem norm_average_orbit_apply_sub_le (U : StronglyContinuousGroup X)
    (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1) (s T : ℝ) (v : X) :
    ‖T⁻¹ • ∫ t in (0 : ℝ)..T, U t (U s v - v)‖ ≤ 2 * |s| * ‖v‖ / |T| := by
  rw [U.intervalIntegral_orbit_apply_sub s T v, norm_smul, Real.norm_eq_abs, abs_inv]
  have h1 : ‖∫ t in T..(T + s), U t v‖ ≤ ‖v‖ * |s| := by
    simpa only [add_sub_cancel_left] using U.norm_intervalIntegral_orbit_le hnorm T (T + s) v
  have h2 : ‖∫ t in (0 : ℝ)..s, U t v‖ ≤ ‖v‖ * |s| := by
    simpa only [sub_zero] using U.norm_intervalIntegral_orbit_le hnorm 0 s v
  have hsub : ‖(∫ t in T..(T + s), U t v) - ∫ t in (0 : ℝ)..s, U t v‖ ≤ 2 * |s| * ‖v‖ := by
    calc
      ‖(∫ t in T..(T + s), U t v) - ∫ t in (0 : ℝ)..s, U t v‖
          ≤ ‖∫ t in T..(T + s), U t v‖ + ‖∫ t in (0 : ℝ)..s, U t v‖ := norm_sub_le _ _
      _ ≤ ‖v‖ * |s| + ‖v‖ * |s| := add_le_add h1 h2
      _ = 2 * |s| * ‖v‖ := by ring
  calc
    |T|⁻¹ * ‖(∫ t in T..(T + s), U t v) - ∫ t in (0 : ℝ)..s, U t v‖
        ≤ |T|⁻¹ * (2 * |s| * ‖v‖) := by gcongr
    _ = 2 * |s| * ‖v‖ / |T| := by rw [div_eq_inv_mul]

/-- The time averages of every coboundary `U s v - v` converge to `0`. -/
theorem tendsto_average_orbit_apply_sub (U : StronglyContinuousGroup X)
    (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1) (s : ℝ) (v : X) :
    Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in (0 : ℝ)..T, U t (U s v - v)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun T : ℝ ↦ 2 * |s| * ‖v‖ / T) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    simpa only [abs_of_pos hT] using U.norm_average_orbit_apply_sub_le hnorm s T v
  · simpa only [div_eq_mul_inv, mul_zero] using
      tendsto_inv_atTop_zero.const_mul (2 * |s| * ‖v‖)

private theorem iterate_one_apply (U : StronglyContinuousGroup X) (n : ℕ) (x : X) :
    (U 1)^[n] x = U (n : ℝ) x := by
  have hpow := U.toSemigroup.map_natCast_mul 1 n
  simp only [mul_one, U.toSemigroup_apply, NNReal.coe_one, NNReal.coe_natCast] at hpow
  rw [← FunLike.coe_pow_eq_iterate, ← hpow]

private theorem birkhoffAverage_one_intervalIntegral [CompleteSpace X]
    (U : StronglyContinuousGroup X) (N : ℕ) (v : X) :
    birkhoffAverage ℝ (U 1) _root_.id N (∫ t in (0 : ℝ)..1, U t v) =
      (N : ℝ)⁻¹ • ∫ t in (0 : ℝ)..(N : ℝ), U t v := by
  have hterm (k : ℕ) :
      (U 1)^[k] (∫ t in (0 : ℝ)..1, U t v) =
        ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), U t v := by
    rw [U.iterate_one_apply k, U.map_intervalIntegral_orbit (k : ℝ) 0 1 v, zero_add,
      add_comm 1 (k : ℝ), Nat.cast_succ]
  rw [birkhoffAverage, birkhoffSum]
  congr 1
  simp_rw [id_eq, hterm]
  simpa only [Nat.cast_zero] using
    intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ ↦ (k : ℝ))
      (f := fun t : ℝ ↦ U t v) fun k _ ↦ (U.continuous_orbit v).intervalIntegrable _ _

/-- Commutation of a group operator with orbit averaging produces the averaged coboundary. -/
private theorem average_orbit_apply_sub [CompleteSpace X] (U : StronglyContinuousGroup X)
    (s T : ℝ) (v : X) :
    U s (T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) - T⁻¹ • ∫ t in (0 : ℝ)..T, U t v =
      T⁻¹ • ∫ t in (0 : ℝ)..T, U t (U s v - v) := by
  have hcont := U.continuous_orbit v
  have hcomm : U s (∫ t in (0 : ℝ)..T, U t v) = ∫ t in (0 : ℝ)..T, U t (U s v) := by
    rw [← (U s).intervalIntegral_comp_comm (hcont.intervalIntegrable 0 T)]
    exact intervalIntegral.integral_congr fun t _ ↦ U.map_comm s t v
  have hsub : (fun t : ℝ ↦ U t (U s v - v)) = fun t : ℝ ↦ U t (U s v) - U t v :=
    funext fun t ↦ (U t).map_sub (U s v) v
  rw [map_smul, hcomm, hsub, intervalIntegral.integral_sub
    ((U.continuous_orbit (U s v)).intervalIntegrable 0 T) (hcont.intervalIntegrable 0 T),
    smul_sub]

end RealNormed

/-! ## Real Hilbert-space mean ergodic theorem -/

section RealInnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem tendsto_average_orbit_orthogonalProjectionOnto_eqLocus_one
    (U : StronglyContinuousGroup H) (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1) (v : H) :
    Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) atTop
      (𝓝 (((U 1).eqLocus (1 : H →L[ℝ] H)).orthogonalProjectionOnto
        (∫ t in (0 : ℝ)..1, U t v) : H)) := by
  let v₁ : H := ∫ t in (0 : ℝ)..1, U t v
  let w : H := ((U 1).eqLocus (1 : H →L[ℝ] H)).orthogonalProjectionOnto v₁
  have hBirkhoff : Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in (0 : ℝ)..(⌊T⌋₊ : ℝ), U t v) atTop
      (𝓝 w) := by
    have hdisc := ((U 1).tendsto_birkhoffAverage_orthogonalProjection (hnorm 1) v₁).comp
      (tendsto_nat_floor_atTop (α := ℝ))
    have hscaled : Tendsto (fun T : ℝ ↦
        ((⌊T⌋₊ : ℝ) / T) • birkhoffAverage ℝ (U 1) _root_.id ⌊T⌋₊ v₁) atTop (𝓝 ((1 : ℝ) • w)) :=
      (tendsto_nat_floor_div_atTop (R := ℝ)).smul hdisc
    rw [one_smul] at hscaled
    refine hscaled.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hN0 : (⌊T⌋₊ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.floor_pos.mpr hT).ne'
    rw [U.birkhoffAverage_one_intervalIntegral ⌊T⌋₊ v, smul_smul]
    congr 1
    field_simp
  have htail : Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in (⌊T⌋₊ : ℝ)..T, U t v) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun T : ℝ ↦ ‖v‖ / T) ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
      have hle : |T - (⌊T⌋₊ : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg (sub_nonneg.mpr (Nat.floor_le hTpos.le))]
        linarith [Nat.lt_floor_add_one T]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hTpos]
      calc
        T⁻¹ * ‖∫ t in (⌊T⌋₊ : ℝ)..T, U t v‖
            ≤ T⁻¹ * (‖v‖ * |T - (⌊T⌋₊ : ℝ)|) := by
              gcongr
              exact U.norm_intervalIntegral_orbit_le hnorm _ _ v
        _ ≤ T⁻¹ * (‖v‖ * 1) := by gcongr
        _ = ‖v‖ / T := by rw [mul_one, div_eq_inv_mul]
    · simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul ‖v‖
  have hadd := hBirkhoff.add htail
  rw [add_zero] at hadd
  refine hadd.congr fun T ↦ ?_
  have hcont := U.continuous_orbit v
  rw [← smul_add, intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 _) (hcont.intervalIntegrable _ T)]

/-- Pairing a nonzero orbit average of a contractive C₀-group with a fixed vector preserves the
inner product. -/
private theorem inner_average_orbit_of_mem_fixedSpace (U : StronglyContinuousGroup H)
    (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1) (v : H) {u : H} (hu : u ∈ U.fixedSpace)
    {T : ℝ} (hT : T ≠ 0) :
    ⟪T⁻¹ • ∫ t in (0 : ℝ)..T, U t v, u⟫_ℝ = ⟪v, u⟫_ℝ := by
  have hcomm : ⟪∫ t in (0 : ℝ)..T, U t v, u⟫_ℝ = ∫ t in (0 : ℝ)..T, ⟪U t v, u⟫_ℝ := by
    rw [real_inner_comm, ← innerSL_apply_apply ℝ u,
      ← (innerSL ℝ u).intervalIntegral_comp_comm ((U.continuous_orbit v).intervalIntegrable 0 T)]
    simp_rw [innerSL_apply_apply, real_inner_comm]
  have hpt : (fun t : ℝ ↦ ⟪U t v, u⟫_ℝ) = fun _ ↦ ⟪v, u⟫_ℝ := by
    funext t
    let L : H →ₗᵢ[ℝ] H :=
      { toLinearMap := (U (-t)).toLinearMap
        norm_map' := U.norm_map_apply_eq_of_norm_le_one (-t) (hnorm (-t))
          (by simpa only [neg_neg] using hnorm t) }
    calc
      ⟪U t v, u⟫_ℝ = ⟪L (U t v), L u⟫_ℝ := (L.inner_map_map (U t v) u).symm
      _ = ⟪v, u⟫_ℝ := by simp [L, (U.mem_fixedSpace_iff u).mp hu (-t)]
  rw [real_inner_smul_left, hcomm, hpt, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hT, one_mul]

/-- **Continuous-time von Neumann mean ergodic theorem** on a real Hilbert space: for any
contractive C₀-group, the orbit averages `T⁻¹ • ∫ t in 0..T, U t v` converge in norm to the
orthogonal projection of `v` onto `U.fixedSpace`. -/
theorem tendsto_average_orbit_starProjection_fixedSpace (U : StronglyContinuousGroup H)
    (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1) (v : H) :
    Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) atTop
      (𝓝 (U.fixedSpace.starProjection v)) := by
  let w : H := ((U 1).eqLocus (1 : H →L[ℝ] H)).orthogonalProjectionOnto
    (∫ t in (0 : ℝ)..1, U t v)
  have htend : Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) atTop (𝓝 w) :=
    U.tendsto_average_orbit_orthogonalProjectionOnto_eqLocus_one hnorm v
  have hw_fixed : w ∈ U.fixedSpace := by
    rw [mem_fixedSpace_iff]
    intro s
    have h1 : Tendsto (fun T : ℝ ↦ U s (T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) -
        T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) atTop (𝓝 (U s w - w)) :=
      (((U s).continuous.tendsto w).comp htend).sub htend
    have h2 : Tendsto (fun T : ℝ ↦ U s (T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) -
        T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) atTop (𝓝 0) :=
      (U.tendsto_average_orbit_apply_sub hnorm s v).congr fun T ↦
        (U.average_orbit_apply_sub s T v).symm
    exact sub_eq_zero.mp (tendsto_nhds_unique h1 h2)
  have hproj : U.fixedSpace.starProjection v = w := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hw_fixed fun u hu ↦ ?_
    have hlim : Tendsto (fun T : ℝ ↦ ⟪T⁻¹ • ∫ t in (0 : ℝ)..T, U t v, u⟫_ℝ) atTop (𝓝 ⟪w, u⟫_ℝ) :=
      htend.inner tendsto_const_nhds
    have hconst : Tendsto (fun T : ℝ ↦ ⟪T⁻¹ • ∫ t in (0 : ℝ)..T, U t v, u⟫_ℝ) atTop
        (𝓝 ⟪v, u⟫_ℝ) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
        exact (U.inner_average_orbit_of_mem_fixedSpace hnorm v hu hT.ne').symm)
    rw [inner_sub_left, tendsto_nhds_unique hconst hlim, sub_self]
  rwa [hproj]

end RealInnerProduct

/-! ## Unitary C₀-groups on complex Hilbert spaces -/

/-- Commuting an inner product past an interval integral along a C₀-group orbit. -/
theorem inner_intervalIntegral_orbit {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (U : StronglyContinuousGroup H) (y v : H) (a b : ℝ) :
    ⟪y, ∫ t in a..b, U t v⟫_ℂ = ∫ t in a..b, ⟪y, U t v⟫_ℂ := by
  have hint : IntervalIntegrable (fun t : ℝ ↦ U t v) volume a b :=
    (U.continuous_orbit v).intervalIntegrable a b
  simpa only [innerSL_apply_apply] using ((innerSL ℂ y).intervalIntegral_comp_comm hint).symm

namespace IsUnitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {U : StronglyContinuousGroup H}

/-- For a unitary C₀-group `U`, the interval integral of an orbit has norm at most
`‖v‖ * |b - a|`. -/
theorem norm_intervalIntegral_orbit_le (hU : U.IsUnitary) (a b : ℝ) (v : H) :
    ‖∫ t in a..b, U t v‖ ≤ ‖v‖ * |b - a| :=
  StronglyContinuousGroup.norm_intervalIntegral_orbit_le U hU.opNorm_le_one a b v

section ComplexMeanErgodic

attribute [local instance] InnerProductSpace.complexToReal

/-- **Continuous-time von Neumann mean ergodic theorem.** For a unitary C₀-group `U` on a complete
complex Hilbert space `H` and any `v : H`, the time averages `T⁻¹ • ∫ t in (0 : ℝ)..T, U t v`
converge in norm as `T → ∞` to the orthogonal projection of `v` onto the common fixed subspace
`U.fixedSubmodule hU.isComplexLinear`. -/
theorem tendsto_average_starProjection [CompleteSpace H] (hU : U.IsUnitary) (v : H) :
    Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) atTop
      (𝓝 ((U.fixedSubmodule hU.isComplexLinear).starProjection v)) := by
  have h := U.tendsto_average_orbit_starProjection_fixedSpace hU.opNorm_le_one v
  have hcongr : ∀ {K₁ K₂ : Submodule ℝ H} [K₁.HasOrthogonalProjection]
      [K₂.HasOrthogonalProjection], K₁ = K₂ → K₁.starProjection v = K₂.starProjection v := by
    rintro K₁ _ _ _ rfl
    rfl
  have hproj :
      U.fixedSpace.starProjection v = (U.fixedSubmodule hU.isComplexLinear).starProjection v :=
    (hcongr (U.fixedSubmodule_restrictScalars hU.isComplexLinear)).symm.trans
      (Submodule.starProjection_restrictScalars_apply (U.fixedSubmodule hU.isComplexLinear) v)
  rwa [hproj] at h

end ComplexMeanErgodic

/-- **Twisted continuous-time mean ergodic projection.** For a unitary C₀-group `U` on a complete
complex Hilbert space `H`, an angular frequency `ω : ℝ`, and `v : H`, the twisted averages
`T⁻¹ • ∫ t in (0 : ℝ)..T, exp (-(ω * t * I)) • U t v` converge in norm as `T → ∞` to the orthogonal
projection of `v` onto the common eigenspace `U.eigenspace hU.isComplexLinear ω`. -/
theorem tendsto_twistedAverage_starProjection [CompleteSpace H] (hU : U.IsUnitary) (ω : ℝ) (v : H) :
    Tendsto (fun T : ℝ ↦
        T⁻¹ • ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) • U t v)
      atTop (𝓝 ((U.eigenspace hU.isComplexLinear ω).starProjection v)) := by
  have h := (hU.phaseShift ω).tendsto_average_starProjection v
  -- `eigenspace` is not `@[expose]` across `module` boundaries, so `rfl` cannot unfold it here;
  -- transport `starProjection` along `eigenspace_eq_fixedSubmodule_phaseShift`.
  have hproj : ((U.phaseShift hU.isComplexLinear ω).fixedSubmodule
      (hU.phaseShift ω).isComplexLinear).starProjection v =
      (U.eigenspace hU.isComplexLinear ω).starProjection v := by
    have hcongr : ∀ {K₁ K₂ : Submodule ℂ H} [K₁.HasOrthogonalProjection]
        [K₂.HasOrthogonalProjection], K₁ = K₂ → K₁.starProjection v = K₂.starProjection v := by
      rintro K₁ _ _ _ rfl
      rfl
    exact hcongr (U.eigenspace_eq_fixedSubmodule_phaseShift hU.isComplexLinear ω).symm
  rw [hproj] at h
  refine h.congr fun T ↦ ?_
  congr 1
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [phaseShift_apply_apply]
  congr 2
  ring

end IsUnitary

end TauCeti.Semigroups.StronglyContinuousGroup

end
