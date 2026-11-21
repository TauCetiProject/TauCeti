/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Semigroups.Group.Eigenspace
import Mathlib.Analysis.InnerProductSpace.MeanErgodic

/-!
# Continuous-time mean ergodic projection for unitary C₀-groups

When `U` is a unitary C₀-group on a complete complex Hilbert space `H`, the continuous-time
von Neumann mean ergodic theorem holds without separability: the time averages
`T⁻¹ • ∫ t in (0 : ℝ)..T, U t v` converge in norm as `T → ∞` to the orthogonal projection of `v`
onto the common fixed subspace (`IsUnitary.tendsto_average_starProjection`), and the twisted
averages `T⁻¹ • ∫ t in (0 : ℝ)..T, exp (-(ω * t * I)) • U t v` converge in norm to the orthogonal
projection onto the common eigenspace at `ω` (`IsUnitary.tendsto_twistedAverage_starProjection`).

The proof reduces the continuous-time averages to discrete Birkhoff averages of `U 1` acting on
`∫ t in (0 : ℝ)..1, U t v` via Mathlib's
`ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection`, extends to real endpoints, and
identifies the limit with the orthogonal projection onto `U.fixedSubmodule hU.isComplexLinear` using
the shift invariance of the time averages.

## Main results

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

namespace IsUnitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {U : StronglyContinuousGroup H}

/-- **Continuous-time von Neumann mean ergodic theorem.** For a unitary C₀-group `U` on a complete
complex Hilbert space `H` and any `v : H`, the time averages `T⁻¹ • ∫ t in (0 : ℝ)..T, U t v`
converge in norm as `T → ∞` to the orthogonal projection of `v` onto the common fixed subspace
`U.fixedSubmodule hU.isComplexLinear`. -/
theorem tendsto_average_starProjection [CompleteSpace H] (hU : U.IsUnitary) (v : H) :
    Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) atTop
      (𝓝 ((U.fixedSubmodule hU.isComplexLinear).starProjection v)) := by
  let f : H →L[ℂ] H :=
    { toFun := U 1
      map_add' := (U 1).map_add
      map_smul' := hU.map_smul 1
      cont := (U 1).continuous }
  have hf_norm : ‖f‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
    simpa [f] using (hU.norm_map 1 x).le
  let w₀ : H := ∫ t in (0 : ℝ)..1, U t v
  obtain ⟨L, hbirk⟩ : ∃ L : H, Tendsto (birkhoffAverage ℂ f _root_.id · w₀) atTop (𝓝 L) :=
    ⟨_, f.tendsto_birkhoffAverage_orthogonalProjection hf_norm w₀⟩
  have hint (a b : ℝ) : IntervalIntegrable (fun t : ℝ ↦ U t v) volume a b :=
    (U.continuous_orbit v).intervalIntegrable a b
  have hf_iter (k : ℕ) (x : H) : f^[k] x = U (k : ℝ) x := by
    induction k generalizing x with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, show ((k + 1 : ℕ) : ℝ) = 1 + (k : ℝ) by push_cast; ring,
        U.map_add_apply]
      rfl
  have hbirk_eq (N : ℕ) :
      birkhoffAverage ℂ f _root_.id N w₀ = (N : ℝ)⁻¹ • ∫ t in (0 : ℝ)..(N : ℝ), U t v := by
    rw [birkhoffAverage, birkhoffSum, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
      Complex.coe_smul]
    congr 1
    have hterm (k : ℕ) : f^[k] w₀ = ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), U t v := by
      rw [hf_iter]
      dsimp only [w₀]
      rw [← (U (k : ℝ)).intervalIntegral_comp_comm (hint 0 1)]
      have hcomp : (fun t : ℝ ↦ U (k : ℝ) (U t v)) = fun t : ℝ ↦ U (t + (k : ℝ)) v := by
        funext t
        rw [← U.map_add_apply, add_comm]
      rw [hcomp, intervalIntegral.integral_comp_add_right (a := 0) (b := 1)
        (f := fun t : ℝ ↦ U t v) (k : ℝ), zero_add, show (1 : ℝ) + (k : ℝ) = ((k + 1 : ℕ) : ℝ) by
        push_cast; ring]
    simp only [id_eq]
    simp_rw [hterm]
    simpa only [Nat.cast_zero] using intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ ↦ (k : ℝ)) (n := N) fun k _ ↦ hint k (k + 1 : ℕ)
  have hN : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹ • ∫ t in (0 : ℝ)..(N : ℝ), U t v) atTop (𝓝 L) := by
    simpa only [hbirk_eq] using hbirk
  have hfloor : Tendsto (fun T : ℝ ↦ (⌊T⌋₊ : ℝ)⁻¹ • ∫ t in (0 : ℝ)..(⌊T⌋₊ : ℝ), U t v)
      atTop (𝓝 L) :=
    hN.comp tendsto_nat_floor_atTop
  have htail : Tendsto (fun T : ℝ ↦
      (T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) -
        (⌊T⌋₊ : ℝ)⁻¹ • ∫ t in (0 : ℝ)..(⌊T⌋₊ : ℝ), U t v) atTop (𝓝 0) := by
    have hlim : Tendsto (fun T : ℝ ↦ T⁻¹ * (2 * ‖v‖)) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.mul_const (2 * ‖v‖)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    set N : ℕ := ⌊T⌋₊
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast Nat.floor_pos.mpr hT
    have hNle : (N : ℝ) ≤ T := Nat.floor_le (zero_le_one.trans hT)
    have hTN : T - (N : ℝ) < 1 := by
      linarith [Nat.lt_floor_add_one T]
    have hsub :
        (T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) -
          (N : ℝ)⁻¹ • ∫ t in (0 : ℝ)..(N : ℝ), U t v =
          (T⁻¹ • (∫ t in (N : ℝ)..T, U t v)) +
            (T⁻¹ - (N : ℝ)⁻¹) • ∫ t in (0 : ℝ)..(N : ℝ), U t v := by
      have hadj := (intervalIntegral.integral_add_adjacent_intervals
        (hint 0 (N : ℝ)) (hint (N : ℝ) T)).symm
      rw [hadj, smul_add, sub_smul]
      abel
    have h1 : ‖T⁻¹ • ∫ t in (N : ℝ)..T, U t v‖ ≤ T⁻¹ * ‖v‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hT))]
      have hnorm_int : ‖∫ t in (N : ℝ)..T, U t v‖ ≤ ‖v‖ * |T - (N : ℝ)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun t _ ↦ (hU.norm_map t v).le
      rw [abs_of_nonneg (sub_nonneg.mpr hNle)] at hnorm_int
      calc T⁻¹ * ‖∫ t in (N : ℝ)..T, U t v‖
          ≤ T⁻¹ * (‖v‖ * (T - (N : ℝ))) := by gcongr
        _ ≤ T⁻¹ * (‖v‖ * 1) := by gcongr
        _ = T⁻¹ * ‖v‖ := by ring
    have h2 : ‖(T⁻¹ - (N : ℝ)⁻¹) • ∫ t in (0 : ℝ)..(N : ℝ), U t v‖ ≤ T⁻¹ * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have hcoef : |T⁻¹ - (N : ℝ)⁻¹| = (T - (N : ℝ)) / (T * (N : ℝ)) := by
        have hle : T⁻¹ ≤ (N : ℝ)⁻¹ := inv_anti₀ hNpos hNle
        rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub,
          inv_sub_inv hNpos.ne' (zero_lt_one.trans_le hT).ne', mul_comm (N : ℝ) T]
      have hnorm_int : ‖∫ t in (0 : ℝ)..(N : ℝ), U t v‖ ≤ ‖v‖ * (N : ℝ) := by
        simpa [sub_zero, abs_of_pos hNpos] using
          intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (N : ℝ))
            (f := fun t : ℝ ↦ U t v) (C := ‖v‖) fun t _ ↦ (hU.norm_map t v).le
      rw [hcoef]
      calc (T - (N : ℝ)) / (T * (N : ℝ)) * ‖∫ t in (0 : ℝ)..(N : ℝ), U t v‖
          ≤ (T - (N : ℝ)) / (T * (N : ℝ)) * (‖v‖ * (N : ℝ)) := by gcongr
        _ = (T - (N : ℝ)) * T⁻¹ * ‖v‖ := by field_simp [hNpos.ne', (zero_lt_one.trans_le hT).ne']
        _ ≤ 1 * T⁻¹ * ‖v‖ := by gcongr
        _ = T⁻¹ * ‖v‖ := by ring
    rw [hsub]
    have htri := norm_add_le (T⁻¹ • ∫ t in (N : ℝ)..T, U t v)
      ((T⁻¹ - (N : ℝ)⁻¹) • ∫ t in (0 : ℝ)..(N : ℝ), U t v)
    linarith [htri, h1, h2]
  have hA : Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) atTop (𝓝 L) := by
    simpa only [sub_add_cancel, zero_add] using htail.add hfloor
  have hL_mem : L ∈ U.fixedSubmodule hU.isComplexLinear := by
    rw [mem_fixedSubmodule_iff]
    intro s
    have hUs : Tendsto (fun T : ℝ ↦ U s (T⁻¹ • ∫ t in (0 : ℝ)..T, U t v)) atTop (𝓝 (U s L)) :=
      ((U s).continuous.continuousAt.tendsto).comp hA
    have hshift_zero : Tendsto (fun T : ℝ ↦
        U s (T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) - T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) atTop (𝓝 0) := by
      have hlim : Tendsto (fun T : ℝ ↦ T⁻¹ * (2 * (‖v‖ * |s|))) atTop (𝓝 0) := by
        simpa using tendsto_inv_atTop_zero.mul_const (2 * (‖v‖ * |s|))
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      have hdiff : U s (T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) - T⁻¹ • ∫ t in (0 : ℝ)..T, U t v =
          T⁻¹ • ((∫ t in T..(T + s), U t v) - ∫ t in (0 : ℝ)..s, U t v) := by
        have hsplit : (fun t : ℝ ↦ U s (U t v)) = fun t : ℝ ↦ U (t + s) v := by
          funext t
          rw [← U.map_add_apply, add_comm]
        have hshift : ∫ t in (0 : ℝ)..T, U (t + s) v = ∫ t in s..(T + s), U t v := by
          rw [intervalIntegral.integral_comp_add_right (a := 0) (b := T)
            (f := fun t : ℝ ↦ U t v) s, zero_add]
        rw [(U s).map_smul, ← (U s).intervalIntegral_comp_comm (hint 0 T), hsplit, hshift,
          ← smul_sub, intervalIntegral.integral_interval_sub_interval_comm' (hint s (T + s))
            (hint 0 T) (hint s 0)]
      rw [hdiff, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hT.le)]
      gcongr
      have h1 : ‖∫ t in T..(T + s), U t v‖ ≤ ‖v‖ * |s| := by
        simpa [add_sub_cancel_left] using
          intervalIntegral.norm_integral_le_of_norm_le_const (a := T) (b := T + s)
            (f := fun t : ℝ ↦ U t v) (C := ‖v‖) fun t _ ↦ (hU.norm_map t v).le
      have h2 : ‖∫ t in (0 : ℝ)..s, U t v‖ ≤ ‖v‖ * |s| := by
        simpa [sub_zero] using
          intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := s)
            (f := fun t : ℝ ↦ U t v) (C := ‖v‖) fun t _ ↦ (hU.norm_map t v).le
      calc ‖(∫ t in T..(T + s), U t v) - ∫ t in (0 : ℝ)..s, U t v‖
          ≤ ‖∫ t in T..(T + s), U t v‖ + ‖∫ t in (0 : ℝ)..s, U t v‖ := norm_sub_le _ _
        _ ≤ 2 * (‖v‖ * |s|) := by linarith
    have hdiff_lim : Tendsto (fun T : ℝ ↦
        U s (T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) - T⁻¹ • ∫ t in (0 : ℝ)..T, U t v)
        atTop (𝓝 (U s L - L)) := hUs.sub hA
    exact sub_eq_zero.mp (tendsto_nhds_unique hdiff_lim hshift_zero)
  have hL_orth : v - L ∈ (U.fixedSubmodule hU.isComplexLinear)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    have hlim : Tendsto (fun T : ℝ ↦ ⟪y, T⁻¹ • ∫ t in (0 : ℝ)..T, U t v⟫_ℂ) atTop (𝓝 ⟪y, L⟫_ℂ) :=
      ((innerSL ℂ y).continuous.continuousAt.tendsto).comp hA
    have hconst : ∀ᶠ T : ℝ in atTop, ⟪y, T⁻¹ • ∫ t in (0 : ℝ)..T, U t v⟫_ℂ = ⟪y, v⟫_ℂ := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      have hy_fix : ∀ t : ℝ, U t y = y := (mem_fixedSubmodule_iff U hU.isComplexLinear y).mp hy
      have hcomm := (innerSL ℂ y).intervalIntegral_comp_comm (hint 0 T)
      rw [inner_smul_right_eq_smul, ← innerSL_apply_apply ℂ y, ← hcomm]
      have hinner_const : (fun t : ℝ ↦ (innerSL ℂ y) (U t v)) = fun _ : ℝ ↦ ⟪y, v⟫_ℂ := by
        funext t
        rw [innerSL_apply_apply, ← hy_fix t, hU.inner_map_map, hy_fix t]
      rw [hinner_const, intervalIntegral.integral_const, sub_zero, Complex.real_smul,
        Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hT.ne',
        Complex.ofReal_one, one_mul]
    have heq : ⟪y, L⟫_ℂ = ⟪y, v⟫_ℂ :=
      tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hconst.mono fun _ h ↦ h.symm))
    rw [inner_sub_right, heq, sub_self]
  have hL_proj : L = (U.fixedSubmodule hU.isComplexLinear).starProjection v :=
    (Submodule.eq_starProjection_of_mem_orthogonal hL_mem hL_orth).symm
  rwa [hL_proj] at hA

/-- **Twisted continuous-time mean ergodic projection.** For a unitary C₀-group `U` on a complete
complex Hilbert space `H`, an angular frequency `ω : ℝ`, and `v : H`, the twisted averages
`T⁻¹ • ∫ t in (0 : ℝ)..T, exp (-(ω * t * I)) • U t v` converge in norm as `T → ∞` to the orthogonal
projection of `v` onto the common eigenspace `U.eigenspace hU.isComplexLinear ω`. -/
theorem tendsto_twistedAverage_starProjection [CompleteSpace H] (hU : U.IsUnitary) (ω : ℝ) (v : H) :
    Tendsto (fun T : ℝ ↦
        T⁻¹ • ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) • U t v)
      atTop (𝓝 ((U.eigenspace hU.isComplexLinear ω).starProjection v)) := by
  have h := (hU.phaseShift ω).tendsto_average_starProjection v
  have hproj : ((U.phaseShift hU.isComplexLinear ω).fixedSubmodule
      (hU.phaseShift ω).isComplexLinear).starProjection v =
      (U.eigenspace hU.isComplexLinear ω).starProjection v := by
    have heq := (U.eigenspace_eq_fixedSubmodule_phaseShift hU.isComplexLinear ω).symm
    refine (Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_).symm
    · rw [← heq]
      exact Submodule.starProjection_apply_mem _ v
    · rw [← heq]
      exact Submodule.sub_starProjection_mem_orthogonal v
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
