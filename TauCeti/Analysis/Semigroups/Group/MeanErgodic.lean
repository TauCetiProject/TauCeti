/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.Eigenspace
public import TauCeti.Analysis.Semigroups.Group.Unitary
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import TauCeti.Analysis.Semigroups.Group.PhaseShift.Unitary

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

* `TauCeti.Semigroups.StronglyContinuousGroup.map_intervalIntegral_orbit`: commuting a C₀-group
  operator past an orbit interval integral shifts the integration bounds.
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

/-- Commuting a C₀-group operator `U s` past an interval integral along an orbit shifts the
integration bounds by `s`. -/
theorem map_intervalIntegral_orbit {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (U : StronglyContinuousGroup X) (s a b : ℝ) (v : X) :
    U s (∫ t in a..b, U t v) = ∫ t in a + s..b + s, U t v := by
  have hint : IntervalIntegrable (fun t : ℝ ↦ U t v) volume a b :=
    (U.continuous_orbit v).intervalIntegrable a b
  rw [← (U s).intervalIntegral_comp_comm hint]
  have hcomp : (fun t : ℝ ↦ U s (U t v)) = fun t : ℝ ↦ U (t + s) v := by
    funext t
    rw [← U.map_add_apply, add_comm]
  rw [hcomp, intervalIntegral.integral_comp_add_right (a := a) (b := b) (f := fun t : ℝ ↦ U t v) s]

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
  intervalIntegral.norm_integral_le_of_norm_le_const fun t _ ↦ (hU.norm_map t v).le

/-- Identify the discrete Birkhoff average of `U 1` acting on `∫ t in (0 : ℝ)..1, U t v` with the
continuous orbit average up to integer time `N`. -/
private theorem birkhoffAverage_eq_inv_smul_intervalIntegral [CompleteSpace H]
    (hU : U.IsUnitary) (N : ℕ) (v : H) :
    birkhoffAverage ℂ (U.toSemigroup.complexLinearOperator hU.isComplexLinear 1) _root_.id N
        (∫ t in (0 : ℝ)..1, U t v) =
      (N : ℝ)⁻¹ • ∫ t in (0 : ℝ)..(N : ℝ), U t v := by
  set f : H →L[ℂ] H := U.toSemigroup.complexLinearOperator hU.isComplexLinear 1
  have hf_iter (k : ℕ) (x : H) : f^[k] x = U (k : ℝ) x := by
    have hcoe : (f : H → H) = U.toSemigroup 1 :=
      funext (U.toSemigroup.complexLinearOperator_apply hU.isComplexLinear 1)
    rw [hcoe, ← pow_apply_eq_iterate, ← U.toSemigroup.map_natCast_mul 1 k, mul_one,
      U.toSemigroup_apply, NNReal.coe_natCast]
  have hterm (k : ℕ) :
      f^[k] (∫ t in (0 : ℝ)..1, U t v) = ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), U t v := by
    rw [hf_iter, U.map_intervalIntegral_orbit (k : ℝ) 0 1 v, zero_add,
      show (1 : ℝ) + (k : ℝ) = ((k + 1 : ℕ) : ℝ) by push_cast; ring]
  rw [birkhoffAverage_apply_congr_ring ℂ ℝ, birkhoffAverage, birkhoffSum]
  congr 1
  simp only [id_eq]
  simp_rw [hterm]
  simpa only [Nat.cast_zero] using intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ ↦ (k : ℝ)) (n := N) fun k _ ↦
      (U.continuous_orbit v).intervalIntegrable k (k + 1 : ℕ)

/-- The difference between the continuous orbit average at `T` and the rescaled orbit average over
`[0, ⌊T⌋₊]` tends to `0` as `T → ∞`. -/
private theorem tendsto_average_sub_floor_zero (hU : U.IsUnitary) (v : H) :
    Tendsto (fun T : ℝ ↦
        (T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) - T⁻¹ • ∫ t in (0 : ℝ)..(⌊T⌋₊ : ℝ), U t v)
      atTop (𝓝 0) := by
  have hint (a b : ℝ) : IntervalIntegrable (fun t : ℝ ↦ U t v) volume a b :=
    (U.continuous_orbit v).intervalIntegrable a b
  have hlim : Tendsto (fun T : ℝ ↦ T⁻¹ * ‖v‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using tendsto_inv_atTop_zero.mul_const ‖v‖
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hNle : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le (zero_le_one.trans hT)
  have hTN : T - (⌊T⌋₊ : ℝ) < 1 := by linarith [Nat.lt_floor_add_one T]
  have hsub :
      (T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) - T⁻¹ • ∫ t in (0 : ℝ)..(⌊T⌋₊ : ℝ), U t v =
        T⁻¹ • ∫ t in (⌊T⌋₊ : ℝ)..T, U t v := by
    rw [← smul_sub, intervalIntegral.integral_interval_sub_left (hint 0 T) (hint 0 (⌊T⌋₊ : ℝ))]
  have hnorm_int : ‖∫ t in (⌊T⌋₊ : ℝ)..T, U t v‖ ≤ ‖v‖ * (T - (⌊T⌋₊ : ℝ)) := by
    simpa only [abs_of_nonneg (sub_nonneg.mpr hNle)] using
      hU.norm_intervalIntegral_orbit_le (⌊T⌋₊ : ℝ) T v
  rw [hsub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hT))]
  calc T⁻¹ * ‖∫ t in (⌊T⌋₊ : ℝ)..T, U t v‖
      ≤ T⁻¹ * (‖v‖ * (T - (⌊T⌋₊ : ℝ))) := by gcongr
    _ ≤ T⁻¹ * (‖v‖ * 1) := by gcongr
    _ = T⁻¹ * ‖v‖ := by ring

/-- Shift-invariance estimate for the continuous orbit average of a unitary C₀-group. -/
private theorem norm_map_average_sub_average_le [CompleteSpace H] (hU : U.IsUnitary)
    (s : ℝ) {T : ℝ} (hT : 0 < T) (v : H) :
    ‖U s (T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) - T⁻¹ • ∫ t in (0 : ℝ)..T, U t v‖ ≤
      T⁻¹ * (2 * (‖v‖ * |s|)) := by
  have hint (a b : ℝ) : IntervalIntegrable (fun t : ℝ ↦ U t v) volume a b :=
    (U.continuous_orbit v).intervalIntegrable a b
  have hdiff : U s (T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) - T⁻¹ • ∫ t in (0 : ℝ)..T, U t v =
      T⁻¹ • ((∫ t in T..(T + s), U t v) - ∫ t in (0 : ℝ)..s, U t v) := by
    rw [(U s).map_smul, U.map_intervalIntegral_orbit s 0 T v, zero_add, ← smul_sub,
      intervalIntegral.integral_interval_sub_interval_comm' (hint s (T + s)) (hint 0 T) (hint s 0)]
  rw [hdiff, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hT.le)]
  gcongr
  have h1 : ‖∫ t in T..(T + s), U t v‖ ≤ ‖v‖ * |s| :=
    (hU.norm_intervalIntegral_orbit_le T (T + s) v).trans_eq (by rw [add_sub_cancel_left])
  have h2 : ‖∫ t in (0 : ℝ)..s, U t v‖ ≤ ‖v‖ * |s| :=
    (hU.norm_intervalIntegral_orbit_le 0 s v).trans_eq (by rw [sub_zero])
  calc ‖(∫ t in T..(T + s), U t v) - ∫ t in (0 : ℝ)..s, U t v‖
      ≤ ‖∫ t in T..(T + s), U t v‖ + ‖∫ t in (0 : ℝ)..s, U t v‖ := norm_sub_le _ _
    _ ≤ 2 * (‖v‖ * |s|) := by linarith

/-- Every vector fixed by `U` is orthogonal to `v - T⁻¹ • ∫ t in (0 : ℝ)..T, U t v` for
`T > 0`. -/
private theorem inner_sub_average_eq_zero_of_mem_fixedSubmodule [CompleteSpace H]
    (hU : U.IsUnitary) {y v : H} (hy : y ∈ U.fixedSubmodule hU.isComplexLinear)
    {T : ℝ} (hT : 0 < T) :
    ⟪y, v - T⁻¹ • ∫ t in (0 : ℝ)..T, U t v⟫_ℂ = 0 := by
  have hy_fix : ∀ t : ℝ, U t y = y := (mem_fixedSubmodule_iff U hU.isComplexLinear y).mp hy
  have hinner_const : (fun t : ℝ ↦ ⟪y, U t v⟫_ℂ) = fun _ : ℝ ↦ ⟪y, v⟫_ℂ := by
    funext t
    rw [← hy_fix t, hU.inner_map_map, hy_fix t]
  have havg : ⟪y, T⁻¹ • ∫ t in (0 : ℝ)..T, U t v⟫_ℂ = ⟪y, v⟫_ℂ := by
    rw [inner_smul_right_eq_smul, U.inner_intervalIntegral_orbit, hinner_const,
      intervalIntegral.integral_const]
    simp [Complex.real_smul, hT.ne']
  rw [inner_sub_right, havg, sub_self]

/-- **Continuous-time von Neumann mean ergodic theorem.** For a unitary C₀-group `U` on a complete
complex Hilbert space `H` and any `v : H`, the time averages `T⁻¹ • ∫ t in (0 : ℝ)..T, U t v`
converge in norm as `T → ∞` to the orthogonal projection of `v` onto the common fixed subspace
`U.fixedSubmodule hU.isComplexLinear`. -/
theorem tendsto_average_starProjection [CompleteSpace H] (hU : U.IsUnitary) (v : H) :
    Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) atTop
      (𝓝 ((U.fixedSubmodule hU.isComplexLinear).starProjection v)) := by
  -- Step 1: Apply Mathlib's discrete Birkhoff mean ergodic theorem to `U 1` on `∫ 0..1, U t v`.
  let f : H →L[ℂ] H := U.toSemigroup.complexLinearOperator hU.isComplexLinear 1
  have hf_norm : ‖f‖ ≤ 1 := by
    rw [← ContinuousLinearMap.norm_restrictScalars (𝕜' := ℝ) f,
      U.toSemigroup.complexLinearOperator_restrictScalars, U.toSemigroup_apply, NNReal.coe_one]
    exact hU.opNorm_le_one 1
  let w₀ : H := ∫ t in (0 : ℝ)..1, U t v
  obtain ⟨L, hbirk⟩ : ∃ L : H, Tendsto (birkhoffAverage ℂ f _root_.id · w₀) atTop (𝓝 L) :=
    ⟨_, f.tendsto_birkhoffAverage_orthogonalProjection hf_norm w₀⟩
  have hN : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹ • ∫ t in (0 : ℝ)..(N : ℝ), U t v) atTop (𝓝 L) :=
    hbirk.congr fun N ↦ hU.birkhoffAverage_eq_inv_smul_intervalIntegral N v
  -- Step 2: Rescale from `N` to `⌊T⌋₊` and bridge the tail `[⌊T⌋₊, T]` to get `avg T → L`.
  have hfloor : Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in (0 : ℝ)..(⌊T⌋₊ : ℝ), U t v) atTop (𝓝 L) := by
    have hrescaled := (tendsto_nat_floor_div_atTop (R := ℝ)).smul (hN.comp tendsto_nat_floor_atTop)
    rw [one_smul] at hrescaled
    refine hrescaled.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hNpos : (0 : ℝ) < (⌊T⌋₊ : ℝ) := by exact_mod_cast Nat.floor_pos.mpr hT
    rw [Function.comp_apply, smul_smul, div_eq_mul_inv, mul_right_comm,
      mul_inv_cancel₀ hNpos.ne', one_mul]
  have hA : Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) atTop (𝓝 L) := by
    simpa only [sub_add_cancel, zero_add] using (hU.tendsto_average_sub_floor_zero v).add hfloor
  -- Step 3: Shift invariance of the time averages shows `L` lies in `fixedSubmodule`.
  have hL_mem : L ∈ U.fixedSubmodule hU.isComplexLinear := by
    rw [mem_fixedSubmodule_iff]
    intro s
    have hUs : Tendsto (fun T : ℝ ↦ U s (T⁻¹ • ∫ t in (0 : ℝ)..T, U t v)) atTop (𝓝 (U s L)) :=
      ((U s).continuous.continuousAt.tendsto).comp hA
    have hlim : Tendsto (fun T : ℝ ↦ T⁻¹ * (2 * (‖v‖ * |s|))) atTop (𝓝 0) := by
      simpa only [zero_mul] using tendsto_inv_atTop_zero.mul_const (2 * (‖v‖ * |s|))
    have hshift_zero : Tendsto (fun T : ℝ ↦
        U s (T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) - T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) atTop (𝓝 0) :=
      squeeze_zero_norm'
        ((eventually_gt_atTop (0 : ℝ)).mono fun _ hT ↦ hU.norm_map_average_sub_average_le s hT v)
        hlim
    exact sub_eq_zero.mp (tendsto_nhds_unique (hUs.sub hA) hshift_zero)
  -- Step 4: Every fixed vector is orthogonal to `v - L`, passing `⟪y, v - avg T⟫ = 0` to `T → ∞`.
  have hL_orth : v - L ∈ (U.fixedSubmodule hU.isComplexLinear)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    have hlim : Tendsto (fun T : ℝ ↦ ⟪y, v - T⁻¹ • ∫ t in (0 : ℝ)..T, U t v⟫_ℂ)
        atTop (𝓝 ⟪y, v - L⟫_ℂ) :=
      ((innerSL ℂ y).continuous.continuousAt.tendsto).comp (tendsto_const_nhds.sub hA)
    have hconst : ∀ᶠ T : ℝ in atTop, ⟪y, v - T⁻¹ • ∫ t in (0 : ℝ)..T, U t v⟫_ℂ = 0 :=
      (eventually_gt_atTop (0 : ℝ)).mono fun _ hT ↦
        hU.inner_sub_average_eq_zero_of_mem_fixedSubmodule hy hT
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hconst.mono fun _ h ↦ h.symm))
  -- Step 5: Identify `L` as the orthogonal projection of `v` onto `fixedSubmodule`.
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
