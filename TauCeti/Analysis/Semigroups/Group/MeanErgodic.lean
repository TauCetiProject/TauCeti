/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import TauCeti.Analysis.PositiveDefinite.AddGroup
public import TauCeti.Analysis.Semigroups.Group.PhaseShift
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.RepresentationTheory.Continuous.Basic
import TauCeti.Analysis.Bochner.CharFun.Bochner
import TauCeti.Analysis.InnerProductSpace.Projection.RestrictScalars
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.RepresentationTheory.Continuous.Invariants
import TauCeti.RepresentationTheory.Continuous.Unitary.PositiveDefinite

/-!
# Continuous-time mean ergodic theorem and spectral atomic mass

This file develops the continuous-time von Neumann mean ergodic theorem and the spectral
atomic-mass identity for strongly continuous one-parameter groups (`StronglyContinuousGroup`).

On a real normed space `X`, the common fixed space `U.fixedSpace` of a C₀-group `U` is a closed
subspace, and the orbit averages `T⁻¹ • ∫ t in 0..T, U t v` telescope on coboundaries `U s v - v`.
When `U` contracts in both time directions (`∀ t, ‖U t‖ ≤ 1`) on a real Hilbert space `H`,
splitting the orbit integral into unit intervals reduces convergence to Mathlib's discrete mean
ergodic theorem for `U 1` applied to `∫ t in 0..1, U t v`; the coboundary estimate shows the
limit is fixed at every time, and pairing with fixed vectors identifies it with
`U.fixedSpace.starProjection v`.

On a complex normed space, a complex-linear C₀-group has closed common eigenspaces
`U.eigenspace hU ω = {u | ∀ t, U t u = exp (i ω t) • u}`, defined as the invariants of the
phase-shifted group `U.phaseShift hU ω`. For a unitary C₀-group on a complex Hilbert space,
transferring the real-Hilbert mean ergodic theorem through `U.phaseShift` and
`Submodule.starProjection_restrictScalars_apply` gives convergence of the twisted averages
`(T⁻¹ : ℂ) • ∫ t in 0..T, exp (-i ω t) • U t v` to `(U.eigenspace _ ω).starProjection v`.

Finally, for a unitary C₀-group, the correlation function `t ↦ ⟪v, U t v⟫_ℂ` is continuous and
positive definite, so Bochner's theorem yields a unique finite spectral measure `σ` with
`⟪v, U t v⟫_ℂ = charFun σ t`. Fubini's theorem expresses the squared norm of each twisted average
as an integral against `σ`, and dominated convergence identifies the squared norm of the
eigenspace projection with the atomic mass `σ.real {ω}`.

## Main definitions

In namespace `TauCeti.Semigroups.StronglyContinuousGroup`:

* `fixedSpace`: the closed real submodule of vectors fixed by every operator of a C₀-group.
* `eigenspace`: the closed complex submodule of common eigenvectors with angular frequency `ω : ℝ`.

## Main results

In namespace `TauCeti.Semigroups.StronglyContinuousGroup`:

* `tendsto_average_orbit_starProjection_fixedSpace`: continuous-time von Neumann mean ergodic
  theorem for a contractive C₀-group on a real Hilbert space.
* `tendsto_twistedAverage_starProjection_eigenspace`: twisted mean ergodic theorem for a unitary
  C₀-group on a complex Hilbert space.
* `IsUnitary.existsUnique_spectralMeasure`: existence and uniqueness of the Bochner spectral
  measure of a vector under a unitary C₀-group.
* `norm_twistedAverage_sq_eq_integral`: spectral representation of the squared norm of a twisted
  average.
* `norm_starProjection_eigenspace_sq_eq_measure_singleton`: the squared norm of the eigenspace
  projection equals the spectral atomic mass `σ.real {ω}`.
* `exists_tendsto_twistedAverage`: bundled continuous-time mean ergodic projection and spectral
  atomic-mass theorem at frequency `2 * π * a`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section V.4 (mean ergodic semigroups).
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Theorem II.11 (von Neumann ergodic theorem) and Section VIII.4 (Stone's theorem).
* M. Hochman, *Notes on Ergodic Theory* (2012), Section 6.6, Lemma 6.6.2 and Proposition 6.6.3
  (discrete analogues for `ℤ`-actions).
-/

public section

noncomputable section

open ComplexConjugate Filter MeasureTheory
open scoped ComplexOrder InnerProductSpace Topology

namespace TauCeti.Semigroups.StronglyContinuousGroup

/-! ## Fixed spaces and orbit averages on real normed spaces -/

section RealNormed

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Package a real C₀-group as a `ContRepresentation ℝ (Multiplicative ℝ) X`. -/
private def toRealContRep (U : StronglyContinuousGroup X) :
    ContRepresentation ℝ (Multiplicative ℝ) X :=
  .ofMonoidHom
    { toFun g := U (Multiplicative.toAdd g)
      map_one' := U.map_zero
      map_mul' g h := U.map_add (Multiplicative.toAdd g) (Multiplicative.toAdd h) }

/-- The real submodule of vectors fixed by every operator of a C₀-group. -/
def fixedSpace (U : StronglyContinuousGroup X) : Submodule ℝ X :=
  U.toRealContRep.invariants

/-- Membership in `fixedSpace` means invariance under every group operator. -/
@[simp]
theorem mem_fixedSpace_iff (U : StronglyContinuousGroup X) (x : X) :
    x ∈ U.fixedSpace ↔ ∀ t : ℝ, U t x = x := by
  rw [fixedSpace, ContRepresentation.mem_invariants]
  exact ⟨fun h t => h (Multiplicative.ofAdd t), fun h g => h (Multiplicative.toAdd g)⟩

/-- The common fixed space of a C₀-group is closed. -/
theorem isClosed_fixedSpace (U : StronglyContinuousGroup X) :
    IsClosed (U.fixedSpace : Set X) :=
  U.toRealContRep.isClosed_invariants

instance fixedSpace.completeSpace [CompleteSpace X] (U : StronglyContinuousGroup X) :
    CompleteSpace U.fixedSpace :=
  inferInstanceAs (CompleteSpace U.toRealContRep.invariants)

/-- Time reversal preserves the common fixed space. -/
@[simp]
theorem fixedSpace_reflect (U : StronglyContinuousGroup X) :
    U.reflect.fixedSpace = U.fixedSpace := by
  ext x
  simp only [mem_fixedSpace_iff, reflect_apply]
  exact ⟨fun h t => by simpa only [neg_neg] using h (-t), fun h t => h (-t)⟩

/-- Every nonzero time average of a fixed vector equals the vector itself. -/
theorem average_orbit_of_mem_fixedSpace [CompleteSpace X] (U : StronglyContinuousGroup X)
    {w : X} (hw : w ∈ U.fixedSpace) {T : ℝ} (hT : T ≠ 0) :
    T⁻¹ • ∫ t in (0 : ℝ)..T, U t w = w := by
  have hfun : (fun t : ℝ => U t w) = fun _ => w := funext fun t => (U.mem_fixedSpace_iff w).mp hw t
  rw [hfun, intervalIntegral.integral_const, sub_zero, smul_smul, inv_mul_cancel₀ hT, one_smul]

/-- Telescoping identity for the interval integral of a coboundary `U s v - v`. -/
theorem intervalIntegral_orbit_apply_sub (U : StronglyContinuousGroup X) (s T : ℝ) (v : X) :
    (∫ t in (0 : ℝ)..T, U t (U s v - v)) =
      (∫ t in T..(T + s), U t v) - ∫ t in (0 : ℝ)..s, U t v := by
  have hcont : Continuous fun t : ℝ => U t v := U.continuous_orbit v
  have hshift : Continuous fun t : ℝ => U (t + s) v :=
    hcont.comp (continuous_id.add continuous_const)
  have hpoint : (fun t : ℝ => U t (U s v - v)) = fun t : ℝ => U (t + s) v - U t v := by
    funext t
    rw [(U t).map_sub, U.map_add_apply]
  rw [hpoint, intervalIntegral.integral_sub (hshift.intervalIntegrable 0 T)
    (hcont.intervalIntegrable 0 T),
    intervalIntegral.integral_comp_add_right (f := fun t : ℝ => U t v) s, zero_add]
  exact intervalIntegral.integral_interval_sub_interval_comm'
    (hcont.intervalIntegrable s (T + s)) (hcont.intervalIntegrable 0 T)
    (hcont.intervalIntegrable s 0)

/-- The interval integral along an orbit of a contractive C₀-group grows at most linearly in the
interval length. -/
theorem norm_intervalIntegral_orbit_le (U : StronglyContinuousGroup X)
    (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1) (a b : ℝ) (v : X) :
    ‖∫ t in a..b, U t v‖ ≤ ‖v‖ * |b - a| :=
  intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => by
    rw [U.norm_map_apply_eq_of_norm_le_one t (hnorm t) (hnorm (-t))]

/-- The time average of an orbit of a contractive C₀-group is a contraction at every `T : ℝ`. -/
theorem norm_average_orbit_le (U : StronglyContinuousGroup X)
    (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1) (T : ℝ) (v : X) :
    ‖T⁻¹ • ∫ t in (0 : ℝ)..T, U t v‖ ≤ ‖v‖ := by
  by_cases hT : T = 0
  · simp [hT]
  rw [← show (∫ t in (0 : ℝ)..1, U (T * t) v) = T⁻¹ • ∫ t in (0 : ℝ)..T, U t v by
      simpa only [mul_zero, mul_one] using
        intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) (fun t => U t v) hT]
  simpa only [sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := ‖v‖) fun t _ =>
      (U.norm_map_apply_eq_of_norm_le_one (T * t) (hnorm _) (hnorm _) v).le

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
        ≤ |T|⁻¹ * (2 * |s| * ‖v‖) :=
      mul_le_mul_of_nonneg_left hsub (inv_nonneg.mpr (abs_nonneg T))
    _ = 2 * |s| * ‖v‖ / |T| := by rw [div_eq_inv_mul]

/-- The time averages of every coboundary `U s v - v` converge to `0`. -/
theorem tendsto_average_orbit_apply_sub (U : StronglyContinuousGroup X)
    (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1) (s : ℝ) (v : X) :
    Tendsto (fun T : ℝ => T⁻¹ • ∫ t in (0 : ℝ)..T, U t (U s v - v)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun T : ℝ => 2 * |s| * ‖v‖ / T) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    simpa only [abs_of_pos hT] using U.norm_average_orbit_apply_sub_le hnorm s T v
  · simpa only [div_eq_mul_inv, mul_zero] using
      tendsto_inv_atTop_zero.const_mul (2 * |s| * ‖v‖)

private theorem iterate_one_apply (U : StronglyContinuousGroup X) (n : ℕ) (x : X) :
    (U 1)^[n] x = U (n : ℝ) x := by
  have hpow : (U.toRealContRep (Multiplicative.ofAdd (1 : ℝ)) ^ n) x =
      U.toRealContRep (Multiplicative.ofAdd (1 : ℝ) ^ n) x :=
    congrArg (fun T => T x) (map_pow U.toRealContRep (Multiplicative.ofAdd (1 : ℝ)) n).symm
  rw [← FunLike.coe_pow_eq_iterate, show U 1 = U.toRealContRep (Multiplicative.ofAdd (1 : ℝ))
    from rfl, hpow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one]
  rfl

private theorem birkhoffAverage_one_intervalIntegral (U : StronglyContinuousGroup X)
    [CompleteSpace X] (N : ℕ) (v : X) :
    birkhoffAverage ℝ (U 1) id N (∫ t in (0 : ℝ)..1, U t v) =
      (N : ℝ)⁻¹ • ∫ t in (0 : ℝ)..(N : ℝ), U t v := by
  have hterm (k : ℕ) :
      (U 1)^[k] (∫ t in (0 : ℝ)..1, U t v) =
        ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), U t v := by
    rw [U.iterate_one_apply k,
      ← (U (k : ℝ)).intervalIntegral_comp_comm ((U.continuous_orbit v).intervalIntegrable 0 1)]
    have hfun : (fun t : ℝ => U (k : ℝ) (U t v)) = fun t : ℝ => U (t + (k : ℝ)) v :=
      funext fun t => (U.map_comm (k : ℝ) t v).trans (U.map_add_apply t (k : ℝ) v).symm
    rw [hfun, intervalIntegral.integral_comp_add_right (f := fun t : ℝ => U t v) (k : ℝ),
      zero_add, add_comm 1 (k : ℝ), Nat.cast_succ]
  rw [birkhoffAverage, birkhoffSum]
  congr 1
  simp_rw [id_eq, hterm]
  simpa only [Nat.cast_zero] using
    intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ))
      (f := fun t : ℝ => U t v) fun k _ => (U.continuous_orbit v).intervalIntegrable _ _

/-- Commutation of a group operator with orbit averaging produces the averaged coboundary. -/
private theorem average_orbit_apply_sub [CompleteSpace X] (U : StronglyContinuousGroup X)
    (s T : ℝ) (v : X) :
    U s (T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) - T⁻¹ • ∫ t in (0 : ℝ)..T, U t v =
      T⁻¹ • ∫ t in (0 : ℝ)..T, U t (U s v - v) := by
  have hcont := U.continuous_orbit v
  have hcomm : U s (∫ t in (0 : ℝ)..T, U t v) = ∫ t in (0 : ℝ)..T, U t (U s v) := by
    rw [← (U s).intervalIntegral_comp_comm (hcont.intervalIntegrable 0 T)]
    exact intervalIntegral.integral_congr fun t _ => U.map_comm s t v
  have hsub : (fun t : ℝ => U t (U s v - v)) = fun t : ℝ => U t (U s v) - U t v :=
    funext fun t => (U t).map_sub (U s v) v
  rw [map_smul, hcomm, hsub, intervalIntegral.integral_sub
    ((U.continuous_orbit (U s v)).intervalIntegrable 0 T) (hcont.intervalIntegrable 0 T),
    smul_sub]

end RealNormed

/-! ## Real Hilbert-space mean ergodic theorem -/

section RealInnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem tendsto_average_orbit_birkhoff (U : StronglyContinuousGroup H)
    (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1) (v : H) :
    Tendsto (fun T : ℝ => T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) atTop
      (𝓝 (((U 1).eqLocus (1 : H →L[ℝ] H)).orthogonalProjectionOnto
        (∫ t in (0 : ℝ)..1, U t v) : H)) := by
  let v₁ : H := ∫ t in (0 : ℝ)..1, U t v
  let w : H := ((U 1).eqLocus (1 : H →L[ℝ] H)).orthogonalProjectionOnto v₁
  have hBirkhoff : Tendsto (fun T : ℝ => T⁻¹ • ∫ t in (0 : ℝ)..(⌊T⌋₊ : ℝ), U t v) atTop
      (𝓝 w) := by
    have hdisc := ((U 1).tendsto_birkhoffAverage_orthogonalProjection (hnorm 1) v₁).comp
      (tendsto_nat_floor_atTop (α := ℝ))
    have hscaled : Tendsto (fun T : ℝ =>
        ((⌊T⌋₊ : ℝ) / T) • birkhoffAverage ℝ (U 1) id ⌊T⌋₊ v₁) atTop (𝓝 ((1 : ℝ) • w)) :=
      (tendsto_nat_floor_div_atTop (R := ℝ)).smul hdisc
    rw [one_smul] at hscaled
    refine hscaled.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hN0 : (⌊T⌋₊ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.floor_pos.mpr hT).ne'
    rw [U.birkhoffAverage_one_intervalIntegral ⌊T⌋₊ v, smul_smul]
    congr 1
    field_simp
  have htail : Tendsto (fun T : ℝ => T⁻¹ • ∫ t in (⌊T⌋₊ : ℝ)..T, U t v) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun T : ℝ => ‖v‖ / T) ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
      have hle : |T - (⌊T⌋₊ : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg (sub_nonneg.mpr (Nat.floor_le hTpos.le))]
        linarith [Nat.lt_floor_add_one T]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hTpos]
      calc
        T⁻¹ * ‖∫ t in (⌊T⌋₊ : ℝ)..T, U t v‖
            ≤ T⁻¹ * (‖v‖ * |T - (⌊T⌋₊ : ℝ)|) :=
          mul_le_mul_of_nonneg_left (U.norm_intervalIntegral_orbit_le hnorm _ _ v)
            (inv_nonneg.mpr hTpos.le)
        _ ≤ T⁻¹ * (‖v‖ * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (norm_nonneg v))
            (inv_nonneg.mpr hTpos.le)
        _ = ‖v‖ / T := by rw [mul_one, div_eq_inv_mul]
    · simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul ‖v‖
  have hadd := hBirkhoff.add htail
  rw [add_zero] at hadd
  refine hadd.congr fun T => ?_
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
  have hpt : (fun t : ℝ => ⟪U t v, u⟫_ℝ) = fun _ => ⟪v, u⟫_ℝ := by
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
    Tendsto (fun T : ℝ => T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) atTop
      (𝓝 (U.fixedSpace.starProjection v)) := by
  let w : H := ((U 1).eqLocus (1 : H →L[ℝ] H)).orthogonalProjectionOnto
    (∫ t in (0 : ℝ)..1, U t v)
  have htend : Tendsto (fun T : ℝ => T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) atTop (𝓝 w) :=
    U.tendsto_average_orbit_birkhoff hnorm v
  have hw_fixed : w ∈ U.fixedSpace := by
    rw [mem_fixedSpace_iff]
    intro s
    have h1 : Tendsto (fun T : ℝ => U s (T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) -
        T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) atTop (𝓝 (U s w - w)) :=
      (((U s).continuous.tendsto w).comp htend).sub htend
    have h2 : Tendsto (fun T : ℝ => U s (T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) -
        T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) atTop (𝓝 0) :=
      (U.tendsto_average_orbit_apply_sub hnorm s v).congr fun T =>
        (U.average_orbit_apply_sub s T v).symm
    exact sub_eq_zero.mp (tendsto_nhds_unique h1 h2)
  have hproj : U.fixedSpace.starProjection v = w := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hw_fixed fun u hu => ?_
    have hlim : Tendsto (fun T : ℝ => ⟪T⁻¹ • ∫ t in (0 : ℝ)..T, U t v, u⟫_ℝ) atTop (𝓝 ⟪w, u⟫_ℝ) :=
      htend.inner tendsto_const_nhds
    have hconst : Tendsto (fun T : ℝ => ⟪T⁻¹ • ∫ t in (0 : ℝ)..T, U t v, u⟫_ℝ) atTop
        (𝓝 ⟪v, u⟫_ℝ) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
        exact (U.inner_average_orbit_of_mem_fixedSpace hnorm v hu hT.ne').symm)
    rw [inner_sub_left, tendsto_nhds_unique hconst hlim, sub_self]
  rwa [hproj]

end RealInnerProduct

/-! ## Common eigenspaces on complex normed spaces -/

section ComplexNormed

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Package a complex-linear C₀-group as a `ContRepresentation ℂ (Multiplicative ℝ) X`. -/
private def toComplexContRep (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) :
    ContRepresentation ℂ (Multiplicative ℝ) X :=
  .ofMonoidHom
    { toFun g :=
        { toFun := U (Multiplicative.toAdd g)
          map_add' := (U (Multiplicative.toAdd g)).map_add
          map_smul' := U.map_smul_of_isComplexLinear hU (Multiplicative.toAdd g)
          cont := (U (Multiplicative.toAdd g)).continuous }
      map_one' := by ext x; simp
      map_mul' g h := by ext x; simp }

private theorem toComplexContRep_apply (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (g : Multiplicative ℝ) (x : X) :
    U.toComplexContRep hU g x = U (Multiplicative.toAdd g) x :=
  rfl

/-- The complex submodule of common eigenvectors of a complex-linear C₀-group at angular
frequency `ω : ℝ`: the vectors satisfying `U t u = exp (i ω t) • u` for all `t : ℝ`. -/
def eigenspace (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) :
    Submodule ℂ X :=
  ((U.phaseShift hU ω).toComplexContRep (U.phaseShift_isComplexLinear hU ω)).invariants

/-- Membership in `eigenspace` means satisfying the common eigenfunction equation at all real
times. -/
@[simp]
theorem mem_eigenspace_iff (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear)
    (ω : ℝ) (u : X) :
    u ∈ U.eigenspace hU ω ↔ ∀ t : ℝ, U t u = Complex.exp (ω * t * Complex.I) • u := by
  rw [eigenspace, ContRepresentation.mem_invariants]
  simp only [toComplexContRep_apply, phaseShift_apply_apply]
  refine ⟨fun h t => ?_, fun h g => ?_⟩
  · have ht : Complex.exp (-(ω * t * Complex.I)) • U t u = u := h (Multiplicative.ofAdd t)
    calc
      U t u = Complex.exp (ω * t * Complex.I) •
          (Complex.exp (-(ω * t * Complex.I)) • U t u) := by
        rw [smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]
      _ = Complex.exp (ω * t * Complex.I) • u := by rw [ht]
  · rw [h (Multiplicative.toAdd g), smul_smul, ← Complex.exp_add, neg_add_cancel,
      Complex.exp_zero, one_smul]

/-- Restricting scalars to `ℝ` identifies the common eigenspace at frequency `ω` with the common
fixed space of the phase-shifted group `U.phaseShift hU ω`. -/
theorem eigenspace_restrictScalars (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) :
    (U.eigenspace hU ω).restrictScalars ℝ = (U.phaseShift hU ω).fixedSpace := by
  ext u
  rw [Submodule.restrictScalars_mem, eigenspace, ContRepresentation.mem_invariants,
    mem_fixedSpace_iff]
  simp only [toComplexContRep_apply]
  exact ⟨fun h t => h (Multiplicative.ofAdd t), fun h g => h (Multiplicative.toAdd g)⟩

/-- At frequency `0`, the real restriction of the eigenspace is the fixed space. -/
@[simp]
theorem eigenspace_zero_restrictScalars (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) :
    (U.eigenspace hU 0).restrictScalars ℝ = U.fixedSpace := by
  rw [U.eigenspace_restrictScalars hU 0, U.phaseShift_zero hU]

/-- Time reversal negates the eigenfrequency of every common eigenspace. -/
@[simp]
theorem eigenspace_reflect (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear)
    (ω : ℝ) :
    U.reflect.eigenspace (U.reflect_isComplexLinear hU) ω = U.eigenspace hU (-ω) := by
  ext u
  simp only [mem_eigenspace_iff, reflect_apply]
  refine ⟨fun h t => ?_, fun h t => ?_⟩
  · simpa only [neg_neg, Complex.ofReal_neg, neg_mul, mul_neg] using h (-t)
  · simpa only [Complex.ofReal_neg, neg_mul, mul_neg, neg_neg] using h (-t)

/-- Phase shifting by `b` shifts the eigenfrequencies by `b`. -/
@[simp]
theorem eigenspace_phaseShift (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b ω : ℝ) :
    (U.phaseShift hU b).eigenspace (U.phaseShift_isComplexLinear hU b) ω =
      U.eigenspace hU (b + ω) := by
  apply Submodule.restrictScalars_injective ℝ
  rw [eigenspace_restrictScalars, eigenspace_restrictScalars, phaseShift_phaseShift]

/-- Every common eigenspace of a complex-linear C₀-group is closed. -/
theorem isClosed_eigenspace (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear)
    (ω : ℝ) : IsClosed (U.eigenspace hU ω : Set X) :=
  ((U.phaseShift hU ω).toComplexContRep (U.phaseShift_isComplexLinear hU ω)).isClosed_invariants

instance eigenspace.completeSpace [CompleteSpace X] (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) : CompleteSpace (U.eigenspace hU ω) :=
  inferInstanceAs (CompleteSpace
    ((U.phaseShift hU ω).toComplexContRep (U.phaseShift_isComplexLinear hU ω)).invariants)

end ComplexNormed

/-! ## Spectral measures, twisted mean ergodic projection, and atomic mass -/

section ComplexInnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem isUnitary_toComplexContRep {U : StronglyContinuousGroup H} (hU : U.IsUnitary) :
    (U.toComplexContRep hU.isComplexLinear).IsUnitary :=
  (ContRepresentation.isUnitary_iff_norm_map _).mpr fun g x =>
    hU.norm_map (Multiplicative.toAdd g) x

/-- The correlation function `t ↦ ⟪v, U t v⟫_ℂ` of a vector under a unitary C₀-group is positive
definite. -/
theorem IsUnitary.isPositiveDefiniteSub_inner {U : StronglyContinuousGroup H} (hU : U.IsUnitary)
    (v : H) : TauCeti.IsPositiveDefiniteSub fun t : ℝ => ⟪v, U t v⟫_ℂ := by
  let π := U.toComplexContRep hU.isComplexLinear
  have hpos := ((isUnitary_toComplexContRep hU).posSemidef_inner_map_inv_mul v).submatrix
    (fun a : ℝ => Multiplicative.ofAdd (-a))
  have heq : (Matrix.of fun g h : Multiplicative ℝ => ⟪v, π (g⁻¹ * h) v⟫_ℂ).submatrix
      (fun a : ℝ => Multiplicative.ofAdd (-a)) (fun a : ℝ => Multiplicative.ofAdd (-a)) =
      fun a b : ℝ => ⟪v, U (a - b) v⟫_ℂ := by
    ext a b
    simp [π, toComplexContRep_apply, sub_eq_add_neg]
  exact TauCeti.IsPositiveDefiniteSub.of_posSemidef (heq ▸ hpos)

/-- **Existence and uniqueness of the Bochner spectral measure**: for every vector `v` and unitary
C₀-group `U`, there is a unique finite Borel measure `σ` on `ℝ` whose characteristic function is
`t ↦ ⟪v, U t v⟫_ℂ`. -/
theorem IsUnitary.existsUnique_spectralMeasure {U : StronglyContinuousGroup H} (hU : U.IsUnitary)
    (v : H) : ∃! σ : Measure ℝ, IsFiniteMeasure σ ∧ ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t := by
  have h := (TauCeti.bochner_charFun_real (fun t : ℝ => ⟪v, U t v⟫_ℂ)).mp
    ⟨continuous_const.inner (U.continuous_orbit v), hU.isPositiveDefiniteSub_inner v⟩
  simpa only [charFun_apply_real] using h

private theorem continuous_intervalIntegral_cexp_mul_sub_mul_I (ω T : ℝ) :
    Continuous fun ξ : ℝ => ∫ t in (0 : ℝ)..T, Complex.exp (t * (ξ - ω) * Complex.I) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) 0 T

/-- Spectral integral representation of the inner product between two twisted orbit vectors. -/
private theorem inner_twisted_orbit_eq_integral (U : StronglyContinuousGroup H) (hU : U.IsUnitary)
    (v : H) {σ : Measure ℝ} (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) (ω s t : ℝ) :
    ⟪Complex.exp (-(ω * s * Complex.I)) • U s v,
      Complex.exp (-(ω * t * Complex.I)) • U t v⟫_ℂ =
      ∫ ξ, conj (Complex.exp (s * (ξ - ω) * Complex.I)) *
        Complex.exp (t * (ξ - ω) * Complex.I) ∂σ := by
  have hUst : ⟪U s v, U t v⟫_ℂ = ⟪v, U (t - s) v⟫_ℂ := by
    simpa only [toComplexContRep_apply, toAdd_mul, toAdd_inv, toAdd_ofAdd, neg_add_eq_sub] using
      ((isUnitary_toComplexContRep hU).inner_map_inv_mul
        (Multiplicative.ofAdd s) (Multiplicative.ofAdd t) v v).symm
  rw [inner_smul_left, inner_smul_right, hUst, hσ (t - s), charFun_apply_real,
    ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [← Complex.exp_conj, map_neg, map_mul, map_sub, Complex.conj_ofReal,
    Complex.conj_I, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Integrating the inner product of twisted orbit vectors over the second time variable via
Fubini's theorem. -/
private theorem intervalIntegral_inner_twisted_orbit_eq (U : StronglyContinuousGroup H)
    (hU : U.IsUnitary) (v : H) {σ : Measure ℝ} [IsFiniteMeasure σ]
    (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) (ω T s : ℝ) :
    (∫ t in (0 : ℝ)..T,
        ⟪Complex.exp (-(ω * s * Complex.I)) • U s v,
          Complex.exp (-(ω * t * Complex.I)) • U t v⟫_ℂ) =
      ∫ ξ, conj (Complex.exp (s * (ξ - ω) * Complex.I)) *
        (∫ t in (0 : ℝ)..T, Complex.exp (t * (ξ - ω) * Complex.I)) ∂σ := by
  simp_rw [inner_twisted_orbit_eq_integral U hU v hσ ω s]
  have : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) T)) :=
    Real.isFiniteMeasure_restrict_Ioc (min 0 T) (max 0 T)
  have hint : Integrable (Function.uncurry fun t ξ : ℝ =>
      conj (Complex.exp (s * (ξ - ω) * Complex.I)) * Complex.exp (t * (ξ - ω) * Complex.I))
      ((volume.restrict (Set.uIoc 0 T)).prod σ) :=
    Integrable.of_bound (by fun_prop : Continuous _).aestronglyMeasurable 1
      (Eventually.of_forall fun p => by
        rw [Function.uncurry_apply_pair, norm_mul, Complex.norm_conj, ← Complex.ofReal_sub,
          ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I, ← Complex.ofReal_mul,
          Complex.norm_exp_ofReal_mul_I, mul_one])
  rw [intervalIntegral_integral_swap hint]
  exact integral_congr_ae (Eventually.of_forall fun ξ => intervalIntegral.integral_const_mul _ _)

variable [CompleteSpace H]

section TwistedMeanErgodic

attribute [local instance] InnerProductSpace.complexToReal

/-- **Twisted continuous-time mean ergodic theorem**: for a unitary C₀-group `U` on a complex
Hilbert space and any angular frequency `ω : ℝ`, the twisted orbit averages
`(T⁻¹ : ℂ) • ∫ t in 0..T, exp (-i ω t) • U t v` converge in norm to the orthogonal projection of
`v` onto `U.eigenspace hU.isComplexLinear ω`. -/
theorem tendsto_twistedAverage_starProjection_eigenspace (U : StronglyContinuousGroup H)
    (hU : U.IsUnitary) (ω : ℝ) (v : H) :
    Tendsto (fun T : ℝ => (T⁻¹ : ℂ) •
        ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) • U t v)
      atTop (𝓝 ((U.eigenspace hU.isComplexLinear ω).starProjection v)) := by
  have h := (U.phaseShift hU.isComplexLinear ω).tendsto_average_orbit_starProjection_fixedSpace
    (hU.phaseShift ω).opNorm_le_one v
  have hcongr : ∀ {K₁ K₂ : Submodule ℝ H} [K₁.HasOrthogonalProjection]
      [K₂.HasOrthogonalProjection], K₁ = K₂ → K₁.starProjection v = K₂.starProjection v := by
    rintro K _ _ _ rfl
    rfl
  have hproj :
      (U.phaseShift hU.isComplexLinear ω).fixedSpace.starProjection v =
        (U.eigenspace hU.isComplexLinear ω).starProjection v :=
    (hcongr (U.eigenspace_restrictScalars hU.isComplexLinear ω)).symm.trans
      (Submodule.starProjection_restrictScalars_apply (U.eigenspace hU.isComplexLinear ω) v)
  rw [hproj] at h
  simpa only [phaseShift_apply_apply, ← Complex.ofReal_inv, Complex.coe_smul] using h

end TwistedMeanErgodic

/-- Squared norm of an interval integral as a double interval integral of inner products. -/
private theorem norm_intervalIntegral_sq_eq {f : ℝ → H} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    ((‖∫ t in a..b, f t‖ ^ 2 : ℝ) : ℂ) = ∫ s in a..b, ∫ t in a..b, ⟪f s, f t⟫_ℂ := by
  calc
    ((‖∫ t in a..b, f t‖ ^ 2 : ℝ) : ℂ)
        = ⟪∫ s in a..b, f s, ∫ t in a..b, f t⟫_ℂ := by
      simpa only [Complex.ofReal_pow, RCLike.ofReal_eq_complex_ofReal] using
        (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (∫ t in a..b, f t)).symm
    _ = ∫ s in a..b, ⟪f s, ∫ t in a..b, f t⟫_ℂ := by
      have hcomm := (innerSL ℂ (∫ t in a..b, f t)).intervalIntegral_comp_comm hf
      simp only [innerSL_apply_apply] at hcomm
      rw [← inner_conj_symm, ← hcomm, ← intervalIntegral.intervalIntegral_conj]
      simp_rw [inner_conj_symm]
    _ = ∫ s in a..b, ∫ t in a..b, ⟪f s, f t⟫_ℂ :=
      intervalIntegral.integral_congr fun s _ =>
        ((innerSL ℂ (f s)).intervalIntegral_comp_comm hf).symm

/-- Unnormalized spectral representation for the squared norm of a twisted orbit integral. -/
private theorem norm_intervalIntegral_twisted_sq_eq (U : StronglyContinuousGroup H)
    (hU : U.IsUnitary) (v : H) {σ : Measure ℝ} [IsFiniteMeasure σ]
    (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) (ω T : ℝ) :
    ‖∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) • U t v‖ ^ 2 =
      ∫ ξ, ‖∫ t in (0 : ℝ)..T, Complex.exp (t * (ξ - ω) * Complex.I)‖ ^ 2 ∂σ := by
  let f : ℝ → H := fun t => Complex.exp (-(ω * t * Complex.I)) • U t v
  let e : ℝ → ℝ → ℂ := fun t ξ => Complex.exp (t * (ξ - ω) * Complex.I)
  let K : ℝ → ℂ := fun ξ => ∫ t in (0 : ℝ)..T, e t ξ
  have hf_int : IntervalIntegrable f volume 0 T :=
    ((by fun_prop : Continuous fun t : ℝ => Complex.exp (-(ω * t * Complex.I))).smul
      (U.continuous_orbit v)).intervalIntegrable 0 T
  have hK_cont : Continuous K := continuous_intervalIntegral_cexp_mul_sub_mul_I ω T
  have : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) T)) :=
    Real.isFiniteMeasure_restrict_Ioc (min 0 T) (max 0 T)
  have hint2 : Integrable (Function.uncurry fun s ξ => conj (e s ξ) * K ξ)
      ((volume.restrict (Set.uIoc 0 T)).prod σ) :=
    Integrable.of_bound
      ((Complex.continuous_conj.comp (by fun_prop)).mul
        (hK_cont.comp continuous_snd)).aestronglyMeasurable |T|
      (Eventually.of_forall fun p => by
        dsimp only [e]
        rw [Function.uncurry_apply_pair, norm_mul, Complex.norm_conj, ← Complex.ofReal_sub,
          ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
        simpa only [one_mul, sub_zero] using
          intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T) (C := 1)
            fun t _ => by
              dsimp only [e]
              rw [← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I])
  have hcomplex :
      ((‖∫ t in (0 : ℝ)..T, f t‖ ^ 2 : ℝ) : ℂ) = ((∫ ξ, ‖K ξ‖ ^ 2 ∂σ : ℝ) : ℂ) := by
    calc
      ((‖∫ t in (0 : ℝ)..T, f t‖ ^ 2 : ℝ) : ℂ)
          = ∫ s in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, ⟪f s, f t⟫_ℂ :=
        norm_intervalIntegral_sq_eq hf_int
      _ = ∫ s in (0 : ℝ)..T, ∫ ξ, conj (e s ξ) * K ξ ∂σ :=
        intervalIntegral.integral_congr fun s _ =>
          intervalIntegral_inner_twisted_orbit_eq U hU v hσ ω T s
      _ = ∫ ξ, (∫ s in (0 : ℝ)..T, conj (e s ξ) * K ξ) ∂σ :=
        intervalIntegral_integral_swap hint2
      _ = ∫ ξ, ((‖K ξ‖ ^ 2 : ℝ) : ℂ) ∂σ := by
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        dsimp only
        rw [intervalIntegral.integral_mul_const, intervalIntegral.intervalIntegral_conj,
          Complex.conj_mul', Complex.ofReal_pow]
      _ = ((∫ ξ, ‖K ξ‖ ^ 2 ∂σ : ℝ) : ℂ) := integral_ofReal
  exact Complex.ofReal_injective hcomplex

/-- **Spectral representation of the squared norm of a twisted average**: if `σ` is a finite Borel
measure whose characteristic function is `t ↦ ⟪v, U t v⟫_ℂ`, then the squared norm of the twisted
average over `[0, T]` is the `σ`-integral of the squared modulus of the Dirichlet average kernel. -/
theorem norm_twistedAverage_sq_eq_integral (U : StronglyContinuousGroup H) (hU : U.IsUnitary)
    (v : H) {σ : Measure ℝ} [IsFiniteMeasure σ]
    (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) (ω T : ℝ) :
    ‖(T⁻¹ : ℂ) • ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) • U t v‖ ^ 2 =
      ∫ ξ, ‖(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T,
        Complex.exp (t * (ξ - ω) * Complex.I)‖ ^ 2 ∂σ := by
  rw [norm_smul, mul_pow, norm_intervalIntegral_twisted_sq_eq U hU v hσ ω T, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [norm_mul, mul_pow]

/-- **Spectral atomic-mass identity**: for any finite Borel measure `σ` on `ℝ` with characteristic
function `t ↦ ⟪v, U t v⟫_ℂ`, the squared norm of the orthogonal projection of `v` onto the common
eigenspace at angular frequency `ω` equals the spectral mass `σ.real {ω}`. -/
theorem norm_starProjection_eigenspace_sq_eq_measure_singleton
    (U : StronglyContinuousGroup H) (hU : U.IsUnitary) (v : H)
    {σ : Measure ℝ} [IsFiniteMeasure σ]
    (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) (ω : ℝ) :
    ‖(U.eigenspace hU.isComplexLinear ω).starProjection v‖ ^ 2 = σ.real {ω} := by
  have h1 : Tendsto (fun T : ℝ =>
      ‖(T⁻¹ : ℂ) • ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) • U t v‖ ^ 2)
      atTop (𝓝 (‖(U.eigenspace hU.isComplexLinear ω).starProjection v‖ ^ 2)) :=
    ((U.tendsto_twistedAverage_starProjection_eigenspace hU ω v).norm).pow 2
  have h2 : Tendsto (fun T : ℝ =>
      ∫ ξ, ‖(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (t * (ξ - ω) * Complex.I)‖ ^ 2 ∂σ)
      atTop (𝓝 (∫ ξ, Set.indicator {ω} (fun _ => (1 : ℝ)) ξ ∂σ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
      (integrable_const 1) (Eventually.of_forall fun ξ => ?_)
    · refine Eventually.of_forall fun T => ?_
      exact ((continuous_const.mul
        (continuous_intervalIntegral_cexp_mul_sub_mul_I ω T)).norm.pow 2).aestronglyMeasurable
    · refine Eventually.of_forall fun T => Eventually.of_forall fun ξ => ?_
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_one₀ (norm_nonneg _) (by
        simpa only [Complex.ofReal_sub] using
          TauCeti.norm_inv_mul_intervalIntegral_cexp_mul_I_le_one (ξ - ω) T)
    · have ht := (TauCeti.tendsto_inv_mul_intervalIntegral_cexp_mul_I (ξ - ω)).norm.pow 2
      have hlim : ‖if ξ - ω = 0 then (1 : ℂ) else 0‖ ^ 2 =
          Set.indicator {ω} (fun _ => (1 : ℝ)) ξ := by
        by_cases hξ : ξ = ω
        · simp [hξ]
        · simp [sub_eq_zero, hξ]
      simpa only [Complex.ofReal_sub, hlim] using ht
  have heq : (fun T : ℝ =>
      ‖(T⁻¹ : ℂ) • ∫ t in (0 : ℝ)..T, Complex.exp (-(ω * t * Complex.I)) • U t v‖ ^ 2) =
      fun T : ℝ => ∫ ξ, ‖(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T,
        Complex.exp (t * (ξ - ω) * Complex.I)‖ ^ 2 ∂σ :=
    funext fun T => U.norm_twistedAverage_sq_eq_integral hU v hσ ω T
  rw [heq] at h1
  have hlim := tendsto_nhds_unique h1 h2
  simpa only [integral_indicator_const _ (MeasurableSet.singleton ω), smul_eq_mul, mul_one] using
    hlim

/-- **Continuous-time mean ergodic projection and spectral atomic mass**: for a strongly
continuous unitary group `U` on a complex Hilbert space, a frequency `a : ℝ`, and a vector `v`,
the twisted averages `(T⁻¹ : ℂ) • ∫ t in 0..T, exp (-2πiat) • U t v` converge in norm to a vector
`w` in the common eigenspace at frequency `2πa` with `v - w` orthogonal to that eigenspace, and
`‖w‖²` equals the mass at `2πa` of every finite Borel measure whose characteristic function is
`t ↦ ⟪v, U t v⟫_ℂ`. -/
theorem exists_tendsto_twistedAverage (U : StronglyContinuousGroup H) (hU : U.IsUnitary)
    (a : ℝ) (v : H) :
    ∃ w : H, (∀ t : ℝ, U t w = Complex.exp (2 * Real.pi * a * t * Complex.I) • w) ∧
      (∀ u : H, (∀ t : ℝ, U t u = Complex.exp (2 * Real.pi * a * t * Complex.I) • u) →
        ⟪u, v - w⟫_ℂ = 0) ∧
      Tendsto (fun T : ℝ => (T⁻¹ : ℂ) •
          ∫ t in (0 : ℝ)..T, Complex.exp (-(2 * Real.pi * a * t * Complex.I)) • U t v)
        atTop (𝓝 w) ∧
      ∀ σ : Measure ℝ, IsFiniteMeasure σ →
        (∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) →
        ‖w‖ ^ 2 = σ.real {2 * Real.pi * a} := by
  let ω : ℝ := 2 * Real.pi * a
  refine ⟨(U.eigenspace hU.isComplexLinear ω).starProjection v, ?_, ?_, ?_, ?_⟩
  · simpa only [ω, Complex.ofReal_mul, Complex.ofReal_ofNat] using
      (U.mem_eigenspace_iff hU.isComplexLinear ω _).mp
        (Submodule.starProjection_apply_mem _ v)
  · intro u hu
    exact (Submodule.mem_orthogonal _ _).mp
      (Submodule.sub_starProjection_mem_orthogonal (K := U.eigenspace hU.isComplexLinear ω) v) u
      ((U.mem_eigenspace_iff hU.isComplexLinear ω u).mpr
        (by simpa only [ω, Complex.ofReal_mul, Complex.ofReal_ofNat] using hu))
  · simpa only [ω, Complex.ofReal_mul, Complex.ofReal_ofNat] using
      U.tendsto_twistedAverage_starProjection_eigenspace hU ω v
  · intro σ _ hσ
    exact U.norm_starProjection_eigenspace_sq_eq_measure_singleton hU v hσ ω

end ComplexInnerProduct

end TauCeti.Semigroups.StronglyContinuousGroup

end
