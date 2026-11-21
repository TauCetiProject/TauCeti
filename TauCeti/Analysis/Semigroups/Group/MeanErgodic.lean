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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.MetricSpace.UniformConvergence
import TauCeti.Analysis.Bochner.CharFun.Bochner
import TauCeti.Analysis.InnerProductSpace.Gram.PosSemidef
import TauCeti.Analysis.InnerProductSpace.Projection.RestrictScalars
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Continuous-time mean ergodic theorem and spectral atomic mass

This file develops the continuous-time von Neumann mean ergodic theorem and the spectral
atomic-mass identity for strongly continuous one-parameter groups (`StronglyContinuousGroup`).

On a real normed space `X`, the common fixed space `U.fixedSpace` of a C₀-group `U` is a closed
subspace, and the orbit averages `T⁻¹ • ∫ t in 0..T, U t v` telescope on coboundaries `U s v - v`.
When `U` contracts in both time directions (`∀ t, ‖U t‖ ≤ 1`) on a real Hilbert space `H`, the
coboundaries span a dense subspace of `U.fixedSpaceᗮ`, yielding norm convergence of the orbit
averages to the orthogonal projection `U.fixedSpace.starProjection v` without any separability
assumption on `H`.

On a complex normed space, a complex-linear C₀-group has closed common eigenspaces
`U.eigenspace hU ω = {u | ∀ t, U t u = exp (i ω t) • u}`, whose real restriction is the fixed
space of the phase-shifted group `U.phaseShift hU ω`. For a unitary C₀-group on a complex Hilbert
space, transferring the real-Hilbert mean ergodic theorem through `U.phaseShift` and
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
open scoped InnerProductSpace Topology

namespace TauCeti.Semigroups.StronglyContinuousGroup

/-! ## Fixed spaces and orbit averages on real normed spaces -/

section RealNormed

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The real submodule of vectors fixed by every operator of a C₀-group. -/
def fixedSpace (U : StronglyContinuousGroup X) : Submodule ℝ X where
  carrier := {x : X | ∀ t : ℝ, U t x = x}
  zero_mem' t := (U t).map_zero
  add_mem' hx hy t := by rw [(U t).map_add, hx t, hy t]
  smul_mem' c _ hx t := by rw [(U t).map_smul, hx t]

/-- Membership in `fixedSpace` means invariance under every group operator. -/
@[simp]
theorem mem_fixedSpace_iff (U : StronglyContinuousGroup X) (x : X) :
    x ∈ U.fixedSpace ↔ ∀ t : ℝ, U t x = x :=
  (Iff.rfl)

/-- The common fixed space of a C₀-group is closed. -/
theorem isClosed_fixedSpace (U : StronglyContinuousGroup X) :
    IsClosed (U.fixedSpace : Set X) := by
  have h : (U.fixedSpace : Set X) = ⋂ t : ℝ, {x : X | U t x = x} := by
    ext x
    simp
  rw [h]
  exact isClosed_iInter fun t => isClosed_eq (U t).continuous continuous_id

instance fixedSpace.completeSpace [CompleteSpace X] (U : StronglyContinuousGroup X) :
    CompleteSpace U.fixedSpace :=
  U.isClosed_fixedSpace.completeSpace_coe

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
  have hfun : (fun t : ℝ => U t w) = fun _ => w := funext fun t => hw t
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
  rw [norm_smul, Real.norm_eq_abs, abs_inv]
  calc
    |T|⁻¹ * ‖∫ t in (0 : ℝ)..T, U t v‖ ≤ |T|⁻¹ * (‖v‖ * |T - 0|) :=
      mul_le_mul_of_nonneg_left (U.norm_intervalIntegral_orbit_le hnorm 0 T v)
        (inv_nonneg.mpr (abs_nonneg T))
    _ = ‖v‖ := by
      rw [sub_zero, ← mul_assoc, mul_comm |T|⁻¹ ‖v‖, mul_assoc,
        inv_mul_cancel₀ (abs_ne_zero.mpr hT), mul_one]

/-- Quantitative decay of the time average on a coboundary `U s v - v`, for every `T : ℝ`. -/
theorem norm_average_orbit_apply_sub_le (U : StronglyContinuousGroup X)
    (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1) (s T : ℝ) (v : X) :
    ‖T⁻¹ • ∫ t in (0 : ℝ)..T, U t (U s v - v)‖ ≤ 2 * |s| * ‖v‖ / |T| := by
  by_cases hT : T = 0
  · simp [hT]
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

/-- The real submodule of vectors whose orbit averages tend to `0` as `T → ∞`. -/
private def zeroAverageSubmodule (U : StronglyContinuousGroup X) : Submodule ℝ X where
  carrier := {x : X | Tendsto (fun T : ℝ => T⁻¹ • ∫ t in (0 : ℝ)..T, U t x) atTop (𝓝 0)}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    have hsum : (fun T : ℝ => T⁻¹ • ∫ t in (0 : ℝ)..T, U t (a + b)) =
        fun T : ℝ => (T⁻¹ • ∫ t in (0 : ℝ)..T, U t a) +
          (T⁻¹ • ∫ t in (0 : ℝ)..T, U t b) := by
      funext T
      have hfun : (fun t : ℝ => U t (a + b)) = fun t : ℝ => U t a + U t b :=
        funext fun t => (U t).map_add a b
      rw [hfun, intervalIntegral.integral_add ((U.continuous_orbit a).intervalIntegrable 0 T)
        ((U.continuous_orbit b).intervalIntegrable 0 T), smul_add]
    rw [Set.mem_ofPred_eq, hsum]
    simpa only [add_zero] using ha.add hb
  smul_mem' := fun c a ha => by
    have hsmul : (fun T : ℝ => T⁻¹ • ∫ t in (0 : ℝ)..T, U t (c • a)) =
        fun T : ℝ => c • (T⁻¹ • ∫ t in (0 : ℝ)..T, U t a) := by
      funext T
      have hfun : (fun t : ℝ => U t (c • a)) = fun t : ℝ => c • U t a :=
        funext fun t => (U t).map_smul c a
      rw [hfun, intervalIntegral.integral_smul, smul_comm]
    rw [Set.mem_ofPred_eq, hsmul]
    simpa only [smul_zero] using ha.const_smul c

private theorem mem_zeroAverageSubmodule_iff (U : StronglyContinuousGroup X) (x : X) :
    x ∈ U.zeroAverageSubmodule ↔
      Tendsto (fun T : ℝ => T⁻¹ • ∫ t in (0 : ℝ)..T, U t x) atTop (𝓝 0) :=
  Iff.rfl

/-- The zero-average submodule is closed when `U` is contractive, because the averaging operators
are uniformly contractive. -/
private theorem isClosed_zeroAverageSubmodule (U : StronglyContinuousGroup X)
    (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1) : IsClosed (U.zeroAverageSubmodule : Set X) := by
  have hcoe : (U.zeroAverageSubmodule : Set X) =
      {x : X | Tendsto (fun T : ℝ => T⁻¹ • ∫ t in (0 : ℝ)..T, U t x) atTop (𝓝 0)} := by
    ext x
    exact U.mem_zeroAverageSubmodule_iff x
  have hLip : ∀ T : ℝ, LipschitzWith 1 (fun x : X => T⁻¹ • ∫ t in (0 : ℝ)..T, U t x) := by
    intro T
    refine LipschitzWith.mk_one fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : (T⁻¹ • ∫ t in (0 : ℝ)..T, U t x) - (T⁻¹ • ∫ t in (0 : ℝ)..T, U t y) =
        T⁻¹ • ∫ t in (0 : ℝ)..T, U t (x - y) := by
      have hfun : (fun t : ℝ => U t (x - y)) = fun t : ℝ => U t x - U t y :=
        funext fun t => (U t).map_sub x y
      rw [hfun, intervalIntegral.integral_sub ((U.continuous_orbit x).intervalIntegrable 0 T)
        ((U.continuous_orbit y).intervalIntegrable 0 T), smul_sub]
    rw [hsub]
    exact U.norm_average_orbit_le hnorm T (x - y)
  rw [hcoe]
  exact (LipschitzWith.uniformEquicontinuous _ 1 hLip).equicontinuous.isClosed_setOfPred_tendsto
    continuous_const

end RealNormed

/-! ## Real Hilbert-space mean ergodic theorem -/

section RealInnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The orthogonal complement of the span of all coboundaries `U s w - w` is the common fixed
space of a contractive C₀-group. -/
theorem orthogonal_span_sub_eq_fixedSpace (U : StronglyContinuousGroup H)
    (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1) :
    (Submodule.span ℝ {z : H | ∃ (s : ℝ) (w : H), z = U s w - w})ᗮ = U.fixedSpace := by
  ext x
  rw [Submodule.mem_orthogonal, mem_fixedSpace_iff]
  constructor
  · intro hx s
    have hmem : U s x - x ∈ Submodule.span ℝ {z : H | ∃ (s : ℝ) (w : H), z = U s w - w} :=
      Submodule.subset_span ⟨s, x, rfl⟩
    have hzero : ⟪U s x - x, x⟫_ℝ = 0 := hx _ hmem
    rw [inner_sub_left, sub_eq_zero] at hzero
    refine eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℝ) ?_ ?_
    · exact (U.norm_map_apply_eq_of_norm_le_one s (hnorm s) (hnorm (-s)) x).le
    · simpa only [RCLike.re_to_real, real_inner_self_eq_norm_sq] using hzero
  · intro hx y hy
    refine Submodule.span_induction ?_ (by simp) (fun a b _ _ ha hb => by
      rw [inner_add_left, ha, hb, add_zero]) (fun c a _ ha => by
      rw [inner_smul_left, ha, mul_zero]) hy
    rintro _ ⟨s, w, rfl⟩
    let L : H →ₗᵢ[ℝ] H :=
      { toLinearMap := (U s).toLinearMap
        norm_map' := U.norm_map_apply_eq_of_norm_le_one s (hnorm s) (hnorm (-s)) }
    have hinner : ⟪U s w, x⟫_ℝ = ⟪w, x⟫_ℝ := by
      calc
        ⟪U s w, x⟫_ℝ = ⟪L w, L x⟫_ℝ := by simp [L, hx s]
        _ = ⟪w, x⟫_ℝ := L.inner_map_map w x
    rw [inner_sub_left, hinner, sub_self]

variable [CompleteSpace H]

/-- The coboundaries `U s w - w` span a dense subspace of the orthogonal complement of
`U.fixedSpace`. -/
theorem topologicalClosure_span_sub_eq_orthogonal_fixedSpace (U : StronglyContinuousGroup H)
    (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1) :
    (Submodule.span ℝ {z : H | ∃ (s : ℝ) (w : H), z = U s w - w}).topologicalClosure =
      U.fixedSpaceᗮ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure,
    U.orthogonal_span_sub_eq_fixedSpace hnorm]

/-- **Continuous-time von Neumann mean ergodic theorem** on a real Hilbert space: for any
contractive C₀-group, the orbit averages `T⁻¹ • ∫ t in 0..T, U t v` converge in norm to the
orthogonal projection of `v` onto `U.fixedSpace`. -/
theorem tendsto_average_orbit_starProjection_fixedSpace (U : StronglyContinuousGroup H)
    (hnorm : ∀ t : ℝ, ‖U t‖ ≤ 1) (v : H) :
    Tendsto (fun T : ℝ => T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) atTop
      (𝓝 (U.fixedSpace.starProjection v)) := by
  let w : H := U.fixedSpace.starProjection v
  let y : H := v - w
  have hw_tendsto : Tendsto (fun T : ℝ => T⁻¹ • ∫ t in (0 : ℝ)..T, U t w) atTop (𝓝 w) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact (U.average_orbit_of_mem_fixedSpace (Submodule.starProjection_apply_mem _ v) hT.ne').symm
  have hspan_le : Submodule.span ℝ {z : H | ∃ (s : ℝ) (u : H), z = U s u - u} ≤
      U.zeroAverageSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨s, u, rfl⟩
    exact U.tendsto_average_orbit_apply_sub hnorm s u
  have hclos_le : U.fixedSpaceᗮ ≤ U.zeroAverageSubmodule := by
    rw [← U.topologicalClosure_span_sub_eq_orthogonal_fixedSpace hnorm]
    exact Submodule.topologicalClosure_minimal _ hspan_le
      (U.isClosed_zeroAverageSubmodule hnorm)
  have hy_tendsto : Tendsto (fun T : ℝ => T⁻¹ • ∫ t in (0 : ℝ)..T, U t y) atTop (𝓝 0) :=
    hclos_le (Submodule.sub_starProjection_mem_orthogonal v)
  have hv_eq : (fun T : ℝ => T⁻¹ • ∫ t in (0 : ℝ)..T, U t v) =
      fun T : ℝ => (T⁻¹ • ∫ t in (0 : ℝ)..T, U t w) + (T⁻¹ • ∫ t in (0 : ℝ)..T, U t y) := by
    funext T
    have hfun : (fun t : ℝ => U t v) = fun t : ℝ => U t w + U t y :=
      funext fun t => by rw [← (U t).map_add, add_sub_cancel]
    rw [hfun, intervalIntegral.integral_add ((U.continuous_orbit w).intervalIntegrable 0 T)
      ((U.continuous_orbit y).intervalIntegrable 0 T), smul_add]
  rw [hv_eq]
  simpa only [add_zero] using hw_tendsto.add hy_tendsto

end RealInnerProduct

/-! ## Common eigenspaces on complex normed spaces -/

section ComplexNormed

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The complex submodule of common eigenvectors of a complex-linear C₀-group at angular
frequency `ω : ℝ`: the vectors satisfying `U t u = exp (i ω t) • u` for all `t : ℝ`. -/
def eigenspace (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) :
    Submodule ℂ X where
  carrier := {u : X | ∀ t : ℝ, U t u = Complex.exp (ω * t * Complex.I) • u}
  zero_mem' t := by rw [(U t).map_zero, smul_zero]
  add_mem' hx hy t := by rw [(U t).map_add, hx t, hy t, smul_add]
  smul_mem' c u hu t := by
    rw [U.map_smul_of_isComplexLinear hU, hu t, smul_comm]

/-- Membership in `eigenspace` means satisfying the common eigenfunction equation at all real
times. -/
@[simp]
theorem mem_eigenspace_iff (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear)
    (ω : ℝ) (u : X) :
    u ∈ U.eigenspace hU ω ↔ ∀ t : ℝ, U t u = Complex.exp (ω * t * Complex.I) • u :=
  (Iff.rfl)

/-- Restricting scalars to `ℝ` identifies the common eigenspace at frequency `ω` with the common
fixed space of the phase-shifted group `U.phaseShift hU ω`. -/
theorem eigenspace_restrictScalars (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) :
    (U.eigenspace hU ω).restrictScalars ℝ = (U.phaseShift hU ω).fixedSpace := by
  ext u
  simp only [Submodule.restrictScalars_mem, mem_eigenspace_iff, mem_fixedSpace_iff,
    phaseShift_apply_apply]
  refine ⟨fun hu t => ?_, fun hu t => ?_⟩
  · rw [hu t, smul_smul, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_smul]
  · calc
      U t u = Complex.exp (ω * t * Complex.I) •
          (Complex.exp (-(ω * t * Complex.I)) • U t u) := by
        rw [smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]
      _ = Complex.exp (ω * t * Complex.I) • u := by rw [hu t]

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
    (ω : ℝ) : IsClosed (U.eigenspace hU ω : Set X) := by
  have h := (U.phaseShift hU ω).isClosed_fixedSpace
  rwa [← U.eigenspace_restrictScalars hU ω] at h

instance eigenspace.completeSpace [CompleteSpace X] (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (ω : ℝ) : CompleteSpace (U.eigenspace hU ω) :=
  (U.isClosed_eigenspace hU ω).completeSpace_coe

end ComplexNormed

/-! ## Spectral measures, twisted mean ergodic projection, and atomic mass -/

section ComplexInnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The correlation function `t ↦ ⟪v, U t v⟫_ℂ` of a vector under a unitary C₀-group is positive
definite. -/
theorem IsUnitary.isPositiveDefiniteSub_inner {U : StronglyContinuousGroup H} (hU : U.IsUnitary)
    (v : H) : TauCeti.IsPositiveDefiniteSub fun t : ℝ => ⟪v, U t v⟫_ℂ := by
  refine TauCeti.IsPositiveDefiniteSub.of_posSemidef ?_
  have hgram : (fun a b : ℝ => ⟪v, U (a - b) v⟫_ℂ) = Matrix.gram ℂ (fun t : ℝ => U (-t) v) := by
    ext a b
    rw [Matrix.gram_apply, ← hU.inner_map_map (-a), ← U.map_add_apply, sub_eq_add_neg,
      neg_add_cancel_left]
  rw [hgram]
  exact TauCeti.posSemidef_gram ℂ fun t : ℝ => U (-t) v

/-- **Existence and uniqueness of the Bochner spectral measure**: for every vector `v` and unitary
C₀-group `U`, there is a unique finite Borel measure `σ` on `ℝ` whose characteristic function is
`t ↦ ⟪v, U t v⟫_ℂ`. -/
theorem IsUnitary.existsUnique_spectralMeasure {U : StronglyContinuousGroup H} (hU : U.IsUnitary)
    (v : H) : ∃! σ : Measure ℝ, IsFiniteMeasure σ ∧ ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t := by
  have h := (TauCeti.bochner_charFun_real (fun t : ℝ => ⟪v, U t v⟫_ℂ)).mp
    ⟨continuous_const.inner (U.continuous_orbit v), hU.isPositiveDefiniteSub_inner v⟩
  simpa only [charFun_apply_real] using h

/-- Spectral integral representation of the inner product between two twisted orbit vectors. -/
private theorem inner_twisted_orbit_eq_integral (U : StronglyContinuousGroup H) (hU : U.IsUnitary)
    (v : H) {σ : Measure ℝ} (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) (ω s t : ℝ) :
    ⟪Complex.exp (-(ω * s * Complex.I)) • U s v,
      Complex.exp (-(ω * t * Complex.I)) • U t v⟫_ℂ =
      ∫ ξ, conj (Complex.exp (s * (ξ - ω) * Complex.I)) *
        Complex.exp (t * (ξ - ω) * Complex.I) ∂σ := by
  have hUst : ⟪U s v, U t v⟫_ℂ = ⟪v, U (t - s) v⟫_ℂ := by
    calc
      ⟪U s v, U t v⟫_ℂ = ⟪U (-s) (U s v), U (-s) (U t v)⟫_ℂ :=
        (hU.inner_map_map (-s) _ _).symm
      _ = ⟪v, U (t - s) v⟫_ℂ := by
        rw [U.map_neg_apply_map_apply, ← U.map_add_apply, neg_add_eq_sub]
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
  have : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) T)) := ⟨by simp [Real.volume_uIoc]⟩
  have he_norm : ∀ a ξ : ℝ, ‖Complex.exp (a * (ξ - ω) * Complex.I)‖ = 1 := fun a ξ => by
    have : (a : ℂ) * ((ξ : ℂ) - ω) * Complex.I = ((a * (ξ - ω) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have hint : Integrable (Function.uncurry fun t ξ : ℝ =>
      conj (Complex.exp (s * (ξ - ω) * Complex.I)) * Complex.exp (t * (ξ - ω) * Complex.I))
      ((volume.restrict (Set.uIoc 0 T)).prod σ) :=
    Integrable.of_bound (by fun_prop : Continuous _).aestronglyMeasurable 1
      (Eventually.of_forall fun p => by
        rw [Function.uncurry_apply_pair, norm_mul, Complex.norm_conj, he_norm, he_norm, mul_one])
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
  have he_norm : ∀ t ξ : ℝ, ‖e t ξ‖ = 1 := fun t ξ => by
    have : (t : ℂ) * ((ξ : ℂ) - ω) * Complex.I = ((t * (ξ - ω) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    simp only [e, this, Complex.norm_exp_ofReal_mul_I]
  have hK_cont : Continuous K :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) 0 T
  have : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) T)) := ⟨by simp [Real.volume_uIoc]⟩
  have hint2 : Integrable (Function.uncurry fun s ξ => conj (e s ξ) * K ξ)
      ((volume.restrict (Set.uIoc 0 T)).prod σ) :=
    Integrable.of_bound
      ((Complex.continuous_conj.comp (by fun_prop)).mul
        (hK_cont.comp continuous_snd)).aestronglyMeasurable |T|
      (Eventually.of_forall fun p => by
        rw [Function.uncurry_apply_pair, norm_mul, Complex.norm_conj, he_norm, one_mul]
        simpa only [one_mul, sub_zero] using
          intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T) (C := 1) fun t _ =>
            (he_norm t p.2).le)
  have hcomplex :
      ((‖∫ t in (0 : ℝ)..T, f t‖ ^ 2 : ℝ) : ℂ) = ((∫ ξ, ‖K ξ‖ ^ 2 ∂σ : ℝ) : ℂ) := by
    calc
      ((‖∫ t in (0 : ℝ)..T, f t‖ ^ 2 : ℝ) : ℂ)
          = ⟪∫ s in (0 : ℝ)..T, f s, ∫ t in (0 : ℝ)..T, f t⟫_ℂ := by
        simpa only [Complex.ofReal_pow, RCLike.ofReal_eq_complex_ofReal] using
          (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (∫ t in (0 : ℝ)..T, f t)).symm
      _ = ∫ s in (0 : ℝ)..T, ⟪f s, ∫ t in (0 : ℝ)..T, f t⟫_ℂ := by
        have hcomm := (innerSL ℂ (∫ t in (0 : ℝ)..T, f t)).intervalIntegral_comp_comm hf_int
        simp only [innerSL_apply_apply] at hcomm
        rw [← inner_conj_symm, ← hcomm, ← intervalIntegral.intervalIntegral_conj]
        simp_rw [inner_conj_symm]
      _ = ∫ s in (0 : ℝ)..T, ∫ t in (0 : ℝ)..T, ⟪f s, f t⟫_ℂ :=
        intervalIntegral.integral_congr fun s _ =>
          ((innerSL ℂ (f s)).intervalIntegral_comp_comm hf_int).symm
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
      have hcont : Continuous fun ξ : ℝ =>
          ∫ t in (0 : ℝ)..T, Complex.exp (t * (ξ - ω) * Complex.I) :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) 0 T
      exact ((continuous_const.mul hcont).norm.pow 2).aestronglyMeasurable
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
    exact Submodule.sub_starProjection_mem_orthogonal
      (K := U.eigenspace hU.isComplexLinear ω) v u
      ((U.mem_eigenspace_iff hU.isComplexLinear ω u).mpr
        (by simpa only [ω, Complex.ofReal_mul, Complex.ofReal_ofNat] using hu))
  · simpa only [ω, Complex.ofReal_mul, Complex.ofReal_ofNat] using
      U.tendsto_twistedAverage_starProjection_eigenspace hU ω v
  · intro σ _ hσ
    exact U.norm_starProjection_eigenspace_sq_eq_measure_singleton hU v hσ ω

end ComplexInnerProduct

end TauCeti.Semigroups.StronglyContinuousGroup

end
