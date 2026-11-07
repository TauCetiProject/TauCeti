/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import TauCeti.Analysis.Calculus.TwistedPeriodic
public import TauCeti.Analysis.ODE.DysonSeries
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Twisted periodic solutions of a periodic linear equation

Let `M : ℝ → End(V)` be a continuous path of bounded operators on a real Banach space with
period `d`, so that the time-dependent linear equation `w' t = M t (w t)` has a propagator
`Γ t = dysonSeriesLeft M t` with `Γ (t + d) = Γ t * Γ d`. Its value `P = Γ d` over one period is
the *monodromy* of the equation. For a real number `c`, a function `x : ℝ → V` is
*`c`-twisted periodic* when `x (t + d) = c • x t`; for `c = 1` these are the periodic functions,
and for `c = -1` the antiperiodic ones. For `c ≠ 0` they are the `V`-valued sections of the flat
real line bundle over the circle `ℝ / dℤ` with holonomy `c`.

This file compares the first-order operator

`L x = x' - M x`

from the `C¹` to the continuous `c`-twisted periodic functions
(`TauCeti.periodicLinearODEOperator`) with the bounded operator `c • 1 - P` on `V`:

* **Kernel.** Evaluation at `0` is a linear equivalence from `ker L` onto `ker (c • 1 - P)`,
  with inverse `v ↦ (t ↦ Γ t v)` (`TauCeti.periodicLinearODEOperatorKerEquiv`).
* **Range.** Let `E g = Γ d (∫₀ᵈ Γ s⁻¹ (g s))` be the *endpoint map*, the value at time `d` of the
  solution of `w' = M w + g` with `w 0 = 0` (`TauCeti.periodicLinearODEEndpointMap`). Every
  solution of `w' = M w + g` satisfies `w d = P (w 0) + E g`
  (`TauCeti.apply_eq_dysonSeriesLeft_apply_add_periodicLinearODEEndpointMap`), and such a
  solution with `w d = c • w 0` is `c`-twisted periodic when `g` is
  (`TauCeti.add_eq_smul_of_hasDerivAt_of_apply_eq_smul`). Consequently `g` lies in the range of
  `L` exactly when `E g` lies in the range of `c • 1 - P`
  (`TauCeti.range_periodicLinearODEOperator`).
* **Cokernel.** For `d > 0` and `c ≠ 0` the endpoint map is onto from the twisted periodic
  functions (`TauCeti.periodicLinearODEEndpointMap_domRestrict_surjective`), so it induces a
  linear equivalence between the cokernel of `L` and the cokernel `V ⧸ range (c • 1 - P)`
  (`TauCeti.periodicLinearODEOperatorCokerEquiv`). In finite dimension the kernel and cokernel of
  `L` therefore have the same dimension
  (`TauCeti.finrank_ker_periodicLinearODEOperator_eq_finrank_quotient_range`).

Together these form the endpoint exact sequence
`0 → ker L → V → V → coker L → 0`, whose middle map is `c • 1 - P`. For `c = 1` and a
monodromy `P = φ^*` acting on the cohomology of the fibre of a mapping torus, the middle map
`1 - φ^*` is the map of the Wang sequence, so the periodic equation along the base circle has the
kernel and cokernel of that finite complex. For `c = ±1` it describes the operator along a closed
orbit twisted by a real sign character, whose kernel and cokernel are those of `±1 - P`.

The twisted periodic function spaces and the extension of a continuous function on `[0, d]` with
`f d = c • f 0`, used to produce forcings for the cokernel, are in
`TauCeti.Analysis.Calculus.TwistedPeriodic`.

## References

* E. A. Coddington and N. Levinson, *Theory of Ordinary Differential Equations*, McGraw–Hill,
  1955, Chapter 3 (linear systems, the variation of constants formula and systems with periodic
  coefficients).
-/

public section

noncomputable section

open Set intervalIntegral

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### The periodic linear operator -/

variable {M : ℝ → V →L[ℝ] V} {d c : ℝ}

variable (c) in
/-- The first-order operator `L x = x' - M x` from the `C¹` to the continuous `c`-twisted
periodic functions, for a continuous path `M` of bounded operators of period `d`. -/
def periodicLinearODEOperator (hM : Continuous M) (hper : Function.Periodic M d) :
    twistedPeriodicContDiff V d c →ₗ[ℝ] twistedPeriodicContinuous V d c where
  toFun x := ⟨⟨fun t => deriv x.1 t - M t (x.1 t),
      ((mem_twistedPeriodicContDiff.1 x.2).1.continuous_deriv le_rfl).sub
        (hM.clm_apply (mem_twistedPeriodicContDiff.1 x.2).1.continuous)⟩,
    mem_twistedPeriodicContinuous.2 fun t => by
      have hx := (mem_twistedPeriodicContDiff.1 x.2).2
      simp [deriv_add_eq_smul hx, hper t, hx t, smul_sub]⟩
  map_add' x y := by
    ext t
    simp [deriv_add (((mem_twistedPeriodicContDiff.1 x.2).1.differentiable one_ne_zero) t)
      (((mem_twistedPeriodicContDiff.1 y.2).1.differentiable one_ne_zero) t)]
    abel
  map_smul' a x := by
    ext t
    simp [deriv_const_smul_field, smul_sub]

@[simp]
theorem periodicLinearODEOperator_apply (hM : Continuous M) (hper : Function.Periodic M d)
    (x : twistedPeriodicContDiff V d c) (t : ℝ) :
    (periodicLinearODEOperator c hM hper x : C(ℝ, V)) t = deriv x.1 t - M t (x.1 t) :=
  (rfl)

/-- An element `x` of the domain of `L` solves `x' = M x + L x`. -/
theorem hasDerivAt_periodicLinearODEOperator (hM : Continuous M) (hper : Function.Periodic M d)
    (x : twistedPeriodicContDiff V d c) (t : ℝ) :
    HasDerivAt x.1 (M t (x.1 t) + (periodicLinearODEOperator c hM hper x : C(ℝ, V)) t) t := by
  rw [periodicLinearODEOperator_apply, add_sub_cancel]
  exact (((mem_twistedPeriodicContDiff.1 x.2).1.differentiable one_ne_zero) t).hasDerivAt

/-- The kernel of `L` consists of the twisted periodic solutions of `x' = M x`. -/
theorem mem_ker_periodicLinearODEOperator (hM : Continuous M) (hper : Function.Periodic M d)
    {x : twistedPeriodicContDiff V d c} :
    x ∈ LinearMap.ker (periodicLinearODEOperator c hM hper) ↔
      ∀ t, HasDerivAt x.1 (M t (x.1 t)) t := by
  refine ⟨fun h t => by simpa [LinearMap.mem_ker.1 h] using
    hasDerivAt_periodicLinearODEOperator hM hper x t, fun h => ?_⟩
  refine LinearMap.mem_ker.2 (Subtype.ext (ContinuousMap.ext fun t => ?_))
  simp [periodicLinearODEOperator_apply, (h t).deriv]

/-! ### The kernel -/

variable [CompleteSpace V]

/-- The initial value of a solution of `w' = M w` lies in the kernel of `c • 1 - P`, where
`P = dysonSeriesLeft M d`, exactly when the solution satisfies `w d = c • w 0`. -/
theorem sub_dysonSeriesLeft_apply_eq_zero_iff (hM : Continuous M) {w : ℝ → V}
    (hw : ∀ t, HasDerivAt w (M t (w t)) t) :
    (c • (1 : V →L[ℝ] V) - dysonSeriesLeft M d) (w 0) = 0 ↔ w d = c • w 0 := by
  rw [ContinuousLinearMap.smul_one_sub_apply_eq_zero_iff, eq_dysonSeriesLeft_apply hM hw d]

/-- The solution `t ↦ Γ t v` through a vector `v` of the kernel of `c • 1 - P` is a `C¹`
`c`-twisted periodic function. -/
theorem dysonSeriesLeft_apply_mem_twistedPeriodicContDiff (hM : Continuous M)
    (hper : Function.Periodic M d) {v : V}
    (hv : (c • (1 : V →L[ℝ] V) - dysonSeriesLeft M d) v = 0) :
    (fun t => dysonSeriesLeft M t v) ∈ twistedPeriodicContDiff V d c := by
  refine mem_twistedPeriodicContDiff.2 ⟨?_, fun t => ?_⟩
  · simpa using (contDiff_dysonSeriesLeft (n := 0) (contDiff_zero.2 hM)).clm_apply
      (contDiff_const (c := v))
  rw [dysonSeriesLeft_add_of_periodic hM hper, mul_apply_eq_comp,
    ContinuousLinearMap.smul_one_sub_apply_eq_zero_iff.1 hv, map_smul]

variable (c) in
/-- **The kernel of the periodic operator.** Evaluation at `0` identifies the kernel of
`L = d/dt - M` on `c`-twisted periodic functions with the kernel of `c • 1 - P`, where
`P = dysonSeriesLeft M d` is the monodromy. The inverse sends `v` to the solution `t ↦ Γ t v`. -/
def periodicLinearODEOperatorKerEquiv (hM : Continuous M) (hper : Function.Periodic M d) :
    LinearMap.ker (periodicLinearODEOperator c hM hper) ≃ₗ[ℝ]
      LinearMap.ker (c • 1 - (dysonSeriesLeft M d).toLinearMap) where
  toFun x := ⟨x.1.1 0, by
    have hw := (mem_ker_periodicLinearODEOperator hM hper).1 x.2
    exact LinearMap.mem_ker.2 ((sub_dysonSeriesLeft_apply_eq_zero_iff hM hw).2
      (by simpa using (mem_twistedPeriodicContDiff.1 x.1.2).2 0))⟩
  invFun v := ⟨⟨fun t => dysonSeriesLeft M t v,
      dysonSeriesLeft_apply_mem_twistedPeriodicContDiff hM hper (LinearMap.mem_ker.1 v.2)⟩,
    (mem_ker_periodicLinearODEOperator hM hper).2 fun t =>
      hasDerivAt_dysonSeriesLeft_apply hM v t⟩
  map_add' x y := rfl
  map_smul' a x := rfl
  left_inv x := by
    have hw := (mem_ker_periodicLinearODEOperator hM hper).1 x.2
    exact Subtype.ext (Subtype.ext (funext fun t => (eq_dysonSeriesLeft_apply hM hw t).symm))
  right_inv v := Subtype.ext (by simp)

@[simp]
theorem periodicLinearODEOperatorKerEquiv_apply (hM : Continuous M)
    (hper : Function.Periodic M d) (x : LinearMap.ker (periodicLinearODEOperator c hM hper)) :
    (periodicLinearODEOperatorKerEquiv c hM hper x : V) = x.1.1 0 :=
  (rfl)

@[simp]
theorem periodicLinearODEOperatorKerEquiv_symm_apply (hM : Continuous M)
    (hper : Function.Periodic M d)
    (v : LinearMap.ker (c • 1 - (dysonSeriesLeft M d).toLinearMap)) (t : ℝ) :
    ((periodicLinearODEOperatorKerEquiv c hM hper).symm v : twistedPeriodicContDiff V d c).1 t =
      dysonSeriesLeft M t v :=
  (rfl)

/-! ### The endpoint map and the range -/

variable (d) in
/-- The endpoint map `E g = Γ d (∫₀ᵈ Φ s (g s))`, with `Γ = dysonSeriesLeft M` and
`Φ = dysonSeries (-M)` its inverse. It is the value at time `d` of the solution of
`w' = M w + g` with `w 0 = 0`
(`TauCeti.apply_eq_dysonSeriesLeft_apply_add_periodicLinearODEEndpointMap`). -/
def periodicLinearODEEndpointMap (hM : Continuous M) : C(ℝ, V) →ₗ[ℝ] V where
  toFun g := dysonSeriesLeft M d (∫ s in 0..d, dysonSeries (-M) s (g s))
  map_add' f g := by
    have hi (g : C(ℝ, V)) :
        IntervalIntegrable (fun s => dysonSeries (-M) s (g s)) MeasureTheory.volume 0 d :=
      ((continuous_dysonSeries hM.neg).clm_apply g.continuous).intervalIntegrable 0 d
    simp only [ContinuousMap.add_apply, map_add]
    rw [integral_add (hi f) (hi g), map_add]
  map_smul' a g := by
    simp [integral_smul]

theorem periodicLinearODEEndpointMap_apply (hM : Continuous M) (g : C(ℝ, V)) :
    periodicLinearODEEndpointMap d hM g =
      dysonSeriesLeft M d (∫ s in 0..d, dysonSeries (-M) s (g s)) :=
  (rfl)

/-- **The endpoint relation.** Every solution of `w' = M w + g` satisfies
`w d = P (w 0) + E g`, where `P = dysonSeriesLeft M d` and `E` is the endpoint map. -/
theorem apply_eq_dysonSeriesLeft_apply_add_periodicLinearODEEndpointMap (hM : Continuous M)
    {g : C(ℝ, V)} {w : ℝ → V} (hw : ∀ t, HasDerivAt w (M t (w t) + g t) t) :
    w d = dysonSeriesLeft M d (w 0) + periodicLinearODEEndpointMap d hM g := by
  rw [eq_dysonSeriesLeft_apply_add_integral hM g.continuous hw d, map_add,
    periodicLinearODEEndpointMap_apply]

/-- A solution of `w' = M w + g`, for a path `M` of period `d` and a `c`-twisted periodic
forcing `g`, is `c`-twisted periodic as soon as `w d = c • w 0`: the difference
`t ↦ w (t + d) - c • w t` solves `y' = M y` and vanishes at `0`. -/
theorem add_eq_smul_of_hasDerivAt_of_apply_eq_smul (hM : Continuous M)
    (hper : Function.Periodic M d) {g w : ℝ → V} (hg : ∀ t, g (t + d) = c • g t)
    (hw : ∀ t, HasDerivAt w (M t (w t) + g t) t) (hwd : w d = c • w 0) (t : ℝ) :
    w (t + d) = c • w t := by
  have hy := eq_dysonSeriesLeft_apply hM (w := fun t => w (t + d) - c • w t)
    (fun t => (((hw (t + d)).comp_add_const t d).sub ((hw t).const_smul c)).congr_deriv (by
      rw [hper t, hg t]
      simp [smul_add, map_sub, map_smul])) t
  rw [zero_add, hwd, sub_self, map_zero, sub_eq_zero] at hy
  exact hy

/-- A solution of `w' = M w + g`, for a continuous path `M` of period `d` and a continuous
`c`-twisted periodic forcing `g`, is a `C¹` `c`-twisted periodic function as soon as
`w d = c • w 0`. -/
theorem mem_twistedPeriodicContDiff_of_hasDerivAt_of_apply_eq_smul (hM : Continuous M)
    (hper : Function.Periodic M d) {g : C(ℝ, V)} (hg : ∀ t, g (t + d) = c • g t) {w : ℝ → V}
    (hw : ∀ t, HasDerivAt w (M t (w t) + g t) t) (hwd : w d = c • w 0) :
    w ∈ twistedPeriodicContDiff V d c :=
  mem_twistedPeriodicContDiff.2 ⟨contDiff_one_iff_deriv.2 ⟨fun t => (hw t).differentiableAt, by
      rw [funext fun t => (hw t).deriv]
      exact (hM.clm_apply (continuous_iff_continuousAt.2 fun t => (hw t).continuousAt)).add
        g.continuous⟩,
    add_eq_smul_of_hasDerivAt_of_apply_eq_smul hM hper hg hw hwd⟩

/-- **The range of the periodic operator.** A continuous `c`-twisted periodic forcing `g` is
`x' - M x` for some `C¹` `c`-twisted periodic `x` exactly when its endpoint `E g` lies in the
range of `c • 1 - P`. -/
theorem range_periodicLinearODEOperator (hM : Continuous M) (hper : Function.Periodic M d) :
    LinearMap.range (periodicLinearODEOperator c hM hper) =
      (LinearMap.range (c • 1 - (dysonSeriesLeft M d).toLinearMap)).comap
        ((periodicLinearODEEndpointMap d hM).domRestrict (twistedPeriodicContinuous V d c)) := by
  ext g
  simp only [LinearMap.mem_range, Submodule.mem_comap, LinearMap.domRestrict_apply]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x.1 0, ?_⟩
    have h := apply_eq_dysonSeriesLeft_apply_add_periodicLinearODEEndpointMap (d := d) hM
      (hasDerivAt_periodicLinearODEOperator hM hper x)
    have hx := (mem_twistedPeriodicContDiff.1 x.2).2 0
    rw [zero_add] at hx
    rw [hx] at h
    simp [h]
  · rintro ⟨x₀, hx₀⟩
    -- The solution of `w' = M w + g` with `w 0 = x₀`.
    set w : ℝ → V := fun t => dysonSeriesLeft M t (x₀ + ∫ s in 0..t, dysonSeries (-M) s (g.1 s))
    have hw (t : ℝ) : HasDerivAt w (M t (w t) + g.1 t) t :=
      hasDerivAt_dysonSeriesLeft_apply_add_integral hM g.1.continuous x₀ t
    have hw0 : w 0 = x₀ := by simp [w]
    have hwd : w d = c • w 0 := by
      rw [apply_eq_dysonSeriesLeft_apply_add_periodicLinearODEEndpointMap hM hw, hw0, ← hx₀]
      simp
    refine ⟨⟨w, mem_twistedPeriodicContDiff_of_hasDerivAt_of_apply_eq_smul hM hper
      (mem_twistedPeriodicContinuous.1 g.2) hw hwd⟩, Subtype.ext (ContinuousMap.ext fun t => ?_)⟩
    simp [periodicLinearODEOperator_apply, (hw t).deriv]

/-! ### The cokernel -/

/-- For `d > 0` and `c ≠ 0`, the endpoint map is onto from the continuous `c`-twisted periodic
functions. -/
theorem periodicLinearODEEndpointMap_domRestrict_surjective (hM : Continuous M) (hd : 0 < d)
    (hc : c ≠ 0) :
    Function.Surjective
      ((periodicLinearODEEndpointMap d hM).domRestrict (twistedPeriodicContinuous V d c)) := by
  intro v
  -- The forcing `s (d - s) Γ s u` on `[0, d]` has endpoint `(d ^ 3 / 6) Γ d u`.
  set u : V := (6 / d ^ 3) • dysonSeries (-M) d v
  set f : ℝ → V := fun s => (s * (d - s)) • dysonSeriesLeft M s u
  have hf : Continuous f :=
    ((continuous_id.mul (continuous_const.sub continuous_id)).smul
      ((continuous_dysonSeriesLeft hM).clm_apply continuous_const))
  obtain ⟨g, hg, hgper, hgf⟩ := exists_continuous_add_eq_smul_eqOn hd hc hf.continuousOn
    (by simp [f])
  refine ⟨⟨⟨g, hg⟩, mem_twistedPeriodicContinuous.2 hgper⟩, ?_⟩
  have hint : ∫ s in 0..d, dysonSeries (-M) s (g s) = ∫ s in 0..d, (s * (d - s)) • u := by
    refine integral_congr fun s hs => ?_
    rw [uIcc_of_le hd.le] at hs
    rw [hgf hs]
    simp only [f, map_smul, dysonSeries_neg_apply_dysonSeriesLeft_apply hM]
  have hpoly : ∫ s in 0..d, s * (d - s) = d ^ 3 / 6 := by
    simp only [mul_sub, ← pow_two]
    rw [integral_sub (f := fun s => s * d) (g := fun s => s ^ 2)
      ((continuous_id.mul continuous_const).intervalIntegrable _ _)
      ((continuous_pow 2).intervalIntegrable _ _), intervalIntegral.integral_mul_const,
      integral_id, integral_pow]
    ring
  rw [LinearMap.domRestrict_apply, periodicLinearODEEndpointMap_apply]
  simp only [ContinuousMap.coe_mk]
  rw [hint, intervalIntegral.integral_smul_const, hpoly, smul_smul, map_smul,
    dysonSeriesLeft_apply_dysonSeries_neg_apply hM]
  field_simp
  simp

variable (c) in
/-- **The cokernel of the periodic operator.** For `d > 0` and `c ≠ 0`, the endpoint map
induces a linear equivalence from the cokernel of `L = d/dt - M` on `c`-twisted periodic
functions onto the cokernel of `c • 1 - P`, where `P = dysonSeriesLeft M d` is the monodromy. -/
def periodicLinearODEOperatorCokerEquiv (hM : Continuous M) (hper : Function.Periodic M d)
    (hd : 0 < d) (hc : c ≠ 0) :
    (twistedPeriodicContinuous V d c ⧸ LinearMap.range (periodicLinearODEOperator c hM hper))
      ≃ₗ[ℝ] V ⧸ LinearMap.range (c • 1 - (dysonSeriesLeft M d).toLinearMap) :=
  (Submodule.quotEquivOfEq _ (LinearMap.ker
    ((LinearMap.range (c • 1 - (dysonSeriesLeft M d).toLinearMap)).mkQ ∘ₗ
      (periodicLinearODEEndpointMap d hM).domRestrict (twistedPeriodicContinuous V d c))) (by
    rw [range_periodicLinearODEOperator, LinearMap.ker_comp, Submodule.ker_mkQ])).trans
    (LinearMap.quotKerEquivOfSurjective _
      ((Submodule.mkQ_surjective _).comp
        (periodicLinearODEEndpointMap_domRestrict_surjective hM hd hc)))

@[simp]
theorem periodicLinearODEOperatorCokerEquiv_mk (hM : Continuous M)
    (hper : Function.Periodic M d) (hd : 0 < d) (hc : c ≠ 0)
    (g : twistedPeriodicContinuous V d c) :
    periodicLinearODEOperatorCokerEquiv c hM hper hd hc (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk (periodicLinearODEEndpointMap d hM g) :=
  (rfl)

/-- **Index zero.** In finite dimension, for `d > 0` and `c ≠ 0`, the kernel and the cokernel of
the periodic operator `L = d/dt - M` on `c`-twisted periodic functions have the same dimension,
that of the kernel of `c • 1 - P`. -/
theorem finrank_ker_periodicLinearODEOperator_eq_finrank_quotient_range [FiniteDimensional ℝ V]
    (hM : Continuous M) (hper : Function.Periodic M d) (hd : 0 < d) (hc : c ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (periodicLinearODEOperator c hM hper)) =
      Module.finrank ℝ
        (twistedPeriodicContinuous V d c ⧸
        LinearMap.range (periodicLinearODEOperator c hM hper)) := by
  rw [(periodicLinearODEOperatorKerEquiv c hM hper).finrank_eq,
    (periodicLinearODEOperatorCokerEquiv c hM hper hd hc).finrank_eq]
  have h₁ := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (c • 1 - (dysonSeriesLeft M d).toLinearMap))
  have h₂ := LinearMap.finrank_range_add_finrank_ker
    (c • 1 - (dysonSeriesLeft M d).toLinearMap)
  omega

end TauCeti
