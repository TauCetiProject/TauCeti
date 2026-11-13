/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Periodic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Analysis.SpecialFunctions.Trigonometric.PeriodicBump
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Variation
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Integral
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Variations of loops and the variational principle for periodic orbits

Let `σ` be a nondegenerate two-form on a manifold `M` modelled on a finite-dimensional space and
`H : ℝ → M → ℝ` a time-dependent Hamiltonian, with Hamiltonian vector fields `ι_{X_{H_t}} σ = dH_t`.
A **variation through loops** is a map `w : ℝ × ℝ → M`, `1`-periodic in its second coordinate
`t`; its loops are `γ_s = w (s, ·)`. An action functional on loops has the form
`A_H(γ) = a(γ) - ∫₀¹ H(t, γ(t)) dt`, whose area term `a` is the integral of `σ` over a surface
attached to the loop: a cap for contractible loops
(`TauCeti.contractibleLoopAction`), a cylinder to a reference loop on all free loops
(`TauCeti.SmoothTwoForm.referenceAction`). In either case moving the loop changes the area term by
the area swept out by the variation, and this file collects what follows from that alone.

* **The first variation formula.** If the area term of the loops `w (s, ·)` has derivative
  `-∫₀¹ σ(∂_s w, ∂_t w) dt` at `s₀`, then
  `d/ds A_H(γ_s) = ∫₀¹ σ(∂_t w - X_{H_t}(w), ∂_s w) dt`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_sub_intervalIntegral`).
* **Periodic orbits are critical.** Along a variation of a `1`-periodic orbit `γ` of `X_H`, the
  integrand vanishes at `s = 0`
  (`TauCeti.SmoothTwoForm.intervalIntegral_apply_sub_hamiltonianVectorField_eq_zero`).
* **Critical loops are periodic orbits.** Conversely, for a Hamiltonian which is `1`-periodic in
  time, if `γ' ≠ X_H(γ)` at some time `t₀`, pushing `γ` near `t₀ + ℤ` in a chart direction `e`
  with `σ(γ' - X_H, e) > 0` gives a variation along which the integral is positive. So on a
  manifold without boundary, a `C^n` loop, `n ≥ 1`, along all of whose `C^n` variations the
  integral vanishes at `s = 0` is a `1`-periodic orbit of `X_H`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.mem_periodicSolutions_of_forall_integral_eq_zero`).

The converse follows the chart-variation argument of the variational characterization of
geodesics, `TauCeti.Manifold.IsEnergyCritical.isGeodesicCurveOn`, and reuses its chart variations
`TauCeti.Manifold.chartVariation`, with amplitude `sin s` so that the displaced loops stay in a
chart for every `s`, and the smooth `1`-periodic bump profile `TauCeti.periodicBump` so that the
variations are again loops. These results are the common part of the variational
characterizations of the critical points of the contractible action
(`TauCeti.SmoothTwoForm.IsNondegenerate.isContractibleLoopActionCritical_iff`) and of the action
relative to a reference loop
(`TauCeti.SmoothTwoForm.IsNondegenerate.isReferenceActionCritical_iff`).

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_sub_intervalIntegral`: the first variation
  formula, from the variation of the area term.
* `TauCeti.SmoothTwoForm.intervalIntegral_apply_sub_hamiltonianVectorField_eq_zero`: the first
  variation vanishes at a periodic orbit.
* `TauCeti.SmoothTwoForm.IsNondegenerate.mem_periodicSolutions_of_forall_integral_eq_zero`:
  a loop along all of whose variations the first variation vanishes is a periodic orbit.

## References

* H. Hofer and E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Chapter 3 (the action functional on loops and its critical points).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1 (the first variation of the symplectic action).
-/

public section

noncomputable section

open Function Set Filter MeasureTheory
open scoped Manifold Interval Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-! ### The first variation formula -/

section FirstVariation

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E] {σ : SmoothTwoForm I M} {H : ℝ → M → ℝ}
  {w : ℝ × ℝ → M}

namespace SmoothTwoForm.IsNondegenerate

/-- **The first variation of an action functional.** Let `σ` be a nondegenerate two-form, `H` a
jointly `C¹` time-dependent Hamiltonian and `w` a `C¹` map of the plane. If a function `A`, the
area term of an action functional along the loops `w (s, ·)`, has at `s₀` the derivative
`-∫₀¹ σ(∂_s w, ∂_t w) dt` of the area swept out by these loops, then
`A(s) - ∫₀¹ H(t, w(s, t)) dt` has derivative `∫₀¹ σ(∂_t w - X_{H_t}(w), ∂_s w) dt` at `s₀`, with
all terms taken at `(s₀, t)`. -/
theorem hasDerivAt_sub_intervalIntegral (h : σ.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hwc : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 w)
    {A : ℝ → ℝ} {s₀ : ℝ}
    (hA : HasDerivAt A (-∫ t in 0..1, σ.1 (w (s₀, t)) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (1, 0),
      mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (0, 1)]) s₀) :
    HasDerivAt (fun s ↦ A s - ∫ t in 0..1, H t (w (s, t)))
      (∫ t in 0..1, σ.1 (w (s₀, t))
        ![mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (0, 1) - σ.hamiltonianVectorField (H t) (w (s₀, t)),
          mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (1, 0)]) s₀ := by
  have hσ : IsSmoothForm I 0 σ.1 := σ.isSmoothForm.of_le (by simp)
  convert hA.sub (Manifold.hasDerivAt_intervalIntegral_apply_comp hH hwc s₀ 0 1) using 1
  rw [← intervalIntegral.integral_neg]
  refine (intervalIntegral.integral_congr fun t _ ↦
    h.apply_sub_hamiltonianVectorField (H t) (w (s₀, t)) _ _).trans ?_
  exact intervalIntegral.integral_sub
    (((hσ.continuous_apply_mfderiv hwc (1, 0) (0, 1)).comp
      (continuous_const.prodMk continuous_id)).neg.intervalIntegrable _ _)
    ((Manifold.continuous_mvfderiv_apply_mfderiv hH hwc s₀).intervalIntegrable _ _)

/-- For a jointly `C¹` Hamiltonian and a `C¹` map of the plane, the integrand of the first
variation formula is continuous in `t`. -/
private theorem continuous_apply_sub_hamiltonianVectorField (h : σ.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hwc : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 w)
    (s₀ : ℝ) :
    Continuous fun t ↦ σ.1 (w (s₀, t))
      ![mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (0, 1) - σ.hamiltonianVectorField (H t) (w (s₀, t)),
        mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (1, 0)] :=
  ((((σ.isSmoothForm.of_le (by simp)).continuous_apply_mfderiv hwc (1, 0) (0, 1)).comp
    (continuous_const.prodMk continuous_id)).neg.sub
    (Manifold.continuous_mvfderiv_apply_mfderiv hH hwc s₀)).congr fun t ↦
    (h.apply_sub_hamiltonianVectorField (H t) (w (s₀, t)) _ _).symm

end SmoothTwoForm.IsNondegenerate

omit [FiniteDimensional ℝ E] in
/-- Along a variation of the loop `γ`, the first-variation integrand at `s = 0` is written with
the velocity of `γ`. -/
private theorem apply_eq_of_apply_zero {γ : ℝ → M} (h0 : ∀ t, w (0, t) = γ t) {t : ℝ}
    (hwd : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I w (0, t)) :
    σ.1 (w (0, t))
      ![mfderiv 𝓘(ℝ, ℝ × ℝ) I w (0, t) (0, 1) - σ.hamiltonianVectorField (H t) (w (0, t)),
        mfderiv 𝓘(ℝ, ℝ × ℝ) I w (0, t) (1, 0)] =
      σ.1 (γ t) ![Manifold.curveVelocity I γ t - σ.hamiltonianVectorField (H t) (γ t),
        mfderiv 𝓘(ℝ, ℝ × ℝ) I w (0, t) (1, 0)] := by
  have hγw : (fun t ↦ w (0, t)) = γ := funext h0
  have hv : Manifold.curveVelocity I γ t = mfderiv 𝓘(ℝ, ℝ × ℝ) I w (0, t) (0, 1) := by
    rw [← hγw]
    exact Manifold.curveVelocity_eq_mfderiv_snd (f := fun a b ↦ w (a, b)) hwd
  rw [hv, h0 t]

omit [FiniteDimensional ℝ E] in
/-- **The first variation vanishes at a periodic orbit.** Along a variation `w` of a `1`-periodic
orbit `γ` of `X_H`, differentiable along `s = 0`, the integrand
`σ(∂_t w - X_{H_t}(w), ∂_s w)` of the first variation formula vanishes at `s = 0`, since
`∂_t w(0, t) = γ'(t) = X_{H_t}(γ(t))`; so does its integral. -/
theorem SmoothTwoForm.intervalIntegral_apply_sub_hamiltonianVectorField_eq_zero {γ : ℝ → M}
    (horbit : γ ∈ periodicSolutions (fun t ↦ σ.hamiltonianVectorField (H t)) 1)
    (hwd : ∀ t, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I w (0, t)) (h0 : ∀ t, w (0, t) = γ t)
    (a b : ℝ) :
    ∫ t in a..b, σ.1 (w (0, t))
      ![mfderiv 𝓘(ℝ, ℝ × ℝ) I w (0, t) (0, 1) - σ.hamiltonianVectorField (H t) (w (0, t)),
        mfderiv 𝓘(ℝ, ℝ × ℝ) I w (0, t) (1, 0)] = 0 := by
  refine (intervalIntegral.integral_congr fun t _ ↦ ?_).trans intervalIntegral.integral_zero
  have hv : Manifold.curveVelocity I γ t = σ.hamiltonianVectorField (H t) (γ t) := by
    rw [← Manifold.curveVelocityWithin_univ]
    exact Manifold.curveVelocityWithin_eq_of_hasMFDerivWithinAt
      ((mem_periodicSolutions.mp horbit).1 t).hasMFDerivWithinAt uniqueDiffWithinAt_univ
  rw [apply_eq_of_apply_zero h0 (hwd t), hv, sub_self]
  exact (σ.1 (γ t)).map_coord_zero 0 rfl

/-- Along a `C¹` variation of the loop `γ`, the first-variation integrand at `s = 0` is
continuous. -/
private theorem SmoothTwoForm.IsNondegenerate.continuous_apply_curveVelocity_sub {γ : ℝ → M}
    (h : σ.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hwc : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 w) (h0 : ∀ t, w (0, t) = γ t) :
    Continuous fun t ↦ σ.1 (γ t) ![Manifold.curveVelocity I γ t -
      σ.hamiltonianVectorField (H t) (γ t), mfderiv 𝓘(ℝ, ℝ × ℝ) I w (0, t) (1, 0)] :=
  (h.continuous_apply_sub_hamiltonianVectorField hH hwc 0).congr fun t ↦
    apply_eq_of_apply_zero h0 ((hwc (0, t)).mdifferentiableAt one_ne_zero)

end FirstVariation

/-! ### Chart variations of a loop -/

section ChartVariation

variable {γ : ℝ → M} {x₀ : M} {J : Set ℝ} {φ : ℝ → ℝ} {e : E}

variable (I) in
/-- The chart variation `TauCeti.Manifold.chartVariation` of the loop `γ` with amplitude `sin s`:
`(s, t) ↦ ψ⁻¹ (ψ (γ t) + (sin s * φ t) • e)` at the times of `J`, and `γ` outside `J`. As the
amplitude stays in `[-1, 1]`, the displaced points stay near `γ` for every `s`. -/
private def loopChartVariation (γ : ℝ → M) (x₀ : M) (J : Set ℝ) (φ : ℝ → ℝ) (e : E)
    (z : ℝ × ℝ) : M :=
  Manifold.chartVariation I γ x₀ J φ e (Real.sin z.1) z.2

/-- The loop of the chart variation at `s = 0` is `γ`. -/
private theorem loopChartVariation_zero (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source) (t : ℝ) :
    loopChartVariation I γ x₀ J φ e (0, t) = γ t :=
  Manifold.chartVariation_of_mul_eq_zero hJ (by rw [Real.sin_zero, zero_mul])

/-- The chart variation of a `1`-periodic loop, with a `1`-periodic set of times and profile, is
`1`-periodic in `t`. -/
private theorem loopChartVariation_add_one (hγ : ∀ t, γ (t + 1) = γ t)
    (hJ : ∀ t, t + 1 ∈ J ↔ t ∈ J) (hφ : ∀ t, φ (t + 1) = φ t) (z : ℝ × ℝ) :
    loopChartVariation I γ x₀ J φ e (z.1, z.2 + 1) = loopChartVariation I γ x₀ J φ e z := by
  by_cases h : z.2 ∈ J
  · simp only [loopChartVariation, Manifold.chartVariation_of_mem h,
      Manifold.chartVariation_of_mem ((hJ _).mpr h), hγ, hφ]
  · simp only [loopChartVariation, Manifold.chartVariation_of_notMem h,
      Manifold.chartVariation_of_notMem (mt (hJ _).mp h), hγ]

/-- Outside `J`, the variation field of the chart variation vanishes. -/
private theorem mfderiv_loopChartVariation_of_notMem {t : ℝ}
    (hw : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (loopChartVariation I γ x₀ J φ e) (0, t))
    (htJ : t ∉ J) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I (loopChartVariation I γ x₀ J φ e) (0, t) (1, 0) = 0 := by
  have hfun : (fun s ↦ loopChartVariation I γ x₀ J φ e (s, t)) = fun _ ↦ γ t :=
    funext fun s ↦ Manifold.chartVariation_of_notMem htJ _
  rw [← Manifold.curveVelocity_eq_mfderiv_fst (f := fun a b ↦ loopChartVariation I γ x₀ J φ e
      (a, b)) hw, hfun, Manifold.curveVelocity_const]
  rfl

variable [I.Boundaryless] [IsManifold I ∞ M] {n : ℕ∞}

/-- On a `C^n` manifold without boundary, the chart variation of a `C^n` loop, for a `C^n` profile
supported in the open set `J` along which the displaced points stay in the chart target, is
`C^n`. -/
private theorem contMDiff_loopChartVariation (hJo : IsOpen J)
    (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source)
    (hT : ∀ t ∈ J, ∀ c : ℝ, |c| ≤ 1 →
      extChartAt I x₀ (γ t) + (c * φ t) • e ∈ (extChartAt I x₀).target)
    (hφ : ContDiff ℝ n φ) (hφJ : tsupport φ ⊆ J) (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I n (loopChartVariation I γ x₀ J φ e) := by
  have : IsManifold I n M := IsManifold.of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
  rintro ⟨s, t⟩
  exact (Manifold.contMDiffAt_chartVariation (n := n) hJo hJ hφ hφJ (hγ t)
    fun htJ ↦ hT t htJ _ (Real.abs_sin_le_one s)).comp (s, t)
    ((Real.contDiff_sin.prodMap contDiff_id).contMDiff (s, t))

/-- The variation field of the chart variation: at a time `t` of `J` it is `φ t` times the tangent
vector at `γ t` with coordinates `e` in the tangent-bundle trivialization at `x₀`. -/
private theorem mfderiv_loopChartVariation_of_mem (hn : 1 ≤ n) (hJo : IsOpen J)
    (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source) (hφ : ContDiff ℝ n φ) (hφJ : tsupport φ ⊆ J)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ)
    (hw : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n (loopChartVariation I γ x₀ J φ e)) {t : ℝ} (htJ : t ∈ J) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I (loopChartVariation I γ x₀ J φ e) (0, t) (1, 0) =
      φ t • (trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ t) e := by
  have : IsManifold I n M := IsManifold.of_le (n := ∞) (WithTop.coe_le_coe.2 le_top)
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hn).ne'
  -- the transverse curve of the chart variation at `t` is differentiable at `s = 0`
  have hd : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s ↦ Manifold.chartVariation I γ x₀ J φ e s t) 0 :=
    ((Manifold.contMDiffAt_chartVariation (n := n) (e := e) (s := 0) hJo hJ hφ hφJ (hγ t)
      fun htJ ↦ by simpa using (extChartAt I x₀).map_source (hJ t htJ)).comp 0
      ((contDiff_id.prodMk contDiff_const).contMDiff 0)).mdifferentiableAt hn0
  -- reparametrizing by `s ↦ sin s`, whose derivative at `0` is `1`, with the base point `sin 0`
  -- normalized to `0`
  have hvel : ∀ y, Real.sin 0 = y →
      MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s ↦ Manifold.chartVariation I γ x₀ J φ e s t) y →
      Manifold.curveVelocity I (fun s ↦ loopChartVariation I γ x₀ J φ e (s, t)) 0 =
        Manifold.curveVelocity I (fun s ↦ Manifold.chartVariation I γ x₀ J φ e s t) y := by
    rintro y rfl hy
    have h := Manifold.curveVelocity_comp (c := 1) (by simpa using Real.hasDerivAt_sin 0) hy
    rw [one_smul] at h
    exact h
  rw [← Manifold.curveVelocity_eq_mfderiv_fst (f := fun a b ↦ loopChartVariation I γ x₀ J φ e
      (a, b)) ((hw (0, t)).mdifferentiableAt hn0), hvel 0 Real.sin_zero hd,
    ← Manifold.variationField_apply, Manifold.variationField_chartVariation hJ htJ]

end ChartVariation

/-! ### Loops along which the first variation vanishes -/

section CriticalLoops

open Real

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E] {σ : SmoothTwoForm I M} {H : ℝ → M → ℝ}
  {γ : ℝ → M} {n : ℕ∞}

namespace SmoothTwoForm.IsNondegenerate

/-- **The chart variations of a loop.** Let `γ` be a `C^n` loop, `n ≥ 1`, along all of whose `C^n`
variations through loops the first variation vanishes at `s = 0`. Let `J` be an open `1`-periodic
set of times on which `γ` stays in the chart at `x₀`, and `φ` a `C^n` `1`-periodic profile
supported in `J` such that the points `ψ (γ t) + (c φ(t)) • e`, `|c| ≤ 1`, stay in the chart
target. Write `g t` for the pairing of the obstruction `γ' - X_H` at `t` with the tangent vector of
chart coordinates `e` at `γ t`. Then `∫₀¹ φ g = 0`, and `φ g` is continuous. -/
private theorem integral_mul_apply_eq_zero [I.Boundaryless] (h : σ.IsNondegenerate)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hn : 1 ≤ n)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ) (hγper : ∀ t, γ (t + 1) = γ t)
    (hvar : ∀ ⦃w : ℝ × ℝ → M⦄, ContMDiff 𝓘(ℝ, ℝ × ℝ) I n w →
      (∀ z : ℝ × ℝ, w (z.1, z.2 + 1) = w z) → (∀ t, w (0, t) = γ t) →
      ∫ t in 0..1, σ.1 (w (0, t))
        ![mfderiv 𝓘(ℝ, ℝ × ℝ) I w (0, t) (0, 1) - σ.hamiltonianVectorField (H t) (w (0, t)),
          mfderiv 𝓘(ℝ, ℝ × ℝ) I w (0, t) (1, 0)] = 0)
    {x₀ : M} {J : Set ℝ} {φ : ℝ → ℝ} {e : E} (hJo : IsOpen J) (hJper : ∀ t, t + 1 ∈ J ↔ t ∈ J)
    (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source)
    (hT : ∀ t ∈ J, ∀ c : ℝ, |c| ≤ 1 →
      extChartAt I x₀ (γ t) + (c * φ t) • e ∈ (extChartAt I x₀).target)
    (hφ : ContDiff ℝ n φ) (hφper : ∀ t, φ (t + 1) = φ t) (hφJ : tsupport φ ⊆ J) :
    (∫ t in 0..1, φ t * σ.1 (γ t) ![Manifold.curveVelocity I γ t -
        σ.hamiltonianVectorField (H t) (γ t), (trivializationAt E (TangentSpace I) x₀).symmL ℝ
          (γ t) e]) = 0 ∧
      Continuous fun t ↦ φ t * σ.1 (γ t) ![Manifold.curveVelocity I γ t -
        σ.hamiltonianVectorField (H t) (γ t), (trivializationAt E (TangentSpace I) x₀).symmL ℝ
          (γ t) e] := by
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hn).ne'
  set w := loopChartVariation I γ x₀ J φ e
  have hwc : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n w := contMDiff_loopChartVariation hJo hJ hT hφ hφJ hγ
  have hwc1 : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 w := hwc.of_le (by exact_mod_cast hn)
  have hw0 : ∀ t, w (0, t) = γ t := loopChartVariation_zero hJ
  have hwper := loopChartVariation_add_one (I := I) (x₀ := x₀) (e := e) hγper hJper hφper
  -- the first-variation integrand along `w` is `φ g`
  have hpt : ∀ t, σ.1 (γ t) ![Manifold.curveVelocity I γ t -
      σ.hamiltonianVectorField (H t) (γ t), mfderiv 𝓘(ℝ, ℝ × ℝ) I w (0, t) (1, 0)] =
      φ t * σ.1 (γ t) ![Manifold.curveVelocity I γ t - σ.hamiltonianVectorField (H t) (γ t),
        (trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ t) e] := by
    intro t
    by_cases htJ : t ∈ J
    · rw [mfderiv_loopChartVariation_of_mem hn hJo hJ hφ hφJ hγ hwc htJ,
        ← SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_smul_right,
        SmoothBundleForm.eval₂_apply, smul_eq_mul]
    · have hφt : φ t = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦ htJ (hφJ h')
      rw [mfderiv_loopChartVariation_of_notMem ((hwc (0, t)).mdifferentiableAt hn0) htJ, hφt,
        zero_mul]
      exact (σ.1 (γ t)).map_coord_zero 1 rfl
  refine ⟨?_, (h.continuous_apply_curveVelocity_sub hH hwc1 hw0).congr hpt⟩
  exact (intervalIntegral.integral_congr fun t _ ↦ (hpt t).symm.trans
    (apply_eq_of_apply_zero hw0 ((hwc (0, t)).mdifferentiableAt hn0)).symm).trans
    (hvar hwc hwper hw0)

/-- **Loops along which the first variation vanishes are periodic orbits.** Let `σ` be a
nondegenerate two-form on a manifold without boundary modelled on a finite-dimensional space, and
`H` a jointly `C¹` Hamiltonian, `1`-periodic in time. Let `γ` be a `1`-periodic `C^n` loop,
`n ≥ 1`, such that for every `C^n` variation `w` through loops starting at `γ`,
`∫₀¹ σ(∂_t w - X_{H_t}(w), ∂_s w) dt = 0` at `s = 0`. Then `γ` is a `1`-periodic orbit of
`X_H`. -/
theorem mem_periodicSolutions_of_forall_integral_eq_zero [I.Boundaryless]
    (h : σ.IsNondegenerate) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hP : ∀ t, H (t + 1) = H t) (hn : 1 ≤ n) (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ)
    (hγper : ∀ t, γ (t + 1) = γ t)
    (hvar : ∀ ⦃w : ℝ × ℝ → M⦄, ContMDiff 𝓘(ℝ, ℝ × ℝ) I n w →
      (∀ z : ℝ × ℝ, w (z.1, z.2 + 1) = w z) → (∀ t, w (0, t) = γ t) →
      ∫ t in 0..1, σ.1 (w (0, t))
        ![mfderiv 𝓘(ℝ, ℝ × ℝ) I w (0, t) (0, 1) - σ.hamiltonianVectorField (H t) (w (0, t)),
          mfderiv 𝓘(ℝ, ℝ × ℝ) I w (0, t) (1, 0)] = 0) :
    γ ∈ periodicSolutions (fun t ↦ σ.hamiltonianVectorField (H t)) 1 := by
  have hγd : MDifferentiable 𝓘(ℝ, ℝ) I γ :=
    hγ.mdifferentiable (by exact_mod_cast (zero_lt_one.trans_le hn).ne')
  have hγp : Periodic γ 1 := hγper
  refine TauCeti.mem_periodicSolutions.mpr ⟨fun t₀ ↦ ?_, hγper⟩
  suffices hv : Manifold.curveVelocity I γ t₀ = σ.hamiltonianVectorField (H t₀) (γ t₀) by
    rw [← hv]
    exact Manifold.hasMFDerivAt_curveVelocity (hγd t₀)
  by_contra hne
  set x₀ := γ t₀
  -- a tangent vector `u` at `x₀` pairing positively with the obstruction `γ' - X_H` at `t₀`
  obtain ⟨u, hu⟩ : ∃ u : TangentSpace I x₀, 0 < σ.1 x₀
      ![Manifold.curveVelocity I γ t₀ - σ.hamiltonianVectorField (H t₀) x₀, u] := by
    obtain ⟨v, hv⟩ : ∃ v, SmoothBundleForm.eval₂ σ x₀
        (Manifold.curveVelocity I γ t₀ - σ.hamiltonianVectorField (H t₀) x₀) v ≠ 0 := by
      by_contra hcon
      exact sub_ne_zero.mpr hne (SmoothTwoForm.isNondegenerate_iff_separatingLeft.mp h x₀ _
        fun v ↦ not_not.mp (not_exists.mp hcon v))
    rw [SmoothBundleForm.eval₂_apply] at hv
    refine ⟨(σ.1 x₀ ![Manifold.curveVelocity I γ t₀ - σ.hamiltonianVectorField (H t₀) x₀, v]) • v,
      ?_⟩
    rw [← SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_smul_right,
      SmoothBundleForm.eval₂_apply, smul_eq_mul]
    exact mul_self_pos.mpr hv
  -- a ball of radius `2ρ` around `ψ x₀` in the target of the extended chart `ψ` at `x₀`
  obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0,
      Metric.ball (extChartAt I x₀ x₀) (2 * ρ) ⊆ (extChartAt I x₀).target := by
    obtain ⟨ε, hε, hb⟩ :=
      Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := I) x₀) _ (mem_extChartAt_target x₀)
    exact ⟨ε / 2, by positivity, by rwa [mul_div_cancel₀ _ two_ne_zero]⟩
  -- a radius `δ ≤ 1/4` of times near `t₀` along which `γ` stays within `ρ` of `x₀` in the chart
  obtain ⟨δ₀, hδ₀, hδ₀U⟩ := Metric.mem_nhds_iff.mp
    ((hγ.continuous.continuousAt (x := t₀)).preimage_mem_nhds
      (inter_mem ((isOpen_extChartAt_source (I := I) x₀).mem_nhds (mem_extChartAt_source x₀))
        ((continuousAt_extChartAt (I := I) x₀).preimage_mem_nhds (Metric.ball_mem_nhds _ hρ))))
  set δ := min δ₀ (1 / 4)
  have hδ : 0 < δ := lt_min hδ₀ (by norm_num)
  have hδ2 : δ ≤ 1 / 2 := (min_le_right _ _).trans (by norm_num)
  have hγU : ∀ t, |t - t₀| < δ → γ t ∈ (extChartAt I x₀).source ∧
      dist (extChartAt I x₀ (γ t)) (extChartAt I x₀ x₀) < ρ := fun t ht ↦
    hδ₀U (by rw [Metric.mem_ball, Real.dist_eq]; exact ht.trans_le (min_le_left _ _))
  -- the chart vector `e`, shorter than `ρ`, of tangent vector `κ • u` at `x₀`
  set e₀ : E := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x₀ u
  set κ : ℝ := ρ / (‖e₀‖ + 1)
  have hκ : 0 < κ := by positivity
  set e : E := κ • e₀
  have he : ‖e‖ < ρ := by
    rw [norm_smul, Real.norm_of_nonneg hκ.le, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg e₀]
  -- `g t` pairs the obstruction at `t` with the tangent vector of chart coordinates `e`
  set g : ℝ → ℝ := fun t ↦ σ.1 (γ t) ![Manifold.curveVelocity I γ t -
    σ.hamiltonianVectorField (H t) (γ t), (trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ t) e]
  have hg₀ : 0 < g t₀ := by
    have he₀ : (trivializationAt E (TangentSpace I) x₀).symmL ℝ x₀ e = κ • u := by
      rw [map_smul, Bundle.Trivialization.symmL_continuousLinearMapAt _
        (FiberBundle.mem_baseSet_trivializationAt' x₀)]
    simp only [g]
    rw [he₀, ← SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_smul_right,
      SmoothBundleForm.eval₂_apply, smul_eq_mul]
    exact mul_pos hκ hu
  have hgper : Periodic g 1 := fun t ↦ by
    simp only [g]
    rw [hγp.curveVelocity_add (hγd _), hP, hγper]
  -- the bump of radius `r ≤ δ`, supported where `cos (2π(t - t₀)) > cos (πr)`, has a chart
  -- variation, so `∫₀¹ φ g = 0` with `φ g` continuous
  have hcosr : ∀ r, 0 < r → r ≤ 1 / 2 → cos (2 * π * r) < cos (π * r) :=
    fun r hr hr2 ↦ cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith [pi_pos])
      (by nlinarith [pi_pos])
  have hcos1 : ∀ r, 0 < r → r ≤ 1 / 2 → cos (π * r) < 1 := fun r hr hr2 ↦ by
    simpa using cos_lt_cos_of_nonneg_of_le_pi le_rfl (by nlinarith [pi_pos])
      (by positivity : 0 < π * r)
  have hbump : ∀ r, 0 < r → r ≤ δ → (∫ t in 0..1, periodicBump t₀ (cos (π * r)) t * g t) = 0 ∧
      Continuous fun t ↦ periodicBump t₀ (cos (π * r)) t * g t := by
    intro r hr hrδ
    have hr2 : r ≤ 1 / 2 := hrδ.trans hδ2
    set J := {t | cos (2 * π * r) < cos (2 * π * (t - t₀))}
    -- on `J`, `γ` stays within `ρ` of `x₀` in the chart, by periodicity
    have hJγ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source ∧
        dist (extChartAt I x₀ (γ t)) (extChartAt I x₀ x₀) < ρ := by
      intro t ht
      obtain ⟨k, hk⟩ := exists_abs_sub_int_lt_of_cos_lt hr.le ht
      have h' := hγU (t - k * 1) (by
        rw [mul_one, show t - k - t₀ = t - t₀ - k by ring]
        exact hk.trans_le hrδ)
      rwa [hγp.sub_int_mul_eq] at h'
    refine integral_mul_apply_eq_zero h hH hn hγ hγper hvar
      (isOpen_lt continuous_const (by fun_prop))
      (fun t ↦ by simp only [mem_ofPred_eq,
        show 2 * π * (t + 1 - t₀) = 2 * π * (t - t₀) + 2 * π by ring, cos_add_two_pi])
      (fun t ht ↦ (hJγ t ht).1) (fun t ht c hc1 ↦ ?_) (contDiff_periodicBump _ _)
      (periodicBump_add_one _ _)
      ((tsupport_periodicBump_subset (hcos1 r hr hr2)).trans fun t ht ↦
        (hcosr r hr hr2).trans_le ht)
    -- the displaced points stay in the ball of radius `2ρ`
    have hc1' : |c| * periodicBump t₀ (cos (π * r)) t ≤ 1 := by
      simpa using mul_le_mul hc1 (periodicBump_le_one t₀ (cos (π * r)) t)
        (periodicBump_nonneg _ _ _) zero_le_one
    have hce : ‖(c * periodicBump t₀ (cos (π * r)) t) • e‖ ≤ ‖e‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (periodicBump_nonneg _ _ _)]
      exact mul_le_of_le_one_left (norm_nonneg e) hc1'
    refine hball (Metric.mem_ball.mpr ?_)
    calc dist (extChartAt I x₀ (γ t) + (c * periodicBump t₀ (cos (π * r)) t) • e)
          (extChartAt I x₀ x₀)
        ≤ dist (extChartAt I x₀ (γ t)) (extChartAt I x₀ x₀) +
            ‖(c * periodicBump t₀ (cos (π * r)) t) • e‖ := by
          rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]
          exact norm_add_le _ _
      _ < ρ + ρ := add_lt_add_of_lt_of_le (hJγ t ht).2 (hce.trans he.le)
      _ = 2 * ρ := by ring
  -- `g` is continuous at `t₀`, where it agrees with `φ g` for a bump `φ` equal to `1` near `t₀`
  have hgcont : ContinuousAt g t₀ := by
    refine (hbump δ hδ le_rfl).2.continuousAt.congr ?_
    filter_upwards [eventually_periodicBump_eq_one (hcos1 δ hδ hδ2)] with t ht
    rw [ht, one_mul]
  -- a bump supported, on `[t₀ - 1/2, t₀ + 1/2]`, where `g > 0` gives a nonnegative continuous
  -- periodic `φ g` with zero integral over a period, but `φ g = g > 0` at `t₀`
  obtain ⟨ε, hε, hεg⟩ := Metric.eventually_nhds_iff.mp (hgcont.eventually (lt_mem_nhds hg₀))
  set r := min δ ε
  have hr : 0 < r := lt_min hδ hε
  have hr2 : r ≤ 1 / 2 := (min_le_left _ _).trans hδ2
  obtain ⟨hint, hcont⟩ := hbump r hr (min_le_left _ _)
  have hnn : ∀ t ∈ Icc (t₀ - 1 / 2) (t₀ - 1 / 2 + 1),
      0 ≤ periodicBump t₀ (cos (π * r)) t * g t := by
    intro t ht
    by_cases hb : periodicBump t₀ (cos (π * r)) t = 0
    · simp [hb]
    have hlt := lt_cos_of_periodicBump_ne_zero (hcos1 r hr hr2) hb
    rw [show π * r = 2 * π * (r / 2) by ring] at hlt
    obtain ⟨k, hk⟩ := exists_abs_sub_int_lt_of_cos_lt (by positivity) hlt
    -- the only integer within `r / 2 ≤ 1/4` of `t - t₀ ∈ [-1/2, 1/2]` is `0`
    have hk0 : k = 0 := by
      have htt : |t - t₀| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have h1 : |(k : ℝ)| < 1 := by
        calc |(k : ℝ)| = |(t - t₀) - (t - t₀ - k)| := by ring_nf
          _ ≤ |t - t₀| + |t - t₀ - k| := abs_sub _ _
          _ < 1 := by linarith
      exact Int.abs_lt_one_iff.mp (by exact_mod_cast h1)
    subst hk0
    rw [Int.cast_zero, sub_zero] at hk
    exact mul_nonneg (periodicBump_nonneg _ _ _)
      (hεg (by rw [Real.dist_eq]; linarith [min_le_right δ ε])).le
  have heq : periodicBump t₀ (cos (π * r)) t₀ * g t₀ = 0 :=
    Periodic.eqOn_zero_of_intervalIntegral_eq_zero
    (fun t ↦ by simp only [periodicBump_add_one, hgper t]) hcont hnn hint
    (⟨by linarith, by linarith⟩ : t₀ ∈ Ioo (t₀ - 1 / 2) (t₀ - 1 / 2 + 1))
  rw [(eventually_periodicBump_eq_one (hcos1 r hr hr2)).self_of_nhds, one_mul] at heq
  exact hg₀.ne' heq

end SmoothTwoForm.IsNondegenerate

end CriticalLoops

end TauCeti
