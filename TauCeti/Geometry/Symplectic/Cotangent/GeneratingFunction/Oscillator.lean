/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Oscillator.Basic

/-!
# The harmonic oscillator as a generated canonical transformation

The harmonic oscillator with Hamiltonian `(q² + p²) / 2` has the globally smooth evolution
`TauCeti.oscillatorEvolution t (q, p) = (q cos t + p sin t, -q sin t + p cos t)`.
Its position projection `(q, p) ↦ (q, Q)` is invertible exactly when `sin t ≠ 0`.
At those times `TauCeti.oscillatorGeneratingFunction` generates this evolution through the
existing first-kind cotangent relation and its inverse-function branch. At multiples of π the
position projection fails, although the evolution itself remains smooth and symplectic.

Cotangent covectors on the real line are identified with scalar momenta by evaluation at `1`,
using Mathlib's `ContinuousLinearMap.toSpanSingletonCLE` in the reverse direction.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, §48
  (generating functions and their coordinate singularities).
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter
open scoped Topology

/-- The type-one position projection `(q, p) ↦ (q, Q)` of oscillator evolution. -/
def oscillatorPositionProjection (t : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
  (fst ℝ ℝ ℝ).prod (Real.cos t • fst ℝ ℝ ℝ + Real.sin t • snd ℝ ℝ ℝ)

@[simp]
theorem oscillatorPositionProjection_apply (t : ℝ) (x : ℝ × ℝ) :
    oscillatorPositionProjection t x = (x.1, (oscillatorEvolution t x).1) := by
  simp [oscillatorPositionProjection, oscillatorEvolution_apply]

/-- The type-one projection is invertible precisely away from multiples of π. -/
theorem isInvertible_oscillatorPositionProjection_iff (t : ℝ) :
    (oscillatorPositionProjection t).IsInvertible ↔ Real.sin t ≠ 0 := by
  constructor
  · rintro ⟨e, he⟩ hs
    have h : e (0, 1) = e (0, 0) := by
      have h₁ := DFunLike.congr_fun he (0, 1)
      have h₀ := DFunLike.congr_fun he (0, 0)
      calc
        e (0, 1) = oscillatorPositionProjection t (0, 1) := h₁
        _ = oscillatorPositionProjection t (0, 0) := by
          simp [oscillatorPositionProjection, hs]
        _ = e (0, 0) := h₀.symm
    have := e.injective h
    norm_num at this
  · intro hs
    refine IsInvertible.of_inverse
      (g := (fst ℝ ℝ ℝ).prod
        ((Real.sin t)⁻¹ • (snd ℝ ℝ ℝ - Real.cos t • fst ℝ ℝ ℝ))) ?_ ?_
    all_goals
      ext <;> simp [oscillatorPositionProjection, hs, field]

/-- Integer multiples of π are exactly the singular times of the position projection. -/
theorem not_isInvertible_oscillatorPositionProjection_iff (t : ℝ) :
    ¬(oscillatorPositionProjection t).IsInvertible ↔ ∃ k : ℤ, (k : ℝ) * Real.pi = t := by
  simp [isInvertible_oscillatorPositionProjection_iff, Real.sin_eq_zero_iff]

/-- The first-kind oscillator generating function, meaningful as a generator when `sin t ≠ 0`.
Lean's total division assigns a value also at the singular times. -/
def oscillatorGeneratingFunction (t : ℝ) (x : ℝ × ℝ) : ℝ :=
  (2 * x.1 * x.2 - (x.1 ^ 2 + x.2 ^ 2) * Real.cos t) / (2 * Real.sin t)

/-- The defining formula of the oscillator generating function. -/
theorem oscillatorGeneratingFunction_apply (t : ℝ) (x : ℝ × ℝ) :
    oscillatorGeneratingFunction t x =
      (2 * x.1 * x.2 - (x.1 ^ 2 + x.2 ^ 2) * Real.cos t) / (2 * Real.sin t) :=
  (rfl)

/-- For fixed time the generating function is smooth in both position variables. -/
theorem contDiff_oscillatorGeneratingFunction {n : WithTop ℕ∞} (t : ℝ) :
    ContDiff ℝ n (oscillatorGeneratingFunction t) :=
  (((contDiff_const.mul contDiff_fst).mul contDiff_snd).sub
    (((contDiff_fst.pow 2).add (contDiff_snd.pow 2)).mul contDiff_const)).div_const _

/-- Derivative of the generating function, in the source and target position variables. -/
theorem fderiv_oscillatorGeneratingFunction (t : ℝ) (x u : ℝ × ℝ) :
    fderiv ℝ (oscillatorGeneratingFunction t) x u =
      ((x.2 - Real.cos t * x.1) * u.1 + (x.1 - Real.cos t * x.2) * u.2) /
        Real.sin t := by
  have h := ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).const_mul 2).mul
    (hasFDerivAt_snd (𝕜 := ℝ) (p := x))).sub ((((hasFDerivAt_fst (𝕜 := ℝ) (p := x)).pow 2).add
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := x)).pow 2)).mul_const
        (Real.cos t))).mul_const (2 * Real.sin t)⁻¹
  have hf : (fun y : ℝ × ℝ ↦
      (2 * y.1 * y.2 - (y.1 ^ 2 + y.2 ^ 2) * Real.cos t) * (2 * Real.sin t)⁻¹) =
      oscillatorGeneratingFunction t := by
    funext y
    simp [oscillatorGeneratingFunction_apply, div_eq_mul_inv]
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply] at h
  rw [← hf, h.fderiv]
  simp
  ring

/-- The source momentum is `(Q - q cos t) / sin t`. -/
@[simp]
theorem cotangentGeneratingSource_oscillatorGeneratingFunction (t q Q : ℝ) :
    cotangentGeneratingSource (oscillatorGeneratingFunction t) (q, Q) =
      (q, toSpanSingleton ℝ ((Q - Real.cos t * q) / Real.sin t)) := by
  apply Prod.ext (by simp)
  apply ContinuousLinearMap.ext
  intro a
  simp [fderiv_oscillatorGeneratingFunction, toSpanSingleton_apply]
  ring

/-- The target momentum is `(Q cos t - q) / sin t`. -/
@[simp]
theorem cotangentGeneratingTarget_oscillatorGeneratingFunction (t q Q : ℝ) :
    cotangentGeneratingTarget (oscillatorGeneratingFunction t) (q, Q) =
      (Q, toSpanSingleton ℝ ((Real.cos t * Q - q) / Real.sin t)) := by
  apply Prod.ext (by simp)
  apply ContinuousLinearMap.ext
  intro a
  simp [fderiv_oscillatorGeneratingFunction, toSpanSingleton_apply]
  ring

/-- The generating relation is exactly the graph of oscillator evolution, after identifying
scalar momenta with covectors on the real line. -/
theorem oscillatorGeneratingFunction_relation_iff {t q p Q P : ℝ} (ht : Real.sin t ≠ 0) :
    (cotangentGeneratingSource (oscillatorGeneratingFunction t) (q, Q) =
        (q, toSpanSingleton ℝ p) ∧
      cotangentGeneratingTarget (oscillatorGeneratingFunction t) (q, Q) =
        (Q, toSpanSingleton ℝ P)) ↔ oscillatorEvolution t (q, p) = (Q, P) := by
  have hc := Real.sin_sq_add_cos_sq t
  simp only [cotangentGeneratingSource_oscillatorGeneratingFunction,
    cotangentGeneratingTarget_oscillatorGeneratingFunction, Prod.mk.injEq, true_and,
    toSpanSingleton_inj, oscillatorEvolution_apply]
  constructor
  · rintro ⟨hp, hP⟩
    rw [div_eq_iff ht] at hp hP
    constructor
    · nlinarith
    · apply (mul_right_inj' ht).mp
      linear_combination -Real.cos t * hp + hP - q * hc
  · rintro ⟨hq, hP⟩
    constructor <;> apply (div_eq_iff ht).2
    · linarith
    · linear_combination -Real.cos t * hq + Real.sin t * hP + q * hc

/-- The mixed Hessian is multiplication by `1 / sin t`, with scalar momenta viewed as covectors. -/
theorem cotangentMixedHessian_oscillatorGeneratingFunction_apply_apply (t : ℝ)
    (x : ℝ × ℝ) (b a : ℝ) :
    cotangentMixedHessian (oscillatorGeneratingFunction t) x b a = b * a / Real.sin t := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ :=
    ((Real.sin t)⁻¹ * a) • (snd ℝ ℝ ℝ - Real.cos t • fst ℝ ℝ ℝ)
  have hf : (fun y ↦ fderiv ℝ (oscillatorGeneratingFunction t) y (a, 0)) = L := by
    funext y
    simp [fderiv_oscillatorGeneratingFunction, L, div_eq_mul_inv]
    ring
  have hd : DifferentiableAt ℝ (fderiv ℝ (oscillatorGeneratingFunction t)) x :=
    (((contDiff_oscillatorGeneratingFunction (n := 2) t).contDiffAt.fderiv_right
      (m := 1) le_rfl).differentiableAt one_ne_zero)
  have h := congrArg (fun f : (ℝ × ℝ) → ℝ ↦ fderiv ℝ f x (0, b)) hf
  rw [fderiv_clm_apply hd (differentiableAt_const (a, 0)), L.fderiv] at h
  rw [cotangentMixedHessian_apply_apply]
  simpa [L, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

/-- At a nonsingular time the mixed Hessian is a continuous linear equivalence. -/
theorem isInvertible_cotangentMixedHessian_oscillatorGeneratingFunction {t : ℝ}
    (ht : Real.sin t ≠ 0) (x : ℝ × ℝ) :
    (cotangentMixedHessian (oscillatorGeneratingFunction t) x).IsInvertible := by
  refine ⟨(Units.mk0 (Real.sin t)⁻¹ (inv_ne_zero ht)) •
    (toSpanSingletonCLE : ℝ ≃L[ℝ] StrongDual ℝ ℝ), ?_⟩
  apply ContinuousLinearMap.ext
  intro b
  apply ContinuousLinearMap.ext
  intro a
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (cotangentMixedHessian_oscillatorGeneratingFunction_apply_apply t x b a).symm

/-- The inverse-function branch of the generating relation gives the oscillator evolution near
any source point at a nonsingular time. -/
theorem cotangentGeneratedMap_oscillatorGeneratingFunction_eventuallyEq {t : ℝ}
    (ht : Real.sin t ≠ 0) {x₀ : ℝ × ℝ}
    (hS : ContDiffAt ℝ 2 (oscillatorGeneratingFunction t) x₀)
    (hM : (cotangentMixedHessian (oscillatorGeneratingFunction t) x₀).IsInvertible) :
    cotangentGeneratedMap hS hM =ᶠ[𝓝 (cotangentGeneratingSource
        (oscillatorGeneratingFunction t) x₀)]
      fun y ↦ (let z := oscillatorEvolution t (y.1, y.2 1)
        (z.1, toSpanSingleton ℝ z.2)) := by
  filter_upwards [eventually_cotangentGeneratingSource_cotangentGeneratingBranch hS hM]
    with y hy
  rcases hb : cotangentGeneratingBranch hS hM y with ⟨q, Q⟩
  rw [hb] at hy
  have hp : y.2 = toSpanSingleton ℝ (y.2 1) :=
    ((toSpanSingletonCLE : ℝ ≃L[ℝ] StrongDual ℝ ℝ).apply_symm_apply y.2).symm
  have hs : cotangentGeneratingSource (oscillatorGeneratingFunction t) (q, Q) =
      (q, toSpanSingleton ℝ (y.2 1)) := by
    rw [hy, ← hp]
    exact Prod.ext (by simpa using (congrArg Prod.fst hy).symm) rfl
  have he := (oscillatorGeneratingFunction_relation_iff ht).1
    ⟨hs, cotangentGeneratingTarget_oscillatorGeneratingFunction t q Q⟩
  have hq : y.1 = q := by simpa using (congrArg Prod.fst hy).symm
  rw [cotangentGeneratedMap_def, Function.comp_apply, hb,
    cotangentGeneratingTarget_oscillatorGeneratingFunction, hq, he]

end TauCeti
