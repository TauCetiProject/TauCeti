/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Line integrals along piecewise `C¹` and periodic curves

Let `γ : ℝ → M` be a curve which agrees, on the open intervals between consecutive parameters
`t i` and `t (i + 1)`, with `C¹` curves `f i`. Then a continuous `1`-form evaluated on the
velocity of `γ` is integrable from `t 0` to `t n`, and the line integral along `γ` from `t 0` to
`t n` is the sum of the line integrals along the pieces `f i` from `t i` to `t (i + 1)`.

The velocity of a `T`-periodic curve is `T`-periodic, also at the parameters where the curve is
not differentiable (`Function.Periodic.curveVelocity_add`), so a `1`-form evaluated on it is
`T`-periodic. Hence the line integral of a `1`-form along a `T`-periodic curve over an interval of
length `T` does not depend on the interval, and an integrand which is integrable over one period
is integrable over every interval. A closed curve on the circle `AddCircle T`, seen as a periodic
curve on `ℝ`, is the basic example: when it is given on a period by finitely many `C¹` pieces,
its line integral over any interval of length `T` is the sum of the line integrals along the
pieces.

## Main results

* `TauCeti.pathIntegral_eq_sum_of_eqOn`: the line integral along a curve given by `C¹` pieces is
  the sum of the line integrals along the pieces.
* `TauCeti.IsSmoothForm.intervalIntegrable_apply_curveVelocity_of_eqOn`: the integrand along such
  a curve is integrable.
* `Function.Periodic.pathIntegral_add_eq`: the line integral along a `T`-periodic curve over
  `a..a + T` does not depend on `a`.
* `Function.Periodic.intervalIntegrable_apply_curveVelocity`: an integrand along a periodic curve
  which is integrable over one period is integrable over every interval.
-/
public section

noncomputable section

open Set Function Filter MeasureTheory
open scoped Manifold Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : RoughForm I M F 1} {γ : ℝ → M}

/-! ### Curves given by `C¹` pieces -/

section Pieces

variable {f : ℕ → ℝ → M} {t : ℕ → ℝ} {n : ℕ}

private theorem apply_curveVelocity_eq_of_eventuallyEq {γ' : ℝ → M} {s : ℝ}
    (h : γ =ᶠ[𝓝 s] γ') :
    (φ (γ s) fun _ ↦ Manifold.curveVelocity I γ s) =
      φ (γ' s) fun _ ↦ Manifold.curveVelocity I γ' s := by
  rw [h.curveVelocity_eq]
  exact congrArg (fun x : M ↦ φ x fun _ ↦ (Manifold.curveVelocity I γ' s : E)) h.eq_of_nhds

variable [IsManifold I 1 M]

private theorem intervalIntegrable_apply_curveVelocity_of_eqOn_uIoo (hφ : IsSmoothForm I 0 φ)
    {γ' : ℝ → M} (hγ' : ContMDiff 𝓘(ℝ, ℝ) I 1 γ') {a b : ℝ} (h : EqOn γ γ' (uIoo a b)) :
    IntervalIntegrable (fun s ↦ φ (γ s) fun _ ↦ Manifold.curveVelocity I γ s) volume a b :=
  (hφ.intervalIntegrable_apply_curveVelocity hγ' a b).congr_uIoo fun _ hs ↦
    (apply_curveVelocity_eq_of_eventuallyEq (h.eventuallyEq_of_mem
      (isOpen_Ioo.mem_nhds hs))).symm

/-- A continuous `1`-form evaluated on the velocity of a curve which agrees with `C¹` curves
`f i` between consecutive parameters `t i` and `t (i + 1)` is integrable from `t 0` to `t n`. -/
theorem IsSmoothForm.intervalIntegrable_apply_curveVelocity_of_eqOn (hφ : IsSmoothForm I 0 φ)
    (hf : ∀ i < n, ContMDiff 𝓘(ℝ, ℝ) I 1 (f i))
    (hγ : ∀ i < n, EqOn γ (f i) (uIoo (t i) (t (i + 1)))) :
    IntervalIntegrable (fun s ↦ φ (γ s) fun _ ↦ Manifold.curveVelocity I γ s) volume
      (t 0) (t n) :=
  IntervalIntegrable.trans_iterate fun i hi ↦
    intervalIntegrable_apply_curveVelocity_of_eqOn_uIoo hφ (hf i hi) (hγ i hi)

/-- **Line integrals along piecewise `C¹` curves.** The line integral of a continuous `1`-form
along a curve which agrees with `C¹` curves `f i` between consecutive parameters `t i` and
`t (i + 1)` is the sum of the line integrals along the pieces. -/
theorem pathIntegral_eq_sum_of_eqOn (hφ : IsSmoothForm I 0 φ)
    (hf : ∀ i < n, ContMDiff 𝓘(ℝ, ℝ) I 1 (f i))
    (hγ : ∀ i < n, EqOn γ (f i) (uIoo (t i) (t (i + 1)))) :
    pathIntegral φ γ (t 0) (t n) =
      ∑ i ∈ Finset.range n, pathIntegral φ (f i) (t i) (t (i + 1)) := by
  rw [pathIntegral_def, ← intervalIntegral.sum_integral_adjacent_intervals fun i hi ↦
    intervalIntegrable_apply_curveVelocity_of_eqOn_uIoo hφ (hf i hi) (hγ i hi)]
  exact Finset.sum_congr rfl fun i hi ↦ by
    rw [← pathIntegral_def]
    exact pathIntegral_congr_of_eqOn_uIoo (hγ i (Finset.mem_range.mp hi))

end Pieces

/-! ### Periodic curves -/

section Periodic

variable {T : ℝ}

/-- A `1`-form evaluated on the velocity of a `T`-periodic curve is `T`-periodic. -/
theorem _root_.Function.Periodic.apply_curveVelocity (hγ : Periodic γ T)
    (φ : RoughForm I M F 1) :
    Periodic (fun s ↦ φ (γ s) fun _ ↦ Manifold.curveVelocity I γ s) T := fun s ↦ by
  dsimp only
  rw [hγ.curveVelocity_add]
  exact congrArg (fun x : M ↦ φ x fun _ ↦ (Manifold.curveVelocity I γ s : E)) (hγ s)

/-- The line integral of a `1`-form along a `T`-periodic curve over an interval of length `T`
does not depend on the interval. -/
theorem _root_.Function.Periodic.pathIntegral_add_eq (hγ : Periodic γ T)
    (φ : RoughForm I M F 1) (a b : ℝ) :
    pathIntegral φ γ a (a + T) = pathIntegral φ γ b (b + T) := by
  simpa only [pathIntegral_def] using (hγ.apply_curveVelocity φ).intervalIntegral_add_eq a b

/-- A `1`-form evaluated on the velocity of a `T`-periodic curve, integrable over one period, is
integrable over every interval. -/
theorem _root_.Function.Periodic.intervalIntegrable_apply_curveVelocity (hγ : Periodic γ T)
    (hT : T ≠ 0) {a : ℝ}
    (h : IntervalIntegrable (fun s ↦ φ (γ s) fun _ ↦ Manifold.curveVelocity I γ s) volume a
      (a + T)) (b c : ℝ) :
    IntervalIntegrable (fun s ↦ φ (γ s) fun _ ↦ Manifold.curveVelocity I γ s) volume b c :=
  (hγ.apply_curveVelocity φ).intervalIntegrable hT h b c

end Periodic

end TauCeti
