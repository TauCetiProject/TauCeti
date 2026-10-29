/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.DegreeOne
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path

/-!
# The time form of the circle `AddCircle p`

For a positive real `p`, the circle `AddCircle p = ℝ ⧸ pℤ` carries a canonical one-form `dt_p`,
the time form `AddCircle.timeForm p`. It is the unique one-form whose pullback along the quotient
map `q_p : ℝ → AddCircle p` is the differential `dt` of the coordinate of `ℝ`. It descends from
`dt` because `dt` is invariant under the translations `t ↦ t + k p` by which `ℝ` covers the circle.

The charts of `AddCircle p` are local real lifts (`AddCircle.coe_apply_of_mem_atlas`), so its
tangent spaces are read as `ℝ` through lifts, and `dt_p` sends each tangent vector to itself.
In every chart its coordinate expression is constant, so it is a smooth one-form. As a section of
the cotangent bundle it is the constant section `id : ℝ →L[ℝ] ℝ`. On the source of any local real
lift `c`, `dt_p` is the differential of `c`. It is closed, since the circle is one-dimensional,
and it vanishes nowhere.

The time form is invariant under the translations of the circle. Multiplication by an integer
`k` pulls it back to `k • dt_p`, and the rescaling `AddCircle p ≃ AddCircle q` pulls `dt_q` back to
`(p⁻¹ * q) • dt_p`. Its integral along the curve `t ↦ q_p t` from `a` to `b` is `b - a`; one
circuit `0 ≤ t ≤ p` of the circle has integral `p`.

## Main definitions

* `AddCircle.timeForm p`: the time form `dt_p` of `AddCircle p`, a smooth real one-form.

## Main results

* `AddCircle.mpullback_coe_timeForm`: the pullback of `dt_p` along `q_p` is `dt`.
* `AddCircle.mpullback_coe_injective`, `AddCircle.eq_timeForm_iff`: a form on `AddCircle p` is
  determined by its pullback along `q_p`, so `dt_p` is the only form pulling back to `dt`.
* `AddCircle.timeForm_apply_eq_mextDeriv_of_coe_apply`: on the source of a local real lift `c`,
  `dt_p` is the differential of `c`.
* `AddCircle.isClosed_timeForm`, `AddCircle.timeForm_apply_ne_zero`: `dt_p` is closed and
  nowhere vanishing.
* `AddCircle.mpullback_add_right_timeForm`, `AddCircle.mpullback_zsmul_timeForm`,
  `AddCircle.mpullback_diffeomorphAddCircle_timeForm`: the pullbacks of the time form along
  translations, integer multiplications and rescalings.
* `AddCircle.pathIntegral_timeForm_coe`: the integral of `dt_p` along `q_p` from `a` to `b` is
  `b - a`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 11 (covectors on the circle and line integrals).
-/

public section

noncomputable section

open Set Filter TauCeti
open scoped Manifold Topology ContDiff

namespace AddCircle

variable (p : ℝ) [Fact (0 < p)]

/-- The constant family of identity covectors on `AddCircle p` is a smooth one-form: in every chart
its coordinate expression is constant. -/
private theorem isSmoothForm_timeForm :
    IsSmoothForm 𝓘(ℝ) ∞ (fun x : AddCircle p ↦ ContinuousAlternatingMap.ofSubsingleton ℝ
      (TangentSpace 𝓘(ℝ) x) ℝ (0 : Fin 1) (ContinuousLinearMap.id ℝ ℝ)) := by
  refine IsSmoothForm.of_contDiffWithinAt_inChartAt_self fun x ↦ ?_
  have hx := mem_extChartAt_target (I := 𝓘(ℝ)) x
  refine (contDiffWithinAt_const (c := ContinuousAlternatingMap.ofSubsingleton ℝ ℝ ℝ (0 : Fin 1)
    (ContinuousLinearMap.id ℝ ℝ))).congr_of_eventuallyEq_of_mem ?_ (by simp)
  filter_upwards [nhdsWithin_le_nhds
    ((isOpen_extChartAt_target (I := 𝓘(ℝ)) x).mem_nhds hx)] with z hz
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp only [RoughForm.inChartAt_apply, modelWithCornersSelf_coe, range_id, mfderivWithin_univ,
    mfderiv_extChartAt_symm x hz]
  -- Tangent vectors of `AddCircle p` are real numbers, on which the identity of `ℝ` acts.
  rfl

/-- The time form `dt_p` of the circle `AddCircle p`: the smooth one-form sending each tangent
vector, read in `ℝ` through the local real lifts that are the charts of `AddCircle p`, to itself.
It is the unique form pulling back to `dt` along the quotient map `ℝ → AddCircle p`
(`AddCircle.eq_timeForm_iff`). -/
def timeForm : SmoothForm 𝓘(ℝ) (AddCircle p) ℝ 1 :=
  ⟨fun x ↦ ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace 𝓘(ℝ) x) ℝ 0
    (ContinuousLinearMap.id ℝ ℝ), (isSmoothForm_timeForm p).mem_smoothForms⟩

/-- The time form sends a tangent vector of `AddCircle p` to itself. -/
@[simp]
theorem timeForm_apply (x : AddCircle p) (v : Fin 1 → TangentSpace 𝓘(ℝ) x) :
    (timeForm p).1 x v = v 0 :=
  (rfl)

/-- As a section of the cotangent bundle, the time form is the constant section `id`. -/
@[simp]
theorem degreeOneEquiv_timeForm (x : AddCircle p) :
    SmoothForm.degreeOneEquiv (timeForm p) x = ContinuousLinearMap.id ℝ ℝ := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  rw [SmoothForm.degreeOneEquiv_apply_apply, timeForm_apply]
  -- Tangent vectors of `AddCircle p` are real numbers, on which the identity of `ℝ` acts.
  rfl

/-- The time form vanishes nowhere. -/
theorem timeForm_apply_ne_zero (x : AddCircle p) : (timeForm p).1 x ≠ 0 := fun h ↦ by
  -- The time form sends the tangent vector `1` to `1` (`AddCircle.timeForm_apply`).
  have h₁ : (1 : ℝ) = 0 := DFunLike.congr_fun h fun _ ↦ (1 : ℝ)
  exact one_ne_zero h₁

/-- The time form is closed: on the one-dimensional circle every two-form vanishes. -/
theorem isClosed_timeForm : (timeForm p).IsClosed :=
  (SmoothForm.isClosed_def _).mpr (mextDeriv_eq_zero_of_finrank_le (by simp) _)

/-! ### Pullback to the real line -/

/-- The time form pulls back along the quotient map `ℝ → AddCircle p` to the differential `dt` of
the coordinate of `ℝ`. -/
theorem mpullback_coe_timeForm :
    mpullback 𝓘(ℝ) 𝓘(ℝ) ((↑) : ℝ → AddCircle p) (timeForm p).1 =
      mextDeriv (RoughForm.ofFunction 𝓘(ℝ) id) := by
  funext t
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp only [mpullback_apply, mfderiv_coe, timeForm_apply, mextDeriv_ofFunction, mvfderiv_eq_fderiv,
    fderiv_id, ContinuousLinearMap.id_comp, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    ContinuousLinearEquiv.coe_coe]
  -- Tangent vectors of `AddCircle p` are real numbers, on which the identity of `ℝ` acts.
  rfl

/-- A form on `AddCircle p` is determined by its pullback along the quotient map
`ℝ → AddCircle p`: the quotient map is surjective with derivative the identity. -/
theorem mpullback_coe_injective {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} :
    Function.Injective (mpullback 𝓘(ℝ) 𝓘(ℝ) ((↑) : ℝ → AddCircle p) :
      RoughForm 𝓘(ℝ) (AddCircle p) F k → RoughForm 𝓘(ℝ) ℝ F k) := by
  intro α β h
  funext x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  have h₁ (w : Fin k → TangentSpace 𝓘(ℝ) t) :
      mpullback 𝓘(ℝ) 𝓘(ℝ) ((↑) : ℝ → AddCircle p) α t w =
        mpullback 𝓘(ℝ) 𝓘(ℝ) ((↑) : ℝ → AddCircle p) β t w :=
    DFunLike.congr_fun (congrFun h t) w
  simp only [mpullback_apply, mfderiv_coe] at h₁
  -- The identity of `ℝ` fixes the tangent vectors of `AddCircle p`, which are real numbers.
  exact h₁ v

variable {p} in
/-- The time form is the unique one-form on `AddCircle p` pulling back to `dt` along the quotient
map `ℝ → AddCircle p`. -/
theorem eq_timeForm_iff {α : RoughForm 𝓘(ℝ) (AddCircle p) ℝ 1} :
    α = (timeForm p).1 ↔
      mpullback 𝓘(ℝ) 𝓘(ℝ) ((↑) : ℝ → AddCircle p) α =
        mextDeriv (RoughForm.ofFunction 𝓘(ℝ) id) := by
  refine ⟨fun h ↦ h ▸ mpullback_coe_timeForm p, fun h ↦ mpullback_coe_injective p ?_⟩
  rw [h, mpullback_coe_timeForm]

variable {p} in
/-- On the source of a local real lift `c` of `AddCircle p`, the time form is the differential of
`c`. -/
theorem timeForm_apply_eq_mextDeriv_of_coe_apply {c : OpenPartialHomeomorph (AddCircle p) ℝ}
    (hc : ∀ x ∈ c.source, (c x : AddCircle p) = x) {x : AddCircle p} (hx : x ∈ c.source) :
    (timeForm p).1 x = mextDeriv (RoughForm.ofFunction 𝓘(ℝ) c) x := by
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp only [timeForm_apply, mextDeriv_ofFunction, mvfderiv, mfderiv_of_coe_apply hc hx,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply]
  -- Tangent vectors of `AddCircle p` are real numbers, on which the identity of `ℝ` acts.
  rfl

/-! ### Pullback along maps of circles -/

/-- The time form is invariant under the translations of `AddCircle p`. -/
@[simp]
theorem mpullback_add_right_timeForm (a : AddCircle p) :
    mpullback 𝓘(ℝ) 𝓘(ℝ) (· + a) (timeForm p).1 = (timeForm p).1 := by
  funext x
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp only [mpullback_apply, mfderiv_add_right, timeForm_apply]
  -- Tangent vectors of `AddCircle p` are real numbers, on which the identity of `ℝ` acts.
  rfl

/-- Multiplication by an integer `k` pulls the time form back to `k • dt_p`. -/
@[simp]
theorem mpullback_zsmul_timeForm (k : ℤ) :
    mpullback 𝓘(ℝ) 𝓘(ℝ) (fun y : AddCircle p ↦ k • y) (timeForm p).1 = k • (timeForm p).1 := by
  funext x
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp only [mpullback_apply, mfderiv_zsmul, timeForm_apply, Pi.smul_apply,
    ContinuousAlternatingMap.coe_smul]
  -- Tangent vectors of `AddCircle p` are real numbers, on which the identity of `ℝ` acts.
  rfl

/-- The rescaling `AddCircle p ≃ AddCircle q` pulls the time form of `AddCircle q` back to
`(p⁻¹ * q) • dt_p`. -/
@[simp]
theorem mpullback_diffeomorphAddCircle_timeForm (q : ℝ) [Fact (0 < q)] (n : ℕ∞ω) :
    mpullback 𝓘(ℝ) 𝓘(ℝ) (diffeomorphAddCircle p q n) (timeForm q).1 =
      (p⁻¹ * q) • (timeForm p).1 := by
  funext x
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  simp only [mpullback_apply, mfderiv_diffeomorphAddCircle, timeForm_apply, Pi.smul_apply,
    ContinuousAlternatingMap.coe_smul]
  -- Tangent vectors of `AddCircle p` are real numbers, on which the identity of `ℝ` acts.
  rfl

/-! ### Integration along the circle -/

/-- The integral of the time form along the curve `t ↦ (t : AddCircle p)` from `a` to `b` is
`b - a`. In particular one circuit `0 ≤ t ≤ p` of the circle has integral `p`. -/
@[simp]
theorem pathIntegral_timeForm_coe (a b : ℝ) :
    pathIntegral (timeForm p).1 ((↑) : ℝ → AddCircle p) a b = b - a := by
  simp only [pathIntegral_def, Manifold.curveVelocity_apply, mfderiv_coe]
  -- The velocity `1` of the curve is a real number, sent to itself by the identity of `ℝ`.
  exact (intervalIntegral.integral_const (1 : ℝ)).trans (by simp)

end AddCircle
