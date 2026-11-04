/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.CircleFamily
public import TauCeti.Geometry.Manifold.Instances.CircleFamily.Pullback

/-!
# The angle form and the time form of a smooth family of circles

For a positive period function `p : B → ℝ_{>0}` on a smooth manifold `B`, the family
`TauCeti.CircleFamily.Pullback p` has the circle `AddCircle (p b)` as its fiber over `b`, and is
normalized to `B × AddCircle 1` by `N_p (b, x) = (b, D_(p b, 1) x)`. This file puts on it the two
one-forms that extend the time forms `dt_(p b)` of the individual circles across the family, as
the total family `TauCeti.CircleFamily` of positive-period circles does for `p = id`.

* The **angle form** `β = (pr₂ ∘ N_p)^* dt_1` (`TauCeti.CircleFamily.Pullback.angleForm`) is the
  pullback of the time form of the unit-period circle along the normalized angle. It is defined
  and closed for every period function `p`, smooth or not, and restricts on the circle over `b`
  to `(p b)⁻¹ • dt_(p b)`.
* The **time form** `η = p • β` (`TauCeti.CircleFamily.Pullback.timeForm`), for a smooth period
  function `p`, is the pullback of the time form of the total family along `(b, x) ↦ (p b, x)`.
  It restricts on the circle over `b` to its time form `dt_(p b)`, and its exterior derivative is
  `d(p ∘ base) ∧ β`. For the identity period function on `ℝ_{>0}` this is the time form of the
  total family, which is not closed (`TauCeti.CircleFamily.not_isClosed_timeForm`).

Both forms are natural. The map `(b, x) ↦ (p b, x)` to the total family pulls back its angle and
time forms to `β` and `η`, and base change along a smooth map `f : B' → B` pulls back the forms
of `p` to those of `p ∘ f`. In particular, along the inclusion of an open subset `U ⊆ B`, the
forms of `p` restrict to those of the family over `U`.
The fiberwise rescaling from the periods `p` to the periods `q` keeps the normalized angle, so it
pulls the angle form of `q` back to that of `p`, and the time form `η_q` back to `(q / p) • η_p`.

## Main definitions

* `TauCeti.CircleFamily.Pullback.angleForm p IB`: the angle form `β = (pr₂ ∘ N_p)^* dt_1`.
* `TauCeti.CircleFamily.Pullback.timeForm p IB hp`: the time form `η = p • β`.

## Main results

* `TauCeti.CircleFamily.Pullback.isClosed_angleForm`,
  `TauCeti.CircleFamily.Pullback.mpullback_mk_angleForm`: the angle form is closed and restricts
  to `(p b)⁻¹ • dt_(p b)` on the circle over `b`.
* `TauCeti.CircleFamily.Pullback.timeForm_apply`,
  `TauCeti.CircleFamily.Pullback.mpullback_mk_timeForm`: the time form is the angle form rescaled
  by the period, and restricts to `dt_(p b)` on the circle over `b`.
* `TauCeti.CircleFamily.Pullback.mextDeriv_timeForm`: `dη = d(p ∘ base) ∧ β`.
* `TauCeti.CircleFamily.Pullback.mpullback_toCircleFamily_angleForm`,
  `TauCeti.CircleFamily.Pullback.mpullback_toCircleFamily_timeForm`: compatibility with the total
  family.
* `TauCeti.CircleFamily.Pullback.mpullback_comap_angleForm`,
  `TauCeti.CircleFamily.Pullback.mpullback_comap_timeForm`: compatibility with base change.
* `TauCeti.CircleFamily.Pullback.mpullback_rescale_angleForm`,
  `TauCeti.CircleFamily.Pullback.mpullback_rescale_timeForm`: the fiberwise rescaling preserves the
  angle form and pulls `η_q` back to `(q / p) • η_p`.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

namespace CircleFamily.Pullback

variable {B : Type*} (p : B → PositivePeriod) {EB HB : Type*} [NormedAddCommGroup EB]
  [NormedSpace ℝ EB] [TopologicalSpace HB] (IB : ModelWithCorners ℝ EB HB) [TopologicalSpace B]
  [ChartedSpace HB B] [IsManifold IB ∞ B]

omit [IsManifold IB ∞ B] in
/-- The normalized angle `pr₂ ∘ N_p` of the family is smooth. -/
private theorem contMDiff_angle :
    ContMDiff (IB.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ fun z : Pullback p ↦ (normalization p IB ∞ z).2 :=
  contMDiff_snd.comp (normalization p IB ∞).contMDiff

/-! ### The angle form -/

/-- The angle form `β = (pr₂ ∘ N_p)^* dt_1` of the family of the circles `AddCircle (p b)`: the
pullback of the time form of the unit-period circle along the normalized angle. -/
def angleForm : SmoothForm (IB.prod 𝓘(ℝ)) (Pullback p) ℝ 1 :=
  SmoothForm.mpullback _ (contMDiff_angle p IB) (AddCircle.timeForm 1)

/-- The angle form is the differential of the normalized angle `pr₂ ∘ N_p`, read in the real
tangent lines of the unit-period circle. -/
@[simp]
theorem angleForm_apply (z : Pullback p) (v : Fin 1 → TangentSpace (IB.prod 𝓘(ℝ)) z) :
    (angleForm p IB).1 z v =
      mfderiv (IB.prod 𝓘(ℝ)) 𝓘(ℝ) (fun z ↦ (normalization p IB ∞ z).2) z (v 0) := by
  rw [angleForm, SmoothForm.mpullback_apply, AddCircle.timeForm_apply]

/-- The angle form is closed. -/
theorem isClosed_angleForm : (angleForm p IB).IsClosed :=
  (AddCircle.isClosed_timeForm 1).mpullback _ _

/-- On the circle over `b`, the angle form restricts to `(p b)⁻¹ • dt_(p b)`. -/
@[simp]
theorem mpullback_mk_angleForm (b : B) :
    SmoothForm.mpullback (mk b) (contMDiff_mk p IB ∞ b) (angleForm p IB) =
      (p b : ℝ)⁻¹ • AddCircle.timeForm (p b : ℝ) := by
  have hcomp : (fun z ↦ (normalization p IB ∞ z).2) ∘ mk (p := p) b =
      AddCircle.diffeomorphAddCircle (p b : ℝ) 1 ⊤ := by
    funext x
    simp
  apply Subtype.ext
  rw [angleForm, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback,
    ← mpullback_comp ((contMDiff_mk p IB ∞ b).mdifferentiable (by simp))
      ((contMDiff_angle p IB).mdifferentiable (by simp)), hcomp,
    AddCircle.mpullback_diffeomorphAddCircle_timeForm, mul_one, SetLike.val_smul]

/-- The map `(b, x) ↦ (p b, x)` to the total family pulls its angle form back to the angle form of
the family of `p`. -/
@[simp]
theorem mpullback_toCircleFamily_angleForm (hp : ContMDiff IB 𝓘(ℝ) ∞ p) :
    SmoothForm.mpullback (toCircleFamily p) (contMDiff_toCircleFamily p IB hp)
      CircleFamily.angleForm = angleForm p IB := by
  have hcomp : (Prod.snd ∘ CircleFamily.normalization ∞) ∘ toCircleFamily p =
      Prod.snd ∘ normalization p IB ∞ := by
    funext z
    simp only [Function.comp_apply, normalization_toCircleFamily, normalization_snd]
  refine Subtype.ext <| funext fun z ↦ ContinuousAlternatingMap.ext fun v ↦ ?_
  have h := mfderiv_comp_apply z
    ((contMDiff_snd.comp (CircleFamily.normalization ∞).contMDiff).mdifferentiableAt (by simp))
    ((contMDiff_toCircleFamily p IB hp).mdifferentiableAt (by simp)) (v 0)
  rw [hcomp] at h
  rw [SmoothForm.mpullback_apply, CircleFamily.angleForm_apply, angleForm_apply]
  -- `h` is the goal up to the eta-expansion `Prod.snd ∘ N = fun z ↦ (N z).2` and the reading of
  -- the tangent lines of the unit-period circle as `ℝ`.
  exact h.symm

/-! ### The time form -/

/-- The time form `η = p • β` of the family of the circles `AddCircle (p b)`, for a smooth period
function `p`: the pullback of the time form of the total family along `(b, x) ↦ (p b, x)`. It
restricts to the time form `dt_(p b)` on the circle over each `b`. -/
def timeForm (hp : ContMDiff IB 𝓘(ℝ) ∞ p) : SmoothForm (IB.prod 𝓘(ℝ)) (Pullback p) ℝ 1 :=
  SmoothForm.mpullback (toCircleFamily p) (contMDiff_toCircleFamily p IB hp)
    CircleFamily.timeForm

/-- The time form of the family is the pullback of the time form of the total family. -/
@[simp]
theorem mpullback_toCircleFamily_timeForm (hp : ContMDiff IB 𝓘(ℝ) ∞ p) :
    SmoothForm.mpullback (toCircleFamily p) (contMDiff_toCircleFamily p IB hp)
      CircleFamily.timeForm = timeForm p IB hp :=
  (rfl)

/-- The time form is the angle form rescaled by the period at the base point. -/
@[simp]
theorem timeForm_apply (hp : ContMDiff IB 𝓘(ℝ) ∞ p) (z : Pullback p)
    (v : Fin 1 → TangentSpace (IB.prod 𝓘(ℝ)) z) :
    (timeForm p IB hp).1 z v = p z.base * (angleForm p IB).1 z v := by
  have h := DFunLike.congr_fun
    (congrFun (congrArg Subtype.val (mpullback_toCircleFamily_angleForm p IB hp)) z) v
  rw [SmoothForm.mpullback_apply] at h
  rw [← mpullback_toCircleFamily_timeForm, SmoothForm.mpullback_apply, CircleFamily.timeForm_apply,
    period_toCircleFamily, h]

/-- On the circle over `b`, the time form restricts to its time form `dt_(p b)`. -/
@[simp]
theorem mpullback_mk_timeForm (hp : ContMDiff IB 𝓘(ℝ) ∞ p) (b : B) :
    SmoothForm.mpullback (mk b) (contMDiff_mk p IB ∞ b) (timeForm p IB hp) =
      AddCircle.timeForm (p b : ℝ) := by
  have hcomp : toCircleFamily p ∘ mk (p := p) b = CircleFamily.mk (p b) :=
    funext (toCircleFamily_mk p b)
  apply Subtype.ext
  rw [← mpullback_toCircleFamily_timeForm, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback,
    ← mpullback_comp ((contMDiff_mk p IB ∞ b).mdifferentiable (by simp))
      ((contMDiff_toCircleFamily p IB hp).mdifferentiable (by simp)), hcomp,
    ← SmoothForm.coe_mpullback _ (CircleFamily.contMDiff_mk (p b) ∞),
    CircleFamily.mpullback_mk_timeForm]

/-- The exterior derivative of the time form is `d(p ∘ base) ∧ β`. -/
theorem mextDeriv_timeForm (hp : ContMDiff IB 𝓘(ℝ) ∞ p) :
    mextDeriv (timeForm p IB hp).1 =
      RoughForm.wedge
        (mextDeriv (RoughForm.ofFunction (IB.prod 𝓘(ℝ))
          fun z : Pullback p ↦ (p z.base : ℝ)))
        (angleForm p IB).1 := by
  have hf := contMDiff_toCircleFamily p IB hp
  have hcomp : (fun w : CircleFamily ↦ (w.period : ℝ)) ∘ toCircleFamily p =
      fun z ↦ (p z.base : ℝ) :=
    funext fun z ↦ by simp
  rw [← mpullback_toCircleFamily_timeForm, ← mextDerivₗ_apply, SmoothForm.mextDerivₗ_mpullback,
    SmoothForm.coe_mpullback, mextDerivₗ_apply, CircleFamily.mextDeriv_timeForm, mpullback_wedge,
    mpullback_mextDeriv_ofFunction (hf.mdifferentiable (by simp))
      (CircleFamily.contMDiff_periodReal (n := 1).mdifferentiable one_ne_zero), hcomp,
    ← SmoothForm.coe_mpullback _ hf, mpullback_toCircleFamily_angleForm p IB hp]

/-! ### Base change -/

section BaseChange

variable {B' : Type*} (f : B' → B) {EB' HB' : Type*} [NormedAddCommGroup EB']
  [NormedSpace ℝ EB'] [TopologicalSpace HB'] {IB' : ModelWithCorners ℝ EB' HB'}
  [TopologicalSpace B'] [ChartedSpace HB' B'] [IsManifold IB' ∞ B']

/-- Base change along a smooth map `f` pulls the angle form of the family of `p` back to the angle
form of the family of `p ∘ f`. -/
@[simp]
theorem mpullback_comap_angleForm (hf : ContMDiff IB' IB ∞ f) :
    SmoothForm.mpullback (comap p f) (contMDiff_comap p f IB hf) (angleForm p IB) =
      angleForm (p ∘ f) IB' := by
  have hcomp : (fun z ↦ (normalization p IB ∞ z).2) ∘ comap p f =
      fun z ↦ (normalization (p ∘ f) IB' ∞ z).2 := by
    funext z
    rcases z with ⟨b', x⟩
    rw [Function.comp_apply, comap_mk, normalization_mk, normalization_mk]
    -- The period `(p ∘ f) b'` is `p (f b')` by definition of composition.
    rfl
  apply Subtype.ext
  rw [angleForm, angleForm, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback,
    SmoothForm.coe_mpullback, ← mpullback_comp ((contMDiff_comap p f IB hf).mdifferentiable
      (by simp)) ((contMDiff_angle p IB).mdifferentiable (by simp)), hcomp]

/-- Base change along a smooth map `f` pulls the time form of the family of `p` back to the time
form of the family of `p ∘ f`. -/
@[simp]
theorem mpullback_comap_timeForm (hp : ContMDiff IB 𝓘(ℝ) ∞ p) (hf : ContMDiff IB' IB ∞ f) :
    SmoothForm.mpullback (comap p f) (contMDiff_comap p f IB hf) (timeForm p IB hp) =
      timeForm (p ∘ f) IB' (hp.comp hf) := by
  have hcomp : toCircleFamily p ∘ comap p f = toCircleFamily (p ∘ f) := by
    funext z
    rcases z with ⟨b', x⟩
    rw [Function.comp_apply, comap_mk, toCircleFamily_mk, toCircleFamily_mk]
    -- The period `(p ∘ f) b'` is `p (f b')` by definition of composition.
    rfl
  apply Subtype.ext
  rw [← mpullback_toCircleFamily_timeForm, ← mpullback_toCircleFamily_timeForm,
    SmoothForm.coe_mpullback, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback,
    ← mpullback_comp ((contMDiff_comap p f IB hf).mdifferentiable (by simp))
      ((contMDiff_toCircleFamily p IB hp).mdifferentiable (by simp)), hcomp]

end BaseChange

/-! ### Fiberwise rescaling -/

variable (q : B → PositivePeriod)

/-- The fiberwise rescaling from the periods `p` to the periods `q` keeps the normalized angle, so
it pulls the angle form of `q` back to the angle form of `p`. -/
@[simp]
theorem mpullback_rescale_angleForm :
    SmoothForm.mpullback (rescale p IB q ∞) (rescale p IB q ∞).contMDiff (angleForm q IB) =
      angleForm p IB := by
  have hcomp : (fun z ↦ (normalization q IB ∞ z).2) ∘ rescale p IB q ∞ =
      fun z ↦ (normalization p IB ∞ z).2 :=
    funext fun z ↦ by rw [Function.comp_apply, normalization_rescale]
  apply Subtype.ext
  rw [angleForm, angleForm, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback,
    SmoothForm.coe_mpullback, ← mpullback_comp ((rescale p IB q ∞).contMDiff.mdifferentiable
      (by simp)) ((contMDiff_angle q IB).mdifferentiable (by simp)), hcomp]

/-- The fiberwise rescaling from the periods `p` to the periods `q` pulls the time form `η_q` back
to `(q / p) • η_p`. -/
theorem mpullback_rescale_timeForm (hp : ContMDiff IB 𝓘(ℝ) ∞ p) (hq : ContMDiff IB 𝓘(ℝ) ∞ q) :
    (SmoothForm.mpullback (rescale p IB q ∞) (rescale p IB q ∞).contMDiff
        (timeForm q IB hq)).1 =
      fun z ↦ ((q z.base : ℝ) / p z.base) • (timeForm p IB hp).1 z := by
  refine funext fun z ↦ ContinuousAlternatingMap.ext fun v ↦ ?_
  have h := DFunLike.congr_fun
    (congrFun (congrArg Subtype.val (mpullback_rescale_angleForm p IB q)) z) v
  rw [SmoothForm.mpullback_apply] at h
  rw [SmoothForm.mpullback_apply, timeForm_apply, base_rescale, h,
    ContinuousAlternatingMap.smul_apply, timeForm_apply, smul_eq_mul]
  field_simp [(p z.base).property.ne']

end CircleFamily.Pullback

end TauCeti
