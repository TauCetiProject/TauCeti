/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.AddCircle
public import TauCeti.Geometry.Manifold.DifferentialForm.Leibniz
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
public import TauCeti.Geometry.Manifold.Instances.CircleFamily

/-!
# The angle, time and total forms of the family of positive-period circles

The total family `C = {(p, x) : p > 0, x ∈ AddCircle p}` (`TauCeti.CircleFamily`) is normalized
to `ℝ_{>0} × AddCircle 1` by `N(p, x) = (p, D_(p,1) x)`. This file puts on `C` the two one-forms
that extend the time forms `dt_p` of the individual circles across the family, and the two-form
that orients it.

* The **angle form** `β = (pr₂ ∘ N)^* dt_1` (`TauCeti.CircleFamily.angleForm`) is the pullback of
  the time form of the unit-period circle along the normalized angle. It is closed, and it
  restricts on the circle of period `p` to `p⁻¹ • dt_p`.
* The **time form** `η = p • β` (`TauCeti.CircleFamily.timeForm`) restricts on the circle of
  period `p` to its time form `dt_p`. It is not closed: its exterior derivative is `dp ∧ β`.
* The **total form** `dp ∧ η` (`TauCeti.CircleFamily.totalForm`) vanishes nowhere. On the circle
  of period `p` it pairs a tangent vector `u` of the family with a tangent vector `w` of the circle
  to `dp(u) * dt_p(w)`, so it orients the family by the base direction followed by the fiber
  direction (`TauCeti.CircleFamily.orientation`).

On the real cover `Q(p, t) = (p, [t]_p)` (`TauCeti.CircleFamily.representative`) the angle form is
the differential of the normalized time `t / p`, and the time form is `dt - (t / p) • dp`. This
pullback is invariant under the deck translations `(p, t) ↦ (p, t + k p)`: the derivative `k dp` of
the translated time coordinate is cancelled by the change `k dp` of `(t / p) • dp`. Moreover
`Q^*(dη) = p⁻¹ • (dp ∧ dt)` and `Q^*(dp ∧ η) = dp ∧ dt`.

The fiber restrictions alone do not determine `η`: adding the pullback of a one-form on the
positive base does not change them. The normalization by `N`, under which `β` annihilates the
direction in which the normalized angle is constant, fixes the extension.

## Main definitions

* `TauCeti.CircleFamily.angleForm`: the angle form `β = (pr₂ ∘ N)^* dt_1`.
* `TauCeti.CircleFamily.timeForm`: the time form `η = p • β`.
* `TauCeti.CircleFamily.totalForm`: the total form `dp ∧ η`.

## Main results

* `TauCeti.CircleFamily.isClosed_angleForm`, `TauCeti.CircleFamily.mpullback_mk_angleForm`: the
  angle form is closed and restricts to `p⁻¹ • dt_p` on the circle of period `p`.
* `TauCeti.CircleFamily.mpullback_mk_timeForm`: the time form restricts to `dt_p` on the circle of
  period `p`.
* `TauCeti.CircleFamily.mextDeriv_timeForm`: `dη = dp ∧ β`.
* `TauCeti.CircleFamily.not_isClosed_timeForm`: the time form is not closed.
* `TauCeti.CircleFamily.mpullback_representative_angleForm`,
  `TauCeti.CircleFamily.mpullback_representative_timeForm`: on the real cover,
  `Q^* β = d(t / p)` and `Q^* η = dt - (t / p) • dp`.
* `TauCeti.CircleFamily.mpullback_deck_mpullback_representative`: forms pulled back to the real
  cover, such as `Q^* η`, are invariant under the deck translations.
* `TauCeti.CircleFamily.mpullback_representative_mextDeriv_timeForm`: `Q^*(dη) = p⁻¹ • (dp ∧ dt)`.
* `TauCeti.CircleFamily.mpullback_representative_totalForm`,
  `TauCeti.CircleFamily.eval₂_totalForm_mfderiv_representative`: `Q^*(dp ∧ η) = dp ∧ dt`.
* `TauCeti.CircleFamily.totalForm_apply_ne_zero`: the total form vanishes nowhere.
* `TauCeti.CircleFamily.eval₂_totalForm_mfderiv_mk`: on a fiber, the total form is
  `dp(u) * dt_p(w)`.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

namespace CircleFamily

/-- The normalized angle `pr₂ ∘ N` of the family, in the unit-period circle. -/
private def angle (z : CircleFamily) : AddCircle (1 : ℝ) := (normalization ∞ z).2

private theorem contMDiff_angle : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ angle :=
  contMDiff_snd.comp (normalization ∞).contMDiff

/-! ### The angle form -/

/-- The angle form `β = (pr₂ ∘ N)^* dt_1` of the family of positive-period circles: the pullback
of the time form of the unit-period circle along the normalized angle. -/
def angleForm : SmoothForm (𝓘(ℝ).prod 𝓘(ℝ)) CircleFamily ℝ 1 :=
  SmoothForm.mpullback angle contMDiff_angle (AddCircle.timeForm 1)

/-- The angle form is the differential of the normalized angle `pr₂ ∘ N`, read in the real
tangent lines of the unit-period circle. -/
@[simp]
theorem angleForm_apply (z : CircleFamily) (v : Fin 1 → TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) z) :
    angleForm.1 z v =
      mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) (fun z ↦ (normalization ∞ z).2) z (v 0) := by
  rw [angleForm, SmoothForm.coe_mpullback, mpullback_apply, AddCircle.timeForm_apply]
  -- The private `angle` is `fun z ↦ (normalization ∞ z).2` by definition.
  rfl

/-- The angle form is closed. -/
theorem isClosed_angleForm : angleForm.IsClosed :=
  (AddCircle.isClosed_timeForm 1).mpullback _ _

/-- On the circle of period `p`, the angle form restricts to `p⁻¹ • dt_p`. -/
@[simp]
theorem mpullback_mk_angleForm (p : PositivePeriod) :
    SmoothForm.mpullback (mk p) (contMDiff_mk p ∞) angleForm =
      (p : ℝ)⁻¹ • AddCircle.timeForm (p : ℝ) := by
  have hcomp : angle ∘ mk p = AddCircle.diffeomorphAddCircle (p : ℝ) 1 ⊤ := by
    funext x
    simp [angle]
  apply Subtype.ext
  rw [angleForm, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback,
    ← mpullback_comp ((contMDiff_mk p ∞).mdifferentiable (by simp))
      (contMDiff_angle.mdifferentiable (by simp)), hcomp,
    AddCircle.mpullback_diffeomorphAddCircle_timeForm, mul_one, SetLike.val_smul]

/-! ### The time form -/

/-- The time form `η = p • β` of the family of positive-period circles: the angle form rescaled
by the period. It restricts to the time form `dt_p` on each circle of period `p`. -/
def timeForm : SmoothForm (𝓘(ℝ).prod 𝓘(ℝ)) CircleFamily ℝ 1 :=
  ⟨fun z ↦ (z.period : ℝ) • angleForm.1 z,
    (angleForm.isSmoothForm.fun_smul contMDiff_periodReal).mem_smoothBundleForms⟩

/-- The time form is the angle form rescaled by the period. -/
@[simp]
theorem timeForm_apply (z : CircleFamily) (v : Fin 1 → TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) z) :
    timeForm.1 z v = z.period * angleForm.1 z v :=
  (rfl)

/-- On the circle of period `p`, the time form restricts to its time form `dt_p`. -/
@[simp]
theorem mpullback_mk_timeForm (p : PositivePeriod) :
    SmoothForm.mpullback (mk p) (contMDiff_mk p ∞) timeForm = AddCircle.timeForm (p : ℝ) := by
  have h := mpullback_mk_angleForm p
  refine Subtype.ext <| funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ ?_
  have hx := DFunLike.congr_fun (congrFun (congrArg Subtype.val h) x) v
  simp only [SmoothForm.coe_mpullback, mpullback_apply] at hx ⊢
  rw [timeForm_apply, hx]
  simp only [SetLike.val_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  field_simp [(p.property.ne' : (p : ℝ) ≠ 0)]

/-- The exterior derivative of the time form is `dp ∧ β`. -/
theorem mextDeriv_timeForm :
    mextDeriv timeForm.1 =
      RoughForm.wedge
        (mextDeriv (RoughForm.ofFunction (𝓘(ℝ).prod 𝓘(ℝ))
          fun z : CircleFamily ↦ (z.period : ℝ)))
        angleForm.1 := by
  funext z
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  have h := mextDeriv_fun_smul
    (contMDiff_periodReal (n := 1).mdifferentiableAt one_ne_zero (x := z))
    (angleForm.mdifferentiableAt z) v
  rw [(SmoothForm.isClosed_iff_forall_mextDeriv_apply_eq_zero angleForm).mp
    isClosed_angleForm z] at h
  simp only [Nat.reduceAdd, Fin.cast_refl, CompTriple.comp_eq, ContinuousAlternatingMap.coe_zero,
    Pi.zero_apply, mul_zero, add_zero] at h
  -- `timeForm.1` is `fun z ↦ z.period • angleForm.1 z` by definition.
  exact h

/-- The time form is not closed. -/
theorem not_isClosed_timeForm : ¬ timeForm.IsClosed := by
  intro h
  -- Pull `dp ∧ β = 0` back along the inverse normalization, where `p` and the angle are the two
  -- coordinates of `ℝ_{>0} × AddCircle 1`.
  let g := (normalization ∞).symm
  have hg : MDifferentiable (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) g :=
    g.contMDiff.mdifferentiable (by simp)
  have h0 := congrArg (mpullback (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) g)
    (((SmoothForm.isClosed_def _).mp h).symm.trans mextDeriv_timeForm)
  have hp : (fun z : CircleFamily ↦ (z.period : ℝ)) ∘ g = fun w ↦ (w.1 : ℝ) := by
    funext w
    simp [g]
  have hangle : angle ∘ g = Prod.snd :=
    funext fun w ↦ congrArg Prod.snd ((normalization ∞).apply_symm_apply w)
  rw [mpullback_zero, mpullback_wedge, mpullback_mextDeriv_ofFunction hg
      (contMDiff_periodReal (n := 1).mdifferentiable one_ne_zero), hp, angleForm,
    SmoothForm.coe_mpullback, ← mpullback_comp hg (contMDiff_angle.mdifferentiable (by simp)),
    hangle] at h0
  let w : PositivePeriod × AddCircle (1 : ℝ) := (⟨1, by norm_num⟩, 0)
  let e₁ : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) w := ((1 : ℝ), (0 : ℝ))
  let e₂ : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) w := ((0 : ℝ), (1 : ℝ))
  have h1 := DFunLike.congr_fun (congrFun h0 w) ![e₁, e₂]
  -- `erw`: the degree `0 + 1` of `dp` is `1` only up to reduction.
  erw [RoughForm.wedge_apply_one_one] at h1
  have hsnd (v : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) w) :
      mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) (Prod.snd : PositivePeriod × AddCircle (1 : ℝ) → _) w v =
        v.2 := by
    rw [mfderiv_snd]
    -- Tangent vectors of `ℝ_{>0} × AddCircle 1` are pairs of real numbers.
    rfl
  simp only [mpullback_apply, mextDeriv_ofFunction_coe_fst_apply, hsnd] at h1
  -- The time form of the circle sends each tangent vector to itself; `erw` because the
  -- tangent vectors here are read as real numbers.
  erw [AddCircle.timeForm_apply, AddCircle.timeForm_apply] at h1
  simp [e₁, e₂] at h1

/-! ### The real cover -/

private theorem contMDiff_normalizedTime {n : ℕ∞ω} :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ) n fun z : PositivePeriod × ℝ ↦ z.2 / (z.1 : ℝ) :=
  contMDiff_snd.div₀ (contMDiff_subtype_val.comp contMDiff_fst) fun z ↦ z.1.property.ne'

/-- On the real cover `Q(p, t) = (p, [t]_p)`, the angle form is the differential of the
normalized time `t / p`. -/
theorem mpullback_representative_angleForm :
    mpullback (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) representative angleForm.1 =
      mextDeriv (RoughForm.ofFunction (𝓘(ℝ).prod 𝓘(ℝ))
        fun z : PositivePeriod × ℝ ↦ z.2 / (z.1 : ℝ)) := by
  have hcomp : angle ∘ representative =
      ((↑) : ℝ → AddCircle (1 : ℝ)) ∘ fun z : PositivePeriod × ℝ ↦ z.2 / (z.1 : ℝ) := by
    funext z
    simp [angle]
  rw [angleForm, SmoothForm.coe_mpullback,
    ← mpullback_comp ((contMDiff_representative ∞).mdifferentiable (by simp))
      (contMDiff_angle.mdifferentiable (by simp)), hcomp,
    mpullback_comp (contMDiff_normalizedTime (n := ∞).mdifferentiable (by simp))
      ((AddCircle.contMDiff_coe 1 ∞).mdifferentiable (by simp)),
    AddCircle.mpullback_coe_timeForm, mpullback_mextDeriv_ofFunction
      (contMDiff_normalizedTime (n := ∞).mdifferentiable (by simp)) mdifferentiable_id]
  rfl

/-- On the real cover, the product rule for `t = p * (t / p)` expresses `dt` through `dp` and
`d(t / p)`. -/
private theorem mextDeriv_ofFunction_snd_eq_mul (z : PositivePeriod × ℝ) :
    mextDeriv (RoughForm.ofFunction (𝓘(ℝ).prod 𝓘(ℝ)) fun z : PositivePeriod × ℝ ↦ z.2) z =
      (z.1 : ℝ) • mextDeriv (RoughForm.ofFunction (𝓘(ℝ).prod 𝓘(ℝ))
          fun z : PositivePeriod × ℝ ↦ z.2 / (z.1 : ℝ)) z +
        (z.2 / (z.1 : ℝ)) • mextDeriv (RoughForm.ofFunction (𝓘(ℝ).prod 𝓘(ℝ))
          fun z : PositivePeriod × ℝ ↦ (z.1 : ℝ)) z := by
  have ht : (fun z : PositivePeriod × ℝ ↦ (z.1 : ℝ)) * (fun z ↦ z.2 / (z.1 : ℝ)) =
      fun z ↦ z.2 := by
    funext z
    simp [mul_div_cancel₀ _ z.1.property.ne']
  rw [← ht]
  exact mextDeriv_ofFunction_mul
    ((contMDiff_subtype_val.comp contMDiff_fst (n := ∞)).mdifferentiable (by simp) z)
    (contMDiff_normalizedTime (n := ∞).mdifferentiable (by simp) z)

/-- On the real cover `Q(p, t) = (p, [t]_p)`, the time form is `dt - (t / p) • dp`. -/
theorem mpullback_representative_timeForm :
    mpullback (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) representative timeForm.1 =
      mextDeriv (RoughForm.ofFunction (𝓘(ℝ).prod 𝓘(ℝ)) fun z : PositivePeriod × ℝ ↦ z.2) -
        fun z ↦ (z.2 / (z.1 : ℝ)) •
          mextDeriv (RoughForm.ofFunction (𝓘(ℝ).prod 𝓘(ℝ))
            fun z : PositivePeriod × ℝ ↦ (z.1 : ℝ)) z := by
  funext z
  have hβ := congrFun mpullback_representative_angleForm z
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  have hv := DFunLike.congr_fun hβ v
  simp only [mpullback_apply] at hv ⊢
  rw [timeForm_apply, hv, Pi.sub_apply, mextDeriv_ofFunction_snd_eq_mul]
  simp

/-- The period of a real representative is its first coordinate. -/
private theorem period_comp_representative :
    (fun z : CircleFamily ↦ (z.period : ℝ)) ∘ representative = fun z ↦ (z.1 : ℝ) :=
  funext fun z ↦ congrArg Subtype.val (period_representative z)

/-- Every form pulled back to the real cover `Q(p, t) = (p, [t]_p)` is invariant under the deck
translations `(p, t) ↦ (p, t + k p)`, which fix `Q`. For the time form this is the invariance of
`Q^* η = dt - (t / p) • dp`. -/
theorem mpullback_deck_mpullback_representative {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {l : ℕ} (k : ℤ) (φ : RoughForm (𝓘(ℝ).prod 𝓘(ℝ)) CircleFamily F l) :
    mpullback (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ))
        (fun z : PositivePeriod × ℝ ↦ (z.1, z.2 + k * (z.1 : ℝ)))
        (mpullback (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) representative φ) =
      mpullback (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) representative φ := by
  have hdeck : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) ∞
      fun z : PositivePeriod × ℝ ↦ (z.1, z.2 + k * (z.1 : ℝ)) :=
    contMDiff_fst.prodMk
      (contMDiff_snd.add (contMDiff_const.mul (contMDiff_subtype_val.comp contMDiff_fst)))
  have hcomp : representative ∘ (fun z : PositivePeriod × ℝ ↦ (z.1, z.2 + k * (z.1 : ℝ))) =
      representative :=
    funext fun z ↦ representative_add_intCast_mul z.1 z.2 k
  rw [← mpullback_comp (hdeck.mdifferentiable (by simp))
    ((contMDiff_representative ∞).mdifferentiable (by simp)), hcomp]

/-- On the real cover `Q(p, t) = (p, [t]_p)`, the exterior derivative of the time form is
`Q^*(dη) = p⁻¹ • (dp ∧ dt)`. -/
theorem mpullback_representative_mextDeriv_timeForm :
    mpullback (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) representative (mextDeriv timeForm.1) =
      fun z ↦ (z.1 : ℝ)⁻¹ •
        RoughForm.wedge
          (mextDeriv (RoughForm.ofFunction (𝓘(ℝ).prod 𝓘(ℝ))
            fun z : PositivePeriod × ℝ ↦ (z.1 : ℝ)))
          (mextDeriv (RoughForm.ofFunction (𝓘(ℝ).prod 𝓘(ℝ))
            fun z : PositivePeriod × ℝ ↦ z.2)) z := by
  have hQ := (contMDiff_representative (n := ∞)).mdifferentiable (by simp)
  rw [mextDeriv_timeForm, mpullback_wedge, mpullback_mextDeriv_ofFunction hQ
    (contMDiff_periodReal (n := 1).mdifferentiable one_ne_zero), mpullback_representative_angleForm,
    period_comp_representative]
  funext z
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
  rw [hv, ContinuousAlternatingMap.smul_apply, RoughForm.wedge_apply_one_one,
    RoughForm.wedge_apply_one_one, mextDeriv_ofFunction_snd_eq_mul]
  have hp : (z.1 : ℝ) ≠ 0 := z.1.property.ne'
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  field_simp
  ring

/-! ### The total form -/

/-- The **total form** `dp ∧ η` of the family of positive-period circles: the wedge of the
differential of the period with the time form. It vanishes nowhere
(`TauCeti.CircleFamily.totalForm_apply_ne_zero`), so it orients the family. -/
def totalForm : SmoothForm (𝓘(ℝ).prod 𝓘(ℝ)) CircleFamily ℝ 2 :=
  SmoothForm.wedge
    (SmoothForm.mpullback (fun z : CircleFamily ↦ (z.period : ℝ)) contMDiff_periodReal
      SmoothForm.realLineCoordForm)
    timeForm

/-- The total form is the wedge `dp ∧ η` of the differential of the period with the time form. -/
theorem coe_totalForm :
    totalForm.1 =
      RoughForm.wedge
        (mextDeriv (RoughForm.ofFunction (𝓘(ℝ).prod 𝓘(ℝ))
          fun z : CircleFamily ↦ (z.period : ℝ)))
        timeForm.1 := by
  rw [totalForm, SmoothForm.coe_wedge, SmoothForm.coe_mpullback,
    SmoothForm.mpullback_realLineCoordForm]

/-- On the real cover `Q(p, t) = (p, [t]_p)`, the total form is `Q^*(dp ∧ η) = dp ∧ dt`. -/
theorem mpullback_representative_totalForm :
    mpullback (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) representative totalForm.1 =
      RoughForm.wedge
        (mextDeriv (RoughForm.ofFunction (𝓘(ℝ).prod 𝓘(ℝ))
          fun z : PositivePeriod × ℝ ↦ (z.1 : ℝ)))
        (mextDeriv (RoughForm.ofFunction (𝓘(ℝ).prod 𝓘(ℝ))
          fun z : PositivePeriod × ℝ ↦ z.2)) := by
  have hQ := (contMDiff_representative (n := ∞)).mdifferentiable (by simp)
  rw [coe_totalForm, mpullback_wedge, mpullback_mextDeriv_ofFunction hQ
    (contMDiff_periodReal (n := 1).mdifferentiable one_ne_zero), mpullback_representative_timeForm,
    period_comp_representative]
  funext z
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  have hv : v = ![v 0, v 1] := (FinVec.etaExpand_eq v).symm
  rw [hv, RoughForm.wedge_apply_one_one, RoughForm.wedge_apply_one_one]
  simp only [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]
  ring

/-- Read through the real cover `Q(p, t) = (p, [t]_p)`, the total form is the coordinate area form
`dp ∧ dt`: it pairs the images of tangent vectors `v` and `w` of `ℝ_{>0} × ℝ` to
`v.1 * w.2 - w.1 * v.2`. -/
theorem eval₂_totalForm_mfderiv_representative (y : PositivePeriod × ℝ)
    (v w : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) y) :
    SmoothBundleForm.eval₂ totalForm (representative y)
        (mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) representative y v)
        (mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) representative y w) =
      v.1 * w.2 - w.1 * v.2 := by
  have h := DFunLike.congr_fun (congrFun mpullback_representative_totalForm y) ![v, w]
  rw [mpullback_apply, RoughForm.wedge_apply_one_one, mextDeriv_ofFunction_coe_fst_apply,
    mextDeriv_ofFunction_coe_fst_apply, mextDeriv_ofFunction_snd_apply,
    mextDeriv_ofFunction_snd_apply] at h
  rw [SmoothBundleForm.eval₂_apply]
  exact (congrArg (totalForm.1 (representative y)) (FinVec.etaExpand_eq _)).trans h

/-- The total form `dp ∧ η` vanishes nowhere. -/
theorem totalForm_apply_ne_zero (z : CircleFamily) : totalForm.1 z ≠ 0 := by
  obtain ⟨y, rfl⟩ := representative_surjective z
  intro h
  -- On the images of the coordinate frame `(∂_p, ∂_t)` of the real cover, the form is `1`.
  have h1 := eval₂_totalForm_mfderiv_representative y ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))
  rw [SmoothBundleForm.eval₂_apply, h] at h1
  norm_num at h1

/-- On a fiber, the total form is the product of the base and fiber directions: at a point of the
circle of period `p`, it pairs a tangent vector `u` of the family with the image of a tangent
vector `w` of `AddCircle p` to `dp(u) * dt_p(w)`. -/
theorem eval₂_totalForm_mfderiv_mk (p : PositivePeriod) (x : AddCircle (p : ℝ))
    (u : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) (mk p x)) (w : TangentSpace 𝓘(ℝ) x) :
    SmoothBundleForm.eval₂ totalForm (mk p x) u
        (mfderiv 𝓘(ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) (mk p) x w) =
      mextDeriv (RoughForm.ofFunction (𝓘(ℝ).prod 𝓘(ℝ))
          fun z : CircleFamily ↦ (z.period : ℝ)) (mk p x) ![u] *
        (AddCircle.timeForm (p : ℝ)).1 x ![w] := by
  have hmk := (contMDiff_mk p ∞).mdifferentiable (by simp)
  -- The time form restricts to `dt_p` on the fiber.
  have hη := DFunLike.congr_fun (congrFun (congrArg Subtype.val (mpullback_mk_timeForm p)) x) ![w]
  rw [SmoothForm.coe_mpullback, mpullback_apply] at hη
  have hw : (fun i ↦ mfderiv 𝓘(ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) (mk p) x (![w] i)) =
      ![mfderiv 𝓘(ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) (mk p) x w] :=
    (FinVec.etaExpand_eq _).symm
  rw [hw] at hη
  -- The period is constant on the fiber, so `dp` vanishes on fiber directions.
  have hp : mextDeriv (RoughForm.ofFunction (𝓘(ℝ).prod 𝓘(ℝ))
      fun z : CircleFamily ↦ (z.period : ℝ)) (mk p x)
        ![mfderiv 𝓘(ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) (mk p) x w] = 0 := by
    have hconst : (fun z : CircleFamily ↦ (z.period : ℝ)) ∘ mk p = fun _ ↦ (p : ℝ) := rfl
    have hc := mfderiv_comp_apply x
      (contMDiff_periodReal (n := 1).mdifferentiableAt one_ne_zero (x := mk p x)) (hmk x) w
    rw [hconst, mfderiv_const, zero_apply] at hc
    rw [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
      mvfderiv_apply_eq_mfderiv_apply, Matrix.cons_val_zero]
    exact hc.symm
  rw [SmoothBundleForm.eval₂_apply, coe_totalForm, RoughForm.wedge_apply_one_one, hη, hp,
    zero_mul, sub_zero]

end CircleFamily

end TauCeti
