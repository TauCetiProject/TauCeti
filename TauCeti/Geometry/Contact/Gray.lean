/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactomorphism
public import TauCeti.Geometry.Contact.Family
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family

/-!
# Gray stability for families of contact forms on compact manifolds

A smooth time-dependent family of one-forms `α_t` on a manifold `M` is represented by a single
smooth one-form `α` on `ℝ × M`, whose slices `α_t = ι_t^* α` are the forms of the family, and
whose time derivative `∂_t α` (`TauCeti.SmoothForm.timeDeriv`) has as slices the velocities
`d/dt α_t`. When every `α_t` is a contact form, the **Gray vector field**
`TauCeti.SmoothForm.grayVectorField` is the time-dependent vector field `Y_t` which at each time
is the horizontal contact-Moser vector field of `(α_t, ∂_t α_t)`: the unique vector field in the
contact hyperplanes `ker α_t` with `(ι_{Y_t} dα_t + ∂_t α_t)|ker α_t = 0`. It depends smoothly on
time and point, and satisfies Gray's equation
`L_{Y_t} α_t + ∂_t α_t = μ_t α_t` with `μ_t = (∂_t α_t)(R_{α_t})`, where `R_{α_t}` is the Reeb
field.

On a compact manifold without boundary, the time-dependent flow `φ_{s,t}` of the Gray vector field
is defined for all times. **Gray's stability theorem** says that it carries the contact
structures into one another, preserving their coorientations:
`φ_{s,t}^* α_t = exp (∫ₛᵗ μ_u ∘ φ_{s,u} du) α_s`
(`TauCeti.SmoothForm.mpullback_grayDiffeomorph_apply`). So the diffeomorphisms
`TauCeti.SmoothForm.grayDiffeomorph` form a smooth isotopy of coorientation-preserving
contactomorphisms from `ker α_s` to `ker α_t`. The isotopy fixes every point at which the contact
hyperplane `ker α_t` does not move with `t`, because the Gray vector field vanishes there.

## Main definitions

* `TauCeti.SmoothForm.grayVectorField`: the Gray vector field of a family of one-forms.
* `TauCeti.SmoothForm.grayDiffeomorph`: on a compact manifold, its time-dependent flow from time
  `s` to time `t`, as a diffeomorphism.

## Main results

* `TauCeti.SmoothForm.eq_grayVectorField_iff`: the Gray vector field is characterized by the
  horizontal contact-Moser equation.
* `TauCeti.SmoothForm.mlieDerivForm_grayVectorField_add`: Gray's equation.
* `TauCeti.SmoothForm.contMDiff_grayVectorField`: the Gray vector field is jointly smooth.
* `TauCeti.SmoothForm.grayVectorField_eq_zero`: the Gray vector field vanishes at points where the
  contact hyperplane is stationary.
* `TauCeti.SmoothForm.mpullback_grayDiffeomorph_apply`: Gray's stability theorem, in the explicit
  form `φ_{s,t}^* α_t = exp (∫ₛᵗ μ_u ∘ φ_{s,u} du) α_s`.
* `TauCeti.SmoothForm.preservesCoorientation_grayDiffeomorph`,
  `TauCeti.SmoothForm.isContactomorphism_grayDiffeomorph`: the flow maps are
  coorientation-preserving contactomorphisms.
* `TauCeti.SmoothForm.contMDiff_grayDiffeomorph`: they form a smooth isotopy.
* `TauCeti.SmoothForm.grayDiffeomorph_apply_eq_self`: the isotopy fixes the points at which the
  contact hyperplane is stationary.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (Gray stability) and its proof.
* J. W. Gray, *Some global properties of contact structures*, Ann. of Math. 69 (1959), 421–450.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The Gray vector field -/

variable (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1)

/-- The **Gray vector field** of a smooth family of one-forms `α_t = ι_t^* α` on `M`, represented
by a one-form `α` on `ℝ × M`. At time `t` it is the horizontal contact-Moser vector field of `α_t`
and of the velocity `∂_t α_t`: when `α_t` is a contact form, this is the unique vector field `Y_t`
with `α_t(Y_t) = 0` and `(ι_{Y_t} dα_t + ∂_t α_t)|ker α_t = 0`
(`TauCeti.SmoothForm.eq_grayVectorField_iff`). -/
def grayVectorField (t : ℝ) (x : M) : TangentSpace I x :=
  (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).contactMoserVectorField
    (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv) x

/-- The Gray vector field is the contact-Moser vector field of the slice and its velocity. -/
theorem grayVectorField_def (t : ℝ) (x : M) :
    α.grayVectorField t x =
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).contactMoserVectorField
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv) x :=
  (rfl)

/-- The **Gray rate** `μ_t = (∂_t α_t)(R_{α_t})` of a smooth family of one-forms `α_t = ι_t^* α`,
as a function of time and point. When every `α_t` is a contact form, it is the coefficient in
Gray's equation `L_{Y_t} α_t + ∂_t α_t = μ_t α_t`
(`TauCeti.SmoothForm.mlieDerivForm_grayVectorField_add`), and the flow of the Gray vector field
rescales `α_t` by the exponential of its integral
(`TauCeti.SmoothForm.mpullback_grayDiffeomorph_apply`). -/
def grayRate (p : ℝ × M) : ℝ :=
  (mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).1 p.2
    ![(mpullback (Prod.mk p.1) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField p.2]

/-- The Gray rate is the velocity of the slices evaluated on the Reeb field. -/
theorem grayRate_def (t : ℝ) (x : M) :
    α.grayRate (t, x) =
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).1 x
        ![(mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField x] :=
  (rfl)

variable {α} [FiniteDimensional ℝ E]
  (hc : ∀ t, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
include hc

/-- The Gray vector field is horizontal: `α_t(Y_t) = 0`. -/
theorem apply_grayVectorField (t : ℝ) (x : M) :
    (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x
      ![α.grayVectorField t x] = 0 :=
  (hc t).apply_contactMoserVectorField _ x

/-- **The Gray vector field is characterized by the horizontal contact-Moser equation**: a tangent
vector is the value of the Gray vector field at time `t` exactly when it lies in `ker α_t` and
`(ι_v dα_t + ∂_t α_t)|ker α_t = 0`. -/
theorem eq_grayVectorField_iff {t : ℝ} {x : M} {v : TangentSpace I x} :
    v = α.grayVectorField t x ↔
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x ![v] = 0 ∧
        ∀ w ∈ (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x,
          mextDeriv (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x ![v, w] +
            (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).1 x ![w] =
              0 :=
  (hc t).eq_contactMoserVectorField_iff

/-- **Gray's equation**: `L_{Y_t} α_t + ∂_t α_t = μ_t α_t`, where `μ_t = (∂_t α_t)(R_{α_t})` is
the Gray rate, evaluated on a tangent vector. -/
theorem mlieDerivForm_grayVectorField_add (t : ℝ) (x : M) (v : TangentSpace I x) :
    mlieDerivForm (α.grayVectorField t)
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x ![v] +
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).1 x ![v] =
        α.grayRate (t, x) *
          (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x ![v] :=
  (hc t).mlieDerivForm_contactMoserVectorField_add _ x v

/-- The Gray vector field of a smooth family of contact forms depends smoothly on time and point:
`(t, x) ↦ (x, Y_t(x))` is smooth into the tangent bundle. -/
theorem contMDiff_grayVectorField :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, α.grayVectorField p.1 p.2⟩ : TangentBundle I M)) :=
  contMDiff_contactMoserVectorField_mpullback_prodMk α α.timeDeriv hc

/-- The Gray rate `μ_t = (∂_t α_t)(R_{α_t})` of a smooth family of contact forms depends smoothly
on time and point. -/
theorem contMDiff_grayRate : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ α.grayRate := fun p ↦ by
  have hR := contMDiff_reebVectorField_mpullback_prodMk α hc p
  have hβ := (contMDiffAt_sectionAlong_degreeOneEquiv_iff (b := Prod.snd)
    (α := fun q : ℝ × M ↦ mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id)
      α.timeDeriv)).2 (contMDiff_mpullback_prodMk α.timeDeriv p)
  have h := (contMDiffAt_totalSpace.1
    (ContMDiffAt.clm_bundle_apply (E₂ := Trivial M ℝ) hβ hR)).2
  simp only [Trivial.eq_trivialization, degreeOneEquiv_apply_apply_vec] at h
  -- This is the defining formula of the Gray rate.
  exact h

/-- **The Gray vector field vanishes where the contact hyperplane is stationary.** If the
hyperplane `ker α_t` at `x` is the same for all times, then `Y_t(x) = 0` for all times: the
velocity `∂_t α_t` annihilates the hyperplane at `x`, which the contact-Moser field then ignores. -/
theorem grayVectorField_eq_zero [I.Boundaryless] {x : M}
    (hx : ∀ u, (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x =
      (mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x)
    (t : ℝ) : α.grayVectorField t x = 0 := by
  rw [grayVectorField_def, (hc t).contactMoserVectorField_eq_zero_iff]
  intro w hw
  -- The vector `w` stays in the hyperplane at all times, so `u ↦ α_u(w)` vanishes identically,
  -- and its derivative `(∂_t α_t)(w)` is zero.
  have hzero (u : ℝ) :
      (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).1 x ![w] = 0 :=
    mem_kerDistribution.1 (by rw [hx u, ← hx t]; exact hw)
  have hd := (ContinuousAlternatingMap.apply ℝ E ℝ ![w]).hasFDerivAt.comp_hasDerivAt t
    (α.hasDerivAt_mpullback_prodMk_timeDeriv t x)
  have hfun : (⇑(ContinuousAlternatingMap.apply ℝ E ℝ ![w]) ∘ fun u ↦
      (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).1 x) = fun _ ↦ 0 :=
    funext fun u ↦ ContinuousAlternatingMap.apply_apply.trans (hzero u)
  rw [hfun] at hd
  -- `ContinuousAlternatingMap.apply_apply` evaluates the left side, read in the fibre
  -- `Trivial M ℝ x`, which is `ℝ`.
  exact hd.unique (hasDerivAt_const t (0 : ℝ))

/-! ### Gray's stability theorem on compact manifolds -/

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

/-- On a compact manifold, the Gray vector field has a complete suspension: its time-dependent flow
is defined for all times. -/
theorem isCompleteVectorField_timeDependentSuspensionField_grayVectorField :
    IsCompleteVectorField (timeDependentSuspensionField α.grayVectorField) :=
  isCompleteVectorField_timeDependentSuspensionField
    ((contMDiff_grayVectorField hc).of_le (by simp)) isCompact_univ (by simp)

/-- **Gray's isotopy.** On a compact manifold without boundary, the time-dependent flow of the
Gray vector field of a smooth family of contact forms, from time `s` to time `t`, as a
diffeomorphism. It pulls `α_t` back to a positive multiple of `α_s`
(`TauCeti.SmoothForm.mpullback_grayDiffeomorph_apply`). -/
def grayDiffeomorph (s t : ℝ) : M ≃ₘ⟮I, I⟯ M :=
  timeDependentFlowDiffeomorph (isCompleteVectorField_timeDependentSuspensionField_grayVectorField
    hc) le_top (contMDiff_grayVectorField hc) s t

/-- Gray's isotopy is the time-dependent flow of the Gray vector field. -/
theorem grayDiffeomorph_apply (s t : ℝ) (x : M) :
    grayDiffeomorph hc s t x = timeDependentFlowOf α.grayVectorField s t x :=
  timeDependentFlowDiffeomorph_apply _ _ _ s t x

/-- The inverse of Gray's isotopy from `s` to `t` is Gray's isotopy from `t` to `s`. -/
@[simp]
theorem grayDiffeomorph_symm_apply (s t : ℝ) (x : M) :
    (grayDiffeomorph hc s t).symm x = grayDiffeomorph hc t s x :=
  (timeDependentFlowDiffeomorph_symm_apply _ _ _ s t x).trans (grayDiffeomorph_apply hc t s x).symm

/-- Gray's isotopy from a time to itself is the identity. -/
@[simp]
theorem grayDiffeomorph_self (s : ℝ) (x : M) : grayDiffeomorph hc s s x = x := by
  rw [grayDiffeomorph_apply,
    timeDependentFlowOf_self ((contMDiff_grayVectorField hc).of_le (by simp))]

/-- Gray's isotopy composes: flowing from `r` to `s` and then from `s` to `t` is flowing from `r`
to `t`. -/
@[simp]
theorem grayDiffeomorph_grayDiffeomorph (r s t : ℝ) (x : M) :
    grayDiffeomorph hc s t (grayDiffeomorph hc r s x) = grayDiffeomorph hc r t x := by
  simp only [grayDiffeomorph_apply]
  exact timeDependentFlowOf_trans
    (isCompleteVectorField_timeDependentSuspensionField_grayVectorField hc)
    ((contMDiff_grayVectorField hc).of_le (by simp)) r s t x

/-- Gray's isotopy depends smoothly on the final time and the point. -/
theorem contMDiff_grayDiffeomorph (s : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ grayDiffeomorph hc s p.1 p.2) := by
  simp only [grayDiffeomorph_apply]
  exact (contMDiff_timeDependentFlowOf
    (isCompleteVectorField_timeDependentSuspensionField_grayVectorField hc) le_top
    (contMDiff_grayVectorField hc)).comp
      (((contMDiff_const (c := s)).prodMk contMDiff_fst).prodMk contMDiff_snd)

/-- **Gray's stability theorem.** On a compact manifold without boundary, the time-dependent flow
`φ_{s,t}` of the Gray vector field of a smooth family of contact forms `α_t` rescales the forms:
`φ_{s,t}^* α_t = exp (∫ₛᵗ μ_u ∘ φ_{s,u} du) α_s`, where `μ_u = (∂_t α_u)(R_{α_u})`. -/
theorem mpullback_grayDiffeomorph_apply (s t : ℝ) (x : M) :
    (mpullback (grayDiffeomorph hc s t) (grayDiffeomorph hc s t).contMDiff
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α)).1 x =
      Real.exp (∫ u in s..t, α.grayRate (u, grayDiffeomorph hc s u x)) •
        (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).1 x := by
  have hX := contMDiff_grayVectorField hc
  -- Gray's equation says that the rate `∂_t α_t + L_{Y_t} α_t` is `μ_t α_t`.
  have hL (t : ℝ) :
      TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α.1) +
        mlieDerivForm (α.grayVectorField t) (TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α.1) =
      fun y ↦ α.grayRate (t, y) • TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α.1 y := by
    funext y
    ext v
    have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
    have h := mlieDerivForm_grayVectorField_add hc t y (v 0)
    rw [hv]
    simp only [coe_mpullback, coe_timeDeriv, Pi.add_apply, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h ⊢
    rw [add_comm, h]
  have h := mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul
    (hX.of_le (by simp)) (isCompleteVectorField_timeDependentSuspensionField_grayVectorField hc)
    (contMDiff_grayRate hc).continuous (α.contMDiff.of_le (by simp)) hL s t x
  have hφ : ⇑(grayDiffeomorph hc s t) = timeDependentFlowOf α.grayVectorField s t :=
    funext (grayDiffeomorph_apply hc s t)
  simpa only [coe_mpullback, grayDiffeomorph_apply, hφ] using h

/-- **Gray's stability theorem**, coorientation form: Gray's isotopy from `s` to `t` is a
contactomorphism from `ker α_s` to `ker α_t` carrying the coorientation given by `α_s` to that
given by `α_t`. -/
theorem preservesCoorientation_grayDiffeomorph (s t : ℝ) :
    (grayDiffeomorph hc s t).PreservesCoorientation
      (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α)
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α) :=
  Diffeomorph.preservesCoorientation_def.2 fun x ↦
    ⟨_, Real.exp_pos _, mpullback_grayDiffeomorph_apply hc s t x⟩

/-- **Gray's stability theorem**: Gray's isotopy from `s` to `t` is a contactomorphism from
`ker α_s` to `ker α_t`. -/
theorem isContactomorphism_grayDiffeomorph (s t : ℝ) :
    (grayDiffeomorph hc s t).IsContactomorphism
      (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α)
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α) :=
  (preservesCoorientation_grayDiffeomorph hc s t).isContactomorphism

/-- Gray's isotopy fixes every point at which the contact hyperplane `ker α_t` is the same for all
times. -/
theorem grayDiffeomorph_apply_eq_self {x : M}
    (hx : ∀ u, (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x =
      (mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x)
    (s t : ℝ) : grayDiffeomorph hc s t x = x := by
  rw [grayDiffeomorph_apply]
  exact timeDependentFlowOf_eq_self_of_forall_eq_zero
    ((contMDiff_grayVectorField hc).of_le (by simp)) (grayVectorField_eq_zero hc hx) s t

end TauCeti.SmoothForm
