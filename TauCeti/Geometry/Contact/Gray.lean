/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactomorphism
public import TauCeti.Geometry.Contact.Family
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
public import TauCeti.Geometry.Manifold.Flow.TimeDependent

/-!
# Gray stability

Let `α` be a smooth one-form on `ℝ × M` whose slices `α_t = ι_t^* α`, the pullbacks along the
inclusions `ι_t : y ↦ (t, y)`, are contact forms on a finite-dimensional boundaryless manifold
`M`. Gray's stability theorem says that on a compact `M` the contact structures `ker α_t` are all
isotopic: there is an isotopy `φ_t` with `φ_t^* α_t = g_t α_0` for positive functions `g_t`.

The isotopy is the time-dependent flow of the **Gray vector field** `Y_t`
(`TauCeti.SmoothForm.grayVectorField`), the horizontal contact-Moser vector field of the pair
`(α_t, ∂_t α_t)`: the unique vector field with `Y_t ∈ ker α_t` and
`(ι_(Y_t) dα_t + ∂_t α_t)|ker α_t = 0`. Here the time derivative `∂_t α`
(`TauCeti.SmoothForm.timeDeriv`) is the Lie derivative of `α` along the time field `∂_t`, as a
smooth one-form on `ℝ × M`; its slices are the velocities of the slices of `α`. The contact-Moser
identity `L_Y α + β = β(R_α) α` turns the defining equations into the rate identity

`∂_t α_t + L_(Y_t) α_t = g_t α_t`, with `g_t = ∂_t α_t(R_(α_t))`

(`TauCeti.SmoothForm.mpullback_prodMk_mlieDerivForm_add_mlieDerivForm_grayVectorField`), and
Moser's principle for families of forms integrates it along the flow. On a compact manifold the
flow exists for all times, and its time maps `φ_(s,t)` form the **Gray isotopy**
(`TauCeti.SmoothForm.grayIsotopy`), with

`φ_(s,t)^* α_t = exp (∫ₛᵗ g (u, φ_(s,u) x) du) • α_s`

(`TauCeti.SmoothForm.mpullback_timeDependentFlowOf_grayVectorField_apply`). So each `φ_(s,t)`
preserves the coorientation from `α_s` to `α_t`, and carries `ker α_s` onto `ker α_t`.

The construction is relative: `Y_t(x) = 0` at every point `x` where the hyperplanes `ker α_u` at
`x` do not move with `u`, because there `∂_t α_t` annihilates `ker α_t`. The Gray isotopy therefore
fixes pointwise every set on which the contact structures agree for all times.

## Main definitions

* `TauCeti.SmoothForm.timeDeriv`: the time derivative `∂_t α = L_(∂_t) α` of a smooth one-form on
  `ℝ × M`.
* `TauCeti.SmoothForm.grayVectorField`: the Gray vector field of a family of one-forms.
* `TauCeti.SmoothForm.grayIsotopy`: on a compact manifold, the time-dependent flow of the Gray
  vector field of a family of contact forms, as diffeomorphisms.

## Main results

* `TauCeti.SmoothForm.hasDerivAt_mpullback_prodMk_timeDeriv`: the slices of `∂_t α` are the
  velocities of the slices of `α`.
* `TauCeti.SmoothForm.eq_grayVectorField_iff`: the defining equations of the Gray vector field.
* `TauCeti.SmoothForm.contMDiff_grayVectorField`: the Gray vector field is jointly smooth.
* `TauCeti.SmoothForm.preservesCoorientation_grayIsotopy`,
  `TauCeti.SmoothForm.isContactomorphism_grayIsotopy`: **Gray stability**. The Gray isotopy pulls
  `α_t` back to a positive multiple of `α_s`, so it carries the contact structure `ker α_s` with
  its coorientation onto `ker α_t`.
* `TauCeti.SmoothForm.grayIsotopy_apply_eq_self_of_kerDistribution_eq`: the Gray isotopy fixes
  every point at which the contact hyperplanes are the same for all times.

## References

* J. W. Gray, *Some global properties of contact structures*, Annals of Mathematics 69 (1959),
  421–450.
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (Gray stability) and its proof.
-/

public section

noncomputable section

open Bundle Set
open scoped ContDiff Manifold Topology

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The time derivative of a family of one-forms -/

/-- The unit vector field `∂_t` of the time coordinate on `ℝ × M`, as a smooth section. -/
private def timeField :
    Cₛ^∞⟮𝓘(ℝ, ℝ).prod I; ℝ × E, TangentSpace (𝓘(ℝ, ℝ).prod I) (M := ℝ × M)⟯ :=
  ⟨fun _ ↦ ((1 : ℝ), (0 : E)), contMDiff_const_prod_field (X := 0) 1
    ((contMDiff_zeroSection ℝ (TangentSpace I)).comp contMDiff_snd)⟩

@[simp]
private theorem timeField_apply (p : ℝ × M) : timeField (I := I) p = ((1 : ℝ), (0 : E)) :=
  (rfl)

/-- The contraction `α(∂_t)` of a smooth one-form on `ℝ × M` with the time field is smooth. -/
private theorem contMDiff_apply_timeField (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ fun p : ℝ × M ↦ α.1 p ![((1 : ℝ), (0 : E))] := by
  intro p
  have h := (contMDiffAt_totalSpace.1 (ContMDiffAt.clm_bundle_apply
    (E₂ := Trivial (ℝ × M) ℝ) ((degreeOneEquiv α).contMDiff p)
    ((timeField (I := I) (M := M)).contMDiff p))).2
  simp only [Trivial.eq_trivialization, timeField_apply] at h
  -- The trivial line bundle's trivialization reads off the value of `α(∂_t)` itself.
  convert h using 2 with q
  exact (degreeOneEquiv_apply_apply_vec α q _).symm

/-- The **time derivative** `∂_t α = L_(∂_t) α` of a smooth one-form `α` on `ℝ × M`, as a smooth
one-form: the Lie derivative of `α` along the unit vector field `∂_t` of the time coordinate. Its
slices `ι_t^* ∂_t α` are the velocities of the slices `ι_t^* α`
(`TauCeti.SmoothForm.hasDerivAt_mpullback_prodMk_timeDeriv`). -/
def timeDeriv (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1) :
    SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1 :=
  -- Cartan's formula `L_(∂_t) α = ι_(∂_t) dα + d (α(∂_t))` exhibits the Lie derivative as smooth.
  SmoothTwoForm.interiorₗ (mextDerivₗ (𝓘(ℝ, ℝ).prod I) 1 α) timeField +
    mextDerivₗ (𝓘(ℝ, ℝ).prod I) 0
      ⟨RoughForm.ofFunction _ fun p ↦ α.1 p ![((1 : ℝ), (0 : E))],
        (isSmoothForm_ofFunction_iff.2 (contMDiff_apply_timeField α)).mem_smoothBundleForms⟩

/-- The time derivative is the Lie derivative along the time field `∂_t`. -/
theorem coe_timeDeriv (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1) :
    (timeDeriv α).1 = mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α.1 := by
  funext p
  ext v
  obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, by ext i; fin_cases i; rfl⟩
  rw [mlieDerivForm_apply_eq_mextDeriv_add (f := fun p ↦ α.1 p ![((1 : ℝ), (0 : E))])
    (fun _ ↦ rfl) (α.mdifferentiableAt p)
    ((timeField (I := I) (M := M)).contMDiff.mdifferentiableAt (by simp))]
  simp [timeDeriv, RoughForm.interior_apply, mextDeriv_ofFunction_apply]

/-- **The time derivative is the velocity of the slices.** For a smooth one-form `α` on `ℝ × M`,
the slices `α_u = ι_u^* α` at a point `x` have velocity `(ι_t^* ∂_t α)_x` at time `t`. -/
theorem hasDerivAt_mpullback_prodMk_timeDeriv [I.Boundaryless]
    (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1) (t : ℝ) (x : M) :
    HasDerivAt (F := E [⋀^Fin 1]→L[ℝ] ℝ)
      (fun u ↦ (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).1 x)
      ((mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (timeDeriv α)).1 x) t := by
  simpa only [coe_mpullback, coe_timeDeriv] using
    hasDerivAt_mpullback_prodMk t x (α.mdifferentiableAt (t, x))

/-! ### The Gray vector field -/

variable {α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1}

variable (α) in
/-- The **Gray vector field** of a smooth family of one-forms `α_t = ι_t^* α` on `M`: at time `t`
it is the horizontal contact-Moser vector field `Y_t` of `(α_t, ∂_t α_t)`, the solution of
`α_t(Y_t) = 0` and `(ι_(Y_t) dα_t + ∂_t α_t)|ker α_t = 0`. -/
def grayVectorField (t : ℝ) (x : M) : TangentSpace I x :=
  (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).contactMoserVectorField
    (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (timeDeriv α)) x

variable (α) in
/-- The Gray vector field at time `t` is the contact-Moser vector field of `(α_t, ∂_t α_t)`. -/
theorem grayVectorField_def (t : ℝ) :
    grayVectorField α t =
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).contactMoserVectorField
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (timeDeriv α)) :=
  (rfl)

section Contact

variable [FiniteDimensional ℝ E]
  (hc : ∀ t, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
include hc

/-- **Characterization of the Gray vector field.** For a family of contact forms, `Y_t(x)` is the
unique tangent vector `v` with `α_t(v) = 0` and `dα_t(v, w) + ∂_t α_t(w) = 0` for every `w` in the
contact hyperplane `ker α_t`. -/
theorem eq_grayVectorField_iff {t : ℝ} {x : M} {v : TangentSpace I x} :
    v = grayVectorField α t x ↔
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x ![v] = 0 ∧
        ∀ w ∈ (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x,
          mextDeriv (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x ![v, w] +
            (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (timeDeriv α)).1 x
              ![w] = 0 :=
  grayVectorField_def α t ▸ (hc t).eq_contactMoserVectorField_iff

/-- The Gray vector field of a smooth family of contact forms is jointly smooth in time and
space. -/
theorem contMDiff_grayVectorField :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, grayVectorField α p.1 p.2⟩ : TangentBundle I M)) :=
  contMDiff_contactMoserVectorField_mpullback_prodMk α (timeDeriv α) hc

/-- **Gray's rate identity.** Along the Gray vector field, the time derivative of a family of
contact forms plus the Lie derivative of the slice is the multiple `g_t α_t` of the slice, where
`g_t = ∂_t α_t(R_(α_t))` is the Reeb component of the time derivative. -/
theorem mpullback_prodMk_mlieDerivForm_add_mlieDerivForm_grayVectorField (t : ℝ) :
    TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α.1) +
      mlieDerivForm (grayVectorField α t)
        (TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α.1) =
    fun y ↦ (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (timeDeriv α)).1 y
        ![(mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField y] •
      TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α.1 y := by
  funext y
  ext v
  obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, by ext i; fin_cases i; rfl⟩
  have h := (hc t).mlieDerivForm_contactMoserVectorField_add
    (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) (timeDeriv α)) y w
  simp only [coe_mpullback, coe_timeDeriv] at h
  rw [Pi.add_apply, ContinuousAlternatingMap.add_apply, add_comm,
    grayVectorField_def,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, coe_mpullback, coe_timeDeriv]
  exact h

variable [I.Boundaryless]

/-- **The Gray vector field vanishes where the hyperplanes are stationary.** If the contact
hyperplanes `ker α_u` at `x` are the same for all times `u`, then `Y_t(x) = 0`. -/
theorem grayVectorField_eq_zero_of_kerDistribution_eq {t : ℝ} {x : M}
    (hx : ∀ u, (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x =
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x) :
    grayVectorField α t x = 0 := by
  rw [grayVectorField_def, (hc t).contactMoserVectorField_eq_zero_iff]
  intro w hw
  -- The function `u ↦ α_u(w)` vanishes identically, so its derivative `∂_t α_t(w)` vanishes.
  have hd := (ContinuousAlternatingMap.apply ℝ E ℝ ![w]).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_mpullback_prodMk_timeDeriv α t x)
  have hzero : (⇑(ContinuousAlternatingMap.apply ℝ E ℝ ![w]) ∘
      fun u ↦ (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).1 x) = fun _ ↦ 0 :=
    funext fun u ↦ ContinuousAlternatingMap.apply_apply.trans
      (mem_kerDistribution.1 ((hx u).symm ▸ hw))
  exact ContinuousAlternatingMap.apply_apply.symm.trans <| hd.unique <|
    (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq (.of_forall fun u ↦ congrFun hzero u)

variable [T2Space M] [CompactSpace M]

/-- On a compact manifold, the suspension of the Gray vector field of a smooth family of contact
forms is complete, so its time-dependent flow is defined for all times. -/
theorem isCompleteVectorField_timeDependentSuspensionField_grayVectorField :
    IsCompleteVectorField (timeDependentSuspensionField (grayVectorField α)) :=
  isCompleteVectorField_timeDependentSuspensionField ((contMDiff_grayVectorField hc).of_le
    (by simp)) isCompact_univ fun _ _ hy ↦ absurd (mem_univ _) hy

/-- **Gray stability, with the conformal factor.** On a compact manifold, the time-dependent flow
`φ_(s,t)` of the Gray vector field of a smooth family of contact forms pulls `α_t` back to a
positive multiple of `α_s`:
`(φ_(s,t)^* α_t)_x = exp (∫ₛᵗ g (u, φ_(s,u) x) du) • (α_s)_x`, where
`g (u, y) = ∂_t α_u (R_(α_u) y)` is the Reeb component of the time derivative. -/
theorem mpullback_timeDependentFlowOf_grayVectorField_apply (s t : ℝ) (x : M) :
    TauCeti.mpullback I I (timeDependentFlowOf (grayVectorField α) s t)
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x =
      Real.exp (∫ u in s..t,
          (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) (timeDeriv α)).1
            (timeDependentFlowOf (grayVectorField α) s u x)
            ![(mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).reebVectorField
              (timeDependentFlowOf (grayVectorField α) s u x)]) •
        (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).1 x := by
  simpa only [coe_mpullback] using
    mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul
      ((contMDiff_grayVectorField hc).of_le (by simp))
      (isCompleteVectorField_timeDependentSuspensionField_grayVectorField hc)
      (contMDiff_apply_reebVectorField_mpullback_prodMk α (timeDeriv α) hc).continuous
      (α.contMDiff.of_le (by simp))
      (mpullback_prodMk_mlieDerivForm_add_mlieDerivForm_grayVectorField hc) s t x

variable (α) in
/-- The **Gray isotopy** of a smooth family of contact forms `α_t` on a compact manifold: the
time-dependent flow `φ_(s,t)` of the Gray vector field from time `s` to time `t`, as a
diffeomorphism. It pulls `α_t` back to a positive multiple of `α_s`
(`TauCeti.SmoothForm.preservesCoorientation_grayIsotopy`). -/
def grayIsotopy (s t : ℝ) : M ≃ₘ⟮I, I⟯ M :=
  timeDependentFlowDiffeomorph (isCompleteVectorField_timeDependentSuspensionField_grayVectorField
    hc) le_top (contMDiff_grayVectorField hc) s t

/-- The Gray isotopy is the time-dependent flow of the Gray vector field. -/
@[simp]
theorem coe_grayIsotopy (s t : ℝ) :
    ⇑(grayIsotopy α hc s t) = timeDependentFlowOf (grayVectorField α) s t :=
  funext <| timeDependentFlowDiffeomorph_apply _ _ _ s t

/-- The Gray isotopy is the time-dependent flow of the Gray vector field. -/
theorem grayIsotopy_apply (s t : ℝ) (x : M) :
    grayIsotopy α hc s t x = timeDependentFlowOf (grayVectorField α) s t x := by
  rw [coe_grayIsotopy]

/-- The inverse of the Gray isotopy from `s` to `t` is the Gray isotopy from `t` to `s`. -/
@[simp]
theorem grayIsotopy_symm_apply (s t : ℝ) (x : M) :
    (grayIsotopy α hc s t).symm x = grayIsotopy α hc t s x :=
  (timeDependentFlowDiffeomorph_symm_apply _ _ _ s t x).trans (grayIsotopy_apply hc t s x).symm

/-- The Gray isotopy from a time to itself is the identity. -/
@[simp]
theorem grayIsotopy_self_apply (s : ℝ) (x : M) : grayIsotopy α hc s s x = x :=
  (grayIsotopy_apply hc s s x).trans <|
    timeDependentFlowOf_self ((contMDiff_grayVectorField hc).of_le (by simp)) s x

/-- Composition law of the Gray isotopy: flowing from `r` to `s` and then from `s` to `t` is
flowing from `r` to `t`. -/
theorem grayIsotopy_grayIsotopy (r s t : ℝ) (x : M) :
    grayIsotopy α hc s t (grayIsotopy α hc r s x) = grayIsotopy α hc r t x := by
  simp only [grayIsotopy_apply]
  exact timeDependentFlowOf_trans
    (isCompleteVectorField_timeDependentSuspensionField_grayVectorField hc)
    ((contMDiff_grayVectorField hc).of_le (by simp)) r s t x

/-- The Gray isotopy is jointly smooth in both times and the point. -/
theorem contMDiff_grayIsotopy :
    ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
      (fun p : (ℝ × ℝ) × M ↦ grayIsotopy α hc p.1.1 p.1.2 p.2) := by
  simp only [grayIsotopy_apply]
  exact contMDiff_timeDependentFlowOf
    (isCompleteVectorField_timeDependentSuspensionField_grayVectorField hc) le_top
    (contMDiff_grayVectorField hc)

/-- **Gray stability.** On a compact manifold, the Gray isotopy `φ_(s,t)` of a smooth family of
contact forms pulls `α_t` back to a positive multiple of `α_s` at every point; in particular it
carries the contact structure `ker α_s` with its coorientation onto `ker α_t`. -/
theorem preservesCoorientation_grayIsotopy (s t : ℝ) :
    (grayIsotopy α hc s t).PreservesCoorientation
      (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α)
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α) :=
  Diffeomorph.preservesCoorientation_def.2 fun x ↦ ⟨_, Real.exp_pos _, by
    simpa only [coe_mpullback, coe_grayIsotopy] using
      mpullback_timeDependentFlowOf_grayVectorField_apply hc s t x⟩

/-- **Gray stability**, for contact structures: on a compact manifold the Gray isotopy `φ_(s,t)`
of a smooth family of contact forms carries the contact structure `ker α_s` onto `ker α_t`. -/
theorem isContactomorphism_grayIsotopy (s t : ℝ) :
    (grayIsotopy α hc s t).IsContactomorphism
      (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α)
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α) :=
  (preservesCoorientation_grayIsotopy hc s t).isContactomorphism

/-- **Relative Gray stability.** If the contact hyperplanes `ker α_u` at `x` agree for all times
`u`, then the Gray isotopy fixes `x`. In particular, it fixes pointwise every set on which the
contact structures `ker α_u` all agree. -/
theorem grayIsotopy_apply_eq_self_of_kerDistribution_eq {x : M}
    (hx : ∀ u, (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x =
      (mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x)
    (s t : ℝ) : grayIsotopy α hc s t x = x :=
  (grayIsotopy_apply hc s t x).trans <| timeDependentFlowOf_eq_self_of_forall_eq_zero
    ((contMDiff_grayVectorField hc).of_le (by simp))
    (fun u ↦ grayVectorField_eq_zero_of_kerDistribution_eq hc fun v ↦ (hx v).trans (hx u).symm)
    s t

end Contact

end TauCeti.SmoothForm
