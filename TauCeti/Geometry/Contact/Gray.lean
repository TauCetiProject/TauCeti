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
# Gray stability for families of contact forms

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

Without compactness the flow need not be defined for all times, but its domain is open, and on it
the same computation applies. The time map from `s` to `t` is then a smooth partial
diffeomorphism `TauCeti.SmoothForm.grayPartialDiffeomorph`, defined on the open set of points
whose trajectory exists from time `s` up to time `t`, with inverse the flow back from `t` to `s`.
It rescales the forms by `exp (∫ₛᵗ μ_u ∘ φ_{s,u} du)` on its source
(`TauCeti.SmoothForm.mpullback_grayPartialDiffeomorph_apply`). At a point where the contact
hyperplane does not move, the Gray vector field vanishes at all times, so the constant trajectory
is defined for all times. Hence the source and the target contain every such point, and the
partial isotopy fixes it. This is **relative Gray stability**: if the contact hyperplanes of the
family agree along a set `K` of points, a partial contactomorphism from `ker α_s` to `ker α_t`
fixing `K` is defined on an open neighbourhood of `K`
(`TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_smul`). Neither `K` nor `M` need be
compact. A compact set of times admits one open neighbourhood of `K` on which all time maps
are defined and rescale the forms
(`TauCeti.SmoothForm.exists_isOpen_superset_forall_mpullback_eq_smul`).

## Main definitions

* `TauCeti.SmoothForm.grayVectorField`: the Gray vector field of a family of one-forms.
* `TauCeti.SmoothForm.grayPartialDiffeomorph`: its time-dependent flow from time `s` to time `t`,
  as a partial diffeomorphism.
* `TauCeti.SmoothForm.grayDiffeomorph`: on a compact manifold, its time-dependent flow from time
  `s` to time `t`, as a diffeomorphism.

## Main results

* `TauCeti.SmoothForm.eq_grayVectorField_iff`: the Gray vector field is characterized by the
  horizontal contact-Moser equation.
* `TauCeti.SmoothForm.mlieDerivForm_grayVectorField_add`: Gray's equation.
* `TauCeti.SmoothForm.contMDiff_grayVectorField`: the Gray vector field is jointly smooth.
* `TauCeti.SmoothForm.grayVectorField_eq_zero`: the Gray vector field vanishes at points where the
  contact hyperplane is stationary.
* `TauCeti.SmoothForm.mpullback_grayPartialDiffeomorph_apply`: Gray's stability theorem on the
  domain of the flow, `φ_{s,t}^* α_t = exp (∫ₛᵗ μ_u ∘ φ_{s,u} du) α_s`.
* `TauCeti.SmoothForm.mem_grayPartialDiffeomorph_source`,
  `TauCeti.SmoothForm.mem_grayPartialDiffeomorph_target`,
  `TauCeti.SmoothForm.grayPartialDiffeomorph_apply_eq_self`: the partial isotopy is defined at, and
  fixes, the points at which the contact hyperplane is stationary.
* `TauCeti.SmoothForm.exists_partialDiffeomorph_mpullback_eq_smul`: relative Gray stability near
  a set of points with stationary contact hyperplanes.
* `TauCeti.SmoothForm.exists_isOpen_superset_forall_mpullback_eq_smul`: one open neighbourhood
  of the stationary set on which the Gray flow rescales the forms for every time of a compact set.
* `TauCeti.SmoothForm.mpullback_grayDiffeomorph_apply`: Gray's stability theorem on a compact
  manifold, in the explicit form `φ_{s,t}^* α_t = exp (∫ₛᵗ μ_u ∘ φ_{s,u} du) α_s`.
* `TauCeti.SmoothForm.preservesCoorientation_grayDiffeomorph`,
  `TauCeti.SmoothForm.isContactomorphism_grayDiffeomorph`: the flow maps are
  coorientation-preserving contactomorphisms.
* `TauCeti.SmoothForm.contMDiff_grayDiffeomorph`: they form a smooth isotopy, jointly smooth in
  both times and the point.
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

section Slice

variable {t : ℝ}
  (hc : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
include hc

/-- The Gray vector field is horizontal: `α_t(Y_t) = 0` whenever the slice `α_t` is a contact
form. -/
theorem apply_grayVectorField (x : M) :
    (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x
      ![α.grayVectorField t x] = 0 :=
  hc.apply_contactMoserVectorField _ x

/-- **The Gray vector field is characterized by the horizontal contact-Moser equation**: if the
slice `α_t` is a contact form, a tangent vector is the value of the Gray vector field at time `t`
exactly when it lies in `ker α_t` and `(ι_v dα_t + ∂_t α_t)|ker α_t = 0`. -/
theorem eq_grayVectorField_iff {x : M} {v : TangentSpace I x} :
    v = α.grayVectorField t x ↔
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x ![v] = 0 ∧
        ∀ w ∈ (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x,
          mextDeriv (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x ![v, w] +
            (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).1 x ![w] =
              0 :=
  hc.eq_contactMoserVectorField_iff

/-- **Gray's equation**: if the slice `α_t` is a contact form, then
`L_{Y_t} α_t + ∂_t α_t = μ_t α_t`, where `μ_t = (∂_t α_t)(R_{α_t})` is the Gray rate, evaluated on
a tangent vector. -/
theorem mlieDerivForm_grayVectorField_add (x : M) (v : TangentSpace I x) :
    mlieDerivForm (α.grayVectorField t)
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x ![v] +
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).1 x ![v] =
        α.grayRate (t, x) *
          (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x ![v] :=
  hc.mlieDerivForm_contactMoserVectorField_add _ x v

/-- **The Gray vector field vanishes where the contact hyperplane is stationary.** If the slice
`α_t` is a contact form and the hyperplane `ker α_u` at `x` is the same for all times `u`, then
`Y_t(x) = 0`: the velocity `∂_t α_t` annihilates the hyperplane at `x`, which the contact-Moser
field then ignores. -/
theorem grayVectorField_eq_zero [I.Boundaryless] {x : M}
    (hx : ∀ u, (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x =
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x) :
    α.grayVectorField t x = 0 := by
  rw [grayVectorField_def, hc.contactMoserVectorField_eq_zero_iff]
  intro w hw
  -- The vector `w` stays in the hyperplane at all times, so `u ↦ α_u(w)` vanishes identically,
  -- and its derivative `(∂_t α_t)(w)` is zero.
  have hzero (u : ℝ) :
      (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).1 x ![w] = 0 :=
    mem_kerDistribution.1 (by rw [hx u]; exact hw)
  have hd := (ContinuousAlternatingMap.apply ℝ E ℝ ![w]).hasFDerivAt.comp_hasDerivAt t
    (α.hasDerivAt_mpullback_prodMk_timeDeriv t x)
  have hfun : (⇑(ContinuousAlternatingMap.apply ℝ E ℝ ![w]) ∘ fun u ↦
      (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).1 x) = fun _ ↦ 0 :=
    funext fun u ↦ ContinuousAlternatingMap.apply_apply.trans (hzero u)
  rw [hfun] at hd
  -- `ContinuousAlternatingMap.apply_apply` evaluates the left side, read in the fibre
  -- `Trivial M ℝ x`, which is `ℝ`.
  exact hd.unique (hasDerivAt_const t (0 : ℝ))

end Slice

variable (hc : ∀ t, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
include hc

/-- The Gray vector field of a smooth family of contact forms depends smoothly on time and point:
`(t, x) ↦ (x, Y_t(x))` is smooth into the tangent bundle. -/
theorem contMDiff_grayVectorField :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, α.grayVectorField p.1 p.2⟩ : TangentBundle I M)) :=
  contMDiff_contactMoserVectorField_mpullback_prodMk α α.timeDeriv hc

/-- The Gray rate `μ_t = (∂_t α_t)(R_{α_t})` of a smooth family of contact forms depends smoothly
on time and point. -/
theorem contMDiff_grayRate : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞ α.grayRate :=
  contMDiff_apply_reebVectorField_mpullback_prodMk α α.timeDeriv hc

/-- The Gray vector field of a smooth family of contact forms vanishes at every time at a point
where the contact hyperplane `ker α_u` is the same for all times `u`. -/
theorem grayVectorField_eq_zero_of_kerDistribution_eq [I.Boundaryless] {x : M} {t₀ : ℝ}
    (hx : ∀ u, (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x =
      (mpullback (Prod.mk t₀) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x)
    (u : ℝ) : α.grayVectorField u x = 0 :=
  grayVectorField_eq_zero (hc u) fun v ↦ (hx v).trans (hx u).symm

/-- **Gray's equation** as an identity of forms on `M` at time `t`: the rate
`ι_t^* L_{∂_t} α + L_{Y_t} α_t` of the family `α_t` along the Gray vector field is `μ_t α_t`. This
is the hypothesis of Moser's principle for families of forms, which turns it into the rescaling of
the slices by the flow of the Gray vector field. -/
private theorem mpullback_prodMk_mlieDerivForm_add_mlieDerivForm_grayVectorField (t : ℝ) :
    TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) α.1) +
      mlieDerivForm (α.grayVectorField t) (TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α.1) =
    fun y ↦ α.grayRate (t, y) • TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) α.1 y := by
  funext y
  ext v
  have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
  have h := mlieDerivForm_grayVectorField_add (hc t) y (v 0)
  rw [hv]
  simp only [coe_mpullback, coe_timeDeriv, Pi.add_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h ⊢
  rw [add_comm, h]

/-! ### Relative Gray stability -/

section Relative

variable [I.Boundaryless] [T2Space M]

/-- **Gray's partial isotopy.** The time-dependent flow of the Gray vector field of a smooth
family of contact forms, from time `s` to time `t`, as a smooth partial diffeomorphism of `M`. Its
source is the open set of points from which the flow is defined from time `s` up to time `t`, and
its inverse is the flow from `t` back to `s`. It contains every point at which the contact
hyperplane does not move (`TauCeti.SmoothForm.mem_grayPartialDiffeomorph_source`), and it pulls
`α_t` back to a positive multiple of `α_s` on its source
(`TauCeti.SmoothForm.mpullback_grayPartialDiffeomorph_apply`). No compactness is needed. -/
def grayPartialDiffeomorph (s t : ℝ) : PartialDiffeomorph I I M M ∞ :=
  timeDependentFlowPartialDiffeomorph le_top (contMDiff_grayVectorField hc) s t

/-- Gray's partial isotopy is the time-dependent flow of the Gray vector field. -/
@[simp]
theorem grayPartialDiffeomorph_apply (s t : ℝ) (x : M) :
    grayPartialDiffeomorph hc s t x = timeDependentFlowOf α.grayVectorField s t x :=
  timeDependentFlowPartialDiffeomorph_apply _ _ s t x

/-- The coercion of Gray's partial isotopy is the time-dependent flow of the Gray vector field. -/
theorem coe_grayPartialDiffeomorph (s t : ℝ) :
    ⇑(grayPartialDiffeomorph hc s t) = timeDependentFlowOf α.grayVectorField s t :=
  funext (grayPartialDiffeomorph_apply hc s t)

/-- The inverse of Gray's partial isotopy from `s` to `t` is the time-dependent flow of the Gray
vector field from `t` to `s`. -/
@[simp]
theorem grayPartialDiffeomorph_symm_apply (s t : ℝ) (x : M) :
    (grayPartialDiffeomorph hc s t).toPartialEquiv.symm x =
      timeDependentFlowOf α.grayVectorField t s x :=
  timeDependentFlowPartialDiffeomorph_symm_apply _ _ s t x

/-- A point lies in the source of Gray's partial isotopy from `s` to `t` exactly when the flow of
the Gray vector field from `(s, x)` is defined up to time `t`. -/
@[simp]
theorem mem_grayPartialDiffeomorph_source_iff {s t : ℝ} {x : M} :
    x ∈ (grayPartialDiffeomorph hc s t).source ↔
      ((s, t), x) ∈ timeDependentFlowDomain α.grayVectorField :=
  mem_timeDependentFlowPartialDiffeomorph_source_iff _ _

/-- A point lies in the target of Gray's partial isotopy from `s` to `t` exactly when the flow of
the Gray vector field from `(t, x)` is defined back to time `s`. -/
@[simp]
theorem mem_grayPartialDiffeomorph_target_iff {s t : ℝ} {x : M} :
    x ∈ (grayPartialDiffeomorph hc s t).target ↔
      ((t, s), x) ∈ timeDependentFlowDomain α.grayVectorField :=
  mem_timeDependentFlowPartialDiffeomorph_target_iff _ _

/-- Gray's partial isotopy depends smoothly on the final time and the point, on the open set of
pairs `(t, x)` for which the flow from `(s, x)` is defined up to time `t`. -/
theorem contMDiffOn_grayPartialDiffeomorph (s : ℝ) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ grayPartialDiffeomorph hc s p.1 p.2)
      {p | ((s, p.1), p.2) ∈ timeDependentFlowDomain α.grayVectorField} := by
  simp only [grayPartialDiffeomorph_apply]
  exact (contMDiffOn_timeDependentFlowOf le_top (contMDiff_grayVectorField hc)).comp
    (((contMDiff_const (c := s)).prodMk contMDiff_fst).prodMk contMDiff_snd).contMDiffOn
    fun _ hp ↦ hp

/-- **Gray's stability theorem along the domain of the flow.** On the source of Gray's partial
isotopy `φ_{s,t}`, the flow of the Gray vector field of a smooth family of contact forms `α_t`
rescales the forms: `φ_{s,t}^* α_t = exp (∫ₛᵗ μ_u ∘ φ_{s,u} du) α_s`, where
`μ_u = (∂_t α_u)(R_{α_u})`. -/
theorem mpullback_grayPartialDiffeomorph_apply {s t : ℝ} {x : M}
    (hx : x ∈ (grayPartialDiffeomorph hc s t).source) :
    TauCeti.mpullback I I (grayPartialDiffeomorph hc s t)
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x =
      Real.exp (∫ u in s..t, α.grayRate (u, grayPartialDiffeomorph hc s u x)) •
        (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).1 x := by
  have h := mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_mem
    ((contMDiff_grayVectorField hc).of_le (by simp)) (contMDiff_grayRate hc).continuous
    (α.contMDiff.of_le (by simp))
    (mpullback_prodMk_mlieDerivForm_add_mlieDerivForm_grayVectorField hc)
    ((mem_grayPartialDiffeomorph_source_iff hc).1 hx)
  simpa only [coe_mpullback, coe_grayPartialDiffeomorph] using h

/-- A point at which the contact hyperplane `ker α_t` is the same for all times lies in the source
of Gray's partial isotopy between any two times: the Gray vector field vanishes there, so the
constant trajectory is defined for all times. -/
theorem mem_grayPartialDiffeomorph_source {x : M}
    (hx : ∀ u, (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x =
      (mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x)
    (s t : ℝ) : x ∈ (grayPartialDiffeomorph hc s t).source :=
  (mem_grayPartialDiffeomorph_source_iff hc).2
    (mem_timeDependentFlowDomain_of_forall_eq_zero
      (grayVectorField_eq_zero_of_kerDistribution_eq hc hx) s t)

/-- A point at which the contact hyperplane `ker α_t` is the same for all times lies in the target
of Gray's partial isotopy between any two times. -/
theorem mem_grayPartialDiffeomorph_target {x : M}
    (hx : ∀ u, (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x =
      (mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x)
    (s t : ℝ) : x ∈ (grayPartialDiffeomorph hc s t).target :=
  (mem_grayPartialDiffeomorph_target_iff hc).2
    (mem_timeDependentFlowDomain_of_forall_eq_zero
      (grayVectorField_eq_zero_of_kerDistribution_eq hc hx) t s)

/-- Gray's partial isotopy fixes every point at which the contact hyperplane `ker α_t` is the same
for all times. -/
theorem grayPartialDiffeomorph_apply_eq_self {x : M}
    (hx : ∀ u, (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x =
      (mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x)
    (s t : ℝ) : grayPartialDiffeomorph hc s t x = x := by
  rw [grayPartialDiffeomorph_apply]
  exact timeDependentFlowOf_eq_self_of_forall_eq_zero
    ((contMDiff_grayVectorField hc).of_le (by simp))
    (grayVectorField_eq_zero_of_kerDistribution_eq hc hx) s t

/-- **Relative Gray stability.** Let `α_t` be a smooth family of contact forms on a boundaryless
manifold, and let `K` be a set of points at each of which the contact hyperplane `ker α_t` is the
same for all times. Then for all times `s` and `t` there is a smooth partial diffeomorphism `φ` of
`M`, whose source and target are open neighbourhoods of `K`, which fixes every point of `K` and
pulls `α_t` back to a positive multiple of `α_s` on its source. It is Gray's partial isotopy
`TauCeti.SmoothForm.grayPartialDiffeomorph`. Neither `K` nor `M` need be compact, and `K` need not
be closed. -/
theorem exists_partialDiffeomorph_mpullback_eq_smul {K : Set M}
    (hK : ∀ x ∈ K, ∀ u,
      (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x =
        (mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x)
    (s t : ℝ) :
    ∃ φ : PartialDiffeomorph I I M M ∞, K ⊆ φ.source ∧ K ⊆ φ.target ∧ (∀ x ∈ K, φ x = x) ∧
      ∀ x ∈ φ.source, ∃ g : ℝ, 0 < g ∧
        TauCeti.mpullback I I φ
            (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x =
          g • (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).1 x :=
  ⟨grayPartialDiffeomorph hc s t, fun x hx ↦ mem_grayPartialDiffeomorph_source hc (hK x hx) s t,
    fun x hx ↦ mem_grayPartialDiffeomorph_target hc (hK x hx) s t,
    fun x hx ↦ grayPartialDiffeomorph_apply_eq_self hc (hK x hx) s t,
    fun _ hx ↦ ⟨_, Real.exp_pos _, mpullback_grayPartialDiffeomorph_apply hc hx⟩⟩

/-- **Relative Gray stability.** Let `α_t` be a smooth family of contact forms on a manifold without
boundary, not necessarily compact, and let `K` be a set of points at which the contact hyperplane
`ker α_t` is the same for all times. For an initial time `s` and a compact set of times `T`, such as
`[0, 1]`, there is an open neighbourhood `V` of `K` on which the Gray flow `φ_{s,t}` is defined for
every `t ∈ T` and pulls `α_t` back to a positive multiple of `α_s`. The flow fixes every point of
`K` (`TauCeti.SmoothForm.grayPartialDiffeomorph_apply_eq_self`), so this is an isotopy of
germs of coorientation-preserving contactomorphisms along `K`, from `ker α_s` to `ker α_t`. -/
theorem exists_isOpen_superset_forall_mpullback_eq_smul {K : Set M}
    (hK : ∀ x ∈ K, ∀ u,
      (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x =
        (mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x)
    {T : Set ℝ} (hT : IsCompact T) (s : ℝ) :
    ∃ V : Set M, IsOpen V ∧ K ⊆ V ∧ ∀ t ∈ T, ∀ x ∈ V,
      ((s, t), x) ∈ timeDependentFlowDomain α.grayVectorField ∧ ∃ c : ℝ, 0 < c ∧
        TauCeti.mpullback I I (timeDependentFlowOf α.grayVectorField s t)
            (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x =
          c • (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).1 x := by
  refine ⟨_, isOpen_setOf_forall_mem_timeDependentFlowDomain
      ((contMDiff_grayVectorField hc).of_le (by simp)) hT s, ?_, ?_⟩
  · intro x hx t _
    exact (mem_grayPartialDiffeomorph_source_iff hc).1
      (mem_grayPartialDiffeomorph_source hc (hK x hx) s t)
  · intro t ht x hx
    refine ⟨hx t ht,
      Real.exp (∫ u in s..t, α.grayRate (u, timeDependentFlowOf α.grayVectorField s u x)),
      Real.exp_pos _, ?_⟩
    simpa only [coe_grayPartialDiffeomorph] using mpullback_grayPartialDiffeomorph_apply hc
      ((mem_grayPartialDiffeomorph_source_iff hc).2 (hx t ht))

end Relative

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
  rw [grayDiffeomorph_apply, timeDependentFlowOf_self]

/-- Gray's isotopy composes: flowing from `r` to `s` and then from `s` to `t` is flowing from `r`
to `t`. -/
@[simp]
theorem grayDiffeomorph_grayDiffeomorph (r s t : ℝ) (x : M) :
    grayDiffeomorph hc s t (grayDiffeomorph hc r s x) = grayDiffeomorph hc r t x := by
  simp only [grayDiffeomorph_apply]
  exact timeDependentFlowOf_trans
    (isCompleteVectorField_timeDependentSuspensionField_grayVectorField hc)
    ((contMDiff_grayVectorField hc).of_le (by simp)) r s t x

/-- Gray's isotopy depends smoothly on the initial time, the final time and the point. -/
theorem contMDiff_grayDiffeomorph :
    ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
      (fun p : (ℝ × ℝ) × M ↦ grayDiffeomorph hc p.1.1 p.1.2 p.2) := by
  simp only [grayDiffeomorph_apply]
  exact contMDiff_timeDependentFlowOf
    (isCompleteVectorField_timeDependentSuspensionField_grayVectorField hc) le_top
    (contMDiff_grayVectorField hc)

/-- **Gray's stability theorem.** On a compact manifold without boundary, the time-dependent flow
`φ_{s,t}` of the Gray vector field of a smooth family of contact forms `α_t` rescales the forms:
`φ_{s,t}^* α_t = exp (∫ₛᵗ μ_u ∘ φ_{s,u} du) α_s`, where `μ_u = (∂_t α_u)(R_{α_u})`. -/
theorem mpullback_grayDiffeomorph_apply (s t : ℝ) (x : M) :
    (mpullback (grayDiffeomorph hc s t) (grayDiffeomorph hc s t).contMDiff
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α)).1 x =
      Real.exp (∫ u in s..t, α.grayRate (u, grayDiffeomorph hc s u x)) •
        (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).1 x := by
  have h := mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul
    ((contMDiff_grayVectorField hc).of_le (by simp))
    (isCompleteVectorField_timeDependentSuspensionField_grayVectorField hc)
    (contMDiff_grayRate hc).continuous (α.contMDiff.of_le (by simp))
    (mpullback_prodMk_mlieDerivForm_add_mlieDerivForm_grayVectorField hc) s t x
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
    ((contMDiff_grayVectorField hc).of_le (by simp))
    (grayVectorField_eq_zero_of_kerDistribution_eq hc hx) s t

end TauCeti.SmoothForm
