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

On any manifold without boundary, compact or not, the time-dependent flow `φ_{s,t}` of the Gray
vector field rescales the forms wherever it is defined:
`(φ_{s,t}^* α_t)ₓ = exp (∫ₛᵗ μ_u (φ_{s,u} x) du) (α_s)ₓ`
(`TauCeti.SmoothForm.mpullback_timeDependentFlowOf_grayVectorField_apply`). At a point where the
contact hyperplane `ker α_t` does not move with `t`, the Gray vector field vanishes, so the flow
is defined for all times and fixes the point. Since the domain of the flow is open, this gives
**relative Gray stability**: if the hyperplanes are stationary at every point of a set `K`, the
Gray flow from time `s` to time `t` is a partial diffeomorphism between open neighbourhoods of `K`
which fixes `K` and pulls `α_t` back to a positive multiple of `α_s` at every point of its source
(`TauCeti.SmoothForm.exists_partialDiffeomorph_fix_mpullback_eq_smul`), so it carries `ker α_s` to
`ker α_t` with their coorientations. For a compact set of times, such as `[0, 1]`, these flows are
all defined on one open neighbourhood of `K`
(`TauCeti.SmoothForm.exists_isOpen_superset_forall_mpullback_eq_smul`). No compactness of `M` or
of `K` is needed.

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
* `TauCeti.SmoothForm.mpullback_timeDependentFlowOf_grayVectorField_apply`: Gray's stability
  theorem along the local flow, on a possibly noncompact manifold.
* `TauCeti.SmoothForm.mem_timeDependentFlowDomain_grayVectorField`,
  `TauCeti.SmoothForm.timeDependentFlowOf_grayVectorField_eq_self`: the flow is defined for all
  times at, and fixes, the points where the contact hyperplane is stationary.
* `TauCeti.SmoothForm.exists_partialDiffeomorph_fix_mpullback_eq_smul`,
  `TauCeti.SmoothForm.exists_isOpen_superset_forall_mpullback_eq_smul`: relative Gray stability
  along a set of points where the contact hyperplane is stationary.
* `TauCeti.SmoothForm.mpullback_grayDiffeomorph_apply`: Gray's stability theorem, in the explicit
  form `φ_{s,t}^* α_t = exp (∫ₛᵗ μ_u ∘ φ_{s,u} du) α_s`.
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

/-- Gray's equation for the slices, in the shape consumed by Moser's principle for families of
forms: `ι_t^* L_{∂_t} α + L_{Y_t} α_t = μ_t α_t`. -/
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

/-! ### Gray's stability theorem along the local flow -/

variable [I.Boundaryless]

/-- The Gray flow is defined for all times at every point at which the contact hyperplane
`ker α_t` is the same for all times. -/
theorem mem_timeDependentFlowDomain_grayVectorField {x : M}
    (hx : ∀ u, (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x =
      (mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x)
    (s t : ℝ) : ((s, t), x) ∈ timeDependentFlowDomain α.grayVectorField :=
  mem_timeDependentFlowDomain_of_forall_eq_zero
    (fun u ↦ grayVectorField_eq_zero (hc u) fun v ↦ (hx v).trans (hx u).symm) s t

variable [T2Space M]

/-- **Gray's stability theorem along the local flow.** On a manifold without boundary, not
necessarily compact, the time-dependent flow `φ_{s,t}` of the Gray vector field of a smooth family
of contact forms `α_t` rescales the forms wherever it is defined: if the flow from `(s, x)` is
defined up to time `t`, then `(φ_{s,t}^* α_t)ₓ = exp (∫ₛᵗ μ_u (φ_{s,u} x) du) (α_s)ₓ`, where
`μ_u = (∂_t α_u)(R_{α_u})`. -/
theorem mpullback_timeDependentFlowOf_grayVectorField_apply {s t : ℝ} {x : M}
    (h : ((s, t), x) ∈ timeDependentFlowDomain α.grayVectorField) :
    TauCeti.mpullback I I (timeDependentFlowOf α.grayVectorField s t)
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x =
      Real.exp (∫ u in s..t, α.grayRate (u, timeDependentFlowOf α.grayVectorField s u x)) •
        (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).1 x := by
  simpa only [coe_mpullback] using
    mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul
      ((contMDiff_grayVectorField hc).of_le (by simp)) (contMDiff_grayRate hc).continuous
      (α.contMDiff.of_le (by simp))
      (mpullback_prodMk_mlieDerivForm_add_mlieDerivForm_grayVectorField hc) h

/-- The Gray flow fixes every point at which the contact hyperplane `ker α_t` is the same for all
times. -/
theorem timeDependentFlowOf_grayVectorField_eq_self {x : M}
    (hx : ∀ u, (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x =
      (mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x)
    (s t : ℝ) : timeDependentFlowOf α.grayVectorField s t x = x :=
  timeDependentFlowOf_eq_self_of_forall_eq_zero ((contMDiff_grayVectorField hc).of_le (by simp))
    (fun u ↦ grayVectorField_eq_zero (hc u) fun v ↦ (hx v).trans (hx u).symm) s t

/-- **Relative Gray stability**, at a single time. Let `α_t` be a smooth family of contact forms
on a manifold without boundary, not necessarily compact, and let `K` be a set of points at which
the contact hyperplane `ker α_t` is the same for all times. For all times `s` and `t`, there is a
smooth partial diffeomorphism `φ` whose source and target are open neighbourhoods of `K`, which
fixes every point of `K`, and which pulls `α_t` back to a positive multiple of `α_s` at every point
of its source. It is the Gray flow from time `s` to time `t`, with inverse the Gray flow back. -/
theorem exists_partialDiffeomorph_fix_mpullback_eq_smul {K : Set M}
    (hK : ∀ x ∈ K, ∀ u,
      (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x =
        (mpullback (Prod.mk 0) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x)
    (s t : ℝ) :
    ∃ φ : PartialDiffeomorph I I M M ∞, K ⊆ φ.source ∧ K ⊆ φ.target ∧ (∀ x ∈ K, φ x = x) ∧
      ∀ x ∈ φ.source, ∃ c : ℝ, 0 < c ∧
        TauCeti.mpullback I I φ
            (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x =
          c • (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).1 x := by
  refine ⟨timeDependentFlowPartialDiffeomorph le_top (contMDiff_grayVectorField hc) s t,
    fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rw [timeDependentFlowPartialDiffeomorph_source]
    exact mem_timeDependentFlowDomain_grayVectorField hc (hK x hx) s t
  · rw [timeDependentFlowPartialDiffeomorph_target]
    exact mem_timeDependentFlowDomain_grayVectorField hc (hK x hx) t s
  · rw [coe_timeDependentFlowPartialDiffeomorph]
    exact timeDependentFlowOf_grayVectorField_eq_self hc (hK x hx) s t
  · rw [timeDependentFlowPartialDiffeomorph_source] at hx
    rw [coe_timeDependentFlowPartialDiffeomorph]
    exact ⟨_, Real.exp_pos _, mpullback_timeDependentFlowOf_grayVectorField_apply hc hx⟩

/-- **Relative Gray stability.** Let `α_t` be a smooth family of contact forms on a manifold without
boundary, not necessarily compact, and let `K` be a set of points at which the contact hyperplane
`ker α_t` is the same for all times. For an initial time `s` and a compact set of times `T`, such as
`[0, 1]`, there is an open neighbourhood `V` of `K` on which the Gray flow `φ_{s,t}` is defined for
every `t ∈ T` and pulls `α_t` back to a positive multiple of `α_s`. The flow fixes every point of
`K` (`TauCeti.SmoothForm.timeDependentFlowOf_grayVectorField_eq_self`), so this is an isotopy of
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
          c • (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).1 x :=
  ⟨_, isOpen_setOf_forall_mem_timeDependentFlowDomain
      ((contMDiff_grayVectorField hc).of_le (by simp)) hT s,
    fun x hx t _ ↦ mem_timeDependentFlowDomain_grayVectorField hc (hK x hx) s t,
    fun t ht _ hx ↦ ⟨hx t ht, _, Real.exp_pos _,
      mpullback_timeDependentFlowOf_grayVectorField_apply hc (hx t ht)⟩⟩

/-! ### Gray's stability theorem on compact manifolds -/

variable [CompactSpace M]

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
  have hφ : ⇑(grayDiffeomorph hc s t) = timeDependentFlowOf α.grayVectorField s t :=
    funext (grayDiffeomorph_apply hc s t)
  simpa only [coe_mpullback, grayDiffeomorph_apply, hφ] using
    mpullback_timeDependentFlowOf_grayVectorField_apply hc (mem_timeDependentFlowDomain.2
      ((isCompleteVectorField_timeDependentSuspensionField_grayVectorField hc).mem_flowDomain _ _))

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
  exact timeDependentFlowOf_grayVectorField_eq_self hc hx s t

end TauCeti.SmoothForm
