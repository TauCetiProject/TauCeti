/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Distribution
public import TauCeti.Geometry.Contact.Gray.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Proportional

/-!
# The Gray vector field of a family of contact structures

Let `ξ_t`, `t ∈ ℝ`, be a smooth family of contact structures on a manifold `M`. A contact
structure need not be the kernel of a global one-form, and need not be cooriented, so the family
is described by local data: near every `(t, x)` there is a smooth one-form `α` on `ℝ × M` whose
slices `α_s = ι_s^* α` define the hyperplanes, `ker α_s = ξ_s`, near `(t, x)`
(`TauCeti.SmoothForm.IsLocalDefiningForm`). This is `TauCeti.IsContactDistributionFamily I ξ`.

For one such local defining form, the Gray vector field of `α`
(`TauCeti.SmoothForm.grayVectorField`) is at time `t` the unique `Y ∈ ξ_t` with
`(ι_Y dα_t + ∂_t α_t)|ξ_t = 0`. Two local defining forms differ near `(t, x)` by a nowhere-zero
multiplier, `β_s = f_s α_s`, of either sign. Then on `ξ_t`
the exterior derivatives are related by `dβ_t = f_t dα_t`, and the velocities by
`∂_t β_t = f_t ∂_t α_t`, since `α_t` vanishes there. So both forms give the same vector
(`TauCeti.SmoothForm.IsLocalDefiningForm.grayVectorField_eq`). The comparison of exterior
derivatives goes through the Levi form of `ξ_t`, which both forms carry to their exterior
derivatives (`TauCeti.RoughForm.apply_eq_mextDeriv_of_mkQ_eq_distributionLeviForm`).

The local Gray vector fields therefore glue to the **Gray vector field of the family**
`TauCeti.distributionGrayVectorField ξ`, defined without any global contact form or orientation of
the contact line. It is characterized at each point by the Gray equations of any local defining
form (`TauCeti.SmoothForm.IsLocalDefiningForm.eq_distributionGrayVectorField_iff`), lies in the
contact hyperplanes (`TauCeti.IsContactDistributionFamily.distributionGrayVectorField_mem`), and
depends smoothly on time and point
(`TauCeti.IsContactDistributionFamily.contMDiff_distributionGrayVectorField`). It vanishes at a
point whose hyperplane does not move
(`TauCeti.IsContactDistributionFamily.distributionGrayVectorField_eq_zero`). For the kernels of a
family of contact forms it is the Gray vector field of that family
(`TauCeti.SmoothForm.distributionGrayVectorField_kerDistribution`).

Integrating this field, its time-dependent flow `φ_{s,t}` is defined on an open set containing
every point whose hyperplane does not move, and fixes those points
(`TauCeti.mem_timeDependentFlowDomain_of_forall_eq_zero`,
`TauCeti.timeDependentFlowOf_eq_self_of_forall_eq_zero`). Gray's stability theorem for contact
structures is the statement that `dφ_{s,t}` carries `ξ_s` onto `ξ_t`; this file does not prove it.

## Main definitions

* `TauCeti.SmoothForm.IsLocalDefiningForm`: a smooth one-form on `ℝ × M` whose slices define a
  family of hyperplane fields near a point.
* `TauCeti.IsContactDistributionFamily`: a smooth family of contact structures.
* `TauCeti.distributionGrayVectorField`: the Gray vector field of a family of contact structures.

## Main results

* `TauCeti.SmoothForm.IsLocalDefiningForm.grayVectorField_eq`: two local defining forms of a
  family of contact structures have the same Gray vector at the point.
* `TauCeti.SmoothForm.IsLocalDefiningForm.grayVectorField_eq_distributionGrayVectorField`: the
  Gray vector field of the family is that of any local defining form.
* `TauCeti.SmoothForm.IsLocalDefiningForm.eq_distributionGrayVectorField_iff`: its
  characterization by the horizontal contact-Moser equation.
* `TauCeti.IsContactDistributionFamily.contMDiff_distributionGrayVectorField`: it is jointly
  smooth.
* `TauCeti.IsContactDistributionFamily.distributionGrayVectorField_eq_zero`: it vanishes where the
  hyperplane is stationary.
* `TauCeti.SmoothForm.distributionGrayVectorField_kerDistribution`: for the kernels of a family
  of contact forms, it is the Gray vector field of the forms.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (Gray stability) and its proof.
* J. W. Gray, *Some global properties of contact structures*, Ann. of Math. 69 (1959), 421–450.
-/

public section

noncomputable section

open Set Filter Bundle
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ξ : ℝ → Π x : M, Submodule ℝ (TangentSpace I x)}

/-! ### Local defining forms of a family of hyperplane fields -/

namespace SmoothForm

/-- A smooth one-form `α` on `ℝ × M` is a **local defining form** of a family `ξ` of hyperplane
fields near `p` when, for all `(t, x)` near `p`, the slice `α_t = ι_t^* α` does not vanish at `x`
and its kernel there is `ξ_t(x)`. -/
def IsLocalDefiningForm (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1)
    (ξ : ℝ → Π x : M, Submodule ℝ (TangentSpace I x)) (p : ℝ × M) : Prop :=
  ∀ᶠ q in 𝓝 p, (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α).1 q.2 ≠ 0 ∧
    (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution q.2 =
      ξ q.1 q.2

variable {α β : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1}

/-- The defining property of a local defining form. -/
theorem isLocalDefiningForm_iff {p : ℝ × M} :
    α.IsLocalDefiningForm ξ p ↔
      ∀ᶠ q in 𝓝 p, (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α).1 q.2 ≠ 0 ∧
        (mpullback (Prod.mk q.1) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution q.2 =
          ξ q.1 q.2 :=
  Iff.rfl

/-- A smooth one-form whose slices vanish nowhere is a local defining form, near every point, of
the family of their kernels. -/
theorem isLocalDefiningForm_kerDistribution
    (hα : ∀ t x, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x ≠ 0)
    (p : ℝ × M) :
    α.IsLocalDefiningForm
      (fun t ↦ (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution) p :=
  .of_forall fun q ↦ ⟨hα q.1 q.2, rfl⟩

namespace IsLocalDefiningForm

/-- A local defining form near `p` is a local defining form near every point close to `p`. -/
theorem eventually {p : ℝ × M} (hα : α.IsLocalDefiningForm ξ p) :
    ∀ᶠ q in 𝓝 p, α.IsLocalDefiningForm ξ q :=
  Filter.Eventually.eventually_nhds hα

variable {t : ℝ} {x : M}

/-- The slice of a local defining form at `(t, x)` does not vanish at `x`. -/
theorem apply_ne_zero (hα : α.IsLocalDefiningForm ξ (t, x)) :
    (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x ≠ 0 :=
  hα.self_of_nhds.1

/-- Near `x`, the slice at time `t` of a local defining form at `(t, x)` has kernels `ξ_t`. -/
theorem eventually_kerDistribution_eq (hα : α.IsLocalDefiningForm ξ (t, x)) :
    ∀ᶠ y in 𝓝 x,
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution y =
        ξ t y :=
  ((continuous_const.prodMk continuous_id).tendsto x).eventually (hα.mono fun _ hq ↦ hq.2)

/-- Near time `t`, the slices of a local defining form at `(t, x)` have kernel `ξ_s(x)` at `x`. -/
theorem eventually_kerDistribution_eq_time (hα : α.IsLocalDefiningForm ξ (t, x)) :
    ∀ᶠ s in 𝓝 t,
      (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x =
        ξ s x :=
  ((continuous_id.prodMk continuous_const).tendsto t).eventually (hα.mono fun _ hq ↦ hq.2)

/-- At `(t, x)`, the slice of a local defining form has kernel `ξ_t(x)`. -/
theorem kerDistribution_eq (hα : α.IsLocalDefiningForm ξ (t, x)) :
    (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x = ξ t x :=
  hα.self_of_nhds.2

/-- **The velocities of two local defining forms are proportional on the hyperplane.** If
`β_s = f_s α_s` at `x` for `s` near `t`, then `∂_t β_t = f_t ∂_t α_t` on `ξ_t(x)`, because
`α_t` vanishes there. -/
private theorem timeDeriv_apply_eq_mul [I.Boundaryless]
    (hα : α.IsLocalDefiningForm ξ (t, x))
    (hβ : β.IsLocalDefiningForm ξ (t, x)) {u w : TangentSpace I x}
    (hu : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x ![u] ≠ 0)
    (hw : w ∈ ξ t x) :
    (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β.timeDeriv).1 x ![w] =
      ((mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).1 x ![u] /
          (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x ![u]) *
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).1 x ![w] := by
  -- Evaluating the slices at `x` on a fixed vector gives differentiable functions of time, with
  -- derivatives the slices of the time derivative. Evaluation is `ContinuousAlternatingMap.apply`.
  have hev (γ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1) (v : TangentSpace I x) :
      HasDerivAt (fun s ↦ (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) γ).1 x ![v])
        ((mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) γ.timeDeriv).1 x ![v]) t :=
    (ContinuousAlternatingMap.apply ℝ E ℝ ![v]).hasFDerivAt.comp_hasDerivAt t
      (γ.hasDerivAt_mpullback_prodMk_timeDeriv t x)
  -- Near `t`, `β_s(w) = (β_s(u) / α_s(u)) α_s(w)`, since both slices have kernel `ξ_s(x)`.
  have heq : ∀ᶠ s in 𝓝 t,
      (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) β).1 x ![w] =
        (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) β).1 x ![u] /
          (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).1 x ![u] *
            (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).1 x ![w] := by
    filter_upwards [(hev α u).continuousAt.eventually_ne hu, hα.eventually_kerDistribution_eq_time,
      hβ.eventually_kerDistribution_eq_time] with s hs hαs hβs
    have hker : RoughForm.ker (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).1 x ≤
        RoughForm.ker (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) β).1 x := by
      rw [← kerDistribution_eq_ker, ← kerDistribution_eq_ker, hαs, hβs]
    refine (congrArg (fun L ↦ L ![w]) (RoughForm.apply_eq_div_smul_of_ker_le hker hs)).trans ?_
    rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  -- Differentiating this identity at `t`; the term with `α_t(w) = 0` drops out.
  have hw' : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x ![w] = 0 :=
    mem_kerDistribution.1 (by rw [hα.kerDistribution_eq]; exact hw)
  have hd := (hev β w).unique ((((hev β u).div (hev α u) hu).mul (hev α w)).congr_of_eventuallyEq
    heq)
  rw [hd, hw', mul_zero, zero_add, Pi.div_apply]

end IsLocalDefiningForm

end SmoothForm

/-! ### Smooth families of contact structures -/

variable [FiniteDimensional ℝ E]

variable (I) in
/-- A **smooth family of contact structures** `ξ_t`, `t ∈ ℝ`, on `M`: every `ξ_t` is a contact
structure, and near every `(t, x)` the family is defined by the slices of a smooth one-form on
`ℝ × M` (`TauCeti.SmoothForm.IsLocalDefiningForm`). No global defining form or coorientation is
part of the data. -/
structure IsContactDistributionFamily (ξ : ℝ → Π x : M, Submodule ℝ (TangentSpace I x)) :
    Prop where
  /-- Near every point of `ℝ × M`, the family is defined by the slices of a smooth one-form. -/
  exists_isLocalDefiningForm (p : ℝ × M) :
    ∃ α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1, α.IsLocalDefiningForm ξ p
  /-- Every member of the family is a contact structure. -/
  isContactDistribution (t : ℝ) : IsContactDistribution I ∞ (ξ t)

/-- **The kernels of a smooth family of contact forms form a smooth family of contact
structures.** -/
theorem SmoothForm.isContactDistributionFamily_kerDistribution
    {α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1}
    (hc : ∀ t, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm) :
    IsContactDistributionFamily I
      (fun t ↦ (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution) :=
  ⟨fun p ↦ ⟨α, isLocalDefiningForm_kerDistribution (fun t ↦ (hc t).apply_ne_zero) p⟩,
    fun t ↦ have : IsManifold I (∞ + 1) M := by simpa using ‹IsManifold I ∞ M›
      (hc t).isContactDistribution_kerDistribution⟩

namespace SmoothForm.IsLocalDefiningForm

variable {α β : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1} {t : ℝ} {x : M}
  (hξ : IsContactDistributionFamily I ξ)
include hξ

/-- The slices of a local defining form of a family of contact structures are contact forms. -/
theorem isContactFormAt (hα : α.IsLocalDefiningForm ξ (t, x)) :
    IsContactFormAt (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x := by
  obtain ⟨V, hV, hxV, X, hX⟩ :=
    isContMDiffDistribution_iff.1 (hξ.isContactDistribution t).isContMDiffDistribution x
  refine (RoughForm.isContactFormAt_iff_bijective_distributionLeviForm (hX.of_le (by simp))
    (hV.mem_nhds hxV) (SmoothForm.mdifferentiableAt _ x)
    (hα.eventually_kerDistribution_eq.mono fun y hy ↦ ?_)).2
      ⟨hα.apply_ne_zero, (hξ.isContactDistribution t).bijective_distributionLeviForm x⟩
  rw [← kerDistribution_eq_ker, hy]

/-- **Two local defining forms of a family of contact structures have proportional exterior
derivatives on the contact hyperplane.** If `β_t = c α_t` at `x`, then `dβ_t = c dα_t` on
`ξ_t(x)`. Both forms carry the Levi form of `ξ_t` to their exterior derivatives. -/
private theorem mextDeriv_eq_mul (hα : α.IsLocalDefiningForm ξ (t, x))
    (hβ : β.IsLocalDefiningForm ξ (t, x)) {c : ℝ}
    (hc : (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).1 x =
      c • (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x)
    {v w : TangentSpace I x} (hv : v ∈ ξ t x) (hw : w ∈ ξ t x) :
    mextDeriv (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β).1 x ![v, w] =
      c * mextDeriv (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x
        ![v, w] := by
  obtain ⟨V, hV, hxV, X, hX⟩ :=
    isContMDiffDistribution_iff.1 (hξ.isContactDistribution t).isContMDiffDistribution x
  obtain ⟨z, hz⟩ := (ξ t x).mkQ_surjective (distributionLeviForm (ξ t) x ⟨v, hv⟩ ⟨w, hw⟩)
  -- A local defining form carries the Levi form of `ξ_t` to its exterior derivative.
  have hLevi {γ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1} (hγ : γ.IsLocalDefiningForm ξ (t, x)) :
      (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) γ).1 x ![z] =
        mextDeriv (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) γ).1 x ![v, w] :=
    RoughForm.apply_eq_mextDeriv_of_mkQ_eq_distributionLeviForm (hX.of_le (by simp))
      (hV.mem_nhds hxV) (SmoothForm.mdifferentiableAt _ x)
      (hγ.eventually_kerDistribution_eq.mono fun y hy ↦ by rw [← kerDistribution_eq_ker, hy]) hz
  rw [← hLevi hα, ← hLevi hβ, hc, ContinuousAlternatingMap.smul_apply, smul_eq_mul]

variable [I.Boundaryless]

/-- **The Gray vector field does not depend on the local defining form.** Two local defining forms
at `(t, x)` of a smooth family of contact structures have the same Gray vector at time `t` and
point `x`. They differ near `(t, x)` by a nowhere-zero multiplier of either sign, which changes
neither the contact hyperplane nor the horizontal contact-Moser equation. -/
theorem grayVectorField_eq (hα : α.IsLocalDefiningForm ξ (t, x))
    (hβ : β.IsLocalDefiningForm ξ (t, x)) : α.grayVectorField t x = β.grayVectorField t x := by
  have hxα := hα.isContactFormAt hξ
  have hxβ := hβ.isContactFormAt hξ
  set a := mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α
  set b := mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) β
  -- Test the multiplier on the Reeb vector of `α_t`, on which `α_t` is one.
  set u := a.reebVectorField x
  have hu : a.1 x ![u] ≠ 0 := by rw [hxα.apply_reebVectorField]; exact one_ne_zero
  set c := b.1 x ![u] / a.1 x ![u]
  have hc : b.1 x = c • a.1 x := by
    refine RoughForm.apply_eq_div_smul_of_ker_le ?_ hu
    rw [← kerDistribution_eq_ker, ← kerDistribution_eq_ker, hα.kerDistribution_eq,
      hβ.kerDistribution_eq]
  have hker : b.kerDistribution x = a.kerDistribution x := by
    rw [hα.kerDistribution_eq, hβ.kerDistribution_eq]
  -- The Gray vector of `α` solves the horizontal contact-Moser equation of `α`.
  have hY := (hxα.eq_contactMoserVectorField_iff (v := α.grayVectorField t x)
    (β := mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv)).1
      (grayVectorField_def α t x)
  have hYξ : α.grayVectorField t x ∈ ξ t x := by
    rw [← hα.kerDistribution_eq, mem_kerDistribution]
    exact hY.1
  rw [grayVectorField_def β, hxβ.eq_contactMoserVectorField_iff]
  refine ⟨mem_kerDistribution.1 (hker ▸ (mem_kerDistribution.2 hY.1)), fun w hw ↦ ?_⟩
  have hwξ : w ∈ ξ t x := by rwa [← hβ.kerDistribution_eq]
  rw [mextDeriv_eq_mul hξ hα hβ hc hYξ hwξ, timeDeriv_apply_eq_mul hα hβ hu hwξ, ← mul_add,
    hY.2 w (hker ▸ hw), mul_zero]

end SmoothForm.IsLocalDefiningForm

/-! ### The Gray vector field of a family of contact structures -/

variable [I.Boundaryless]

/-- The **Gray vector field** of a family `ξ` of contact structures, at time `t` and point `x`: the
Gray vector field (`TauCeti.SmoothForm.grayVectorField`) of a local defining form of `ξ` at
`(t, x)`. For a smooth family of contact structures it does not depend on the choice of local
defining form
(`TauCeti.SmoothForm.IsLocalDefiningForm.grayVectorField_eq_distributionGrayVectorField`), and it
is the unique `Y ∈ ξ_t(x)` with `(ι_Y dα_t + ∂_t α_t)|ξ_t(x) = 0` for any local defining
form `α` (`TauCeti.SmoothForm.IsLocalDefiningForm.eq_distributionGrayVectorField_iff`). -/
def distributionGrayVectorField (ξ : ℝ → Π x : M, Submodule ℝ (TangentSpace I x)) (t : ℝ)
    (x : M) : TangentSpace I x :=
  (Classical.epsilon fun α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1 ↦
    α.IsLocalDefiningForm ξ (t, x)).grayVectorField t x

namespace SmoothForm.IsLocalDefiningForm

variable {α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1} {t : ℝ} {x : M}
  (hξ : IsContactDistributionFamily I ξ)
include hξ

/-- **The Gray vector field of a family of contact structures is that of any local defining
form.** -/
theorem grayVectorField_eq_distributionGrayVectorField (hα : α.IsLocalDefiningForm ξ (t, x)) :
    α.grayVectorField t x = distributionGrayVectorField ξ t x :=
  hα.grayVectorField_eq hξ (Classical.epsilon_spec (p := fun β ↦ β.IsLocalDefiningForm ξ (t, x))
    ⟨α, hα⟩)

/-- **Characterization of the Gray vector field of a family of contact structures**: for a local
defining form `α` at `(t, x)`, the Gray vector at `(t, x)` is the unique `v ∈ ξ_t(x)` with
`dα_t(v, w) + (∂_t α_t)(w) = 0` for all `w ∈ ξ_t(x)`. -/
theorem eq_distributionGrayVectorField_iff (hα : α.IsLocalDefiningForm ξ (t, x))
    {v : TangentSpace I x} :
    v = distributionGrayVectorField ξ t x ↔ v ∈ ξ t x ∧ ∀ w ∈ ξ t x,
      mextDeriv (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).1 x ![v, w] +
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α.timeDeriv).1 x ![w] =
          0 := by
  rw [← hα.grayVectorField_eq_distributionGrayVectorField hξ, grayVectorField_def,
    (hα.isContactFormAt hξ).eq_contactMoserVectorField_iff, hα.kerDistribution_eq,
    ← mem_kerDistribution, hα.kerDistribution_eq]

end SmoothForm.IsLocalDefiningForm

namespace IsContactDistributionFamily

variable (hξ : IsContactDistributionFamily I ξ)
include hξ

/-- **The Gray vector field of a family of contact structures lies in the contact
hyperplanes.** -/
theorem distributionGrayVectorField_mem (t : ℝ) (x : M) :
    distributionGrayVectorField ξ t x ∈ ξ t x := by
  obtain ⟨α, hα⟩ := hξ.exists_isLocalDefiningForm (t, x)
  exact ((hα.eq_distributionGrayVectorField_iff hξ).1 rfl).1

/-- **The Gray vector field of a smooth family of contact structures is smooth**: the map
`(t, x) ↦ (x, Y_t(x))` from `ℝ × M` to the tangent bundle is smooth. Near each point it is the
Gray vector field of a local defining form. -/
theorem contMDiff_distributionGrayVectorField :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, distributionGrayVectorField ξ p.1 p.2⟩ : TangentBundle I M)) := by
  intro p
  obtain ⟨α, hα⟩ := hξ.exists_isLocalDefiningForm p
  refine (SmoothForm.contMDiffAt_contactMoserVectorField_mpullback_prodMk α α.timeDeriv
    (hα.eventually.mono fun q hq ↦ hq.isContactFormAt hξ)).congr_of_eventuallyEq ?_
  filter_upwards [hα.eventually] with q hq
  rw [← hq.grayVectorField_eq_distributionGrayVectorField hξ, SmoothForm.grayVectorField_def]

/-- **The Gray vector field vanishes where the contact hyperplane does not move**: if
`ξ_s(x) = ξ_t(x)` for all `s` near `t`, then `Y_t(x) = 0`. -/
theorem distributionGrayVectorField_eq_zero {t : ℝ} {x : M}
    (hx : ∀ᶠ s in 𝓝 t, ξ s x = ξ t x) : distributionGrayVectorField ξ t x = 0 := by
  obtain ⟨α, hα⟩ := hξ.exists_isLocalDefiningForm (t, x)
  refine ((hα.eq_distributionGrayVectorField_iff hξ).2 ⟨zero_mem _, fun w hw ↦ ?_⟩).symm
  -- The vector `w` stays in the hyperplanes `ξ_s(x) = ker α_s` for `s` near `t`, so
  -- `s ↦ α_s(w)` vanishes near `t`, and its derivative `(∂_t α_t)(w)` is zero.
  have hzero : ∀ᶠ s in 𝓝 t,
      (SmoothForm.mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).1 x ![w] =
        0 := by
    filter_upwards [hx, hα.eventually_kerDistribution_eq_time] with s hs hαs
    rw [← SmoothForm.mem_kerDistribution, hαs, hs]
    exact hw
  -- Evaluation on `w` is a continuous linear map, `ContinuousAlternatingMap.apply`.
  have hd : HasDerivAt
      (fun s ↦ (SmoothForm.mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).1 x ![w])
      ((SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        α.timeDeriv).1 x ![w]) t :=
    (ContinuousAlternatingMap.apply ℝ E ℝ ![w]).hasFDerivAt.comp_hasDerivAt t
      (α.hasDerivAt_mpullback_prodMk_timeDeriv t x)
  rw [(hd.congr_of_eventuallyEq (hzero.mono fun _ h ↦ h.symm)).unique (hasDerivAt_const t 0),
    add_zero]
  exact ContinuousAlternatingMap.map_coord_zero _ 0 rfl

/-- The Gray vector field of a smooth family of contact structures vanishes at all times at a
point whose contact hyperplane is the same for all times. -/
theorem distributionGrayVectorField_eq_zero_of_forall {x : M} (hx : ∀ s, ξ s x = ξ 0 x)
    (t : ℝ) : distributionGrayVectorField ξ t x = 0 :=
  hξ.distributionGrayVectorField_eq_zero (.of_forall fun s ↦ (hx s).trans (hx t).symm)

end IsContactDistributionFamily

/-- **For the kernels of a family of contact forms, the Gray vector field of the family is the
Gray vector field of the forms.** -/
theorem SmoothForm.distributionGrayVectorField_kerDistribution
    {α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1}
    (hc : ∀ t, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm) :
    distributionGrayVectorField
        (fun t ↦ (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution) =
      α.grayVectorField := by
  funext t x
  exact ((isLocalDefiningForm_kerDistribution (fun s ↦ (hc s).apply_ne_zero) (t, x)
    ).grayVectorField_eq_distributionGrayVectorField
      (isContactDistributionFamily_kerDistribution hc)).symm

end TauCeti
