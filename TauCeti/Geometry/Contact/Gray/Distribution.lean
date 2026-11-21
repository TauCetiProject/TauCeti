/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Gray
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# The Gray vector field of a family of contact structures

Gray's stability theorem moves a smooth family of contact structures `ξ_t` by the flow of the Gray
vector field `Y_t`, the solution of `Y_t ∈ ξ_t` and `(ι_{Y_t} dα_t + ∂_t α_t)|ξ_t = 0` for
defining forms `α_t` of `ξ_t`. For a family of contact forms on all of `M` this is
`TauCeti.SmoothForm.grayVectorField`. A contact structure need not be the kernel of a global
one-form, so this file constructs the field from the hyperplanes alone.

A time-dependent hyperplane field `ξ_t` is a *smooth family of contact structures*
(`TauCeti.IsContactDistributionFamily`) when near every time and point it has a *local defining
family* (`TauCeti.IsLocalContactFormFamily`): a smooth family of contact forms `α_t` on an open
set `U` whose kernels are the hyperplanes `ξ_t`. No coorientation is chosen, and two local defining
families may differ by a negative multiplier. The Gray vector field of `ξ`
(`TauCeti.distributionGrayVectorField`) is, near each time and point, the Gray vector field of any
local defining family. This is well defined because

* the Gray vector field is natural under maps with bijective differentials
  (`TauCeti.SmoothForm.mfderiv_grayVectorField_mpullback_prodMap`), in particular under restriction
  to smaller open sets, and
* it does not change when `α_t` is replaced by `f_t α_t` for a nowhere-zero function `f`, of either
  sign (`TauCeti.SmoothForm.grayVectorField_eq_of_kerDistribution_eq`),

so the local Gray fields agree on overlaps
(`TauCeti.IsLocalContactFormFamily.mfderiv_grayVectorField_eq`). The glued field lies in the
contact hyperplanes (`TauCeti.IsContactDistributionFamily.distributionGrayVectorField_mem`), is
jointly smooth in time and point
(`TauCeti.IsContactDistributionFamily.contMDiff_distributionGrayVectorField`), and vanishes at a
point where the hyperplane does not move with time
(`TauCeti.IsContactDistributionFamily.distributionGrayVectorField_eq_zero`). For the kernels of a
smooth family of contact forms on `M` it is the Gray vector field of the forms
(`TauCeti.SmoothForm.distributionGrayVectorField_kerDistribution`). Its flow carries `ξ_s` to `ξ_t`
(`TauCeti.IsContactDistributionFamily.map_mfderiv_timeDependentFlowOf`, in
`TauCeti.Geometry.Contact.Gray.Stability`).

## Main definitions

* `TauCeti.IsLocalContactFormFamily ξ U α t₀`: `α` is a local defining family of `ξ` on `U` near
  time `t₀`.
* `TauCeti.IsContactDistributionFamily ξ`: `ξ` is a smooth family of contact structures.
* `TauCeti.distributionGrayVectorField ξ`: its Gray vector field.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (Gray stability) and its proof, which works with local defining forms.
* J. W. Gray, *Some global properties of contact structures*, Ann. of Math. 69 (1959), 421–450.
-/

public section

noncomputable section

open Bundle Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

open SmoothForm TopologicalSpace

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ξ : ℝ → (x : M) → Submodule ℝ (TangentSpace I x)}

/-- A **local defining family** of a time-dependent hyperplane field `ξ_t` near time `t₀`: a smooth
family `α_t` of one-forms on an open set `U`, represented by a one-form `α` on `ℝ × U`, such that
for all times `t` near `t₀` the slice `α_t` is a contact form on `U` whose kernel at every point of
`U` is `ξ_t`, read in `U` through the differential of the inclusion `U → M`. -/
def IsLocalContactFormFamily (ξ : ℝ → (x : M) → Submodule ℝ (TangentSpace I x)) (U : Opens M)
    (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝 t₀,
    (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm ∧
      ∀ x : U,
        (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution
          x = (ξ t x).comap (mfderiv I I (Subtype.val : U → M) x).toLinearMap

/-- Unfolding `TauCeti.IsLocalContactFormFamily`. -/
theorem isLocalContactFormFamily_iff {U : Opens M} {α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1}
    {t₀ : ℝ} :
    IsLocalContactFormFamily ξ U α t₀ ↔ ∀ᶠ t in 𝓝 t₀,
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm ∧
        ∀ x : U,
          (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution
            x = (ξ t x).comap (mfderiv I I (Subtype.val : U → M) x).toLinearMap :=
  Iff.rfl

namespace IsLocalContactFormFamily

variable {U V : Opens M} {α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1} {t₀ : ℝ}

/-- A local defining family restricts to smaller open sets. -/
theorem mpullback_inclusion (hα : IsLocalContactFormFamily ξ U α t₀) (h : V ≤ U) :
    IsLocalContactFormFamily ξ V
      (SmoothForm.mpullback (Prod.map id (Opens.inclusion h))
        (contMDiff_id.prodMap (contMDiff_inclusion h)) α) t₀ := by
  filter_upwards [hα] with t ⟨hc, hk⟩
  refine ⟨?_, fun y ↦ ?_⟩
  · rw [mpullback_prodMk_mpullback_prodMap _ (contMDiff_inclusion h)]
    exact hc.mpullback _ _ (bijective_mfderiv_inclusion h)
  · rw [mpullback_prodMk_mpullback_prodMap _ (contMDiff_inclusion h), kerDistribution_mpullback,
      hk]
    ext v
    simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe]
    rw [mfderiv_subtype_val_inclusion_apply]

variable [FiniteDimensional ℝ E] [I.Boundaryless]

/-- **Local Gray vector fields agree.** Two local defining families of `ξ_t` near `t₀` have the same
Gray vector field at time `t₀`, read in `M`, at every point where both are defined. -/
theorem mfderiv_grayVectorField_eq {U' : Opens M} {α' : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U') ℝ 1}
    (hα : IsLocalContactFormFamily ξ U α t₀) (hα' : IsLocalContactFormFamily ξ U' α' t₀)
    {x : M} (hx : x ∈ U) (hx' : x ∈ U') :
    mfderiv I I (Subtype.val : U' → M) ⟨x, hx'⟩ (α'.grayVectorField t₀ ⟨x, hx'⟩) =
      mfderiv I I (Subtype.val : U → M) ⟨x, hx⟩ (α.grayVectorField t₀ ⟨x, hx⟩) := by
  set y : (U ⊓ U' : Opens M) := ⟨x, hx, hx'⟩
  -- Read in `U ⊓ U'`, each local Gray field is the Gray field of the restricted family.
  have hres (W : Opens M) (hW : U ⊓ U' ≤ W) (γ : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × W) ℝ 1)
      (hγ : IsLocalContactFormFamily ξ W γ t₀) (hxW : x ∈ W) :
      mfderiv I I (Subtype.val : W → M) ⟨x, hxW⟩ (γ.grayVectorField t₀ ⟨x, hxW⟩) =
        mfderiv I I (Subtype.val : (U ⊓ U' : Opens M) → M) y
          ((SmoothForm.mpullback (Prod.map id (Opens.inclusion hW))
            (contMDiff_id.prodMap (contMDiff_inclusion hW)) γ).grayVectorField t₀ y) := by
    rw [← mfderiv_subtype_val_inclusion_apply hW y, mfderiv_grayVectorField_mpullback_prodMap γ
      hγ.self_of_nhds.1 _ (contMDiff_inclusion hW) (bijective_mfderiv_inclusion hW) y]
  have hβ := hα.mpullback_inclusion (inf_le_left : U ⊓ U' ≤ U)
  have hβ' := hα'.mpullback_inclusion (inf_le_right : U ⊓ U' ≤ U')
  rw [hres U' inf_le_right α' hα' hx', hres U inf_le_left α hα hx,
    grayVectorField_eq_of_kerDistribution_eq (hβ.mono fun _ h ↦ h.1)
      (by filter_upwards [hβ, hβ'] with t ht ht' z; rw [ht.2, ht'.2])]

end IsLocalContactFormFamily

/-- A time-dependent hyperplane field `ξ_t` on `M` is a **smooth family of contact structures**
when, near every time and every point, it has a local defining family: a smooth family of contact
forms on an open set whose kernels are the hyperplanes `ξ_t`. No global defining form and no
coorientation of the hyperplanes is assumed. -/
def IsContactDistributionFamily (ξ : ℝ → (x : M) → Submodule ℝ (TangentSpace I x)) : Prop :=
  ∀ t x, ∃ U : Opens M, x ∈ U ∧
    ∃ α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1, IsLocalContactFormFamily ξ U α t

/-- Unfolding `TauCeti.IsContactDistributionFamily`. -/
theorem isContactDistributionFamily_iff :
    IsContactDistributionFamily ξ ↔ ∀ t x, ∃ U : Opens M, x ∈ U ∧
      ∃ α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1, IsLocalContactFormFamily ξ U α t :=
  Iff.rfl

open Classical in
/-- The **Gray vector field** of a smooth family of contact structures `ξ_t`: at time `t` and at
`x`, the Gray vector field of any local defining family of `ξ_t` near `t` on an open set
containing `x` (`TauCeti.IsLocalContactFormFamily.distributionGrayVectorField_eq`). The local
fields agree on overlaps (`TauCeti.IsLocalContactFormFamily.mfderiv_grayVectorField_eq`), so they
glue to a vector field determined by the hyperplanes alone. It is `0` where `ξ` has no local
defining family. -/
def distributionGrayVectorField (ξ : ℝ → (x : M) → Submodule ℝ (TangentSpace I x)) (t : ℝ)
    (x : M) : TangentSpace I x :=
  if h : ∃ U : Opens M, ∃ _ : x ∈ U,
      ∃ α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1, IsLocalContactFormFamily ξ U α t then
    mfderiv I I (Subtype.val : h.choose → M) ⟨x, h.choose_spec.choose⟩
      (h.choose_spec.choose_spec.choose.grayVectorField t ⟨x, h.choose_spec.choose⟩)
  else 0

/-- The Gray vector field of a family of contact structures is the Gray vector field of any local
defining family, read in `M`. -/
theorem IsLocalContactFormFamily.distributionGrayVectorField_eq [FiniteDimensional ℝ E]
    [I.Boundaryless] {U : Opens M} {α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1} {t : ℝ}
    (hα : IsLocalContactFormFamily ξ U α t) {x : M} (hx : x ∈ U) :
    distributionGrayVectorField ξ t x =
      mfderiv I I (Subtype.val : U → M) ⟨x, hx⟩ (α.grayVectorField t ⟨x, hx⟩) := by
  have h : ∃ U : Opens M, ∃ _ : x ∈ U,
      ∃ α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1, IsLocalContactFormFamily ξ U α t :=
    ⟨U, hx, α, hα⟩
  rw [distributionGrayVectorField, dite_eq_left_of_eq_true (eq_true h)]
  exact hα.mfderiv_grayVectorField_eq h.choose_spec.choose_spec.choose_spec hx _

namespace IsContactDistributionFamily

variable [FiniteDimensional ℝ E] [I.Boundaryless] (hξ : IsContactDistributionFamily ξ)
include hξ

/-- The Gray vector field of a smooth family of contact structures is horizontal: at time `t` it
lies in the contact hyperplane `ξ_t`. -/
theorem distributionGrayVectorField_mem (t : ℝ) (x : M) :
    distributionGrayVectorField ξ t x ∈ ξ t x := by
  obtain ⟨U, hx, α, hα⟩ := hξ t x
  have hmem : α.grayVectorField t ⟨x, hx⟩ ∈
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution
        ⟨x, hx⟩ :=
    mem_kerDistribution.2 (apply_grayVectorField hα.self_of_nhds.1 _)
  rw [hα.self_of_nhds.2] at hmem
  rw [hα.distributionGrayVectorField_eq hx]
  exact hmem

/-- **The Gray vector field vanishes where the contact hyperplane is stationary.** If the
hyperplane `ξ_u` at `x` is the same for all times `u` near `t`, then the Gray vector field of a
smooth family of contact structures vanishes at `x` at time `t`. -/
theorem distributionGrayVectorField_eq_zero {t : ℝ} {x : M} (hx : ∀ᶠ u in 𝓝 t, ξ u x = ξ t x) :
    distributionGrayVectorField ξ t x = 0 := by
  obtain ⟨U, hxU, α, hα⟩ := hξ t x
  rw [hα.distributionGrayVectorField_eq hxU, grayVectorField_eq_zero hα.self_of_nhds.1, map_zero]
  filter_upwards [hα, hx] with u hu hux
  rw [hu.2, hα.self_of_nhds.2, hux]

/-- At a point at which the contact hyperplane `ξ_u` is the same for all times, the Gray vector
field of a smooth family of contact structures vanishes at all times. -/
theorem distributionGrayVectorField_eq_zero_of_forall_eq {x : M} {t₀ : ℝ}
    (hx : ∀ u, ξ u x = ξ t₀ x) (u : ℝ) : distributionGrayVectorField ξ u x = 0 :=
  hξ.distributionGrayVectorField_eq_zero (.of_forall fun v ↦ (hx v).trans (hx u).symm)

/-- **The Gray vector field of a smooth family of contact structures is smooth**: the map
`(t, x) ↦ (x, Y_t(x))` into the tangent bundle is smooth. -/
theorem contMDiff_distributionGrayVectorField :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, distributionGrayVectorField ξ p.1 p.2⟩ : TangentBundle I M)) := by
  rintro ⟨t₀, x₀⟩
  obtain ⟨U, hx₀, α, hα⟩ := hξ t₀ x₀
  obtain ⟨T, hT, hTo, ht₀⟩ := eventually_nhds_iff.1 hα
  -- The local Gray field, as a map to the tangent bundle of `U`, is smooth on `T × U`.
  have hloc : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun q : ℝ × U ↦ (⟨q.2, α.grayVectorField q.1 q.2⟩ : TangentBundle I U)) (T ×ˢ Set.univ) :=
    by simpa only [grayVectorField_def] using
      contMDiffOn_contactMoserVectorField_mpullback_prodMk α α.timeDeriv hTo fun t ht ↦ (hT t ht).1
  -- On the open set `T × U`, the glued field is the local field pushed forward to `M`.
  let W : Opens (ℝ × M) := ⟨T ×ˢ U, hTo.prod U.isOpen⟩
  let e : W → ℝ × U := fun q ↦ (q.val.1, ⟨q.val.2, q.property.2⟩)
  have he : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞ e :=
    (contMDiff_fst.comp contMDiff_subtypeVal).prodMk
      ((ContMDiff.subtypeVal_comp_iff U _).1 (contMDiff_snd.comp contMDiff_subtypeVal))
  have heq : (fun q : W ↦
      (⟨q.val.2, distributionGrayVectorField ξ q.val.1 q.val.2⟩ : TangentBundle I M)) =
      tangentMap I I (Subtype.val : U → M) ∘
        (fun q : ℝ × U ↦ (⟨q.2, α.grayVectorField q.1 q.2⟩ : TangentBundle I U)) ∘ e := by
    funext q
    have hq : IsLocalContactFormFamily ξ U α q.val.1 :=
      Filter.eventually_of_mem (hTo.mem_nhds q.property.1) hT
    simp only [Function.comp_apply, tangentMap, e]
    rw [hq.distributionGrayVectorField_eq q.property.2]
  refine contMDiffAt_subtype_iff (U := W) (x := ⟨(t₀, x₀), ht₀, hx₀⟩) |>.1 ?_
  rw [heq]
  exact (((contMDiff_subtypeVal (n := ω)).contMDiff_tangentMap le_top).contMDiffAt).comp _
    ((hloc.contMDiffAt (x := e ⟨(t₀, x₀), ht₀, hx₀⟩)
      (prod_mem_nhds (hTo.mem_nhds ht₀) Filter.univ_mem)).comp _ he.contMDiffAt)

end IsContactDistributionFamily

namespace SmoothForm

variable {α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 1}

/-- The restriction of a smooth family of contact forms to an open set is a local defining family
of its kernels. -/
theorem isLocalContactFormFamily_mpullback_subtype_val
    (hc : ∀ t, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
    (U : Opens M) (t₀ : ℝ) :
    IsLocalContactFormFamily
      (fun t ↦ (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution) U
      (mpullback (Prod.map id (Subtype.val : U → M)) (contMDiff_id.prodMap contMDiff_subtypeVal)
        α) t₀ :=
  .of_forall fun t ↦ by
    rw [mpullback_prodMk_mpullback_prodMap _ contMDiff_subtypeVal]
    exact ⟨(hc t).mpullback _ _ bijective_mfderiv_subtype_val,
      kerDistribution_mpullback _ contMDiff_subtypeVal _⟩

/-- **The kernels of a smooth family of contact forms are a smooth family of contact
structures.** -/
theorem isContactDistributionFamily_kerDistribution
    (hc : ∀ t, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm) :
    IsContactDistributionFamily
      (fun t ↦ (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution) :=
  fun t _ ↦ ⟨⊤, trivial, _, isLocalContactFormFamily_mpullback_subtype_val hc ⊤ t⟩

/-- For the kernels of a smooth family of contact forms, the Gray vector field of the family of
contact structures is the Gray vector field of the family of forms. -/
theorem distributionGrayVectorField_kerDistribution [FiniteDimensional ℝ E] [I.Boundaryless]
    (hc : ∀ t, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm) :
    distributionGrayVectorField
        (fun t ↦ (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution) =
      α.grayVectorField := by
  funext t x
  rw [(isLocalContactFormFamily_mpullback_subtype_val hc ⊤ t).distributionGrayVectorField_eq
    (Set.mem_univ x), mfderiv_grayVectorField_mpullback_prodMap α (hc t) _ contMDiff_subtypeVal
      bijective_mfderiv_subtype_val]

end SmoothForm

end TauCeti
