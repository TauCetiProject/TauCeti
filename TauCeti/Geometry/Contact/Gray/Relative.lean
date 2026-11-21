/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Gray.Distribution
public import TauCeti.Geometry.Manifold.Flow.TimeDependent.Opens

/-!
# Relative Gray stability for families of contact structures

Let `ξ_t` be a smooth family of contact structures on a boundaryless manifold `M`
(`TauCeti.IsContactDistributionFamily`): near every time and point the hyperplanes are the kernels
of a smooth family of contact forms, but no global defining form and no coorientation is chosen.
Gray's stability theorem says that the flow `φ_{s,t}` of its Gray vector field
(`TauCeti.distributionGrayVectorField`) carries the contact structures into each other:

`dφ_{s,t}(ξ_s) = ξ_t`

wherever the flow is defined
(`TauCeti.IsContactDistributionFamily.map_mfderiv_timeDependentFlowOf`). No compactness is needed.
The flow fixes the points at which the hyperplane does not move, so near any set `K` of such points
it gives a partial diffeomorphism fixing `K` and carrying `ξ_s` to `ξ_t`
(`TauCeti.IsContactDistributionFamily.exists_partialDiffeomorph_map_mfderiv_eq`): Gray's partial
isotopy, the time map of the flow
(`TauCeti.IsContactDistributionFamily.grayPartialDiffeomorph`). On a compact manifold the flow is a
global isotopy (`TauCeti.IsContactDistributionFamily.grayDiffeomorph`,
`TauCeti.IsContactDistributionFamily.exists_diffeomorph_map_mfderiv_eq`).

The proof is local in time and space. Near a time `u₀` and a point `y₀`, the contact structures
are the kernels of a local defining family `α_t` on an open set `U`, contact for the times of an
interval `T` around `u₀`. On `U` the Gray vector field is that of `α_t`, so Gray's equation
`L_{Y_t} α_t + ∂_t α_t = μ_t α_t` holds there at the times of `T`, and along the flow it integrates
to `φ_{s,t}^* α_t = exp (∫ₛᵗ μ_u ∘ φ_{s,u} du) α_s` for `s, t ∈ T`
(`TauCeti.SmoothForm.mpullback_timeDependentFlowOf_apply_eq_exp_integral_grayRate_smul`). Hence
the flow maps `ker α_s` into `ker α_t` for nearby times. The flow on `U` is the flow on `M`
(`TauCeti.timeDependentFlowOf_restrict_opens`), and the two-time composition law propagates the
local statement along a whole trajectory, by connectedness of its interval of times
(`TauCeti.map_mfderiv_timeDependentFlowOf_eq_of_eventually`).

## Main definitions

* `TauCeti.IsContactDistributionFamily.grayPartialDiffeomorph`: the flow of the Gray vector field
  from time `s` to time `t`, as a partial diffeomorphism.
* `TauCeti.IsContactDistributionFamily.grayDiffeomorph`: on a compact manifold, the same flow as a
  diffeomorphism.

## Main results

* `TauCeti.IsContactDistributionFamily.map_mfderiv_timeDependentFlowOf`: the flow of the Gray
  vector field carries `ξ_s` to `ξ_t`.
* `TauCeti.IsContactDistributionFamily.map_mfderiv_grayPartialDiffeomorph`: the same on the source
  of Gray's partial isotopy.
* `TauCeti.IsContactDistributionFamily.exists_partialDiffeomorph_map_mfderiv_eq`: relative Gray
  stability near a set of points with stationary contact hyperplanes.
* `TauCeti.IsContactDistributionFamily.map_mfderiv_grayDiffeomorph`,
  `TauCeti.IsContactDistributionFamily.contMDiff_grayDiffeomorph`: Gray's isotopy on a compact
  manifold carries `ξ_s` onto `ξ_t` and is jointly smooth in both times and the point.
* `TauCeti.IsContactDistributionFamily.exists_diffeomorph_map_mfderiv_eq`: Gray's stability
  theorem for contact structures on a compact manifold.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (Gray stability) and its proof, which works with local defining forms.
* J. W. Gray, *Some global properties of contact structures*, Ann. of Math. 69 (1959), 421–450.
-/

public section

noncomputable section

open Set Filter TopologicalSpace
open scoped ContDiff Manifold Topology

namespace TauCeti

/-! ### The flow of the Gray vector field of a family of contact structures -/

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {ξ : ℝ → (x : M) → Submodule ℝ (TangentSpace I x)}

namespace IsContactDistributionFamily

variable (hξ : IsContactDistributionFamily ξ)
include hξ

/-- **The local step of Gray's theorem.** For all times `u` near `u₀`, the flow of the Gray vector
field of a smooth family of contact structures `ξ` from `(u₀, y₀)` to time `u` and its
differentials map `ξ_{u₀}` into `ξ_u` and `ξ_u` back into `ξ_{u₀}`. -/
private theorem eventually_mfderiv_timeDependentFlowOf_mem (u₀ : ℝ) (y₀ : M) :
    ∀ᶠ u in 𝓝 u₀,
      (∀ v ∈ ξ u₀ y₀, mfderiv I I (timeDependentFlowOf (distributionGrayVectorField ξ) u₀ u) y₀ v ∈
        ξ u (timeDependentFlowOf (distributionGrayVectorField ξ) u₀ u y₀)) ∧
      ∀ v ∈ ξ u (timeDependentFlowOf (distributionGrayVectorField ξ) u₀ u y₀),
        mfderiv I I (timeDependentFlowOf (distributionGrayVectorField ξ) u u₀)
          (timeDependentFlowOf (distributionGrayVectorField ξ) u₀ u y₀) v ∈ ξ u₀ y₀ := by
  have hY := hξ.contMDiff_distributionGrayVectorField
  have hY₁ := hY.of_le (m := 1) (by simp)
  -- A local defining family `α` on `U ∋ y₀`, contact on an open interval `T ∋ u₀`.
  obtain ⟨U, hy₀, α, hα⟩ := isContactDistributionFamily_iff.1 hξ u₀ y₀
  lift y₀ to U using hy₀
  obtain ⟨T₀, hT₀, hT₀o, hu₀⟩ := eventually_nhds_iff.1 (isLocalContactFormFamily_iff.1 hα)
  obtain ⟨ε, hε, hεT⟩ := Metric.isOpen_iff.1 hT₀o u₀ hu₀
  set T := Metric.ball u₀ ε
  have hTα (t : ℝ) (ht : t ∈ T) : IsLocalContactFormFamily ξ U α t :=
    isLocalContactFormFamily_iff.2 (Filter.eventually_of_mem (hT₀o.mem_nhds (hεT ht)) hT₀)
  -- On `U`, the restriction `Z` of the Gray vector field is the Gray vector field of `α` on `T`.
  set Z : ℝ → (z : U) → TangentSpace I z := fun t z ↦ distributionGrayVectorField ξ t z
  have hZ := contMDiff_timeDependentField_opens (U := U) hY
  have hZα (t : ℝ) (ht : t ∈ T) : Z t = α.grayVectorField t :=
    funext fun z ↦ ((hTα t ht).grayVectorField_eq_distributionGrayVectorField z).symm
  have hc (t : ℝ) (ht : t ∈ T) := (hTα t ht).isContactForm
  have hT : IsOpen T := Metric.isOpen_ball
  have hTc : T.OrdConnected := (convex_ball u₀ ε).ordConnected
  have hu₀T : u₀ ∈ T := Metric.mem_ball_self hε
  -- For `u` near `u₀`, the flow of `Z` from `(u₀, y₀)` is defined up to time `u`.
  have hdom : ∀ᶠ u in 𝓝 u₀, ((u₀, u), y₀) ∈ timeDependentFlowDomain Z :=
    ((isOpen_timeDependentFlowDomain (hZ.of_le (by simp))).preimage
      (by fun_prop : Continuous fun u : ℝ ↦ ((u₀, u), y₀))).mem_nhds
      (mem_timeDependentFlowDomain_self (hZ.of_le (by simp)) u₀ y₀)
  filter_upwards [hdom, Metric.ball_mem_nhds u₀ hε] with u hu huT
  have hφ := (timeDependentFlowOf_restrict_opens hY₁ hu).2
  obtain ⟨hback, hback'⟩ := timeDependentFlowOf_symm_of_mem (hZ.of_le (by simp)) hu
  refine ⟨fun v hv ↦ ?_, fun v hv ↦ ?_⟩
  · -- Forward: `dφ_{u₀,u}` maps `ker α_{u₀}` into `ker α_u` on `U`.
    have key := (hTα u huT).mem_kerDistribution_iff.1
      ((SmoothForm.mfderiv_timeDependentFlowOf_mem_kerDistribution_iff hT hTc hc
        (hZ.of_le (by simp)) hZα hu₀T huT hu).2 ((hTα u₀ hu₀T).mem_kerDistribution_iff.2 hv))
    rwa [hφ, ← mfderiv_timeDependentFlowOf_restrict_opens_apply hY₁ hu v] at key
  · -- Backward: `dφ_{u,u₀}` maps `ker α_u` back into `ker α_{u₀}` on `U`.
    rw [← hφ] at hv
    have key := (hTα u₀ hu₀T).mem_kerDistribution_iff.1
      ((SmoothForm.mfderiv_timeDependentFlowOf_mem_kerDistribution_iff hT hTc hc
        (hZ.of_le (by simp)) hZα huT hu₀T hback).2 ((hTα u huT).mem_kerDistribution_iff.2 hv))
    rw [hback'] at key
    rw [← hφ, mfderiv_timeDependentFlowOf_restrict_opens_apply hY₁ hback v]
    exact key

/-- **The flow of the Gray vector field carries the contact structures into each other.** If the
flow `φ` of the Gray vector field of a smooth family of contact structures `ξ` on a boundaryless
manifold runs from `(s, x)` up to time `t`, then its differential at `x` maps the hyperplane `ξ_s`
at `x` onto the hyperplane `ξ_t` at `φ_{s,t} x`. No compactness, global defining form or
coorientation is needed. -/
theorem map_mfderiv_timeDependentFlowOf {s t : ℝ} {x : M}
    (h : ((s, t), x) ∈ timeDependentFlowDomain (distributionGrayVectorField ξ)) :
    (ξ s x).map
        (mfderiv I I (timeDependentFlowOf (distributionGrayVectorField ξ) s t) x).toLinearMap =
      ξ t (timeDependentFlowOf (distributionGrayVectorField ξ) s t x) :=
  map_mfderiv_timeDependentFlowOf_eq_of_eventually
    (hξ.contMDiff_distributionGrayVectorField.of_le (by simp))
    (eventually_mfderiv_timeDependentFlowOf_mem hξ) h


/-- **The flow of the Gray vector field preserves the contact structures.** If the flow of the
Gray vector field of a smooth family of contact structures is defined from `(s, x)` up to time
`t`, its differential at `x` maps every vector of `ξ_s` at `x` to a vector of `ξ_t` at the image
point. -/
theorem mfderiv_timeDependentFlowOf_mem {s t : ℝ} {x : M}
    (h : ((s, t), x) ∈ timeDependentFlowDomain (distributionGrayVectorField ξ))
    {v : TangentSpace I x} (hv : v ∈ ξ s x) :
    mfderiv I I (timeDependentFlowOf (distributionGrayVectorField ξ) s t) x v ∈
      ξ t (timeDependentFlowOf (distributionGrayVectorField ξ) s t x) := by
  rw [← hξ.map_mfderiv_timeDependentFlowOf h]
  exact Submodule.mem_map_of_mem hv

/-! ### Gray's partial isotopy and relative Gray stability -/

/-- **Gray's partial isotopy** of a smooth family of contact structures: the time-dependent flow
of its Gray vector field from time `s` to time `t`, as a smooth partial diffeomorphism of `M`. It
carries `ξ_s` to `ξ_t` on its source
(`TauCeti.IsContactDistributionFamily.map_mfderiv_grayPartialDiffeomorph`), whose points are those
from which the flow is defined up to time `t`. -/
def grayPartialDiffeomorph (s t : ℝ) : PartialDiffeomorph I I M M ∞ :=
  timeDependentFlowPartialDiffeomorph le_top hξ.contMDiff_distributionGrayVectorField s t

/-- Gray's partial isotopy is the time-dependent flow of the Gray vector field. -/
@[simp]
theorem grayPartialDiffeomorph_apply (s t : ℝ) (x : M) :
    hξ.grayPartialDiffeomorph s t x = timeDependentFlowOf (distributionGrayVectorField ξ) s t x :=
  timeDependentFlowPartialDiffeomorph_apply _ _ s t x

/-- As a function, Gray's partial isotopy is the time-dependent flow of the Gray vector field. -/
theorem coe_grayPartialDiffeomorph (s t : ℝ) :
    ⇑(hξ.grayPartialDiffeomorph s t) = timeDependentFlowOf (distributionGrayVectorField ξ) s t :=
  funext (hξ.grayPartialDiffeomorph_apply s t)

/-- The inverse of Gray's partial isotopy from `s` to `t` is the time-dependent flow of the Gray
vector field from `t` to `s`. -/
@[simp]
theorem grayPartialDiffeomorph_symm_apply (s t : ℝ) (x : M) :
    (hξ.grayPartialDiffeomorph s t).toPartialEquiv.symm x =
      timeDependentFlowOf (distributionGrayVectorField ξ) t s x :=
  timeDependentFlowPartialDiffeomorph_symm_apply _ _ s t x

/-- A point lies in the source of Gray's partial isotopy from `s` to `t` exactly when the flow of
the Gray vector field from `(s, x)` is defined up to time `t`. -/
@[simp]
theorem mem_grayPartialDiffeomorph_source_iff {s t : ℝ} {x : M} :
    x ∈ (hξ.grayPartialDiffeomorph s t).source ↔
      ((s, t), x) ∈ timeDependentFlowDomain (distributionGrayVectorField ξ) :=
  mem_timeDependentFlowPartialDiffeomorph_source_iff _ _

/-- A point lies in the target of Gray's partial isotopy from `s` to `t` exactly when the flow of
the Gray vector field from `(t, x)` is defined back to time `s`. -/
@[simp]
theorem mem_grayPartialDiffeomorph_target_iff {s t : ℝ} {x : M} :
    x ∈ (hξ.grayPartialDiffeomorph s t).target ↔
      ((t, s), x) ∈ timeDependentFlowDomain (distributionGrayVectorField ξ) :=
  mem_timeDependentFlowPartialDiffeomorph_target_iff _ _

/-- Gray's partial isotopy depends smoothly on the final time and the point, on the open set of
pairs `(t, x)` for which the flow from `(s, x)` is defined up to time `t`. -/
theorem contMDiffOn_grayPartialDiffeomorph (s : ℝ) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ hξ.grayPartialDiffeomorph s p.1 p.2)
      {p | ((s, p.1), p.2) ∈ timeDependentFlowDomain (distributionGrayVectorField ξ)} := by
  simp only [grayPartialDiffeomorph_apply]
  exact (contMDiffOn_timeDependentFlowOf le_top hξ.contMDiff_distributionGrayVectorField).comp
    (((contMDiff_const (c := s)).prodMk contMDiff_fst).prodMk contMDiff_snd).contMDiffOn
    fun _ hp ↦ hp

/-- **Gray's stability theorem on the source of the partial isotopy.** Gray's partial isotopy from
`s` to `t` carries `ξ_s` onto `ξ_t` at every point of its source. -/
theorem map_mfderiv_grayPartialDiffeomorph {s t : ℝ} {x : M}
    (hx : x ∈ (hξ.grayPartialDiffeomorph s t).source) :
    (ξ s x).map (mfderiv I I (hξ.grayPartialDiffeomorph s t) x).toLinearMap =
      ξ t (hξ.grayPartialDiffeomorph s t x) := by
  rw [coe_grayPartialDiffeomorph]
  exact hξ.map_mfderiv_timeDependentFlowOf ((hξ.mem_grayPartialDiffeomorph_source_iff).1 hx)

/-- A point at which the contact hyperplane `ξ_u` is the same for all times lies in the source of
Gray's partial isotopy between any two times. -/
theorem mem_grayPartialDiffeomorph_source {x : M} (hx : ∀ u, ξ u x = ξ 0 x) (s t : ℝ) :
    x ∈ (hξ.grayPartialDiffeomorph s t).source :=
  (hξ.mem_grayPartialDiffeomorph_source_iff).2 (mem_timeDependentFlowDomain_of_forall_eq_zero
    (hξ.distributionGrayVectorField_eq_zero_of_forall_eq hx) s t)

/-- A point at which the contact hyperplane `ξ_u` is the same for all times lies in the target of
Gray's partial isotopy between any two times. -/
theorem mem_grayPartialDiffeomorph_target {x : M} (hx : ∀ u, ξ u x = ξ 0 x) (s t : ℝ) :
    x ∈ (hξ.grayPartialDiffeomorph s t).target :=
  (hξ.mem_grayPartialDiffeomorph_target_iff).2 (mem_timeDependentFlowDomain_of_forall_eq_zero
    (hξ.distributionGrayVectorField_eq_zero_of_forall_eq hx) t s)

/-- Gray's partial isotopy fixes every point at which the contact hyperplane `ξ_u` is the same for
all times. -/
theorem grayPartialDiffeomorph_apply_eq_self {x : M} (hx : ∀ u, ξ u x = ξ 0 x) (s t : ℝ) :
    hξ.grayPartialDiffeomorph s t x = x := by
  rw [grayPartialDiffeomorph_apply]
  exact timeDependentFlowOf_eq_self_of_forall_eq_zero
    (hξ.contMDiff_distributionGrayVectorField.of_le (by simp))
    (hξ.distributionGrayVectorField_eq_zero_of_forall_eq hx) s t

/-- **Relative Gray stability for contact structures.** Let `ξ_t` be a smooth family of contact
structures on a boundaryless manifold, and let `K` be a set of points at each of which the contact
hyperplane `ξ_t` is the same for all times. Then for all times `s` and `t` there is a smooth partial
diffeomorphism `φ` of `M`, whose source and target are open neighbourhoods of `K`, which fixes
every point of `K` and whose differential carries `ξ_s` onto `ξ_t` at every point of its source.
Neither `K` nor `M` need be compact, `K` need not be closed, and no global defining form or
coorientation of `ξ` is needed. -/
theorem exists_partialDiffeomorph_map_mfderiv_eq {K : Set M} (hK : ∀ x ∈ K, ∀ u, ξ u x = ξ 0 x)
    (s t : ℝ) :
    ∃ φ : PartialDiffeomorph I I M M ∞, K ⊆ φ.source ∧ K ⊆ φ.target ∧ (∀ x ∈ K, φ x = x) ∧
      ∀ x ∈ φ.source, (ξ s x).map (mfderiv I I φ x).toLinearMap = ξ t (φ x) :=
  ⟨hξ.grayPartialDiffeomorph s t, fun x hx ↦ hξ.mem_grayPartialDiffeomorph_source (hK x hx) s t,
    fun x hx ↦ hξ.mem_grayPartialDiffeomorph_target (hK x hx) s t,
    fun x hx ↦ hξ.grayPartialDiffeomorph_apply_eq_self (hK x hx) s t,
    fun _ hx ↦ hξ.map_mfderiv_grayPartialDiffeomorph hx⟩

/-! ### Gray's isotopy on a compact manifold -/

variable [CompactSpace M]

/-- On a compact manifold, the Gray vector field of a smooth family of contact structures has a
complete suspension: its time-dependent flow is defined for all times. -/
theorem isCompleteVectorField_timeDependentSuspensionField_distributionGrayVectorField :
    IsCompleteVectorField (timeDependentSuspensionField (distributionGrayVectorField ξ)) :=
  isCompleteVectorField_timeDependentSuspensionField
    (hξ.contMDiff_distributionGrayVectorField.of_le (by simp))
    isCompact_univ (by simp)

/-- **Gray's isotopy** of a smooth family of contact structures on a compact manifold without
boundary: the time-dependent flow of its Gray vector field from time `s` to time `t`, as a
diffeomorphism. It carries `ξ_s` onto `ξ_t`
(`TauCeti.IsContactDistributionFamily.map_mfderiv_grayDiffeomorph`). -/
def grayDiffeomorph (s t : ℝ) : M ≃ₘ⟮I, I⟯ M :=
  timeDependentFlowDiffeomorph
    hξ.isCompleteVectorField_timeDependentSuspensionField_distributionGrayVectorField le_top
    hξ.contMDiff_distributionGrayVectorField s t

/-- Gray's isotopy is the time-dependent flow of the Gray vector field. -/
theorem grayDiffeomorph_apply (s t : ℝ) (x : M) :
    hξ.grayDiffeomorph s t x = timeDependentFlowOf (distributionGrayVectorField ξ) s t x :=
  timeDependentFlowDiffeomorph_apply _ _ _ s t x

/-- As a function, Gray's isotopy is the time-dependent flow of the Gray vector field. -/
theorem coe_grayDiffeomorph (s t : ℝ) :
    ⇑(hξ.grayDiffeomorph s t) = timeDependentFlowOf (distributionGrayVectorField ξ) s t :=
  funext (hξ.grayDiffeomorph_apply s t)

/-- The inverse of Gray's isotopy from `s` to `t` is Gray's isotopy from `t` to `s`. -/
@[simp]
theorem grayDiffeomorph_symm_apply (s t : ℝ) (x : M) :
    (hξ.grayDiffeomorph s t).symm x = hξ.grayDiffeomorph t s x :=
  (timeDependentFlowDiffeomorph_symm_apply _ _ _ s t x).trans (hξ.grayDiffeomorph_apply t s x).symm

/-- Gray's isotopy from a time to itself is the identity. -/
@[simp]
theorem grayDiffeomorph_self (s : ℝ) (x : M) : hξ.grayDiffeomorph s s x = x := by
  rw [grayDiffeomorph_apply, timeDependentFlowOf_self]

/-- Gray's isotopy composes: flowing from `r` to `s` and then from `s` to `t` is flowing from `r`
to `t`. -/
@[simp]
theorem grayDiffeomorph_grayDiffeomorph (r s t : ℝ) (x : M) :
    hξ.grayDiffeomorph s t (hξ.grayDiffeomorph r s x) = hξ.grayDiffeomorph r t x := by
  simp only [grayDiffeomorph_apply]
  exact timeDependentFlowOf_trans
    hξ.isCompleteVectorField_timeDependentSuspensionField_distributionGrayVectorField
    (hξ.contMDiff_distributionGrayVectorField.of_le (by simp)) r s t x

/-- Gray's isotopy depends smoothly on the initial time, the final time and the point. -/
theorem contMDiff_grayDiffeomorph :
    ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
      (fun p : (ℝ × ℝ) × M ↦ hξ.grayDiffeomorph p.1.1 p.1.2 p.2) := by
  simp only [grayDiffeomorph_apply]
  exact contMDiff_timeDependentFlowOf
    hξ.isCompleteVectorField_timeDependentSuspensionField_distributionGrayVectorField le_top
    hξ.contMDiff_distributionGrayVectorField

/-- **Gray's stability theorem on a compact manifold.** On a compact manifold without boundary,
Gray's isotopy of a smooth family of contact structures carries `ξ_s` onto `ξ_t` at every point:
it is a contactomorphism from `ξ_s` to `ξ_t`. -/
theorem map_mfderiv_grayDiffeomorph (s t : ℝ) (x : M) :
    (ξ s x).map (mfderiv I I (hξ.grayDiffeomorph s t) x).toLinearMap =
      ξ t (hξ.grayDiffeomorph s t x) := by
  rw [coe_grayDiffeomorph]
  exact hξ.map_mfderiv_timeDependentFlowOf ((timeDependentFlowDomain_eq_univ
    hξ.isCompleteVectorField_timeDependentSuspensionField_distributionGrayVectorField).symm ▸
      mem_univ _)

/-- Gray's isotopy fixes every point at which the contact hyperplane `ξ_u` is the same for all
times. -/
theorem grayDiffeomorph_apply_eq_self {x : M} (hx : ∀ u, ξ u x = ξ 0 x) (s t : ℝ) :
    hξ.grayDiffeomorph s t x = x := by
  rw [grayDiffeomorph_apply]
  exact timeDependentFlowOf_eq_self_of_forall_eq_zero
    (hξ.contMDiff_distributionGrayVectorField.of_le (by simp))
    (hξ.distributionGrayVectorField_eq_zero_of_forall_eq hx) s t

/-- **Gray's stability theorem for contact structures.** On a compact boundaryless manifold, a
smooth family of contact structures `ξ_t` is carried along by an isotopy: there are diffeomorphisms
`φ_{s,t}`, jointly smooth in both times and the point, with `φ_{s,s} = id`, whose differentials
carry `ξ_s` onto `ξ_t`. No global defining form or coorientation of `ξ` is needed. -/
theorem exists_diffeomorph_map_mfderiv_eq :
    ∃ φ : ℝ → ℝ → M ≃ₘ⟮I, I⟯ M,
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞ (fun p : (ℝ × ℝ) × M ↦ φ p.1.1 p.1.2 p.2) ∧
        (∀ s x, φ s s x = x) ∧
        ∀ s t x, (ξ s x).map (mfderiv I I (φ s t) x).toLinearMap = ξ t (φ s t x) :=
  ⟨hξ.grayDiffeomorph, hξ.contMDiff_grayDiffeomorph, hξ.grayDiffeomorph_self,
    hξ.map_mfderiv_grayDiffeomorph⟩

end IsContactDistributionFamily

end TauCeti
