/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Gray.Distribution
public import TauCeti.Geometry.Manifold.Flow.TimeDependent.Opens

/-!
# Gray stability for families of contact structures

Let `ξ_t` be a smooth family of contact structures on a manifold `M`
(`TauCeti.IsContactDistributionFamily`): near every time and point, `ξ_t` is the kernel of a
smooth family of contact forms on an open set, but there need be no global defining form, and no
coorientation is chosen. Its Gray vector field `Y_t` (`TauCeti.distributionGrayVectorField`) is
glued from the Gray vector fields of the local defining families. This file proves **Gray's
stability theorem** for such families: the time-dependent flow `φ_{s,t}` of `Y_t` carries `ξ_s`
to `ξ_t`,

`dφ_{s,t}(ξ_s) = ξ_t`

at every point at which the flow is defined
(`TauCeti.IsContactDistributionFamily.map_mfderiv_timeDependentFlowOf`). So the time maps of the
flow are contactomorphisms between the members of the family, without any compactness and without
choosing forms.

The proof works along one trajectory at a time. Near a time `t₀` and a point `y`, choose a local
defining family `α_t` on an open set `U ∋ y`. On `U` and at times near `t₀`, `Y_t` is the Gray
vector field of `α_t`, whose flow rescales the forms by Moser's principle along a trajectory,
`φ_{a,b}^* α_b = exp (∫ₐᵇ μ_u du) α_a`
(`mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_forall_mem_uIcc`,
read on `U` through `TauCeti.timeDependentFlowOf_restrictTimeDependentField`). Hence the
differential of `φ_{a,b}` maps `ξ_a` into `ξ_b`, for all initial and final times near `t₀` and all
initial points near `y`. Along a whole trajectory, the differentials compose
(`TauCeti.mfderiv_timeDependentFlowOf_trans_of_mem`), so whether `dφ_{s,u}` maps `ξ_s` into
`ξ_u` is locally constant in the time `u`, and the times at which the flow is defined form an
interval; it therefore holds at all of them
(`TauCeti.IsContactDistributionFamily.mfderiv_timeDependentFlowOf_mem`). Applying this to the
flow back from `t` to `s` gives equality.

At a point at which the contact hyperplane does not move with time, the Gray vector field vanishes
at all times, so the constant trajectory is defined for all times. This gives **relative Gray
stability**: if the hyperplanes of the family agree along a set `K` of points, a partial
diffeomorphism defined on an open neighbourhood of `K`, fixing `K` pointwise, carries `ξ_s` to
`ξ_t` (`TauCeti.IsContactDistributionFamily.exists_partialDiffeomorph_map_mfderiv_eq`). It is
the time map of the flow (`TauCeti.IsContactDistributionFamily.grayPartialDiffeomorph`). Neither
`K` nor `M` need be compact, and `K` need not be closed. On a compact manifold the flow is
defined for all times, and its time maps form an isotopy of diffeomorphisms
(`TauCeti.IsContactDistributionFamily.grayDiffeomorph`) carrying `ξ_s` to `ξ_t`
(`TauCeti.IsContactDistributionFamily.map_mfderiv_grayDiffeomorph`).

For a family of contact forms on all of `M` this recovers the conformal part of the form-level
statement `TauCeti.SmoothForm.mpullback_grayPartialDiffeomorph_apply`; in a local defining family
`α_t`, the equality `dφ_{s,t}(ξ_s) = ξ_t` says that `φ_{s,t}^* α_t` is a nowhere-zero multiple of
`α_s` wherever both are defined.

## Main definitions

* `TauCeti.IsContactDistributionFamily.grayPartialDiffeomorph`: the flow of the Gray vector field
  from time `s` to time `t`, as a partial diffeomorphism.
* `TauCeti.IsContactDistributionFamily.grayDiffeomorph`: on a compact manifold, the same flow as a
  diffeomorphism.

## Main results

* `TauCeti.IsContactDistributionFamily.mfderiv_timeDependentFlowOf_mem`: the flow carries vectors
  of `ξ_s` to vectors of `ξ_t`.
* `TauCeti.IsContactDistributionFamily.map_mfderiv_timeDependentFlowOf`: **Gray's stability
  theorem**, `dφ_{s,t}(ξ_s) = ξ_t` where the flow is defined.
* `TauCeti.IsContactDistributionFamily.exists_partialDiffeomorph_map_mfderiv_eq`: relative Gray
  stability near a set of points with stationary contact hyperplanes.
* `TauCeti.IsContactDistributionFamily.map_mfderiv_grayDiffeomorph`: Gray's stability theorem on a
  compact manifold.
* `TauCeti.IsContactDistributionFamily.contMDiff_grayDiffeomorph`: Gray's isotopy depends smoothly
  on both times and the point.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.2.2 (Gray stability) and its proof, which works with local defining forms.
* J. W. Gray, *Some global properties of contact structures*, Ann. of Math. 69 (1959), 421–450.
-/

public section

noncomputable section

open Bundle Filter Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace TauCeti

open SmoothForm TauCeti.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {ξ : ℝ → (x : M) → Submodule ℝ (TangentSpace I x)}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
/-- Membership of a tangent vector in a family of subspaces of the tangent spaces only depends on
the base point, and on the vector read in the model space, up to equality. -/
private theorem mem_of_eq {V : (x : M) → Submodule ℝ (TangentSpace I x)} {p q : M} (h : p = q)
    {v : TangentSpace I p} {w : TangentSpace I q} (hvw : @Eq E v w) (hv : v ∈ V p) :
    w ∈ V q := by
  subst h
  -- Both vectors live in `TangentSpace I p`, which is the model space `E` by definition, as in
  -- Mathlib's `mfderiv_congr_point`; `show` reads their equality in `E` in that tangent space.
  exact (show w = v from hvw.symm) ▸ hv

namespace IsContactDistributionFamily

variable (hξ : IsContactDistributionFamily ξ)
include hξ

omit [T2Space M] in
/-- The Gray vector field of a smooth family of contact structures is `C¹`, the regularity
consumed by its time-dependent flow. -/
private theorem contMDiff_one_distributionGrayVectorField :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, distributionGrayVectorField ξ p.1 p.2⟩ : TangentBundle I M)) :=
  hξ.contMDiff_distributionGrayVectorField.of_le (by simp)

/-- **Gray's argument on a defining chart.** Let `α_u` be a local defining family of `ξ` on an
open set `U` at every time `u` between `a` and `b`. Where the flow of the Gray vector field of
`ξ`, restricted to `U`, is defined from `(a, z)` up to time `b`, its differential maps the kernel
of `α_a` at `z` into the kernel of `α_b` at the image point: on `U` the flow is that of the Gray
vector field of `α`, which rescales `α_b` back to a multiple of `α_a`. -/
private theorem mfderiv_timeDependentFlowOf_restrictTimeDependentField_mem_kerDistribution
    {U : Opens M} {α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × U) ℝ 1} {a b : ℝ}
    (hα : ∀ u ∈ uIcc a b, IsLocalContactFormFamily ξ U α u) {z : U}
    (hdom : ((a, b), z) ∈
      timeDependentFlowDomain (restrictTimeDependentField (distributionGrayVectorField ξ) U))
    {v : TangentSpace I z}
    (hv : v ∈ (SmoothForm.mpullback (Prod.mk a) (contMDiff_const.prodMk contMDiff_id)
      α).kerDistribution z) :
    mfderiv I I (timeDependentFlowOf (restrictTimeDependentField (distributionGrayVectorField ξ) U)
        a b) z v ∈
      (SmoothForm.mpullback (Prod.mk b) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution
        (timeDependentFlowOf (restrictTimeDependentField (distributionGrayVectorField ξ) U) a b
          z) := by
  set Z := restrictTimeDependentField (distributionGrayVectorField ξ) U
  have hZ : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × U ↦ (⟨p.2, Z p.1 p.2⟩ : TangentBundle I U)) :=
    (contMDiff_restrictTimeDependentField hξ.contMDiff_distributionGrayVectorField U).of_le
      (by simp)
  have hJ := uIcc_subset_setOf_mem_timeDependentFlowDomain hdom
  -- Between `a` and `b`, the Gray vector field of `ξ` on `U` is the Gray vector field of `α`.
  have hZα (u : ℝ) (hu : u ∈ uIcc a b) : Z u = α.grayVectorField u :=
    funext fun y ↦ (restrictTimeDependentField_apply U u y).trans
      (((hα u hu).distributionGrayVectorField_eq y.property).trans
        ((congrArg (fun A ↦ A (α.grayVectorField u y)) (mfderiv_subtype_val y)).trans
          (tangentSpaceOpenEquiv_apply y _)))
  -- So the flow of `Z` rescales the forms `α_u` along the trajectory of `z`, by Gray's equation.
  have hexp :=
    mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_exp_integral_smul_of_forall_mem_uIcc
      (α := α.val) hZ hdom (g := fun u ↦ α.grayRate (u, timeDependentFlowOf Z a u z))
      (fun u hu ↦ by
        have hc := contMDiffAt_grayRate (α := α) (p := (u, timeDependentFlowOf Z a u z))
          ((isLocalContactFormFamily_iff.1 (hα u hu)).mono fun _ h ↦ h.1)
        have hγ := (hasMFDerivAt_timeDependentFlowOf (hZ.of_le (by simp)) (hJ hu)).continuousAt
        refine (ContinuousAt.comp (g := α.grayRate) ?_
          (continuousAt_id.prodMk hγ)).continuousWithinAt
        exact hc.continuousAt)
      (fun _ _ ↦ (α.contMDiff.of_le (by simp)).contMDiffAt)
      (fun u hu ↦ by
        rw [hZα u hu]
        exact congrFun (mpullback_prodMk_mlieDerivForm_add_mlieDerivForm_grayVectorField
          (isLocalContactFormFamily_iff.1 (hα u hu)).self_of_nhds.1) _)
  -- Evaluate the rescaling on `v`, which `α_a` kills.
  rw [mem_kerDistribution, coe_mpullback] at hv
  have h := congrArg (fun A ↦ A ![v]) hexp
  simp only [ContinuousAlternatingMap.smul_apply] at h
  rw [hv, smul_zero, TauCeti.mpullback_apply] at h
  rw [mem_kerDistribution, coe_mpullback]
  convert h using 2
  simp only [Matrix.vec_single_eq_const]

/-- **The local step of Gray's argument.** For initial and final times near `t₀` and initial
points near `y`, the flow of the Gray vector field is defined and its differential maps the
contact hyperplane at the initial time into the contact hyperplane at the final time. Near
`(t₀, y)` the family has a local defining family of contact forms, which the flow rescales. -/
private theorem eventually_mfderiv_timeDependentFlowOf_mem (t₀ : ℝ) (y : M) :
    ∀ᶠ p in 𝓝 ((t₀, t₀), y), p ∈ timeDependentFlowDomain (distributionGrayVectorField ξ) ∧
      ∀ v ∈ ξ p.1.1 p.2,
        mfderiv I I (timeDependentFlowOf (distributionGrayVectorField ξ) p.1.1 p.1.2) p.2 v ∈
          ξ p.1.2 (timeDependentFlowOf (distributionGrayVectorField ξ) p.1.1 p.1.2 p.2) := by
  have hY₁ := hξ.contMDiff_one_distributionGrayVectorField
  obtain ⟨U, hyU, α, hα⟩ := isContactDistributionFamily_iff.1 hξ t₀ y
  set Z := restrictTimeDependentField (distributionGrayVectorField ξ) U
  have hZ : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × U ↦ (⟨p.2, Z p.1 p.2⟩ : TangentBundle I U)) :=
    (contMDiff_restrictTimeDependentField hξ.contMDiff_distributionGrayVectorField U).of_le
      (by simp)
  -- A ball of times around `t₀` at which `α` is a local defining family of `ξ`.
  obtain ⟨T, hT, hTo, ht₀⟩ :=
    eventually_nhds_iff.1 (isLocalContactFormFamily_iff.1 hα).eventually_nhds
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hTo t₀ ht₀
  have hord : (Metric.ball t₀ ε).OrdConnected := by
    rw [Real.ball_eq_Ioo]
    exact ordConnected_Ioo
  -- The triples of `U` whose two times lie in the ball and whose flow is defined, read in `M`,
  -- form a neighbourhood of `((t₀, t₀), y)`.
  set W : Set ((ℝ × ℝ) × U) := timeDependentFlowDomain Z ∩
    {q | q.1.1 ∈ Metric.ball t₀ ε ∧ q.1.2 ∈ Metric.ball t₀ ε}
  have hWo : IsOpen W := (isOpen_timeDependentFlowDomain hZ).inter
    ((Metric.isOpen_ball.preimage (by fun_prop)).inter
      (Metric.isOpen_ball.preimage (by fun_prop)))
  have hmem : ((t₀, t₀), (⟨y, hyU⟩ : U)) ∈ W :=
    ⟨mem_timeDependentFlowDomain_self hZ _ _, Metric.mem_ball_self hε, Metric.mem_ball_self hε⟩
  have hF : IsOpenMap (Prod.map id Subtype.val : (ℝ × ℝ) × U → (ℝ × ℝ) × M) :=
    IsOpenMap.id.prodMap U.isOpen.isOpenMap_subtypeVal
  filter_upwards [(hF W hWo).mem_nhds ⟨_, hmem, rfl⟩]
  rintro _ ⟨⟨⟨a, b⟩, z⟩, ⟨hdom, ha, hb⟩, rfl⟩
  simp only [Prod.map_apply, id_eq]
  obtain ⟨hdomM, hval⟩ := timeDependentFlowOf_restrictTimeDependentField hY₁ hdom
  refine ⟨hdomM, fun v hv ↦ ?_⟩
  -- Between `a` and `b`, `α` is a local defining family of `ξ`, whose kernels on `U` are `ξ`.
  have hαab (u : ℝ) (hu : u ∈ uIcc a b) : IsLocalContactFormFamily ξ U α u :=
    isLocalContactFormFamily_iff.2 (hT u (hball (hord.uIcc_subset ha hb hu)))
  -- Read `v` in the tangent space of `U`, where it lies in the kernel of `α_a`.
  obtain ⟨v', rfl⟩ : ∃ v' : TangentSpace I z, tangentSpaceOpenEquiv (I := I) z v' = v :=
    ⟨_, ContinuousLinearEquiv.apply_symm_apply _ v⟩
  have hvb := (hαab b right_mem_uIcc).mem_iff_mem_kerDistribution.2
    (hξ.mfderiv_timeDependentFlowOf_restrictTimeDependentField_mem_kerDistribution hαab hdom
      ((hαab a left_mem_uIcc).mem_iff_mem_kerDistribution.1 hv))
  -- Read the image back in `M`.
  refine mem_of_eq hval ?_ hvb
  exact (tangentSpaceOpenEquiv_apply _ _).trans
    ((mfderiv_timeDependentFlowOf_restrictTimeDependentField_apply hY₁ hdom v').trans
      (congrArg (mfderiv I I (timeDependentFlowOf (distributionGrayVectorField ξ) a b) z)
        (tangentSpaceOpenEquiv_apply z v').symm))

/-- **The flow of the Gray vector field preserves the contact structures.** If the flow of the
Gray vector field of a smooth family of contact structures is defined from `(s, x)` up to time
`t`, its differential at `x` maps every vector of `ξ_s` at `x` to a vector of `ξ_t` at the image
point. -/
theorem mfderiv_timeDependentFlowOf_mem {s t : ℝ} {x : M}
    (h : ((s, t), x) ∈ timeDependentFlowDomain (distributionGrayVectorField ξ))
    {v : TangentSpace I x} (hv : v ∈ ξ s x) :
    mfderiv I I (timeDependentFlowOf (distributionGrayVectorField ξ) s t) x v ∈
      ξ t (timeDependentFlowOf (distributionGrayVectorField ξ) s t x) := by
  have hY₁ := hξ.contMDiff_one_distributionGrayVectorField
  -- The times up to which the flow from `(s, x)` is defined form an interval `J`.
  set J : Set ℝ := {u | ((s, u), x) ∈ timeDependentFlowDomain (distributionGrayVectorField ξ)}
  let P : J → Prop := fun u ↦ ∀ w ∈ ξ s x,
    mfderiv I I (timeDependentFlowOf (distributionGrayVectorField ξ) s u) x w ∈
      ξ u (timeDependentFlowOf (distributionGrayVectorField ξ) s u x)
  -- Whether the flow from `s` preserves the contact structures is locally constant in time.
  have hP : IsLocallyConstant P := by
    refine (IsLocallyConstant.iff_eventually_eq P).2 fun u₀ ↦ ?_
    have hloc := hξ.eventually_mfderiv_timeDependentFlowOf_mem u₀
      (timeDependentFlowOf (distributionGrayVectorField ξ) s u₀ x)
    -- Forward from `u₀` to nearby times, and back from nearby times to `u₀`.
    have h₁ := (by fun_prop : Continuous fun u : ℝ ↦
      ((((u₀ : ℝ), u), timeDependentFlowOf (distributionGrayVectorField ξ) s u₀ x) :
        (ℝ × ℝ) × M)).continuousAt.eventually hloc
    have h₂ := (((continuousAt_id.prodMk continuousAt_const).prodMk
      (hasMFDerivAt_timeDependentFlowOf hY₁ u₀.property).continuousAt :
        ContinuousAt (fun u : ℝ ↦ (((u, (u₀ : ℝ)),
          timeDependentFlowOf (distributionGrayVectorField ξ) s u x) : (ℝ × ℝ) × M)) u₀)).eventually
      hloc
    filter_upwards [continuous_subtypeVal.continuousAt.eventually (h₁.and h₂)]
      with u ⟨hf, hb⟩
    -- The differentials of the flow compose along the trajectory of `x`.
    refine propext ⟨fun hPu w hw ↦ ?_, fun hPu₀ w hw ↦ ?_⟩
    · exact mem_of_eq (timeDependentFlowOf_trans_of_mem hY₁ u.property hb.1).2
        (congrArg (fun A : E →L[ℝ] E ↦ A w)
          (mfderiv_timeDependentFlowOf_trans_of_mem hY₁ u.property hb.1)).symm
        (hb.2 _ (hPu w hw))
    · exact mem_of_eq (timeDependentFlowOf_trans_of_mem hY₁ u₀.property hf.1).2
        (congrArg (fun A : E →L[ℝ] E ↦ A w)
          (mfderiv_timeDependentFlowOf_trans_of_mem hY₁ u₀.property hf.1)).symm
        (hf.2 _ (hPu₀ w hw))
  -- It holds at the initial time `s`, hence at every time of the interval `J`.
  have hs : s ∈ J := mem_timeDependentFlowDomain_self_of_mem h
  have hPs : P ⟨s, hs⟩ := fun w hw ↦
    mem_of_eq (timeDependentFlowOf_self (distributionGrayVectorField ξ) s x).symm
      (congrArg (fun A : E →L[ℝ] E ↦ A w)
        (mfderiv_timeDependentFlowOf_self (distributionGrayVectorField ξ) s x)).symm hw
  have : PreconnectedSpace J :=
    Subtype.preconnectedSpace (ordConnected_setOf_mem_timeDependentFlowDomain s x).isPreconnected
  have hst := hP.apply_eq_of_isPreconnected isPreconnected_univ (x := ⟨s, hs⟩) (y := ⟨t, h⟩)
    (mem_univ _) (mem_univ _)
  exact (hst ▸ hPs : P ⟨t, h⟩) v hv

/-- **Gray's stability theorem for families of contact structures.** Where the flow `φ_{s,t}` of
the Gray vector field of a smooth family of contact structures `ξ_t` is defined, its differential
carries `ξ_s` onto `ξ_t`: `dφ_{s,t}(ξ_s) = ξ_t`. No global defining forms, coorientation or
compactness are needed. -/
theorem map_mfderiv_timeDependentFlowOf {s t : ℝ} {x : M}
    (h : ((s, t), x) ∈ timeDependentFlowDomain (distributionGrayVectorField ξ)) :
    (ξ s x).map
        (mfderiv I I (timeDependentFlowOf (distributionGrayVectorField ξ) s t) x).toLinearMap =
      ξ t (timeDependentFlowOf (distributionGrayVectorField ξ) s t x) := by
  have hY₁ := hξ.contMDiff_one_distributionGrayVectorField
  refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun v hv ↦
    hξ.mfderiv_timeDependentFlowOf_mem h hv) fun w hw ↦ ?_
  -- A vector of `ξ_t` is the image of its image under the flow back from `t` to `s`.
  obtain ⟨hback, hxy⟩ := timeDependentFlowOf_symm_of_mem hY₁ h
  have hv := mem_of_eq hxy rfl (hξ.mfderiv_timeDependentFlowOf_mem hback hw)
  -- Flowing from `t` back to `s` and forward to `t` again is the identity, to first order.
  refine ⟨_, hv, ?_⟩
  have h₁ := congrArg (fun A : E →L[ℝ] E ↦ A w)
    (mfderiv_timeDependentFlowOf_self (distributionGrayVectorField ξ) t
      (timeDependentFlowOf (distributionGrayVectorField ξ) s t x))
  have h₂ := congrArg (fun A : E →L[ℝ] E ↦ A w)
    (mfderiv_timeDependentFlowOf_trans_of_mem hY₁ hback (by rw [hxy]; exact h))
  have h₃ := congrArg (fun A : E →L[ℝ] E ↦
      A (mfderiv I I (timeDependentFlowOf (distributionGrayVectorField ξ) t s)
        (timeDependentFlowOf (distributionGrayVectorField ξ) s t x) w))
    (mfderiv_congr_point (I := I) (I' := I)
      (f := timeDependentFlowOf (distributionGrayVectorField ξ) s t) hxy)
  exact h₃.symm.trans (h₂.symm.trans h₁)

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
  rw [show ⇑(hξ.grayPartialDiffeomorph s t) =
      timeDependentFlowOf (distributionGrayVectorField ξ) s t from
    funext (hξ.grayPartialDiffeomorph_apply s t)]
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
  exact timeDependentFlowOf_eq_self_of_forall_eq_zero hξ.contMDiff_one_distributionGrayVectorField
    (hξ.distributionGrayVectorField_eq_zero_of_forall_eq hx) s t

/-- **Relative Gray stability for contact structures.** Let `ξ_t` be a smooth family of contact
structures on a boundaryless manifold, and let `K` be a set of points at each of which the contact
hyperplane `ξ_u` is the same for all times. Then for all times `s` and `t` there is a smooth
partial diffeomorphism `φ` of `M`, whose source and target are open neighbourhoods of `K`, which
fixes every point of `K` and carries `ξ_s` onto `ξ_t` at every point of its source. It is Gray's
partial isotopy `TauCeti.IsContactDistributionFamily.grayPartialDiffeomorph`. No global defining
form or coorientation of `ξ_t` is used, `K` and `M` need not be compact, and `K` need not be
closed. -/
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
  isCompleteVectorField_timeDependentSuspensionField hξ.contMDiff_one_distributionGrayVectorField
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
    hξ.contMDiff_one_distributionGrayVectorField r s t x

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
  rw [show ⇑(hξ.grayDiffeomorph s t) = timeDependentFlowOf (distributionGrayVectorField ξ) s t from
    funext (hξ.grayDiffeomorph_apply s t)]
  exact hξ.map_mfderiv_timeDependentFlowOf ((timeDependentFlowDomain_eq_univ
    hξ.isCompleteVectorField_timeDependentSuspensionField_distributionGrayVectorField).symm ▸
      mem_univ _)

/-- Gray's isotopy fixes every point at which the contact hyperplane `ξ_u` is the same for all
times. -/
theorem grayDiffeomorph_apply_eq_self {x : M} (hx : ∀ u, ξ u x = ξ 0 x) (s t : ℝ) :
    hξ.grayDiffeomorph s t x = x := by
  rw [grayDiffeomorph_apply]
  exact timeDependentFlowOf_eq_self_of_forall_eq_zero hξ.contMDiff_one_distributionGrayVectorField
    (hξ.distributionGrayVectorField_eq_zero_of_forall_eq hx) s t

end IsContactDistributionFamily

end TauCeti
