/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Gray.Distribution
public import TauCeti.Geometry.Manifold.Flow.TimeDependent.Opens
import TauCeti.Analysis.ODE.ScalarLinear

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
(`TauCeti.IsContactDistributionFamily.exists_partialDiffeomorph_map_mfderiv_eq`). On a compact
manifold the flow is a global isotopy
(`TauCeti.IsContactDistributionFamily.exists_diffeomorph_map_mfderiv_eq`).

The proof is local in time and space. Near a time `u₀` and a point `y₀`, the contact structures
are the kernels of a local defining family `α_t` on an open set `U`, contact for the times of an
interval `T` around `u₀`. On `U` the Gray vector field is that of `α_t`, so Gray's equation
`L_{Y_t} α_t + ∂_t α_t = μ_t α_t` holds there at the times of `T`, and along the flow it integrates
to `φ_{s,t}^* α_t = exp (∫ₛᵗ μ_u ∘ φ_{s,u} du) α_s` for `s, t ∈ T`
(`TauCeti.SmoothForm.mpullback_timeDependentFlowOf_apply_eq_exp_integral_grayRate_smul`). Hence
the flow maps `ker α_s` into `ker α_t` for nearby times. The flow on `U` is the flow on `M`
(`TauCeti.timeDependentFlowOf_restrict_opens`), and the two-time composition law propagates the
local statement along a whole trajectory, by connectedness of its interval of times.

## Main results

* `TauCeti.SmoothForm.mpullback_timeDependentFlowOf_apply_eq_exp_integral_grayRate_smul`: Gray's
  stability theorem for a family of one-forms which are contact forms on an interval of times,
  along a trajectory.
* `TauCeti.IsContactDistributionFamily.map_mfderiv_timeDependentFlowOf`: the flow of the Gray
  vector field carries `ξ_s` to `ξ_t`.
* `TauCeti.IsContactDistributionFamily.exists_partialDiffeomorph_map_mfderiv_eq`: relative Gray
  stability near a set of points with stationary contact hyperplanes.
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

/-! ### Gray's stability theorem on an interval of times -/

namespace SmoothForm

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace N]
  [ChartedSpace H N] [T2Space N] [IsManifold I ∞ N]
  {α : SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × N) ℝ 1} {T : Set ℝ}
  {Z : ℝ → (x : N) → TangentSpace I x}

/-- **Gray's stability theorem on an interval of times, along a trajectory.** Let `α_t` be a smooth
family of one-forms whose slices are contact forms at the times of an open interval `T`, and let
`Z` be a jointly `C²` time-dependent vector field which is the Gray vector field of `α` at the
times of `T`. If the flow `φ` of `Z` runs from `(s, x)` up to time `t`, with `s, t ∈ T`, then it
rescales the forms: `(φ_{s,t}^* α_t)ₓ = exp (∫ₛᵗ μ_u(φ_{s,u} x) du) (α_s)ₓ`, where
`μ_u = (∂_t α_u)(R_{α_u})` is the Gray rate. -/
theorem mpullback_timeDependentFlowOf_apply_eq_exp_integral_grayRate_smul (hT : IsOpen T)
    (hTc : T.OrdConnected)
    (hc : ∀ t ∈ T, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
    (hZ : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × N ↦ (⟨p.2, Z p.1 p.2⟩ : TangentBundle I N)))
    (hZα : ∀ t ∈ T, Z t = α.grayVectorField t) {s t : ℝ} {x : N} (hs : s ∈ T) (ht : t ∈ T)
    (h : ((s, t), x) ∈ timeDependentFlowDomain Z) :
    TauCeti.mpullback I I (timeDependentFlowOf Z s t)
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).val x =
      Real.exp (∫ u in s..t, α.grayRate (u, timeDependentFlowOf Z s u x)) •
        (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).val x := by
  -- The times `u ∈ T` up to which the flow from `(s, x)` is defined form an interval `J`.
  set J : Set ℝ := {u | ((s, u), x) ∈ timeDependentFlowDomain Z} ∩ T
  have hJ : J.OrdConnected := (ordConnected_setOf_mem_timeDependentFlowDomain s x).inter hTc
  have hflow : ContinuousOn (fun u ↦ timeDependentFlowOf Z s u x)
      {u | ((s, u), x) ∈ timeDependentFlowDomain Z} :=
    (contMDiffOn_timeDependentFlowOf (n := 2) (by norm_num) hZ).continuousOn.comp
      (by fun_prop : Continuous fun u : ℝ ↦ ((s, u), x)).continuousOn fun _ hu ↦ hu
  -- The Gray rate along the trajectory is continuous on `J`.
  have hg : ContinuousOn (fun u ↦ α.grayRate (u, timeDependentFlowOf Z s u x)) J := fun u hu ↦
    (contMDiffAt_grayRate (Filter.eventually_of_mem (hT.mem_nhds hu.2) hc)).continuousAt
      |>.comp_continuousWithinAt
        (continuousWithinAt_id.prodMk ((hflow u hu.1).mono inter_subset_left))
  -- The pullbacks at `x`, as alternating maps on the model space, solve `P' = μ P` on `J`.
  have hP (u : ℝ) (hu : u ∈ J) : HasDerivAt (F := E [⋀^Fin 1]→L[ℝ] ℝ)
      (fun u ↦ TauCeti.mpullback I I (timeDependentFlowOf Z s u)
        (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).val x)
      (α.grayRate (u, timeDependentFlowOf Z s u x) •
        TauCeti.mpullback I I (timeDependentFlowOf Z s u)
          (mpullback (Prod.mk u) (contMDiff_const.prodMk contMDiff_id) α).val x) u := by
    have h := hasDerivAt_mpullback_timeDependentFlowOf_mpullback_prodMk hZ hu.1
      (α.contMDiff.of_le (by simp)).contMDiffAt
    rw [hZα u hu.2, mpullback_prodMk_mlieDerivForm_add_mlieDerivForm_grayVectorField (hc u hu.2),
      mpullback_fun_smul] at h
    beta_reduce at h
    simp only [coe_mpullback]
    exact h
  have hP₀ : TauCeti.mpullback I I (timeDependentFlowOf Z s s)
      (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).val x =
        (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).val x := by
    have hid : timeDependentFlowOf Z s s = id := funext (timeDependentFlowOf_self Z s)
    rw [hid, TauCeti.mpullback_id]
  rw [← hP₀]
  exact eq_exp_integral_smul_of_hasDerivWithinAt_smul (V := E [⋀^Fin 1]→L[ℝ] ℝ) hJ hg
    (fun u hu ↦ (hP u hu).hasDerivWithinAt)
    ⟨mem_timeDependentFlowDomain_self (hZ.of_le (by norm_num)) s x, hs⟩ ⟨h, ht⟩

/-- **The flow of the Gray vector field carries the kernels of a family of contact forms into each
other, on an interval of times.** Under the hypotheses of
`TauCeti.SmoothForm.mpullback_timeDependentFlowOf_apply_eq_exp_integral_grayRate_smul`, the
differential of the flow from `s` to `t` at `x` maps a tangent vector into `ker α_t` exactly when
the vector lies in `ker α_s`. -/
theorem mfderiv_timeDependentFlowOf_mem_kerDistribution_iff (hT : IsOpen T)
    (hTc : T.OrdConnected)
    (hc : ∀ t ∈ T, (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).IsContactForm)
    (hZ : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × N ↦ (⟨p.2, Z p.1 p.2⟩ : TangentBundle I N)))
    (hZα : ∀ t ∈ T, Z t = α.grayVectorField t) {s t : ℝ} {x : N} (hs : s ∈ T) (ht : t ∈ T)
    (h : ((s, t), x) ∈ timeDependentFlowDomain Z) {v : TangentSpace I x} :
    mfderiv I I (timeDependentFlowOf Z s t) x v ∈
        (mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution
          (timeDependentFlowOf Z s t x) ↔
      v ∈ (mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) α).kerDistribution x := by
  have h₁ := congrArg (· ![v])
    (mpullback_timeDependentFlowOf_apply_eq_exp_integral_grayRate_smul hT hTc hc hZ hZα hs ht h)
  rw [TauCeti.mpullback_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h₁
  rw [mem_kerDistribution, mem_kerDistribution]
  -- The two evaluations differ by the positive factor `exp (∫ₛᵗ μ_u ∘ φ_{s,u} du)`.
  have hv : (fun i ↦ mfderiv I I (timeDependentFlowOf Z s t) x (![v] i)) =
      ![mfderiv I I (timeDependentFlowOf Z s t) x v] := by
    ext i
    fin_cases i
    rfl
  rw [hv] at h₁
  rw [h₁, mul_eq_zero, or_iff_right (Real.exp_pos _).ne']

end SmoothForm

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

omit hξ in
/-- **Propagation along a trajectory.** Let `Y` be a jointly `C¹` time-dependent vector field whose
flow, over short times, maps each hyperplane `ξ_{u₀}` into `ξ_u` and back. Then along every
trajectory the differential of the flow from `s` to `t` maps `ξ_s` into `ξ_t`: the times of the
trajectory form an interval, and the two-time composition law chains the short steps. -/
private theorem mfderiv_timeDependentFlowOf_mem_of_eventually {Y : ℝ → (x : M) → TangentSpace I x}
    (hY : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, Y p.1 p.2⟩ : TangentBundle I M)))
    (hloc : ∀ u₀ y₀, ∀ᶠ u in 𝓝 u₀,
      (∀ v ∈ ξ u₀ y₀, mfderiv I I (timeDependentFlowOf Y u₀ u) y₀ v ∈
        ξ u (timeDependentFlowOf Y u₀ u y₀)) ∧
      ∀ v ∈ ξ u (timeDependentFlowOf Y u₀ u y₀),
        mfderiv I I (timeDependentFlowOf Y u u₀) (timeDependentFlowOf Y u₀ u y₀) v ∈ ξ u₀ y₀)
    {s t : ℝ} {x : M} (h : ((s, t), x) ∈ timeDependentFlowDomain Y) :
    ∀ v ∈ ξ s x,
      mfderiv I I (timeDependentFlowOf Y s t) x v ∈ ξ t (timeDependentFlowOf Y s t x) := by
  -- The times at which the trajectory of `x` from time `s` is defined form an interval `J`.
  set J := {u | ((s, u), x) ∈ timeDependentFlowDomain Y}
  -- Between two times of `J`, the flow is defined along the trajectory and follows it.
  have hJ (a : ℝ) (ha : a ∈ J) (b : ℝ) (hb : b ∈ J) :
      ((a, b), timeDependentFlowOf Y s a x) ∈ timeDependentFlowDomain Y ∧
        timeDependentFlowOf Y a b (timeDependentFlowOf Y s a x) = timeDependentFlowOf Y s b x := by
    obtain ⟨h₁, h₂⟩ := timeDependentFlowOf_symm_of_mem hY ha
    have h₃ : ((s, b), timeDependentFlowOf Y a s (timeDependentFlowOf Y s a x)) ∈
        timeDependentFlowDomain Y := by
      rw [h₂]
      exact hb
    obtain ⟨h₄, h₅⟩ := timeDependentFlowOf_trans_of_mem hY h₁ h₃
    exact ⟨h₄, by rw [← h₅, h₂]⟩
  -- `P a b`: the differential of the flow from `a` to `b` maps `ξ_a` into `ξ_b` at the point of
  -- the trajectory at time `a`.
  let P : ℝ → ℝ → Prop := fun a b ↦ ∀ y, y = timeDependentFlowOf Y s a x → ∀ v ∈ ξ a y,
    mfderiv I I (timeDependentFlowOf Y a b) y v ∈ ξ b (timeDependentFlowOf Y s b x)
  have hP : P s t := by
    refine (ordConnected_setOf_mem_timeDependentFlowDomain s x).isPreconnected.induction₂' P
      (fun u₀ hu₀ ↦ ?_) (fun a b c ha hb hc hab hbc ↦ ?_)
      (mem_timeDependentFlowDomain_self_of_mem h) h
    · filter_upwards [nhdsWithin_le_nhds (hloc u₀ (timeDependentFlowOf Y s u₀ x)),
        self_mem_nhdsWithin] with u hu huJ
      rw [(hJ u₀ hu₀ u huJ).2] at hu
      exact ⟨fun y hy ↦ hy ▸ hu.1, fun y hy ↦ hy ▸ hu.2⟩
    · -- The chain rule for the composition law `φ_{b,c} ∘ φ_{a,b} = φ_{a,c}`.
      rintro y rfl v hv
      have hdom := hJ b hb c hc
      rw [← (hJ a ha b hb).2] at hdom
      have e := mfderiv_timeDependentFlowOf_trans_of_mem hY (hJ a ha b hb).1 hdom.1
      rw [(hJ a ha b hb).2] at e
      rw [e]
      -- The composite of the two differentials, applied to `v`.
      exact hbc _ rfl _ (hab _ rfl v hv)
  exact hP x (timeDependentFlowOf_self Y s x).symm

/-- **The flow of the Gray vector field carries the contact structures into each other.** If the
flow `φ` of the Gray vector field of a smooth family of contact structures `ξ` on a boundaryless
manifold runs from `(s, x)` up to time `t`, then its differential at `x` maps the hyperplane `ξ_s`
at `x` onto the hyperplane `ξ_t` at `φ_{s,t} x`. No compactness, global defining form or
coorientation is needed. -/
theorem map_mfderiv_timeDependentFlowOf {s t : ℝ} {x : M}
    (h : ((s, t), x) ∈ timeDependentFlowDomain (distributionGrayVectorField ξ)) :
    (ξ s x).map
        (mfderiv I I (timeDependentFlowOf (distributionGrayVectorField ξ) s t) x).toLinearMap =
      ξ t (timeDependentFlowOf (distributionGrayVectorField ξ) s t x) := by
  have hY := hξ.contMDiff_distributionGrayVectorField.of_le (m := 1) (by simp)
  have hloc := eventually_mfderiv_timeDependentFlowOf_mem hξ
  refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun v hv ↦
    mfderiv_timeDependentFlowOf_mem_of_eventually hY hloc h v hv) fun w hw ↦ ?_
  -- Flowing back from `t` to `s` maps `ξ_t` into `ξ_s`, and its differential inverts that of the
  -- flow from `s` to `t`.
  obtain ⟨hb, hb'⟩ := timeDependentFlowOf_symm_of_mem hY h
  have hw' := mfderiv_timeDependentFlowOf_mem_of_eventually hY hloc hb w hw
  rw [hb'] at hw'
  have hcomp := mfderiv_timeDependentFlowOf_trans_of_mem hY hb (by rwa [hb'])
  rw [mfderiv_timeDependentFlowOf_self] at hcomp
  have hinv : w = mfderiv I I (timeDependentFlowOf (distributionGrayVectorField ξ) s t)
      (timeDependentFlowOf (distributionGrayVectorField ξ) t s
        (timeDependentFlowOf (distributionGrayVectorField ξ) s t x))
      (mfderiv I I (timeDependentFlowOf (distributionGrayVectorField ξ) t s)
        (timeDependentFlowOf (distributionGrayVectorField ξ) s t x) w) :=
    congrArg (fun L ↦ L w) hcomp
  rw [hb'] at hinv
  exact Submodule.mem_map.2 ⟨_, hw', hinv.symm⟩

/-- **Relative Gray stability for contact structures.** Let `ξ_t` be a smooth family of contact
structures on a boundaryless manifold, and let `K` be a set of points at each of which the contact
hyperplane `ξ_t` is the same for all times. Then for all times `s` and `t` there is a smooth partial
diffeomorphism `φ` of `M`, whose source and target are open neighbourhoods of `K`, which fixes
every point of `K` and whose differential carries `ξ_s` onto `ξ_t` at every point of its source.
It is the flow of the Gray vector field from `s` to `t`. Neither `K` nor `M` need be compact, `K`
need not be closed, and no global defining form or coorientation of `ξ` is needed. -/
theorem exists_partialDiffeomorph_map_mfderiv_eq {K : Set M} (hK : ∀ x ∈ K, ∀ u, ξ u x = ξ 0 x)
    (s t : ℝ) :
    ∃ φ : PartialDiffeomorph I I M M ∞, K ⊆ φ.source ∧ K ⊆ φ.target ∧ (∀ x ∈ K, φ x = x) ∧
      ∀ x ∈ φ.source, (ξ s x).map (mfderiv I I φ x).toLinearMap = ξ t (φ x) := by
  have hY := hξ.contMDiff_distributionGrayVectorField
  -- The Gray vector field vanishes at the points of `K` at all times.
  have hzero (x : M) (hx : x ∈ K) (u : ℝ) : distributionGrayVectorField ξ u x = 0 :=
    hξ.distributionGrayVectorField_eq_zero (.of_forall fun v ↦ (hK x hx v).trans (hK x hx u).symm)
  have hφ : ⇑(timeDependentFlowPartialDiffeomorph le_top hY s t) =
      timeDependentFlowOf (distributionGrayVectorField ξ) s t :=
    funext (timeDependentFlowPartialDiffeomorph_apply _ _ s t)
  refine ⟨timeDependentFlowPartialDiffeomorph le_top hY s t, fun x hx ↦ ?_, fun x hx ↦ ?_,
    fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · exact (mem_timeDependentFlowPartialDiffeomorph_source_iff _ _).2
      (mem_timeDependentFlowDomain_of_forall_eq_zero (hzero x hx) s t)
  · exact (mem_timeDependentFlowPartialDiffeomorph_target_iff _ _).2
      (mem_timeDependentFlowDomain_of_forall_eq_zero (hzero x hx) t s)
  · rw [hφ]
    exact timeDependentFlowOf_eq_self_of_forall_eq_zero (hY.of_le (by simp)) (hzero x hx) s t
  · rw [hφ]
    exact hξ.map_mfderiv_timeDependentFlowOf
      ((mem_timeDependentFlowPartialDiffeomorph_source_iff _ _).1 hx)

/-- **Gray's stability theorem for contact structures.** On a compact boundaryless manifold, a
smooth family of contact structures `ξ_t` is carried along by an isotopy: there are diffeomorphisms
`φ_{s,t}`, jointly smooth in both times and the point, with `φ_{s,s} = id`, whose differentials
carry `ξ_s` onto `ξ_t`. They are the flow of the Gray vector field. No global defining form or
coorientation of `ξ` is needed. -/
theorem exists_diffeomorph_map_mfderiv_eq [CompactSpace M] :
    ∃ φ : ℝ → ℝ → M ≃ₘ⟮I, I⟯ M,
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞ (fun p : (ℝ × ℝ) × M ↦ φ p.1.1 p.1.2 p.2) ∧
        (∀ s x, φ s s x = x) ∧
        ∀ s t x, (ξ s x).map (mfderiv I I (φ s t) x).toLinearMap = ξ t (φ s t x) := by
  have hY := hξ.contMDiff_distributionGrayVectorField
  have hc := isCompleteVectorField_timeDependentSuspensionField (hY.of_le (by simp))
    isCompact_univ (by simp)
  have hφ (s t : ℝ) : ⇑(timeDependentFlowDiffeomorph hc le_top hY s t) =
      timeDependentFlowOf (distributionGrayVectorField ξ) s t :=
    funext (timeDependentFlowDiffeomorph_apply _ _ _ s t)
  refine ⟨timeDependentFlowDiffeomorph hc le_top hY, ?_, fun s x ↦ ?_, fun s t x ↦ ?_⟩
  · simp only [hφ]
    exact contMDiff_timeDependentFlowOf hc le_top hY
  · rw [hφ, timeDependentFlowOf_self]
  · rw [hφ]
    exact hξ.map_mfderiv_timeDependentFlowOf (timeDependentFlowDomain_eq_univ hc ▸ mem_univ _)

end IsContactDistributionFamily


end TauCeti
