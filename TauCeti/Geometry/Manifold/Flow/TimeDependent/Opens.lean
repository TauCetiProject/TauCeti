/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Time-dependent flows on open subsets

Let `X` be a time-dependent vector field on a manifold `M` and let `U` be an open subset. Read in
the tangent spaces of `U` through `TauCeti.Manifold.tangentSpaceOpenEquiv`, the values of `X` at
the points of `U` form a time-dependent vector field on `U`, the restriction `X|_U`
(`TauCeti.restrictTimeDependentField`). It is as regular as `X`
(`TauCeti.contMDiff_restrictTimeDependentField`), so it has a time-dependent flow on `U`.

That flow is the flow of `X`, for as long as it stays in `U`: if the flow of `X|_U` from `(s, z)` is
defined up to time `t`, then so is the flow of `X` from `(s, z)`, and the two flows agree at time
`t` (`TauCeti.timeDependentFlowOf_restrictTimeDependentField`). Their differentials then agree
too (`TauCeti.mfderiv_timeDependentFlowOf_restrictTimeDependentField_apply`).

This lets a computation which only makes sense on `U`, such as one using a differential form
defined on `U` alone, be carried out along the trajectories of `X` while they stay in `U`.

## Main definitions

* `TauCeti.restrictTimeDependentField X U`: the restriction of `X` to the open subset `U`.

## Main results

* `TauCeti.contMDiff_restrictTimeDependentField`: the restriction is as regular as the field.
* `TauCeti.timeDependentFlowOf_restrictTimeDependentField`: the flow of the restriction is the
  flow of the field, wherever the former is defined.
* `TauCeti.mfderiv_timeDependentFlowOf_restrictTimeDependentField_apply`: the same for the
  differentials of the time maps.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 9.48
  (time-dependent flows) and Proposition 9.6 (naturality of integral curves).
-/

public section

noncomputable section

open Set Filter Bundle TopologicalSpace TauCeti.Manifold
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {X : ℝ → (x : M) → TangentSpace I x}

/-- The **restriction of a time-dependent vector field** `X` on `M` to an open subset `U`: at time
`t` and at `z ∈ U` it is `X t z`, read in the tangent space of `U` at `z`. -/
def restrictTimeDependentField (X : ℝ → (x : M) → TangentSpace I x) (U : Opens M) (t : ℝ)
    (z : U) : TangentSpace I z :=
  (tangentSpaceOpenEquiv (I := I) z).symm (X t z)

/-- The restriction of a time-dependent vector field to an open subset takes the values of the
field, read in the common model space of the tangent spaces. -/
@[simp]
theorem restrictTimeDependentField_apply (U : Opens M) (t : ℝ) (z : U) :
    restrictTimeDependentField X U t z = X t z :=
  tangentSpaceOpenEquiv_symm_apply z _

/-- **The restriction of a `C^n` time-dependent vector field to an open subset is `C^n`.** In the
charts of `U`, which are restrictions of those of `M`, the restriction has the same tangent
coordinates as the field. -/
theorem contMDiff_restrictTimeDependentField [IsManifold I 1 M] {n : ℕ∞ω}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M))) (U : Opens M) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun p : ℝ × U ↦ (⟨p.2, restrictTimeDependentField X U p.1 p.2⟩ : TangentBundle I U)) := by
  rintro ⟨t₀, z₀⟩
  -- The field, read at the points of `U` in the tangent bundle of `M`, is `C^n`.
  have h := (hX (t₀, z₀)).comp (t₀, z₀)
    (contMDiff_fst.prodMk (contMDiff_subtypeVal.comp contMDiff_snd)).contMDiffAt
  rw [contMDiffAt_totalSpace_iff] at h ⊢
  refine ⟨contMDiffAt_snd, h.2.congr_of_eventuallyEq ?_⟩
  -- Near `z₀`, the tangent coordinates of `U` and of `M` agree.
  set eU := trivializationAt E (TangentSpace I : U → Type _) z₀
  set eM := trivializationAt E (TangentSpace I : M → Type _) (z₀ : M)
  have hz : ∀ᶠ z in 𝓝 z₀, z ∈ eU.baseSet ∧ (z : M) ∈ eM.baseSet ∧ ∀ w : E,
      tangentSpaceOpenEquiv (I := I) z (eU.symmL ℝ z w) = eM.symmL ℝ (z : M) w := by
    filter_upwards [eU.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E _ z₀),
      continuousAt_subtypeVal.eventually (eM.open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E _ (z₀ : M))),
      eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq (I := I) z₀]
      with z hzU hzM hsymm
    exact ⟨hzU, hzM, hsymm⟩
  filter_upwards [continuousAt_snd.eventually hz] with p hp
  obtain ⟨hzU, hzM, hsymm⟩ := hp
  -- Both coordinates are the vector `w` whose inverse images under the two trivializations are
  -- the value of the field.
  set w := (eM ⟨(p.2 : M), X p.1 p.2⟩).2
  have hw : eU.symm p.2 w = restrictTimeDependentField X U p.1 p.2 := by
    have h₁ := hsymm w
    rw [Trivialization.symmL_apply _ hzU, Trivialization.symmL_apply _ hzM,
      eM.symm_apply_apply_mk hzM] at h₁
    rw [restrictTimeDependentField, ContinuousLinearEquiv.eq_symm_apply]
    exact h₁
  -- The two coordinate functions are composites with the projections of `ℝ × U`; `change`
  -- evaluates them at `p`, which no rewrite lemma for the composite with `Prod.snd` exposes.
  change (eU ⟨p.2, restrictTimeDependentField X U p.1 p.2⟩).2 = (eM ⟨(p.2 : M), X p.1 p.2⟩).2
  rw [← hw, eU.apply_mk_symm hzU]

variable [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
include hX

/-- **The flow of the restriction is the flow of the field.** If the time-dependent flow of the
restriction of `X` to an open subset `U` is defined from `(s, z)` up to time `t`, then so is the
time-dependent flow of `X`, and the two agree at time `t`. -/
theorem timeDependentFlowOf_restrictTimeDependentField {U : Opens M} {s t : ℝ} {z : U}
    (h : ((s, t), z) ∈ timeDependentFlowDomain (restrictTimeDependentField X U)) :
    ((s, t), (z : M)) ∈ timeDependentFlowDomain X ∧
      ((timeDependentFlowOf (restrictTimeDependentField X U) s t z : U) : M) =
        timeDependentFlowOf X s t z := by
  have hXU := contMDiff_restrictTimeDependentField hX U
  obtain ⟨a, b, hs, ht, hab⟩ := exists_Ioo_of_mem_timeDependentFlowDomain h
  -- The trajectory of `X|_U`, read in `M`, solves the equation of `X`.
  have hγ (u : ℝ) (hu : u ∈ Ioo a b) : HasMFDerivAt 𝓘(ℝ, ℝ) I
      (fun u ↦ ((timeDependentFlowOf (restrictTimeDependentField X U) s u z : U) : M)) u
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (X u ((timeDependentFlowOf (restrictTimeDependentField X U) s u z : U) : M))) := by
    have h₁ := hasMFDerivAt_timeDependentFlowOf hXU (hab u hu)
    have h₂ := (contMDiff_subtypeVal (I := I) (n := 1) (U := U)).mdifferentiableAt one_ne_zero
      (x := timeDependentFlowOf (restrictTimeDependentField X U) s u z)
    refine (h₂.hasMFDerivAt.comp u h₁).congr_mfderiv (ContinuousLinearMap.ext fun r ↦ ?_)
    simp only [mfderiv_subtype_val, restrictTimeDependentField_apply]
    exact tangentSpaceOpenEquiv_apply _ _
  have hγs : ((timeDependentFlowOf (restrictTimeDependentField X U) s s z : U) : M) = z := by
    rw [timeDependentFlowOf_self]
  refine ⟨hγs ▸ mem_timeDependentFlowDomain_of_hasMFDerivAt hγ hs ht, ?_⟩
  have h := timeDependentFlowOf_eq_of_hasMFDerivAt hX hγ hs ht
  rw [hγs] at h
  exact h.symm

/-- **The differentials of the flow of the restriction are those of the flow of the field.** In
finite dimensions, if the time-dependent flow of the restriction of `X` to an open subset `U` is
defined from `(s, z)` up to time `t`, the differentials at `z` of its time map and of the time map
of `X` agree, on the common model space of the tangent spaces. -/
theorem mfderiv_timeDependentFlowOf_restrictTimeDependentField_apply [FiniteDimensional ℝ E]
    {U : Opens M} {s t : ℝ} {z : U}
    (h : ((s, t), z) ∈ timeDependentFlowDomain (restrictTimeDependentField X U))
    (v : TangentSpace I z) :
    mfderiv I I (timeDependentFlowOf (restrictTimeDependentField X U) s t) z v =
      mfderiv I I (timeDependentFlowOf X s t) z v := by
  have hXU := contMDiff_restrictTimeDependentField hX U
  -- Near `z`, the flow of `X|_U` read in `M` is the flow of `X` read at the points of `U`.
  have heq : Subtype.val ∘ timeDependentFlowOf (restrictTimeDependentField X U) s t =ᶠ[𝓝 z]
      timeDependentFlowOf X s t ∘ Subtype.val := by
    filter_upwards [((isOpen_timeDependentFlowDomain hXU).preimage
      (by fun_prop : Continuous fun y : U ↦ ((s, t), y))).mem_nhds h] with y hy
    exact (timeDependentFlowOf_restrictTimeDependentField hX hy).2
  have hd : HasMFDerivAt I I (timeDependentFlowOf X s t ∘ Subtype.val) z
      ((mfderiv I I (timeDependentFlowOf X s t) z).comp (mfderiv I I (Subtype.val : U → M) z)) :=
    (mdifferentiableAt_timeDependentFlowOf hX
      (timeDependentFlowOf_restrictTimeDependentField hX h).1).hasMFDerivAt.comp z
      ((contMDiff_subtypeVal (I := I) (n := 1) (U := U)).mdifferentiableAt one_ne_zero).hasMFDerivAt
  rw [← mfderiv_subtype_val_comp_apply, (hd.congr_of_eventuallyEq heq).mfderiv]
  simp only [ContinuousLinearMap.comp_apply, mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
    tangentSpaceOpenEquiv_apply]
  -- Both sides apply the differential of the flow of `X` to `v`, once read in `TangentSpace I z`
  -- and once in `TangentSpace I ↑z`. Both tangent spaces are the model space `E` by definition,
  -- as in Mathlib's `mfderiv_congr_point`, so the two vectors are the same.
  rfl

end TauCeti
