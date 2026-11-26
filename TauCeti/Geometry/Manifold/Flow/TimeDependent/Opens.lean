/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Restriction

/-!
# Time-dependent flows on open submanifolds

Let `X` be a time-dependent vector field on a manifold `M` and `U` an open subset of `M`. The
tangent spaces of `U` are those of `M`, so `X` restricts to a time-dependent vector field on `U`,
with the same values. This file compares the two.

* Restriction preserves regularity: a jointly `C^n` time-dependent field restricts to a jointly
  `C^n` field on `U` (`TauCeti.contMDiff_timeDependentField_opens`).
* The flow of the restriction is the flow of `X`, as long as it is defined: if the flow of the
  restriction runs from `(s, x)` up to time `t`, so does the flow of `X`, and the two agree
  (`TauCeti.timeDependentFlowOf_restrict_opens`). Their differentials agree as well
  (`TauCeti.mfderiv_timeDependentFlowOf_restrict_opens_apply`).

So local computations with a flow, for instance with forms only defined on `U`, may be carried out
on the open submanifold `U` and then transferred to `M`.
-/

public section

noncomputable section

open Set Filter Bundle TopologicalSpace
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {U : Opens M}

section Regularity

variable [IsManifold I 1 M]

/-- **A jointly `C^n` time-dependent vector field restricts to a jointly `C^n` field on every open
submanifold.** -/
theorem contMDiff_timeDependentField_opens {n : ℕ∞ω} {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M))) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun p : ℝ × U ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I U)) := fun p ↦
  Manifold.contMDiffAt_tangentBundle_opens_iff.2 ((hX _).comp p
    (contMDiff_fst.prodMk (contMDiff_subtypeVal.comp contMDiff_snd)).contMDiffAt)

end Regularity

section Flow

variable [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  {X : ℝ → (x : M) → TangentSpace I x}
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
  {s t : ℝ} {y : U}
include hX

/-- **The flow of a restriction to an open submanifold is the ambient flow.** If the flow of the
restriction of `X` to an open submanifold `U` runs from `(s, y)` up to time `t`, then so does the
flow of `X`, and the two flows agree at time `t`. -/
theorem timeDependentFlowOf_restrict_opens
    (h : ((s, t), y) ∈ timeDependentFlowDomain (I := I) (M := U) (fun u z ↦ X u z)) :
    ((s, t), (y : M)) ∈ timeDependentFlowDomain X ∧
      (timeDependentFlowOf (I := I) (M := U) (fun u z ↦ X u z) s t y : M) =
        timeDependentFlowOf X s t y := by
  have hXU := contMDiff_timeDependentField_opens (U := U) hX
  obtain ⟨a, b, hs, ht, hab⟩ := exists_Ioo_of_mem_timeDependentFlowDomain h
  -- The trajectory of the restriction, read in `M`, solves the equation of `X`.
  have hγ (u : ℝ) (hu : u ∈ Ioo a b) : HasMFDerivAt 𝓘(ℝ, ℝ) I
      (fun u ↦ (timeDependentFlowOf (I := I) (M := U) (fun u z ↦ X u z) s u y : M)) u
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (X u (timeDependentFlowOf (I := I) (M := U) (fun u z ↦ X u z) s u y))) := by
    have hc := hasMFDerivAt_timeDependentFlowOf hXU (hab u hu)
    refine ((contMDiff_subtypeVal.mdifferentiableAt one_ne_zero).hasMFDerivAt.comp u
      hc).congr_mfderiv (ContinuousLinearMap.ext fun r ↦ ?_)
    exact Manifold.mfderiv_subtype_val_apply _ _
  have hy : (timeDependentFlowOf (I := I) (M := U) (fun u z ↦ X u z) s s y : M) = y := by
    exact congrArg Subtype.val (timeDependentFlowOf_self _ s y)
  refine ⟨hy ▸ mem_timeDependentFlowDomain_of_hasMFDerivAt hγ hs ht, ?_⟩
  rw [← timeDependentFlowOf_eq_of_hasMFDerivAt hX hγ hs ht, hy]

/-- **The differential of the flow of a restriction to an open submanifold is that of the ambient
flow.** If the flow of the restriction of `X` to an open submanifold `U` runs from `(s, y)` up to
time `t`, then its differential at `y` is the differential at `y` of the flow of `X`, the tangent
spaces of `U` and `M` being the same. -/
theorem mfderiv_timeDependentFlowOf_restrict_opens_apply [FiniteDimensional ℝ E]
    (h : ((s, t), y) ∈ timeDependentFlowDomain (I := I) (M := U) (fun u z ↦ X u z)) (v : E) :
    mfderiv I I (timeDependentFlowOf X s t) y v =
      mfderiv I I (timeDependentFlowOf (I := I) (M := U) (fun u z ↦ X u z) s t) y v := by
  have hXU := contMDiff_timeDependentField_opens (U := U) hX
  -- Near `y`, flowing in `U` and then including into `M` is including and then flowing in `M`.
  have heq : timeDependentFlowOf X s t ∘ Subtype.val =ᶠ[𝓝 y]
      Subtype.val ∘ timeDependentFlowOf (I := I) (M := U) (fun u z ↦ X u z) s t := by
    filter_upwards [((isOpen_timeDependentFlowDomain hXU).preimage
      (by fun_prop : Continuous fun z : U ↦ ((s, t), z))).mem_nhds h] with z hz
    exact (timeDependentFlowOf_restrict_opens hX hz).2.symm
  -- The three differentials are read in the model space `E`, which is every tangent space.
  have h₁ : (mfderiv I I (timeDependentFlowOf X s t) y v : E) =
      mfderiv I I (timeDependentFlowOf X s t ∘ Subtype.val) y v :=
    (Manifold.mfderiv_comp_subtype_val_apply v).symm
  have h₂ : (mfderiv I I (timeDependentFlowOf X s t ∘ Subtype.val) y v : E) =
      mfderiv I I (Subtype.val ∘ timeDependentFlowOf (I := I) (M := U) (fun u z ↦ X u z) s t)
        y v := by
    rw [heq.mfderiv_eq]
    -- `tangentSpaceCast` between the tangent spaces at the two equal values is the identity.
    rfl
  exact h₁.trans (h₂.trans (Manifold.mfderiv_subtype_val_comp_apply v))

end Flow

end TauCeti
