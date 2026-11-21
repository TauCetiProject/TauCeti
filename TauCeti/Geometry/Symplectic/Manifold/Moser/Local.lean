/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Moser
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Moser's lemma for families over an open set of times

Let `J` be an open set of times and `σ` a smooth two-form on `J × M`, representing the family of
its slices `σ_t = ι_t^* σ` for `t ∈ J`, pulled back along the inclusions `ι_t : x ↦ (t, x)`, and
let `α` be a smooth one-form on `J × M` whose slices are primitives of the velocity:
`ι_t^* L_{∂_t} σ = dα_t`. **Moser's lemma** says that a time-dependent vector field `X` solving
Moser's equation `ι_{X_t} σ_t = -α_t` has a flow `φ_{s,t}` with `φ_{s,t}^* σ_t = σ_s`. This file
proves it *locally in the domain of the flow*: at every point `x` whose trajectory from time `s`
exists up to time `t`, with all the times between `s` and `t` in `J`,
`(φ_{s,t}^* σ_t)ₓ = (σ_s)ₓ` (`TauCeti.SmoothTwoForm.mpullback_timeDependentFlowOf_apply_eq_of_mem`).
No completeness of the flow and no compactness of `M` are assumed, and the slices need only be
closed between `s` and `t`: nondegeneracy is used only to solve Moser's equation. The field `X` is a
time-dependent field on `ℝ × M` in the sense of `TauCeti.timeDependentFlowOf`; only its values at
the times between `s` and `t` enter, where it solves Moser's equation.

Such fields exist: when the slices are symplectic, for every compact interval of times in `J`
there is a smooth time-dependent field on `ℝ × M` which solves Moser's equation at the times of
the interval (`TauCeti.SmoothTwoForm.exists_contMDiff_interior_eq_neg`). On a compact manifold its
flow is complete, and the time maps form an isotopy `ψ_t` with `ψ_t^* σ_t = σ_a` for the times
`t` of the interval `[a, b]` (`TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq_of_uIcc_subset`).

The proof reduces to Moser's principle for families on `ℝ × M`
(`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc_of_mem`). A
smooth map `g : ℝ → J` which is the identity near the interval of times
(`TopologicalSpace.Opens.exists_contMDiff_eventuallyEq_id`) turns `σ` into the form
`(g × id)^* σ` on `ℝ × M`, whose slices are `σ_{g t}` and whose time derivative near the interval
is that of `σ`
(`TauCeti.mpullback_prodMk_mlieDerivForm_mpullback_prodMap`). Along the trajectory the rate
`ι_t^* L_{∂_t} σ + L_{X_t} σ_t = dα_t + d(ι_{X_t} σ_t)` then vanishes by Cartan's formula for the
closed slices.

## Main results

* `TauCeti.SmoothTwoForm.mpullback_timeDependentFlowOf_apply_eq_of_mem`: Moser's lemma along the
  domain of the flow, for a family over an open set of times.
* `TauCeti.SmoothTwoForm.exists_contMDiff_interior_eq_neg`: smooth solutions of Moser's equation
  at the times of a compact interval.
* `TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq_of_uIcc_subset`: on a compact manifold, the
  Moser isotopy over a compact interval of times.

## References

* J. Moser, *On the volume elements on a manifold*, Transactions of the American Mathematical
  Society 120 (1965), 286–294.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 (Moser isotopy and Moser stability).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 22.13 and its proof (Moser's argument on the domain of the
  time-dependent flow).
-/

public section

noncomputable section

open Bundle Set Function Filter TopologicalSpace
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] {J : Opens ℝ}

/-- **Moser's lemma along the domain of the flow**, for a family over an open set `J` of times.
Let `σ` be a smooth two-form on `J × M` and `α` a smooth one-form on `J × M` whose slices are
primitives of the velocity of the slices of `σ`, `ι_u^* L_{∂_t} σ = dα_u`, at the times `u` between
`s` and `t`, all in `J`, where the slices `σ_u` are moreover closed. Let `X` be a jointly `C²`
time-dependent vector field solving Moser's equation `ι_{X_u} σ_u = -α_u` at these times. If the
flow `φ` of `X` from `(s, x)` is defined up to time `t`, then `(φ_{s,t}^* σ_t)ₓ = (σ_s)ₓ`. -/
theorem mpullback_timeDependentFlowOf_apply_eq_of_mem
    (σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (J × M) ℝ 2) (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (J × M) ℝ 1)
    {s t : ℝ} (hst : uIcc s t ⊆ J)
    (hσ : ∀ u (hu : u ∈ uIcc s t),
      (SmoothForm.mpullback (Prod.mk (⟨u, hst hu⟩ : J)) (contMDiff_const.prodMk contMDiff_id)
        σ).IsClosed)
    (hα : ∀ u (hu : u ∈ uIcc s t), TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk (⟨u, hst hu⟩ : J))
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) σ.val) =
      mextDeriv (SmoothForm.mpullback (Prod.mk (⟨u, hst hu⟩ : J))
        (contMDiff_const.prodMk contMDiff_id) α).val)
    {X : ℝ → (x : M) → TangentSpace I x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hXeq : ∀ u (hu : u ∈ uIcc s t), RoughForm.interior (X u)
        (SmoothForm.mpullback (Prod.mk (⟨u, hst hu⟩ : J)) (contMDiff_const.prodMk contMDiff_id)
          σ).val =
      -(SmoothForm.mpullback (Prod.mk (⟨u, hst hu⟩ : J)) (contMDiff_const.prodMk contMDiff_id)
          α).val)
    {x : M} (hx : ((s, t), x) ∈ timeDependentFlowDomain X) :
    TauCeti.mpullback I I (timeDependentFlowOf X s t)
        (SmoothForm.mpullback (Prod.mk (⟨t, hst right_mem_uIcc⟩ : J))
          (contMDiff_const.prodMk contMDiff_id) σ).val x =
      (SmoothForm.mpullback (Prod.mk (⟨s, hst left_mem_uIcc⟩ : J))
        (contMDiff_const.prodMk contMDiff_id) σ).val x := by
  -- Read the family through a smooth map `g : ℝ → J` which is the identity near the times
  -- between `s` and `t`, so as to obtain the family `σ' = (g × id)^* σ` on `ℝ × M`.
  obtain ⟨g, hg, hgid⟩ :=
    Opens.exists_contMDiff_eventuallyEq_id (convex_uIcc s t) isCompact_uIcc nonempty_uIcc hst
  have hgu {u : ℝ} (hu : u ∈ uIcc s t) : g u = ⟨u, hst hu⟩ :=
    Subtype.ext (hgid u hu).self_of_nhds
  set σ' := SmoothForm.mpullback (Prod.map g id) (hg.prodMap contMDiff_id) σ
  have hslice {u : ℝ} (hu : u ∈ uIcc s t) :
      TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) σ'.val =
        (SmoothForm.mpullback (Prod.mk (⟨u, hst hu⟩ : J)) (contMDiff_const.prodMk contMDiff_id)
          σ).val := by
    rw [← hgu hu, ← SmoothForm.mpullback_prodMk_mpullback_prodMap_id σ hg u]
    simp only [σ', SmoothForm.coe_mpullback]
  -- Along the trajectory, the rate `ι_u^* L_{∂_t} σ' + L_{X_u} σ'_u = dα_u - dα_u` vanishes.
  have hL (u : ℝ) (hu : u ∈ uIcc s t) :
      (TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u)
          (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) σ'.val) +
        mlieDerivForm (X u) (TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk u) σ'.val))
        (timeDependentFlowOf X s u x) = 0 := by
    have hXu : MDifferentiable I I.tangent (fun y ↦ (⟨y, X u y⟩ : TangentBundle I M)) :=
      (hX.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by norm_num)
    rw [mpullback_prodMk_mlieDerivForm_mpullback_prodMap σ hg (hgid u hu), hgu hu, hα u hu,
      hslice hu, SmoothForm.mlieDerivForm_eq_mextDeriv_interior hXu (hσ u hu), hXeq u hu,
      mextDeriv_neg, add_neg_cancel, Pi.zero_apply]
  have hP := mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc_of_mem hX
    hx (fun u _ ↦ σ'.contMDiff.contMDiffAt.of_le (by simp)) hL
  rwa [hslice left_mem_uIcc, hslice right_mem_uIcc] at hP

omit [I.Boundaryless] [T2Space M] in
/-- **Solutions of Moser's equation over a compact interval of times.** Let `σ` be a smooth
two-form on `J × M` with nondegenerate slices and `α` a smooth one-form on `J × M`. For every
compact interval `[[a, b]] ⊆ J` there is a smooth time-dependent vector field `X` on `ℝ × M` with
`ι_{X_u} σ_u = -α_u` at every time `u` of the interval. For instance, the Moser field
`(σ_t♭)⁻¹ (-α_t)` read through a smooth map `ℝ → J` which is the identity near the interval is
such a field. -/
theorem exists_contMDiff_interior_eq_neg (σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (J × M) ℝ 2)
    (hσ : ∀ t : J, IsNondegenerate
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ))
    (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (J × M) ℝ 1) {a b : ℝ} (hab : uIcc a b ⊆ J) :
    ∃ X : ℝ → (x : M) → TangentSpace I x,
      ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
        (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)) ∧
      ∀ u (hu : u ∈ uIcc a b), RoughForm.interior (X u)
          (SmoothForm.mpullback (Prod.mk (⟨u, hab hu⟩ : J)) (contMDiff_const.prodMk contMDiff_id)
            σ).val =
        -(SmoothForm.mpullback (Prod.mk (⟨u, hab hu⟩ : J)) (contMDiff_const.prodMk contMDiff_id)
            α).val := by
  obtain ⟨g, hg, hgid⟩ :=
    Opens.exists_contMDiff_eventuallyEq_id (convex_uIcc a b) isCompact_uIcc nonempty_uIcc hab
  refine ⟨fun u ↦ (hσ (g u)).interiorEquiv.symm
    (SmoothForm.mpullback (Prod.mk (g u)) (contMDiff_const.prodMk contMDiff_id) (-α)),
    (contMDiff_interiorEquiv_symm_mpullback_prodMk σ hσ (-α)).comp (hg.prodMap contMDiff_id),
    fun u hu ↦ ?_⟩
  have hgu : g u = ⟨u, hab hu⟩ := Subtype.ext (hgid u hu).self_of_nhds
  rw [← hgu, IsNondegenerate.interior_interiorEquiv_symm, map_neg, Submodule.coe_neg]

/-- **Moser's theorem over a compact interval of times.** Let `M` be a compact manifold, `σ` a
smooth two-form on `J × M` with symplectic slices, `[[a, b]] ⊆ J` a compact interval of times and
`α` a smooth one-form on `J × M` whose slices are primitives of the velocity of the slices of `σ`,
`ι_t^* L_{∂_t} σ = dα_t`, at the times `t` of the interval. Then there is an isotopy `ψ_t` of
`M`, jointly smooth in `(t, x)`, with `ψ_a = id` and `ψ_t^* σ_t = σ_a` at every time `t` of the
interval. -/
theorem exists_isotopy_mpullback_eq_of_uIcc_subset [CompactSpace M]
    (σ : SmoothForm (𝓘(ℝ, ℝ).prod I) (J × M) ℝ 2) (α : SmoothForm (𝓘(ℝ, ℝ).prod I) (J × M) ℝ 1)
    (hσ : ∀ t : J, IsSymplectic
      (SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id) σ))
    {a b : ℝ} (hab : uIcc a b ⊆ J)
    (hα : ∀ t (ht : t ∈ uIcc a b), TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I)
        (Prod.mk (⟨t, hab ht⟩ : J)) (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) σ.val) =
      mextDeriv (SmoothForm.mpullback (Prod.mk (⟨t, hab ht⟩ : J))
        (contMDiff_const.prodMk contMDiff_id) α).val) :
    ∃ ψ : ℝ → M ≃ₘ⟮I, I⟯ M, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ ψ p.1 p.2) ∧
      (∀ x, ψ a x = x) ∧
      ∀ t (ht : t ∈ uIcc a b), SmoothForm.mpullback (ψ t) (ψ t).contMDiff
          (SmoothForm.mpullback (Prod.mk (⟨t, hab ht⟩ : J)) (contMDiff_const.prodMk contMDiff_id)
            σ) =
        SmoothForm.mpullback (Prod.mk (⟨a, hab left_mem_uIcc⟩ : J))
          (contMDiff_const.prodMk contMDiff_id) σ := by
  obtain ⟨X, hX, hXeq⟩ := exists_contMDiff_interior_eq_neg σ
    (fun t ↦ (hσ t).isNondegenerate) α hab
  -- On a compact manifold the suspension of `X` is complete.
  have hc : IsCompleteVectorField (timeDependentSuspensionField X) :=
    isCompleteVectorField_timeDependentSuspensionField (hX.of_le (by simp)) isCompact_univ
      fun _ _ hy ↦ (hy (mem_univ _)).elim
  refine ⟨fun t ↦ timeDependentFlowDiffeomorph hc (n := ⊤) le_top hX a t, ?_, fun x ↦ ?_,
    fun t ht ↦ Subtype.ext ?_⟩
  · simp only [timeDependentFlowDiffeomorph_apply]
    exact (contMDiff_timeDependentFlowOf hc (n := ⊤) le_top hX).comp
      ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd)
  · rw [timeDependentFlowDiffeomorph_apply]
    exact timeDependentFlowOf_self X a x
  · have hψ : ⇑(timeDependentFlowDiffeomorph hc (n := ⊤) le_top hX a t) =
        timeDependentFlowOf X a t :=
      funext (timeDependentFlowDiffeomorph_apply hc le_top hX a t)
    have hsub : uIcc a t ⊆ uIcc a b := uIcc_subset_uIcc left_mem_uIcc ht
    rw [SmoothForm.coe_mpullback, hψ]
    funext x
    exact mpullback_timeDependentFlowOf_apply_eq_of_mem σ α (hsub.trans hab)
      (fun u hu ↦ (hσ _).isClosed) (fun u hu ↦ hα u (hsub hu)) (hX.of_le (by simp))
      (fun u hu ↦ hXeq u (hsub hu)) ((timeDependentFlowDomain_eq_univ hc).symm ▸ mem_univ _)

end SmoothTwoForm

end TauCeti
