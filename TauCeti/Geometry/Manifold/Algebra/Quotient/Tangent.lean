/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.Quotient
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Tangent spaces of quotients of normed spaces by discrete subgroups

Let `N` be a discrete subgroup of a normed space `E`, so that `E ⧸ N` is a manifold modelled on `E`
whose charts are local inverses of the projection (`AddSubgroup.instChartedSpaceDiscreteQuotient`).
Every tangent space of `E ⧸ N` is `E`, and the charts differ from each other by translations, so
the tangent bundle of `E ⧸ N` is canonically trivial:

* the inverse of a chart is the projection on its target
  (`AddSubgroup.chartAt_symm_eq_quotientMk`);
* the inverse trivializations of the tangent bundle are the identity of `E`
  (`AddSubgroup.symmL_trivializationAt_quotient`);
* consequently an `F`-valued one-form on `E ⧸ N` is just a function `g : E ⧸ N → (E →L[𝕜] F)`, and
  it is a `C^n` section of `Hom(T(E ⧸ N), F)` exactly when `g` is `C^n`
  (`AddSubgroup.contMDiffAt_oneForm_quotient_iff`);
* the differential of a function `σ` on `E ⧸ N` at the class of `z` is the derivative of its lift
  `σ ∘ (↑)` at `z`, with no differentiability hypothesis
  (`AddSubgroup.mvfderiv_quotientMk_apply`).

For a full lattice `Λ ⊆ ℂ` this is the flat structure of the complex torus `ℂ ⧸ Λ`: the one-forms
`dz` and `dzbar` are constant.
-/

public section

noncomputable section

open Bundle Filter Set Topology
open scoped Manifold ContDiff

namespace AddSubgroup

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {N : AddSubgroup E} [DiscreteTopology N]

/-- On its target, the inverse of a chart of `E ⧸ N` is the projection. -/
theorem chartAt_symm_eq_quotientMk {x : E ⧸ N} {y : E} (hy : y ∈ (chartAt E x).target) :
    (chartAt E x).symm y = (y : E ⧸ N) := by
  obtain ⟨y₀, hy₀⟩ := QuotientAddGroup.mk_surjective ((chartAt E x).symm y)
  have hsrc : ((y₀ : E) : E ⧸ N) ∈ (chartAt E x).source := hy₀ ▸ (chartAt E x).map_target hy
  obtain ⟨l, hl, hc⟩ := N.exists_eventuallyEq_sub_of_mem_atlas (chart_mem_atlas E x) hsrc
  have h₀ : (chartAt E x) (y₀ : E ⧸ N) = y := by rw [hy₀, (chartAt E x).right_inv hy]
  have h₁ : y = y₀ - l := h₀.symm.trans hc.self_of_nhds
  rw [← hy₀, h₁, QuotientAddGroup.eq_iff_sub_mem]
  simpa using hl

/-- Near a point of its target, the inverse of a chart of `E ⧸ N` is the projection. -/
theorem chartAt_symm_eventuallyEq_quotientMk {x : E ⧸ N} {y : E}
    (hy : y ∈ (chartAt E x).target) :
    (chartAt E x).symm =ᶠ[𝓝 y] (QuotientAddGroup.mk : E → E ⧸ N) := by
  filter_upwards [(chartAt E x).open_target.mem_nhds hy] with z hz
  exact chartAt_symm_eq_quotientMk hz

/-- **The tangent bundle of `E ⧸ N` is trivial.** Its inverse trivializations are the identity of
`E`: the charts differ from the projection by translations. -/
theorem symmL_trivializationAt_quotient {x₀ x : E ⧸ N} (hx : x ∈ (chartAt E x₀).source) :
    (trivializationAt E (TangentSpace 𝓘(𝕜, E)) x₀).symmL 𝕜 x = ContinuousLinearMap.id 𝕜 E := by
  rw [TangentBundle.symmL_trivializationAt hx]
  have hy : (chartAt E x₀) x ∈ (chartAt E x₀).target := (chartAt E x₀).map_source hx
  simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ, extChartAt,
    OpenPartialHomeomorph.extend, PartialEquiv.coe_trans_symm,
    ModelWithCorners.toPartialEquiv_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_id,
    PartialEquiv.coe_trans, ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe,
    Function.id_comp]
  have h := (chartAt_symm_eventuallyEq_quotientMk hy).mfderiv_eq (I := 𝓘(𝕜, E)) (I' := 𝓘(𝕜, E))
  exact h.trans (N.mfderiv_quotientMk _)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **One-forms on `E ⧸ N` are functions.** Every tangent space of `E ⧸ N` is `E`, so an `F`-valued
one-form is a function `g : E ⧸ N → (E →L[𝕜] F)`; it is a `C^n` section of `Hom(T(E ⧸ N), F)` at a
point exactly when `g` is `C^n` there, since the tangent trivializations are the identity
(`AddSubgroup.symmL_trivializationAt_quotient`). -/
theorem contMDiffAt_oneForm_quotient_iff {n : ℕ∞ω} {g : E ⧸ N → E →L[𝕜] F} {x₀ : E ⧸ N} :
    ContMDiffAt 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E →L[𝕜] F)) n
        (fun x ↦ TotalSpace.mk' (E →L[𝕜] F)
          (E := fun y ↦ TangentSpace 𝓘(𝕜, E) y →L[𝕜] Trivial (E ⧸ N) F y) x (g x)) x₀ ↔
      ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E →L[𝕜] F) n g x₀ := by
  rw [contMDiffAt_hom_bundle]
  refine (and_iff_right contMDiffAt_id).trans (Filter.EventuallyEq.contMDiffAt_iff ?_)
  filter_upwards [(chartAt E x₀).open_source.mem_nhds (mem_chart_source E x₀)] with x hx
  ext v
  simp only [ContinuousLinearMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearMapAt_trivialization, symmL_trivializationAt_quotient hx,
    ContinuousLinearMap.id_comp]
  -- The identity acts on `TangentSpace 𝓘(𝕜, E) x`, which is `E` only by definition, so
  -- `ContinuousLinearMap.comp_id` does not match syntactically; the composite is `g x` by `rfl`.
  rfl

/-- **Differentials on `E ⧸ N` are derivatives of lifts.** The differential of a function `σ` on
`E ⧸ N` at the class of `z` is the derivative of its lift `σ ∘ (↑)` at `z`. There is no
differentiability hypothesis: the projection is a local diffeomorphism with differential the
identity, so `σ` is differentiable at the class of `z` exactly when its lift is at `z`. -/
theorem mvfderiv_quotientMk_apply (σ : E ⧸ N → F) (z v : E) :
    mvfderiv 𝓘(𝕜, E) σ (z : E ⧸ N) v = fderiv 𝕜 (fun w : E ↦ σ w) z v := by
  have h := (N.isLocalDiffeomorph_quotientMk (I := 𝓘(𝕜, E)) (n := ∞) z).mfderiv_comp
    (I' := 𝓘(𝕜, F)) (by simp) σ
  rw [N.mfderiv_quotientMk] at h
  -- Pass from `mvfderiv` to `mfderiv` on both sides, then use the chain rule `h`.
  refine (mvfderiv_apply_eq_mfderiv_apply σ _ v).trans ?_
  refine Eq.trans ?_ (TauCeti.mvfderiv_eq_fderiv_apply (σ ∘ QuotientAddGroup.mk) z v)
  refine Eq.trans ?_ (mvfderiv_apply_eq_mfderiv_apply (F := F) (σ ∘ QuotientAddGroup.mk) z v).symm
  rw [h]
  exact (congrArg _ (ContinuousLinearMap.id_apply (R₁ := 𝕜) v)).symm.trans
    (ContinuousLinearMap.comp_apply (mfderiv 𝓘(𝕜, E) 𝓘(𝕜, F) σ (z : E ⧸ N))
      (ContinuousLinearMap.id 𝕜 E) v).symm

end AddSubgroup
