/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Tangent bundles of open subsets of a normed space

On an open subset of a normed space all charts are restrictions of the identity, so the
tangent-bundle trivializations are the identity; the homothety `v ↦ t • v` of an open set
star-shaped about `0` has differential `t • id`.

## Main results

* `TauCeti.Manifold.trivializationAt_opens_model_space_symmL`: the tangent-bundle
  trivializations of an open subset of a normed space are the identity, and
  `TauCeti.Manifold.contMDiffAt_section_opens_model_space_iff`: so a field of bilinear maps there
  is a `C^n` section exactly when it is `C^n` as a map into the bilinear maps on the normed space.
* `StarConvex.opensHomothety`: the homothety `v ↦ t • v`, `t ∈ [0, 1]`, of an open set that is
  star-shaped about `0`, with differential `t • id` (`StarConvex.mfderiv_opensHomothety`).
-/

public section

open Bundle Manifold Set TopologicalSpace
open scoped Bundle Manifold Topology ContDiff

noncomputable section

namespace TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {U : Opens E}

/-- Every tangent-bundle trivialization of an open subset of a normed space is defined over the
whole subset. -/
theorem mem_trivializationAt_opens_model_space_baseSet (x y : U) :
    y ∈ (trivializationAt E (TangentSpace 𝓘(𝕜, E) : U → Type _) x).baseSet := by
  simp only [TangentBundle.trivializationAt_baseSet, Opens.chartAt_opens_model_space_eq x y]
  exact mem_chart_source E y

/-- The tangent-bundle trivializations of an open subset of a normed space are the identity. -/
@[simp]
theorem trivializationAt_opens_model_space_symmL (x y : U) (u : E) :
    (trivializationAt E (TangentSpace 𝓘(𝕜, E) : U → Type _) x).symmL 𝕜 y u = u := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (by
    simpa using mem_trivializationAt_opens_model_space_baseSet (𝕜 := 𝕜) x y)]
  have hxy : achart E x = achart E y := Subtype.ext (Opens.chartAt_opens_model_space_eq x y)
  rw [hxy]
  exact (tangentBundleCore 𝓘(𝕜, E) U).coordChange_self _ _ (mem_achart_source E y) u

/-- On an open subset of a normed space, a field of bilinear maps on the tangent spaces is a
`C^n` section exactly when it is `C^n` as a map into the bilinear maps on the normed space. -/
theorem contMDiffAt_section_opens_model_space_iff {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {n : ℕ∞ω}
    {b : ∀ x : U, TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, E) x →L[𝕜] F} {x₀ : U} :
    ContMDiffAt 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] F)) n
      (fun x ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] F)
        (E := fun x : U ↦ TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, E) x →L[𝕜] F) x
        (b x)) x₀ ↔
      ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E →L[𝕜] E →L[𝕜] F) n
        (fun x : U ↦ show E →L[𝕜] E →L[𝕜] F from b x) x₀ := by
  rw [Bundle.contMDiffAt_section_iff]
  refine Filter.EventuallyEq.contMDiffAt_iff (Filter.Eventually.of_forall fun y ↦ ?_)
  have hy := mem_trivializationAt_opens_model_space_baseSet (𝕜 := 𝕜) x₀ y
  refine ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦ ?_
  simp only [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ hy hy (by simp)]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
    LinearMap.id_apply]
  rw [← Trivialization.symmL_apply (R := 𝕜) _ hy, trivializationAt_opens_model_space_symmL,
    ← Trivialization.symmL_apply (R := 𝕜) _ hy, trivializationAt_opens_model_space_symmL]
  -- Both sides are `b y v w`, read in `E` and in the tangent space `TangentSpace 𝓘(𝕜, E) y = E`.
  rfl

end TauCeti.Manifold

/-! ### Homotheties of star-shaped open sets -/

namespace StarConvex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {U : Opens V}
  (hU : StarConvex ℝ 0 (U : Set V))

/-- The homothety `v ↦ t • v` with centre `0` and ratio `t ∈ [0, 1]`, as a self-map of an open set
that is star-shaped about `0`. -/
def opensHomothety (t : Icc (0 : ℝ) 1) (v : U) : U :=
  ⟨(t : ℝ) • (v : V), starConvex_zero_iff.1 hU v.property t.property.1 t.property.2⟩

@[simp]
theorem coe_opensHomothety (t : Icc (0 : ℝ) 1) (v : U) :
    (hU.opensHomothety t v : V) = (t : ℝ) • (v : V) :=
  (rfl)

/-- The homothety of ratio `0` is the constant map to the origin. -/
@[simp]
theorem opensHomothety_zero (v : U) :
    hU.opensHomothety 0 v = ⟨0, hU.mem (Set.nonempty_of_mem v.property)⟩ :=
  Subtype.ext ((hU.coe_opensHomothety 0 v).trans (_root_.zero_smul ℝ (v : V)))

/-- The homothety of ratio `1` is the identity. -/
@[simp]
theorem opensHomothety_one : hU.opensHomothety 1 = id :=
  funext fun v ↦ Subtype.ext ((hU.coe_opensHomothety 1 v).trans (one_smul ℝ (v : V)))

theorem contMDiff_opensHomothety {n : ℕ∞ω} (t : Icc (0 : ℝ) 1) :
    ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, V) n (hU.opensHomothety t) := by
  refine (TauCeti.ContMDiff.subtypeVal_comp_iff U (hU.opensHomothety t)).1 ?_
  have h : (Subtype.val ∘ hU.opensHomothety t) = fun v : U ↦ (t : ℝ) • (v : V) :=
    funext (hU.coe_opensHomothety t)
  rw [h]
  exact (contDiff_const_smul (t : ℝ)).contMDiff.comp contMDiff_subtypeVal

/-- The differential of the homothety of ratio `t` is multiplication by `t`. -/
@[simp]
theorem mfderiv_opensHomothety (t : Icc (0 : ℝ) 1) (v : U) :
    mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) (hU.opensHomothety t) v = (t : ℝ) • ContinuousLinearMap.id ℝ V := by
  ext u
  rw [TauCeti.Manifold.mfderiv_apply_of_subtype_val_comp_eq
    (A := ⇑((t : ℝ) • ContinuousLinearMap.id ℝ V)) (funext fun w ↦ hU.coe_opensHomothety t w) u,
    ContinuousLinearMap.mfderiv_eq]
  -- Both sides apply `t • id` to `u`, read in `V` and in the tangent space `TangentSpace _ v = V`.
  rfl

/-- A homothety of nonzero ratio has invertible differential. -/
theorem isInvertible_mfderiv_opensHomothety (t : Icc (0 : ℝ) 1) (ht : (t : ℝ) ≠ 0) (v : U) :
    (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) (hU.opensHomothety t) v).IsInvertible := by
  have h : ((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (Units.mk0 (t : ℝ) ht) : V ≃L[ℝ] V) :
      V →L[ℝ] V) = (t : ℝ) • ContinuousLinearMap.id ℝ V :=
    ContinuousLinearMap.ext fun u ↦ by
      simp [ContinuousLinearEquiv.smulLeft_apply_apply, Units.smul_def]
  rw [hU.mfderiv_opensHomothety t v, ← h]
  exact ContinuousLinearMap.isInvertible_equiv

end StarConvex
