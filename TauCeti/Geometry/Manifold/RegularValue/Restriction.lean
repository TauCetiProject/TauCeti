/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.ManifoldLevel
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Open restrictions of regular fibres

The regular fibre of a map restricted to an open subset is canonically diffeomorphic to the
corresponding open subset of the original regular fibre. Both fibres carry their independently
constructed regular-fibre atlases; the comparison preserves the underlying ambient point.
Thus regular-fibre constructions can be used locally without changing the induced smooth
structure on overlaps. No separation or countability hypotheses are needed, and the open subset
of the fibre may be empty.

The comparison uses the smooth lifting property of immersions from Mathlib, rather than comparing
the implicit-function charts themselves.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013,
  Corollary 5.14 and Proposition 5.38.
-/

public section

open Function Module TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M F G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {m : ℕ∞ω} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I m M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G}
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J m N]
  {f : M → N} {c : N}

/-- The regular fibre of `f` restricted to an open subset `U` is diffeomorphic to the open
submanifold of the regular fibre consisting of points in `U`. The map and its inverse preserve
the ambient point. Each fibre uses its preferred regular-fibre atlas. -/
noncomputable def regularFiberRestrictDiffeomorph (hm : 1 ≤ m) (hf : ContMDiff I J m f)
    (hc : J.IsInteriorPoint c) (hreg : IsRegularValue I J f c) (U : Opens M) :
    letI := regularFiberChartedSpace hm hf hc hreg
    letI := regularFiberChartedSpace (f := fun x : U ↦ f x) hm
      (hf.comp contMDiff_subtype_val) hc
      (hreg.restrict (fun x _ ↦ hf.mdifferentiable (ENat.one_le_iff_ne_zero_withTop.mp hm) x) U)
    {x : U // f x = c} ≃ₘ^m⟮𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ E - finrank ℝ F) → ℝ)⟯
      (Opens.comap ⟨(Subtype.val : {x : M // f x = c} → M), continuous_subtype_val⟩ U) := by
  let hfU : ContMDiff I J m (fun x : U ↦ f x) := hf.comp contMDiff_subtype_val
  let hrU := hreg.restrict
    (fun x _ ↦ hf.mdifferentiable (ENat.one_le_iff_ne_zero_withTop.mp hm) x) U
  letI := regularFiberChartedSpace hm hf hc hreg
  letI := regularFiberChartedSpace hm hfU hc hrU
  haveI := isManifold_regularFiber hm hf hc hreg
  haveI := isManifold_regularFiber hm hfU hc hrU
  let V : Opens {x : M // f x = c} :=
    Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ U
  let e : {x : U // f x = c} ≃ₜ V :=
    { toFun := fun x ↦ ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun x ↦ ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  refine { e with contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · apply (TauCeti.ContMDiff.subtypeVal_comp_iff V _).mp
    apply (ContMDiff.iff_comp_isImmersion
      (isSmoothEmbedding_coe_regularFiber hm hf hc hreg).isImmersion).2
    exact ⟨continuous_subtype_val.comp e.continuous, contMDiff_subtype_val.comp
      (isSmoothEmbedding_coe_regularFiber hm hfU hc hrU).isImmersion.contMDiff⟩
  · apply (ContMDiff.iff_comp_isImmersion
      (isSmoothEmbedding_coe_regularFiber hm hfU hc hrU).isImmersion).2
    refine ⟨e.symm.continuous, ?_⟩
    apply (TauCeti.ContMDiff.subtypeVal_comp_iff U _).mp
    exact ((isSmoothEmbedding_coe_regularFiber hm hf hc hreg).isImmersion.contMDiff).comp
      contMDiff_subtype_val

/-- The restriction comparison preserves the underlying point of the ambient manifold. -/
@[simp]
theorem regularFiberRestrictDiffeomorph_apply (hm : 1 ≤ m) (hf : ContMDiff I J m f)
    (hc : J.IsInteriorPoint c) (hreg : IsRegularValue I J f c) (U : Opens M)
    (x : {x : U // f x = c}) :
    regularFiberRestrictDiffeomorph hm hf hc hreg U x = ⟨⟨x.1.1, x.2⟩, x.1.2⟩ :=
  (rfl)

/-- The inverse restriction comparison preserves the underlying point in the open subset. -/
@[simp]
theorem regularFiberRestrictDiffeomorph_symm_apply (hm : 1 ≤ m) (hf : ContMDiff I J m f)
    (hc : J.IsInteriorPoint c) (hreg : IsRegularValue I J f c) (U : Opens M)
    (x : Opens.comap ⟨(Subtype.val : {x : M // f x = c} → M), continuous_subtype_val⟩ U) :
    letI := regularFiberChartedSpace hm hf hc hreg
    letI := regularFiberChartedSpace (f := fun x : U ↦ f x) hm
      (hf.comp contMDiff_subtype_val) hc
      (hreg.restrict (fun x _ ↦ hf.mdifferentiable (ENat.one_le_iff_ne_zero_withTop.mp hm) x) U)
    (regularFiberRestrictDiffeomorph hm hf hc hreg U).symm x = ⟨⟨x.1.1, x.2⟩, x.1.2⟩ :=
  (rfl)

end TauCeti
