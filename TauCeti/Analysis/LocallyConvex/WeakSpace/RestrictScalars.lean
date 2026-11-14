/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Real restriction of the weak topology

The weak topology of a real or complex topological vector space agrees with the weak topology
of its restriction to real scalars. The identity on the underlying space is bundled as
`WeakSpace.restrictScalars`, a real continuous linear equivalence. Consequently weak
convergence, weak compactness, weak closedness and weak lower semicontinuity are independent
of this scalar restriction. This lets real-valued variational arguments apply to complex spaces.

The construction uses Mathlib's `StrongDual.extendRCLikeₗ`: every continuous real-linear
functional is the real part of a unique continuous scalar-linear functional. No norm,
completeness, local convexity or separation hypothesis is needed.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Chapter 3 (weak topologies).
-/

public section

open Filter Set Topology

namespace WeakSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [ContinuousConstSMul 𝕜 E]

/-- The identity between the scalar weak topology and the real weak topology, as a real
continuous linear equivalence. -/
noncomputable def restrictScalars : WeakSpace 𝕜 E ≃L[ℝ] WeakSpace ℝ E where
  toLinearEquiv := ((toWeakSpace 𝕜 E).restrictScalars ℝ).symm ≪≫ₗ toWeakSpace ℝ E
  continuous_toFun := by
    apply WeakBilin.continuous_of_continuous_eval
    intro f
    have h : Continuous (fun x : WeakSpace 𝕜 E ↦
        RCLike.re (StrongDual.extendRCLike (𝕜 := 𝕜) f ((toWeakSpace 𝕜 E).symm x))) :=
      RCLike.continuous_re.comp
        (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip
          (StrongDual.extendRCLike (𝕜 := 𝕜) f))
    -- The target still contains the linear-equivalence and flipped-pairing projections.
    change Continuous (fun x : WeakSpace 𝕜 E ↦ f ((toWeakSpace 𝕜 E).symm x))
    simpa only [StrongDual.re_extendRCLike_apply] using h
  continuous_invFun := by
    apply WeakBilin.continuous_of_continuous_eval
    intro f
    have hre : Continuous (fun x : WeakSpace ℝ E ↦
        RCLike.re (f ((toWeakSpace ℝ E).symm x))) :=
      WeakBilin.eval_continuous (topDualPairing ℝ E).flip
        (RCLike.reCLM.comp (f.restrictScalars ℝ))
    have him : Continuous (fun x : WeakSpace ℝ E ↦
        RCLike.im (f ((toWeakSpace ℝ E).symm x))) :=
      WeakBilin.eval_continuous (topDualPairing ℝ E).flip
        (RCLike.imCLM.comp (f.restrictScalars ℝ))
    exact ((RCLike.continuous_ofReal.comp hre).add
      ((RCLike.continuous_ofReal.comp him).mul_const (RCLike.I : 𝕜))).congr
        (fun x ↦ RCLike.re_add_im (f ((toWeakSpace ℝ E).symm x)))

/-- Real restriction does not change the underlying vector. -/
@[simp] theorem restrictScalars_toWeakSpace (x : E) :
    restrictScalars (𝕜 := 𝕜) (toWeakSpace 𝕜 E x) = toWeakSpace ℝ E x := (rfl)

/-- The inverse real restriction does not change the underlying vector. -/
@[simp] theorem restrictScalars_symm_toWeakSpace (x : E) :
    (restrictScalars (𝕜 := 𝕜)).symm (toWeakSpace ℝ E x) = toWeakSpace 𝕜 E x := (rfl)

/-- Evaluating the underlying vector after real restriction. -/
@[simp] theorem toWeakSpace_symm_restrictScalars (x : WeakSpace 𝕜 E) :
    (toWeakSpace ℝ E).symm (restrictScalars (𝕜 := 𝕜) x) = (toWeakSpace 𝕜 E).symm x := (rfl)

/-- Evaluating the underlying vector after inverse real restriction. -/
@[simp] theorem toWeakSpace_symm_restrictScalars_symm (x : WeakSpace ℝ E) :
    (toWeakSpace 𝕜 E).symm ((restrictScalars (𝕜 := 𝕜)).symm x) =
      (toWeakSpace ℝ E).symm x := (rfl)

/-- Real restriction carries the weak image of a set to its real weak image. -/
@[simp] theorem restrictScalars_image (s : Set E) :
    restrictScalars (𝕜 := 𝕜) '' (toWeakSpace 𝕜 E '' s) = toWeakSpace ℝ E '' s := by
  simp only [image_image, restrictScalars_toWeakSpace]

/-- Inverse real restriction carries the real weak image of a set to its scalar weak image. -/
@[simp] theorem restrictScalars_symm_image (s : Set E) :
    (restrictScalars (𝕜 := 𝕜)).symm '' (toWeakSpace ℝ E '' s) = toWeakSpace 𝕜 E '' s := by
  simp only [image_image, restrictScalars_symm_toWeakSpace]

end WeakSpace

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [Module ℝ E] [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [ContinuousConstSMul 𝕜 E]

/-- Weak convergence is unchanged by restriction to real scalars, for arbitrary filters. -/
theorem tendsto_toWeakSpace_iff_real {α : Type*} {l : Filter α} {u : α → E} {x : E} :
    Tendsto (fun i ↦ toWeakSpace 𝕜 E (u i)) l (𝓝 (toWeakSpace 𝕜 E x)) ↔
      Tendsto (fun i ↦ toWeakSpace ℝ E (u i)) l (𝓝 (toWeakSpace ℝ E x)) := by
  constructor
  · intro h
    exact ((WeakSpace.restrictScalars (𝕜 := 𝕜) (E := E)).continuous.tendsto _).comp h
  · intro h
    exact ((WeakSpace.restrictScalars (𝕜 := 𝕜) (E := E)).symm.continuous.tendsto _).comp h

/-- Weak compactness is unchanged by restriction to real scalars. -/
theorem isCompact_toWeakSpace_iff_real {s : Set E} :
    IsCompact (toWeakSpace 𝕜 E '' s) ↔ IsCompact (toWeakSpace ℝ E '' s) := by
  simpa only [ContinuousLinearEquiv.coe_toHomeomorph, WeakSpace.restrictScalars_image] using
    ((WeakSpace.restrictScalars (𝕜 := 𝕜) (E := E)).toHomeomorph.isCompact_image
      (s := toWeakSpace 𝕜 E '' s)).symm

/-- Weak closedness is unchanged by restriction to real scalars. -/
theorem isClosed_toWeakSpace_iff_real {s : Set E} :
    IsClosed (toWeakSpace 𝕜 E '' s) ↔ IsClosed (toWeakSpace ℝ E '' s) := by
  simpa only [ContinuousLinearEquiv.coe_toHomeomorph, WeakSpace.restrictScalars_image] using
    ((WeakSpace.restrictScalars (𝕜 := 𝕜) (E := E)).toHomeomorph.isClosed_image
      (s := toWeakSpace 𝕜 E '' s)).symm

/-- Weak lower semicontinuity on an admissible set is unchanged by real scalar restriction. -/
theorem lowerSemicontinuousOn_toWeakSpace_iff_real {β : Type*} [Preorder β]
    {f : E → β} {s : Set E} :
    LowerSemicontinuousOn (fun x : WeakSpace 𝕜 E ↦ f ((toWeakSpace 𝕜 E).symm x))
      (toWeakSpace 𝕜 E '' s) ↔
    LowerSemicontinuousOn (fun x : WeakSpace ℝ E ↦ f ((toWeakSpace ℝ E).symm x))
      (toWeakSpace ℝ E '' s) := by
  constructor
  · intro h
    have hc := h.comp (g := (WeakSpace.restrictScalars (𝕜 := 𝕜)).symm)
      (t := toWeakSpace ℝ E '' s)
      (WeakSpace.restrictScalars (𝕜 := 𝕜)).symm.continuous.continuousOn
      (by
        rintro _ ⟨x, hx, rfl⟩
        rw [WeakSpace.restrictScalars_symm_toWeakSpace]
        exact mem_image_of_mem _ hx)
    simpa only [Function.comp_def, WeakSpace.toWeakSpace_symm_restrictScalars_symm] using hc
  · intro h
    have hc := h.comp (g := WeakSpace.restrictScalars (𝕜 := 𝕜))
      (t := toWeakSpace 𝕜 E '' s)
      (WeakSpace.restrictScalars (𝕜 := 𝕜)).continuous.continuousOn
      (by
        rintro _ ⟨x, hx, rfl⟩
        rw [WeakSpace.restrictScalars_toWeakSpace]
        exact mem_image_of_mem _ hx)
    simpa only [Function.comp_def, WeakSpace.toWeakSpace_symm_restrictScalars] using hc

end TauCeti
