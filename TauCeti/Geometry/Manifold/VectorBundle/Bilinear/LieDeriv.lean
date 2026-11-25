/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.LieDerivBilinear
public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Section
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Lie derivative of covariant two-tensors on manifolds

Defines `TauCeti.mlieDerivBilinWithin` and `TauCeti.mlieDerivBilin` for covariant two-tensors
`b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G` along `V` in the preferred chart
via `TauCeti.lieDerivBilinWithin`, without flows or finite-dimensionality, allowing boundaries and
corners. The definition follows the preferred-chart construction of `VectorField.mlieBracketWithin`
in `Mathlib.Geometry.Manifold.VectorField.LieBracket`. Proves congruence, linearity, the scalar
Leibniz rule, the bracket formula (`mlieDerivBilinWithin_apply_vectorField`,
`mlieDerivBilin_apply_vectorField`), and `C^m` section regularity (`contMDiffAt_mlieDerivBilin`,
`contMDiff_mlieDerivBilin`, `Manifold.lieDerivBilinearSection`).

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed. (2013), Corollary 12.33.
* P. Petersen, *Riemannian Geometry*, 3rd ed. (2016), Chapter 2.
-/

public section

noncomputable section

open Set Filter Bundle VectorField
open scoped ContDiff Manifold Topology

attribute [local instance 1001] NormedAddCommGroup.toSeminormedAddCommGroup
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid NormedSpace.toModule

private local instance {𝕜 V G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    NormedAddCommGroup (V →L[𝕜] G) := ContinuousLinearMap.toNormedAddCommGroup

private local instance {𝕜 V G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    NormedSpace 𝕜 (V →L[𝕜] G) := ContinuousLinearMap.toNormedSpace

namespace TauCeti

variable {𝕜 E H M G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

section LieDeriv

/-- The Lie derivative of a covariant two-tensor `b` along `V` within `s` at `x`. -/
def mlieDerivBilinWithin (I : ModelWithCorners 𝕜 E H) (V : (x : M) → TangentSpace I x)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) (s : Set M) (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G :=
  lieDerivBilinWithin (E := E)
    (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
    (inChartAtBilin I x b) ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x)

/-- The Lie derivative of a covariant two-tensor `b` along a vector field `V`. -/
def mlieDerivBilin (I : ModelWithCorners 𝕜 E H) (V : (x : M) → TangentSpace I x)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G :=
  mlieDerivBilinWithin I V b univ x

theorem mlieDerivBilinWithin_def (V : (x : M) → TangentSpace I x)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) (s : Set M) (x : M) :
    mlieDerivBilinWithin I V b s x =
      lieDerivBilinWithin (E := E)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
        (inChartAtBilin I x b) ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by
  rfl

@[simp] theorem mlieDerivBilinWithin_univ (V : (x : M) → TangentSpace I x)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    mlieDerivBilinWithin I V b univ = mlieDerivBilin I V b := by rfl

theorem mlieDerivBilin_def (V : (x : M) → TangentSpace I x)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) (x : M) :
    mlieDerivBilin I V b x =
      lieDerivBilinWithin (E := E)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
        (inChartAtBilin I x b) (range I) (extChartAt I x x) := by
  rw [← mlieDerivBilinWithin_univ, mlieDerivBilinWithin_def, preimage_univ, univ_inter]

@[simp] theorem mlieDerivBilinWithin_modelSpace (V : (x : E) → TangentSpace 𝓘(𝕜, E) x)
    (b : (x : E) → TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, E) x →L[𝕜] G)
    (s : Set E) (x : E) :
    mlieDerivBilinWithin 𝓘(𝕜, E) V b s x = lieDerivBilinWithin (E := E) V b s x := by
  simp only [mlieDerivBilinWithin_def, inChartAtBilin_modelSpace, extChartAt_model_space_eq_id,
    PartialEquiv.refl_symm, PartialEquiv.refl_coe, preimage_id, modelWithCornersSelf_coe,
    range_id, inter_univ, id_eq, VectorField.mpullbackWithin_univ, VectorField.mpullback_id]
  -- `TangentSpace 𝓘(𝕜, E) x` is definitionally `E`, so the chart pullback coincides with `V`.
  rfl

@[simp] theorem mlieDerivBilin_modelSpace (V : (x : E) → TangentSpace 𝓘(𝕜, E) x)
    (b : (x : E) → TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, E) x →L[𝕜] G) (x : E) :
    mlieDerivBilin 𝓘(𝕜, E) V b x = lieDerivBilin (E := E) V b x := by
  rw [← mlieDerivBilinWithin_univ, mlieDerivBilinWithin_modelSpace]
  exact congrFun (lieDerivBilinWithin_univ (E := E) V b) x

/-- Variant of `mlieDerivBilinWithin_congr_set` where the sets only coincide on the complement of a
point. -/
theorem mlieDerivBilinWithin_congr_set' {V : (x : M) → TangentSpace I x}
    {b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G} {s t : Set M} {x : M}
    (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    mlieDerivBilinWithin I V b s x = mlieDerivBilinWithin I V b t x := by
  rw [mlieDerivBilinWithin_def, mlieDerivBilinWithin_def]
  exact lieDerivBilinWithin_congr_set' (extChartAt I x x)
    (preimage_extChartAt_eventuallyEqSet_compl_singleton y h)

/-- `mlieDerivBilinWithin` only depends on the germ of the set `s` at `x`. -/
theorem mlieDerivBilinWithin_congr_set {V : (x : M) → TangentSpace I x}
    {b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G} {s t : Set M} {x : M}
    (h : s =ᶠ[𝓝 x] t) :
    mlieDerivBilinWithin I V b s x = mlieDerivBilinWithin I V b t x :=
  mlieDerivBilinWithin_congr_set' x <| h.filter_mono inf_le_left

/-- Congruence of `mlieDerivBilinWithin` for vector fields and covariant two-tensors agreeing on
`𝓝[s] x` and at `x`. -/
theorem _root_.Filter.EventuallyEq.mlieDerivBilinWithin_eq
    {V₁ V : (x : M) → TangentSpace I x}
    {b₁ b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G} {s : Set M} {x : M}
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hxV : V₁ x = V x)
    (hb : ∀ᶠ y in 𝓝[s] x, b₁ y = b y) (hxb : b₁ x = b x) :
    mlieDerivBilinWithin I V₁ b₁ s x = mlieDerivBilinWithin I V b s x := by
  rw [mlieDerivBilinWithin_def, mlieDerivBilinWithin_def]
  have hpreV :=
    (continuousAt_extChartAt_symm (I := I) x).continuousWithinAt.preimage_mem_nhdsWithin''
      hV (by simp)
  have hpreb :=
    (continuousAt_extChartAt_symm (I := I) x).continuousWithinAt.preimage_mem_nhdsWithin''
      hb (by simp)
  refine Filter.EventuallyEq.lieDerivBilinWithin_eq (E := E) ?_ ?_ ?_ ?_
  · refine nhdsWithin_mono _ inter_subset_left ?_
    filter_upwards [hpreV] with z hz
    simp only [VectorField.mpullbackWithin_apply]
    exact congrArg _ hz
  · simp only [VectorField.mpullbackWithin_apply]
    have hxV' : V₁ ((extChartAt I x).symm (extChartAt I x x)) =
        V ((extChartAt I x).symm (extChartAt I x x)) := by
      rw [extChartAt_to_inv]
      exact hxV
    exact congrArg _ hxV'
  · refine nhdsWithin_mono _ inter_subset_left ?_
    filter_upwards [hpreb] with z hz
    ext u w
    simp only [inChartAtBilin_apply]
    exact DFunLike.congr_fun (DFunLike.congr_fun hz _) _
  · rw [inChartAtBilin_extChartAt_self, inChartAtBilin_extChartAt_self, hxb]

/-- Congruence of `mlieDerivBilinWithin` for vector fields and covariant two-tensors agreeing on a
neighbourhood of `x`. -/
theorem _root_.Filter.EventuallyEq.mlieDerivBilinWithin_eq_nhds
    {V₁ V : (x : M) → TangentSpace I x}
    {b₁ b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G} {s : Set M} {x : M}
    (hV : V₁ =ᶠ[𝓝 x] V) (hb : ∀ᶠ y in 𝓝 x, b₁ y = b y) :
    mlieDerivBilinWithin I V₁ b₁ s x = mlieDerivBilinWithin I V b s x :=
  (hV.filter_mono nhdsWithin_le_nhds).mlieDerivBilinWithin_eq hV.self_of_nhds
    (hb.filter_mono nhdsWithin_le_nhds) hb.self_of_nhds

/-- Congruence of `mlieDerivBilin` for vector fields and covariant two-tensors agreeing on a
neighbourhood of `x`. -/
theorem _root_.Filter.EventuallyEq.mlieDerivBilin_eq
    {V₁ V : (x : M) → TangentSpace I x}
    {b₁ b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G} {x : M}
    (hV : V₁ =ᶠ[𝓝 x] V) (hb : ∀ᶠ y in 𝓝 x, b₁ y = b y) :
    mlieDerivBilin I V₁ b₁ x = mlieDerivBilin I V b x :=
  hV.mlieDerivBilinWithin_eq_nhds hb

@[simp] theorem mlieDerivBilinWithin_zero (V : (x : M) → TangentSpace I x) (s : Set M) (x : M) :
    mlieDerivBilinWithin I V
      (0 : (y : M) → TangentSpace I y →L[𝕜] TangentSpace I y →L[𝕜] G) s x = 0 := by
  rw [mlieDerivBilinWithin_def, inChartAtBilin_zero]; exact lieDerivBilinWithin_zero (E := E) _ _ _

@[simp] theorem mlieDerivBilin_zero (V : (x : M) → TangentSpace I x) :
    mlieDerivBilin I V (0 : (y : M) → TangentSpace I y →L[𝕜] TangentSpace I y →L[𝕜] G) = 0 :=
  funext (mlieDerivBilinWithin_zero V univ)

/-- The Lie derivative along the zero vector field within `s` vanishes. -/
@[simp] theorem mlieDerivBilinWithin_zero_left
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) (s : Set M) (x : M) :
    mlieDerivBilinWithin I (0 : (x : M) → TangentSpace I x) b s x = 0 := by
  rw [mlieDerivBilinWithin_def, VectorField.mpullbackWithin_zero]
  exact lieDerivBilinWithin_zero_left (E := E) _ _ _

@[simp] theorem mlieDerivBilin_zero_left
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    mlieDerivBilin I (0 : (x : M) → TangentSpace I x) b = 0 :=
  funext (mlieDerivBilinWithin_zero_left b univ)

/-- Negating the vector field negates `mlieDerivBilinWithin`. -/
theorem mlieDerivBilinWithin_neg_left (V : (x : M) → TangentSpace I x)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G)
    {s : Set M} {x : M} (hs : UniqueMDiffWithinAt I s x) :
    mlieDerivBilinWithin I (-V) b s x = -mlieDerivBilinWithin I V b s x := by
  rw [mlieDerivBilinWithin_def, VectorField.mpullbackWithin_neg]
  exact lieDerivBilinWithin_neg_left (E := E) _ _ hs

/-- Negating the vector field negates `mlieDerivBilin`. -/
@[simp] theorem mlieDerivBilin_neg_left (V : (x : M) → TangentSpace I x)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    mlieDerivBilin I (-V) b = -mlieDerivBilin I V b :=
  funext fun _ ↦ mlieDerivBilinWithin_neg_left V b (uniqueMDiffWithinAt_univ I)

/-- Constant scalar multiplication on the vector field commutes with `mlieDerivBilinWithin`. -/
theorem mlieDerivBilinWithin_const_smul_left (c : 𝕜) (V : (x : M) → TangentSpace I x)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G)
    {s : Set M} {x : M} (hs : UniqueMDiffWithinAt I s x) :
    mlieDerivBilinWithin I (c • V) b s x = c • mlieDerivBilinWithin I V b s x := by
  rw [mlieDerivBilinWithin_def, VectorField.mpullbackWithin_const_smul]
  exact lieDerivBilinWithin_const_smul_left (E := E) c _ _ hs

/-- Constant scalar multiplication on the vector field commutes with `mlieDerivBilin`. -/
@[simp] theorem mlieDerivBilin_const_smul_left (c : 𝕜) (V : (x : M) → TangentSpace I x)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    mlieDerivBilin I (c • V) b = c • mlieDerivBilin I V b :=
  funext fun _ ↦ mlieDerivBilinWithin_const_smul_left c V b (uniqueMDiffWithinAt_univ I)

@[simp] theorem mlieDerivBilinWithin_neg (V : (x : M) → TangentSpace I x)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G)
    {s : Set M} {x : M} (hs : UniqueMDiffWithinAt I s x) :
    mlieDerivBilinWithin I V (-b) s x = -mlieDerivBilinWithin I V b s x := by
  rw [mlieDerivBilinWithin_def, inChartAtBilin_neg]; exact lieDerivBilinWithin_neg (E := E) _ _ hs

@[simp] theorem mlieDerivBilin_neg (V : (x : M) → TangentSpace I x)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    mlieDerivBilin I V (-b) = -mlieDerivBilin I V b :=
  funext fun _ ↦ mlieDerivBilinWithin_neg V b (uniqueMDiffWithinAt_univ I)

@[simp] theorem mlieDerivBilinWithin_smul (V : (x : M) → TangentSpace I x) (c : 𝕜)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G)
    {s : Set M} {x : M} (hs : UniqueMDiffWithinAt I s x) :
    mlieDerivBilinWithin I V (c • b) s x = c • mlieDerivBilinWithin I V b s x := by
  rw [mlieDerivBilinWithin_def, inChartAtBilin_smul]; exact lieDerivBilinWithin_smul (E := E) c _ hs

@[simp] theorem mlieDerivBilin_smul (V : (x : M) → TangentSpace I x) (c : 𝕜)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    mlieDerivBilin I V (c • b) = c • mlieDerivBilin I V b :=
  funext fun _ ↦ mlieDerivBilinWithin_smul V c b (uniqueMDiffWithinAt_univ I)

theorem mlieDerivBilinWithin_symm (V : (x : M) → TangentSpace I x)
    {b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G}
    (hb : ∀ y v w, b y v w = b y w v) {s : Set M} {x : M} (hs : UniqueMDiffWithinAt I s x)
    (v w : TangentSpace I x) :
    mlieDerivBilinWithin I V b s x v w = mlieDerivBilinWithin I V b s x w v := by
  have hflip : (fun z ↦ (inChartAtBilin I x b z).flip) = inChartAtBilin I x b := by
    funext z; ext u₁ u₂; simp only [ContinuousLinearMap.flip_apply, inChartAtBilin_apply]
    exact hb _ _ _
  have h := lieDerivBilinWithin_flip (E := E)
    (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
    (inChartAtBilin I x b) hs
  rw [hflip] at h; exact (DFunLike.congr_fun (DFunLike.congr_fun h w) v).symm

theorem mlieDerivBilin_symm (V : (x : M) → TangentSpace I x)
    {b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G}
    (hb : ∀ y v w, b y v w = b y w v) (x : M) (v w : TangentSpace I x) :
    mlieDerivBilin I V b x v w = mlieDerivBilin I V b x w v :=
  mlieDerivBilinWithin_symm V hb (uniqueMDiffWithinAt_univ I) v w

variable [IsManifold I 1 M] {V V₁ V₂ X Y : (x : M) → TangentSpace I x}
  {b b₁ b₂ : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G} {s : Set M} {x : M}

private local instance instIsNormableSpaceTangentSpace (y : M) :
    IsNormableSpace 𝕜 (TangentSpace I y) :=
  (VectorBundle.continuousLinearEquivAt 𝕜 E (TangentSpace I : M → Type _) y).isNormableSpace

theorem mlieDerivBilinWithin_add (hs : UniqueMDiffWithinAt I s x)
    (hb₁ : MDifferentiableWithinAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b₁ y)) s x)
    (hb₂ : MDifferentiableWithinAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b₂ y)) s x) :
    mlieDerivBilinWithin I V (b₁ + b₂) s x =
      mlieDerivBilinWithin I V b₁ s x + mlieDerivBilinWithin I V b₂ s x := by
  rw [mlieDerivBilinWithin_def, inChartAtBilin_add]
  exact lieDerivBilinWithin_add (E := E) hs (differentiableWithinAt_inChartAtBilin hb₁)
    (differentiableWithinAt_inChartAtBilin hb₂)

theorem mlieDerivBilin_add
    (hb₁ : MDifferentiableAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b₁ y)) x)
    (hb₂ : MDifferentiableAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b₂ y)) x) :
    mlieDerivBilin I V (b₁ + b₂) x = mlieDerivBilin I V b₁ x + mlieDerivBilin I V b₂ x :=
  mlieDerivBilinWithin_add (uniqueMDiffWithinAt_univ I) hb₁.mdifferentiableWithinAt
    hb₂.mdifferentiableWithinAt

theorem mlieDerivBilin_sub
    (hb₁ : MDifferentiableAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b₁ y)) x)
    (hb₂ : MDifferentiableAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b₂ y)) x) :
    mlieDerivBilin I V (b₁ - b₂) x = mlieDerivBilin I V b₁ x - mlieDerivBilin I V b₂ x := by
  rw [sub_eq_add_neg, mlieDerivBilin_add hb₁ (mdifferentiableAt_neg_section hb₂),
    mlieDerivBilin_neg, Pi.neg_apply, ← sub_eq_add_neg]

/-- Leibniz rule for multiplying a covariant two-tensor by a scalar function within `s`. -/
theorem mlieDerivBilinWithin_fun_smul {f : M → 𝕜} (hs : UniqueMDiffWithinAt I s x)
    (hf : MDifferentiableWithinAt I 𝓘(𝕜) f s x)
    (hb : MDifferentiableWithinAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b y)) s x) :
    mlieDerivBilinWithin I V (fun y ↦ f y • b y) s x =
      mvfderivWithin I f s x (V x) • b x + f x • mlieDerivBilinWithin I V b s x := by
  have hf_chart : DifferentiableWithinAt 𝕜 (f ∘ (extChartAt I x).symm)
      ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by
    simpa only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.comp_def, id_eq] using hf.differentiableWithinAt_writtenInExtChartAt
  rw [mlieDerivBilinWithin_def, inChartAtBilin_fun_smul]
  refine (lieDerivBilinWithin_fun_smul (E := E) hs hf_chart
    (differentiableWithinAt_inChartAtBilin hb)).trans ?_
  have hdf : fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) ((extChartAt I x).symm ⁻¹' s ∩ range I)
      (extChartAt I x x) (V x) = mvfderivWithin I f s x (V x) := by
    rw [hf.mvfderivWithin]
    -- `tangentSpaceCastModel` and `NormedSpace.fromTangentSpace` are definitionally the identity.
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp]
    rfl
  have hVx : (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I)
      (extChartAt I x x) : E) = (V x : E) :=
    VectorField.mpullbackWithin_extChartAt_symm_self V x
  have hfx : (f ∘ (extChartAt I x).symm) (extChartAt I x x) = f x :=
    congrArg f (extChartAt_to_inv x)
  rw [hVx, inChartAtBilin_extChartAt_self, hfx, hdf, ← mlieDerivBilinWithin_def]
  -- Identify `E →L[𝕜] E →L[𝕜] G` with `TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G`.
  rfl

theorem mlieDerivBilin_fun_smul {f : M → 𝕜} (hf : MDifferentiableAt I 𝓘(𝕜) f x)
    (hb : MDifferentiableAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b y)) x) :
    mlieDerivBilin I V (fun y ↦ f y • b y) x =
      mvfderiv I f x (V x) • b x + f x • mlieDerivBilin I V b x := by
  simpa only [mlieDerivBilinWithin_univ, mvfderivWithin_univ] using
    mlieDerivBilinWithin_fun_smul (uniqueMDiffWithinAt_univ I) hf.mdifferentiableWithinAt
      hb.mdifferentiableWithinAt

theorem mlieDerivBilinWithin_add_left
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) (hs : UniqueMDiffWithinAt I s x)
    (hV₁ : MDifferentiableWithinAt I I.tangent (fun y ↦ (V₁ y : TangentBundle I M)) s x)
    (hV₂ : MDifferentiableWithinAt I I.tangent (fun y ↦ (V₂ y : TangentBundle I M)) s x) :
    mlieDerivBilinWithin I (V₁ + V₂) b s x =
      mlieDerivBilinWithin I V₁ b s x + mlieDerivBilinWithin I V₂ b s x := by
  simp only [mlieDerivBilinWithin_def, VectorField.mpullbackWithin_add]
  exact lieDerivBilinWithin_add_left (E := E) _ hs
    hV₁.differentiableWithinAt_mpullbackWithin_extChartAt_symm
    hV₂.differentiableWithinAt_mpullbackWithin_extChartAt_symm

theorem mlieDerivBilin_add_left (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G)
    (hV₁ : MDifferentiableAt I I.tangent (fun y ↦ (V₁ y : TangentBundle I M)) x)
    (hV₂ : MDifferentiableAt I I.tangent (fun y ↦ (V₂ y : TangentBundle I M)) x) :
    mlieDerivBilin I (V₁ + V₂) b x = mlieDerivBilin I V₁ b x + mlieDerivBilin I V₂ b x :=
  mlieDerivBilinWithin_add_left b (uniqueMDiffWithinAt_univ I) hV₁.mdifferentiableWithinAt
    hV₂.mdifferentiableWithinAt

private theorem fderivWithin_inChartAtBilin_apply_mpullbackWithin
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G)
    (X Y : (y : M) → TangentSpace I y)
    (hb : DifferentiableWithinAt 𝕜 (inChartAtBilin I x b)
      ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x))
    (hX : DifferentiableWithinAt 𝕜
      (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm X (range I))
      ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x))
    (hY : DifferentiableWithinAt 𝕜
      (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm Y (range I))
      ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x)) :
    fderivWithin 𝕜 (fun z ↦ inChartAtBilin I x b z
      (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm X (range I) z)
      (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm Y (range I) z))
      ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) =
        mvfderivWithin I (fun y ↦ b y (X y) (Y y)) s x := by
  have heq : (fun z ↦ inChartAtBilin I x b z
      (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm X (range I) z)
      (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm Y (range I) z))
      =ᶠ[𝓝[range I] (extChartAt I x x)] (fun y ↦ b y (X y) (Y y)) ∘ (extChartAt I x).symm := by
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with z hz
    exact (inChartAtBilin_apply x b z _ _).trans (congrArg₂ (fun u₁ u₂ ↦ b _ u₁ u₂)
      ((isInvertible_mfderivWithin_extChartAt_symm hz).self_apply_inverse _)
      ((isInvertible_mfderivWithin_extChartAt_symm hz).self_apply_inverse _))
  have hpoint := heq.self_of_nhdsWithin (mem_range_self (chartAt H x x))
  have heqs := heq.filter_mono (nhdsWithin_mono _
    (inter_subset_right (s := (extChartAt I x).symm ⁻¹' s)))
  have hp := (((hb.clm_apply hX).clm_apply hY).congr_of_eventuallyEq heqs.symm hpoint.symm
    ).mdifferentiableWithinAt_of_comp_extChartAt_symm
  rw [hp.mvfderivWithin]
  simpa only [writtenInExtChartAt, extChartAt_self_eq, PartialEquiv.refl_coe,
    modelWithCornersSelf_coe, Function.id_comp] using heqs.fderivWithin_eq hpoint

/-- **The bracket formula** within `s`: `(L_V b)_x (X_x, Y_x) = V_x (b (X, Y)) -
b_x ([V, X]_x, Y_x) - b_x (X_x, [V, Y]_x)`. -/
theorem mlieDerivBilinWithin_apply_vectorField
    (hb : MDifferentiableWithinAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b y)) s x)
    (hX : MDifferentiableWithinAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) s x)
    (hY : MDifferentiableWithinAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) s x)
    (hs : UniqueMDiffWithinAt I s x) :
    mlieDerivBilinWithin I V b s x (X x) (Y x) =
      mvfderivWithin I (fun y ↦ b y (X y) (Y y)) s x (V x) -
        b x (mlieBracketWithin I V X s x) (Y x) - b x (X x) (mlieBracketWithin I V Y s x) := by
  let V' : E → E := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I)
  let X' : E → E := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm X (range I)
  let Y' : E → E := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm Y (range I)
  have hb' := differentiableWithinAt_inChartAtBilin hb
  have hX' : DifferentiableWithinAt 𝕜 X'
      ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) :=
    hX.differentiableWithinAt_mpullbackWithin_extChartAt_symm
  have hY' : DifferentiableWithinAt 𝕜 Y'
      ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) :=
    hY.differentiableWithinAt_mpullbackWithin_extChartAt_symm
  have hVx : V' (extChartAt I x x) = (V x : E) :=
    VectorField.mpullbackWithin_extChartAt_symm_self V x
  have hXx : X' (extChartAt I x x) = (X x : E) :=
    VectorField.mpullbackWithin_extChartAt_symm_self X x
  have hYx : Y' (extChartAt I x x) = (Y x : E) :=
    VectorField.mpullbackWithin_extChartAt_symm_self Y x
  have hflat := lieDerivBilinWithin_apply_vectorField (E := E) (V := V') (X := X') (Y := Y')
    hs hb' hX' hY'
  rw [hVx, hXx, hYx, inChartAtBilin_extChartAt_self,
    fderivWithin_inChartAtBilin_apply_mpullbackWithin b X Y hb' hX' hY',
    VectorField.lieBracketWithin_mpullbackWithin_extChartAt_symm V X s x,
    VectorField.lieBracketWithin_mpullbackWithin_extChartAt_symm V Y s x] at hflat
  exact hflat

/-- **The bracket formula:** `(L_V b)_x (X_x, Y_x) = V_x (b (X, Y)) - b_x ([V, X]_x, Y_x) -
b_x (X_x, [V, Y]_x)`. -/
theorem mlieDerivBilin_apply_vectorField
    (hb : MDifferentiableAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b y)) x)
    (hX : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    (hY : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x) :
    mlieDerivBilin I V b x (X x) (Y x) =
      mvfderiv I (fun y ↦ b y (X y) (Y y)) x (V x) -
        b x (mlieBracket I V X x) (Y x) - b x (X x) (mlieBracket I V Y x) := by
  simpa only [mlieDerivBilinWithin_univ, mvfderivWithin_univ, mlieBracketWithin_univ] using
    mlieDerivBilinWithin_apply_vectorField (V := V) hb.mdifferentiableWithinAt
      hX.mdifferentiableWithinAt hY.mdifferentiableWithinAt (uniqueMDiffWithinAt_univ I)

end LieDeriv

section Regularity

variable {V : (x : M) → TangentSpace I x}
  {b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G}

private theorem mvfderiv_apply_trivializationAt_symm_eq [IsManifold I 2 M]
    (x₀ : M) {z : E} (hz : z ∈ (extChartAt I x₀).target)
    (hb : MDifferentiableAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun q ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) q (b q)) ((extChartAt I x₀).symm z))
    (u w : E) :
    mvfderiv I (fun q ↦ b q ((trivializationAt E (TangentSpace I) x₀).symm q u)
        ((trivializationAt E (TangentSpace I) x₀).symm q w))
      ((extChartAt I x₀).symm z) (V ((extChartAt I x₀).symm z)) =
      fderivWithin 𝕜 (inChartAtBilin I x₀ b) (range I) z
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I) z) u w := by
  let _ : IsManifold I 1 M := IsManifold.of_le one_le_two
  set g : M → G := fun q ↦ b q ((trivializationAt E (TangentSpace I) x₀).symm q u)
    ((trivializationAt E (TangentSpace I) x₀).symm q w)
  have hpair_eq : (g ∘ (extChartAt I x₀).symm) =ᶠ[𝓝[range I] z]
      fun ζ ↦ inChartAtBilin I x₀ b ζ u w := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hz] with ζ hζ
    simp only [g, Function.comp_apply, TangentBundle.trivializationAt_symm_extChartAt_symm x₀ hζ,
      inChartAtBilin_apply]
  rw [← fderivWithin_chart_apply_mpullbackWithin (I := I) (p := g) (U := V) hz,
    hpair_eq.fderivWithin_eq (hpair_eq.self_of_nhdsWithin (extChartAt_target_subset_range x₀ hz))]
  exact DFunLike.congr_fun ((((ContinuousLinearMap.apply 𝕜 G w).comp
    (ContinuousLinearMap.apply 𝕜 (E →L[𝕜] G) u)).hasFDerivAt.comp_hasFDerivWithinAt z
      (differentiableWithinAt_inChartAtBilin_of_mem x₀ hz hb).hasFDerivWithinAt).fderivWithin
        (I.uniqueDiffOn _ (extChartAt_target_subset_range x₀ hz))) _

variable [CompleteSpace E] [IsManifold I (minSmoothness 𝕜 2) M]

/-- `minSmoothness 𝕜 2` gives `C¹` atlas smoothness. -/
local instance : IsManifold I 1 M :=
  IsManifold.of_le ((show (1 : ℕ∞ω) ≤ 2 by norm_num).trans (le_minSmoothness (𝕜 := 𝕜)))

private theorem trivializationAt_mlieDerivBilin_eq
    (x₀ : M) {z : E} (hz : z ∈ (extChartAt I x₀).target)
    (hV : MDifferentiableAt I I.tangent (T% V) ((extChartAt I x₀).symm z))
    (hb : MDifferentiableAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun q ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) q (b q)) ((extChartAt I x₀).symm z)) :
    (trivializationAt (E →L[𝕜] E →L[𝕜] G)
      (fun q : M ↦ TangentSpace I q →L[𝕜] TangentSpace I q →L[𝕜] G) x₀
        ⟨(extChartAt I x₀).symm z, mlieDerivBilin I V b ((extChartAt I x₀).symm z)⟩).2 =
      lieDerivBilinWithin (E := E)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I))
        (inChartAtBilin I x₀ b) (range I) z := by
  let _ : IsManifold I 2 M := IsManifold.of_le (le_minSmoothness (𝕜 := 𝕜))
  have hy_chart : (extChartAt I x₀).symm z ∈ (chartAt H x₀).source := by
    simpa only [extChartAt_source] using (extChartAt I x₀).map_target hz
  rw [← inChartAtBilin_eq_trivializationAt x₀ (mlieDerivBilin I V b) hz]
  ext u w
  rw [inChartAtBilin_apply,
    ← TangentBundle.trivializationAt_symm_extChartAt_symm x₀ hz u,
    ← TangentBundle.trivializationAt_symm_extChartAt_symm x₀ hz w,
    mlieDerivBilin_apply_vectorField hb
      (TangentBundle.mdifferentiableAt_trivializationAt_symm x₀ hy_chart u)
      (TangentBundle.mdifferentiableAt_trivializationAt_symm x₀ hy_chart w),
    mvfderiv_apply_trivializationAt_symm_eq x₀ hz hb u w,
    VectorField.mlieBracket_trivializationAt_symm_eq x₀ hz hV u,
    VectorField.mlieBracket_trivializationAt_symm_eq x₀ hz hV w,
    TangentBundle.trivializationAt_symm_extChartAt_symm x₀ hz u,
    TangentBundle.trivializationAt_symm_extChartAt_symm x₀ hz w,
    map_neg, neg_apply, map_neg, sub_neg_eq_add, sub_neg_eq_add]
  simp only [← inChartAtBilin_apply]
  exact (lieDerivBilinWithin_apply (E := E)
    (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I))
    (inChartAtBilin I x₀ b) (range I) z u w).symm

variable {m n k : ℕ∞ω} [IsManifold I k M]

omit [CompleteSpace E] in
private theorem contDiffWithinAt_lieDerivBilinWithin_inChartAtBilin {x₀ : M}
    (hk : m + 2 ≤ k) (hmn : m + 1 ≤ n) (hV : ContMDiffAt I I.tangent n (T% V) x₀)
    (hb : ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G)) n
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b y)) x₀) :
    ContDiffWithinAt 𝕜 m
      (lieDerivBilinWithin (E := E)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I))
        (inChartAtBilin I x₀ b) (range I))
      (range I) (extChartAt I x₀ x₀) := by
  let _ : IsManifold I (m + 1 + 1) M :=
    IsManifold.of_le (n := k) (by simpa only [add_assoc, one_add_one_eq_two] using hk)
  let _ : IsManifold I (m + 1) M := IsManifold.of_le (n := m + 1 + 1) le_self_add
  let V₀ : E → E := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I)
  set B₀ := inChartAtBilin I x₀ b
  have hV₀ : ContDiffWithinAt 𝕜 (m + 1) V₀ (extChartAt I x₀).target (extChartAt I x₀ x₀) := by
    have h := ((hV.of_le hmn).contMDiffWithinAt (s := univ)
      ).contDiffWithinAt_mpullbackWithin_extChartAt_symm
    rw [preimage_univ, univ_inter] at h; exact h.mono (extChartAt_target_subset_range x₀)
  have hB₀ : ContDiffWithinAt 𝕜 (m + 1) B₀ (extChartAt I x₀).target (extChartAt I x₀ x₀) := by
    have h := contDiffWithinAt_inChartAtBilin (n := m + 1) (s := univ)
      (hb.of_le hmn).contMDiffWithinAt
    rw [preimage_univ, univ_inter] at h; exact h.mono (extChartAt_target_subset_range x₀)
  have hu_t : UniqueDiffOn 𝕜 (extChartAt I x₀).target := by
    simpa using (uniqueMDiffOn_univ (I := I)).uniqueDiffOn_target_inter x₀
  rw [contDiffWithinAt_congr_set
    (extChartAt_target_eventuallyEqSet_of_mem (mem_extChartAt_target x₀)).symm]
  refine (contDiffWithinAt_lieDerivBilinWithin hV₀ hB₀ hu_t
    (mem_extChartAt_target x₀) le_rfl).congr_of_eventuallyEq_of_mem ?_ (mem_extChartAt_target x₀)
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact lieDerivBilinWithin_congr_set (extChartAt_target_eventuallyEqSet_of_mem hz).symm

/-- **`C^m` section regularity of the Lie derivative of covariant two-tensors.** -/
theorem contMDiffAt_mlieDerivBilin {x₀ : M}
    (hk : m + 2 ≤ k) (hmn : m + 1 ≤ n) (hV : ContMDiffAt I I.tangent n (T% V) x₀)
    (hb : ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G)) n
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b y)) x₀) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G)) m
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (mlieDerivBilin I V b y)) x₀ := by
  -- Step 1: Flat `C^m` regularity of the chart Lie derivative within `range I`.
  have hflat_r := contDiffWithinAt_lieDerivBilinWithin_inChartAtBilin hk hmn hV hb
  -- Step 2: Obtain neighbourhood differentiability of `V` and `b` around `x₀`.
  have hle : (1 : ℕ∞ω) ≤ m + 1 := le_add_self
  have hV_nhds := ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1
    ((hV.of_le hmn).of_le hle)).mono fun _ hy ↦ hy.mdifferentiableAt one_ne_zero
  have hb_nhds := ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1
    ((hb.of_le hmn).of_le hle)).mono fun _ hy ↦ hy.mdifferentiableAt one_ne_zero
  -- Step 3: Identify the hom-bundle trivialization of `mlieDerivBilin I V b` with the flat chart
  -- Lie derivative near `extChartAt I x₀ x₀` within `range I`.
  rw [contMDiffAt_section_iff, ← contMDiffWithinAt_univ, contMDiffWithinAt_iff_source,
    contMDiffWithinAt_iff_contDiffWithinAt]
  simp only [preimage_univ, univ_inter]
  refine hflat_r.congr_of_eventuallyEq_of_mem ?_
    (extChartAt_target_subset_range x₀ (mem_extChartAt_target x₀))
  have hsymm := (continuousAt_extChartAt_symm'' (I := I)
    (mem_extChartAt_target x₀)).continuousWithinAt (s := range I)
  have hx₀ : (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ := extChartAt_to_inv x₀
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x₀,
    hsymm.eventually (hx₀ ▸ hV_nhds), hsymm.eventually (hx₀ ▸ hb_nhds)] with z hz hVz hbz
  exact trivializationAt_mlieDerivBilin_eq x₀ hz hVz hbz

/-- Global `C^m` section regularity of `mlieDerivBilin` when `V` and `b` are `C^n` with
`m + 1 ≤ n` and `m + 2 ≤ k`. -/
theorem contMDiff_mlieDerivBilin
    (hk : m + 2 ≤ k) (hmn : m + 1 ≤ n) (hV : ContMDiff I I.tangent n (T% V))
    (hb : ContMDiff I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G)) n
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b y))) :
    ContMDiff I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G)) m
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (mlieDerivBilin I V b y)) :=
  fun x₀ ↦ contMDiffAt_mlieDerivBilin hk hmn (hV x₀) (hb x₀)

namespace Manifold

variable (G) in
/-- The Lie derivative along a `C^n` vector field `V`, bundled as a linear map from `C^n` bilinear
sections to `C^m` bilinear sections (`m + 1 ≤ n`, `m + 2 ≤ k`). -/
def lieDerivBilinearSection (hk : m + 2 ≤ k) (hmn : m + 1 ≤ n)
    {V : (x : M) → TangentSpace I x} (hV : ContMDiff I I.tangent n (T% V)) :
    BilinearSection I E (TangentSpace I : M → Type _) G n →ₗ[𝕜]
      BilinearSection I E (TangentSpace I : M → Type _) G m :=
  { toFun b := ⟨mlieDerivBilin I V b, contMDiff_mlieDerivBilin hk hmn hV b.contMDiff⟩
    map_add' b₁ b₂ := by
      ext x v w
      have hle : (1 : ℕ∞ω) ≤ n := (show (1 : ℕ∞ω) ≤ m + 1 from le_add_self).trans hmn
      simp only [ContMDiffSection.coe_add, ContMDiffSection.coeFn_mk, Pi.add_apply, add_apply]
      rw [mlieDerivBilin_add ((b₁.contMDiff x).of_le hle |>.mdifferentiableAt one_ne_zero)
        ((b₂.contMDiff x).of_le hle |>.mdifferentiableAt one_ne_zero), add_apply, add_apply]
    map_smul' c b := by
      ext x v w
      simp only [ContMDiffSection.coe_smul, ContMDiffSection.coeFn_mk, RingHom.id_apply,
        Pi.smul_apply, mlieDerivBilin_smul] }

@[simp] theorem lieDerivBilinearSection_apply (hk : m + 2 ≤ k) (hmn : m + 1 ≤ n)
    {V : (x : M) → TangentSpace I x} (hV : ContMDiff I I.tangent n (T% V))
    (b : BilinearSection I E (TangentSpace I : M → Type _) G n) (x : M) :
    lieDerivBilinearSection G hk hmn hV b x = mlieDerivBilin I V b x := by rfl

/-- The Lie derivative linear map `lieDerivBilinearSection` preserves symmetric sections. -/
theorem lieDerivBilinearSection_mem_symmetric (hk : m + 2 ≤ k) (hmn : m + 1 ≤ n)
    {V : (x : M) → TangentSpace I x} (hV : ContMDiff I I.tangent n (T% V))
    {b : BilinearSection I E (TangentSpace I : M → Type _) G n}
    (hb : b ∈ symmetricBilinearSections) :
    lieDerivBilinearSection G hk hmn hV b ∈ symmetricBilinearSections :=
  (mem_symmetricBilinearSections _).2 fun x v w ↦
    mlieDerivBilin_symm V ((mem_symmetricBilinearSections b).1 hb) x v w

end Manifold

end Regularity

end TauCeti
