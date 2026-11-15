/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.LieDerivBilinear
public import TauCeti.Geometry.Manifold.VectorBundle.Bilinear.Pullback
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Lie derivative of covariant two-tensors on manifolds

The Lie derivative `TauCeti.mlieDerivBilinWithin I V b s x` (and its unrestricted form
`TauCeti.mlieDerivBilin I V b x`) of a covariant two-tensor
`b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G` along a vector field `V` is
defined directly in the preferred chart at `x` via the flat operator `TauCeti.lieDerivBilinWithin`,
without flows, completeness, or finite-dimensionality, and allowing boundary and corner points.

Intrinsicness and bundle regularity are established by two main results:

* **The bracket formula** (`TauCeti.mlieDerivBilinWithin_apply_vectorField`,
  `TauCeti.mlieDerivBilin_apply_vectorField`): on differentiable vector fields `X` and `Y`,
  `(L_V b)_x (X_x, Y_x) = V_x (b (X, Y)) - b_x ([V, X]_x, Y_x) - b_x (X_x, [V, Y]_x)`.
* **Section regularity** (`TauCeti.contMDiffAt_mlieDerivBilin`, `TauCeti.contMDiff_mlieDerivBilin`,
  `TauCeti.Manifold.lieDerivBilinearSection`): if `V` and `b` are `C^n` sections with
  `m + 1 ≤ n`, then `mlieDerivBilin I V b` is a `C^m` section of the bilinear-map bundle, preserving
  the submodule of symmetric sections.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 12,
  Corollary 12.33.
* P. Petersen, *Riemannian Geometry*, 3rd ed., Springer GTM 171 (2016), Chapter 2.
-/

public section

noncomputable section

open Set Filter Bundle VectorField
open scoped ContDiff Manifold Topology

-- Resolve normed-space vs seminormed-space diamonds on nested continuous linear map spaces.
attribute [local instance 1001] NormedAddCommGroup.toSeminormedAddCommGroup
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid NormedSpace.toModule

private local instance {𝕜 V G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    NormedAddCommGroup (V →L[𝕜] G) := ContinuousLinearMap.toNormedAddCommGroup

private local instance {𝕜 V G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V]
    [NormedSpace 𝕜 V] [NormedAddCommGroup G] [NormedSpace 𝕜 G] :
    NormedSpace 𝕜 (V →L[𝕜] G) := ContinuousLinearMap.toNormedSpace

namespace TauCeti

section LieDeriv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The Lie derivative of a covariant two-tensor `b` along a vector field `V` within a set `s` at
`x`, defined in the preferred chart at `x` via `TauCeti.lieDerivBilinWithin`. -/
def mlieDerivBilinWithin (I : ModelWithCorners 𝕜 E H) (V : (x : M) → TangentSpace I x)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) (s : Set M) (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G :=
  lieDerivBilinWithin (E := E)
    (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
    (inChartAtBilin I x b)
    ((extChartAt I x).symm ⁻¹' s ∩ range I)
    (extChartAt I x x)

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
        (inChartAtBilin I x b)
        ((extChartAt I x).symm ⁻¹' s ∩ range I)
        (extChartAt I x x) := by
  rfl

@[simp]
theorem mlieDerivBilinWithin_univ (V : (x : M) → TangentSpace I x)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    mlieDerivBilinWithin I V b univ = mlieDerivBilin I V b := by
  rfl

theorem mlieDerivBilin_def (V : (x : M) → TangentSpace I x)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) (x : M) :
    mlieDerivBilin I V b x =
      lieDerivBilinWithin (E := E)
        (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
        (inChartAtBilin I x b) (range I) (extChartAt I x x) := by
  rw [← mlieDerivBilinWithin_univ, mlieDerivBilinWithin_def, preimage_univ, univ_inter]

/-- Over the model space `𝓘(𝕜, E)`, `mlieDerivBilinWithin` reduces to `lieDerivBilinWithin`. -/
@[simp]
theorem mlieDerivBilinWithin_modelSpace (V : (x : E) → TangentSpace 𝓘(𝕜, E) x)
    (b : (x : E) → TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, E) x →L[𝕜] G)
    (s : Set E) (x : E) :
    mlieDerivBilinWithin 𝓘(𝕜, E) V b s x = lieDerivBilinWithin (E := E) V b s x := by
  simp only [mlieDerivBilinWithin_def, inChartAtBilin_modelSpace, extChartAt_model_space_eq_id,
    PartialEquiv.refl_symm, PartialEquiv.refl_coe, preimage_id, modelWithCornersSelf_coe,
    range_id, inter_univ, id_eq, VectorField.mpullbackWithin_univ, VectorField.mpullback_id]
  rfl

/-- Over the model space `𝓘(𝕜, E)`, `mlieDerivBilin` reduces to `lieDerivBilin`. -/
@[simp]
theorem mlieDerivBilin_modelSpace (V : (x : E) → TangentSpace 𝓘(𝕜, E) x)
    (b : (x : E) → TangentSpace 𝓘(𝕜, E) x →L[𝕜] TangentSpace 𝓘(𝕜, E) x →L[𝕜] G) (x : E) :
    mlieDerivBilin 𝓘(𝕜, E) V b x = lieDerivBilin (E := E) V b x := by
  rw [← mlieDerivBilinWithin_univ, mlieDerivBilinWithin_modelSpace]
  exact congrFun (lieDerivBilinWithin_univ (E := E) V b) x

@[simp]
theorem mlieDerivBilinWithin_zero (V : (x : M) → TangentSpace I x) (s : Set M) (x : M) :
    mlieDerivBilinWithin I V
      (0 : (y : M) → TangentSpace I y →L[𝕜] TangentSpace I y →L[𝕜] G) s x = 0 := by
  rw [mlieDerivBilinWithin_def, inChartAtBilin_zero]
  exact lieDerivBilinWithin_zero (E := E) _ _ _

@[simp]
theorem mlieDerivBilin_zero (V : (x : M) → TangentSpace I x) :
    mlieDerivBilin I V
      (0 : (y : M) → TangentSpace I y →L[𝕜] TangentSpace I y →L[𝕜] G) = 0 :=
  funext (mlieDerivBilinWithin_zero V univ)

@[simp]
theorem mlieDerivBilin_zero_left
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    mlieDerivBilin I (0 : (x : M) → TangentSpace I x) b = 0 := by
  funext x
  have hz : (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm
      (0 : (y : M) → TangentSpace I y) (range I) : E → E) = 0 := by
    funext z; simp [VectorField.mpullbackWithin_apply]
  rw [mlieDerivBilin_def]
  erw [hz]
  exact lieDerivBilinWithin_zero_left (E := E) _ _ _

@[simp]
theorem mlieDerivBilinWithin_neg (V : (x : M) → TangentSpace I x)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G)
    {s : Set M} {x : M} (hs : UniqueMDiffWithinAt I s x) :
    mlieDerivBilinWithin I V (-b) s x = -mlieDerivBilinWithin I V b s x := by
  rw [mlieDerivBilinWithin_def, inChartAtBilin_neg]
  exact lieDerivBilinWithin_neg (E := E) _ _ hs

@[simp]
theorem mlieDerivBilin_neg (V : (x : M) → TangentSpace I x)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    mlieDerivBilin I V (-b) = -mlieDerivBilin I V b :=
  funext fun _ ↦ mlieDerivBilinWithin_neg V b (uniqueMDiffWithinAt_univ I)

@[simp]
theorem mlieDerivBilinWithin_smul (V : (x : M) → TangentSpace I x) (c : 𝕜)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G)
    {s : Set M} {x : M} (hs : UniqueMDiffWithinAt I s x) :
    mlieDerivBilinWithin I V (c • b) s x = c • mlieDerivBilinWithin I V b s x := by
  rw [mlieDerivBilinWithin_def, inChartAtBilin_smul]
  exact lieDerivBilinWithin_smul (E := E) c _ hs

@[simp]
theorem mlieDerivBilin_smul (V : (x : M) → TangentSpace I x) (c : 𝕜)
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) :
    mlieDerivBilin I V (c • b) = c • mlieDerivBilin I V b :=
  funext fun _ ↦ mlieDerivBilinWithin_smul V c b (uniqueMDiffWithinAt_univ I)

/-- Within a subset with unique derivatives, the Lie derivative preserves symmetry of covariant
two-tensors with no differentiability assumptions on `V` or `b`. -/
theorem mlieDerivBilinWithin_symm (V : (x : M) → TangentSpace I x)
    {b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G}
    (hb : ∀ y v w, b y v w = b y w v) {s : Set M} {x : M} (hs : UniqueMDiffWithinAt I s x)
    (v w : TangentSpace I x) :
    mlieDerivBilinWithin I V b s x v w = mlieDerivBilinWithin I V b s x w v := by
  have hflip : (fun z ↦ (inChartAtBilin I x b z).flip) = inChartAtBilin I x b := by
    funext z; ext u₁ u₂
    simp only [ContinuousLinearMap.flip_apply, inChartAtBilin_apply]
    exact hb _ _ _
  have h := lieDerivBilinWithin_flip (E := E)
    (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
    (inChartAtBilin I x b) hs
  rw [hflip] at h
  exact (DFunLike.congr_fun (DFunLike.congr_fun h w) v).symm

/-- The Lie derivative preserves symmetry of covariant two-tensors unconditionally, with no
differentiability assumptions on `V` or `b`. -/
theorem mlieDerivBilin_symm (V : (x : M) → TangentSpace I x)
    {b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G}
    (hb : ∀ y v w, b y v w = b y w v) (x : M) (v w : TangentSpace I x) :
    mlieDerivBilin I V b x v w = mlieDerivBilin I V b x w v :=
  mlieDerivBilinWithin_symm V hb (uniqueMDiffWithinAt_univ I) v w

variable [IsManifold I 1 M]

theorem mlieDerivBilinWithin_add {V : (x : M) → TangentSpace I x}
    {b₁ b₂ : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G} {s : Set M} {x : M}
    (hs : UniqueMDiffWithinAt I s x)
    (hb₁ : MDifferentiableWithinAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b₁ y)) s x)
    (hb₂ : MDifferentiableWithinAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b₂ y)) s x) :
    mlieDerivBilinWithin I V (b₁ + b₂) s x =
      mlieDerivBilinWithin I V b₁ s x + mlieDerivBilinWithin I V b₂ s x := by
  rw [mlieDerivBilinWithin_def, inChartAtBilin_add]
  exact lieDerivBilinWithin_add (E := E) hs (differentiableWithinAt_inChartAtBilin hb₁)
    (differentiableWithinAt_inChartAtBilin hb₂)

theorem mlieDerivBilin_add {V : (x : M) → TangentSpace I x}
    {b₁ b₂ : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G} {x : M}
    (hb₁ : MDifferentiableAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b₁ y)) x)
    (hb₂ : MDifferentiableAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b₂ y)) x) :
    mlieDerivBilin I V (b₁ + b₂) x = mlieDerivBilin I V b₁ x + mlieDerivBilin I V b₂ x :=
  mlieDerivBilinWithin_add (uniqueMDiffWithinAt_univ I) hb₁.mdifferentiableWithinAt
    hb₂.mdifferentiableWithinAt

theorem mlieDerivBilin_sub {V : (x : M) → TangentSpace I x}
    {b₁ b₂ : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G} {x : M}
    (hb₁ : MDifferentiableAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b₁ y)) x)
    (hb₂ : MDifferentiableAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b₂ y)) x) :
    mlieDerivBilin I V (b₁ - b₂) x = mlieDerivBilin I V b₁ x - mlieDerivBilin I V b₂ x := by
  have hu := uniqueMDiffWithinAt_univ I (x := x)
  have h : mlieDerivBilinWithin I V (b₁ + -b₂) univ x =
      mlieDerivBilinWithin I V b₁ univ x + -mlieDerivBilinWithin I V b₂ univ x := by
    rw [mlieDerivBilinWithin_def, inChartAtBilin_add, inChartAtBilin_neg]
    exact (lieDerivBilinWithin_add (E := E) hu
      (differentiableWithinAt_inChartAtBilin hb₁.mdifferentiableWithinAt)
      (differentiableWithinAt_inChartAtBilin hb₂.mdifferentiableWithinAt).neg).trans
      (congrArg _ (lieDerivBilinWithin_neg (E := E) _ _ hu))
  simpa only [mlieDerivBilinWithin_univ, ← sub_eq_add_neg] using h

/-- Leibniz rule for multiplying a covariant two-tensor by a scalar function:
`L_V (f • b) = (V f) • b + f • L_V b`. -/
theorem mlieDerivBilinWithin_fun_smul {V : (x : M) → TangentSpace I x} {f : M → 𝕜}
    {b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G} {s : Set M} {x : M}
    (hs : UniqueMDiffWithinAt I s x)
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
  have hVx := VectorField.mpullbackWithin_extChartAt_symm_self V x
  have hbx := inChartAtBilin_extChartAt_self x b
  have hfx : (f ∘ (extChartAt I x).symm) (extChartAt I x x) = f x :=
    congrArg f (extChartAt_to_inv x)
  have hdf : fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) ((extChartAt I x).symm ⁻¹' s ∩ range I)
      (extChartAt I x x) (V x) = mvfderivWithin I f s x (V x) := by
    rw [hf.mvfderivWithin]
    simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp]
    rfl
  erw [hVx, hbx, hfx, hdf]
  rfl

/-- Leibniz rule for multiplying a covariant two-tensor by a scalar function. -/
theorem mlieDerivBilin_fun_smul {V : (x : M) → TangentSpace I x} {f : M → 𝕜}
    {b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G} {x : M}
    (hf : MDifferentiableAt I 𝓘(𝕜) f x)
    (hb : MDifferentiableAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b y)) x) :
    mlieDerivBilin I V (fun y ↦ f y • b y) x =
      mvfderiv I f x (V x) • b x + f x • mlieDerivBilin I V b x := by
  simpa only [mlieDerivBilinWithin_univ, mvfderivWithin_univ] using
    mlieDerivBilinWithin_fun_smul (uniqueMDiffWithinAt_univ I) hf.mdifferentiableWithinAt
      hb.mdifferentiableWithinAt

theorem mlieDerivBilinWithin_add_left {V₁ V₂ : (x : M) → TangentSpace I x}
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) {s : Set M} {x : M}
    (hs : UniqueMDiffWithinAt I s x)
    (hV₁ : MDifferentiableWithinAt I I.tangent (fun y ↦ (V₁ y : TangentBundle I M)) s x)
    (hV₂ : MDifferentiableWithinAt I I.tangent (fun y ↦ (V₂ y : TangentBundle I M)) s x) :
    mlieDerivBilinWithin I (V₁ + V₂) b s x =
      mlieDerivBilinWithin I V₁ b s x + mlieDerivBilinWithin I V₂ b s x := by
  simp only [mlieDerivBilinWithin_def, VectorField.mpullbackWithin_add]
  exact lieDerivBilinWithin_add_left (E := E) _ hs
    hV₁.differentiableWithinAt_mpullbackWithin_extChartAt_symm
    hV₂.differentiableWithinAt_mpullbackWithin_extChartAt_symm

theorem mlieDerivBilin_add_left {V₁ V₂ : (x : M) → TangentSpace I x}
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G) {x : M}
    (hV₁ : MDifferentiableAt I I.tangent (fun y ↦ (V₁ y : TangentBundle I M)) x)
    (hV₂ : MDifferentiableAt I I.tangent (fun y ↦ (V₂ y : TangentBundle I M)) x) :
    mlieDerivBilin I (V₁ + V₂) b x = mlieDerivBilin I V₁ b x + mlieDerivBilin I V₂ b x :=
  mlieDerivBilinWithin_add_left b (uniqueMDiffWithinAt_univ I) hV₁.mdifferentiableWithinAt
    hV₂.mdifferentiableWithinAt

/-! ### The bracket formula -/

private theorem inChartAtBilin_apply_mpullbackWithin_eventuallyEq
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G)
    (X Y : (y : M) → TangentSpace I y) (x : M) :
    (fun z ↦ inChartAtBilin I x b z
      (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm X (range I) z)
      (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm Y (range I) z))
      =ᶠ[𝓝[range I] (extChartAt I x x)]
        (fun y ↦ b y (X y) (Y y)) ∘ (extChartAt I x).symm := by
  filter_upwards [extChartAt_target_mem_nhdsWithin x] with z hz
  exact (inChartAtBilin_apply x b z _ _).trans
    (congrArg₂ (fun u₁ u₂ ↦ b ((extChartAt I x).symm z) u₁ u₂)
      ((isInvertible_mfderivWithin_extChartAt_symm hz).self_apply_inverse
        (X ((extChartAt I x).symm z)))
      ((isInvertible_mfderivWithin_extChartAt_symm hz).self_apply_inverse
        (Y ((extChartAt I x).symm z))))

private theorem fderivWithin_inChartAtBilin_apply_mpullbackWithin
    (b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G)
    (X Y : (y : M) → TangentSpace I y) {s : Set M} {x : M}
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
  have heq := inChartAtBilin_apply_mpullbackWithin_eventuallyEq (I := I) b X Y x
  have hpoint := heq.self_of_nhdsWithin (mem_range_self (chartAt H x x))
  have heqs := heq.filter_mono (nhdsWithin_mono _
    (inter_subset_right (s := (extChartAt I x).symm ⁻¹' s)))
  have hpflat := ((hb.clm_apply hX).clm_apply hY).congr_of_eventuallyEq heqs.symm hpoint.symm
  have hp := hpflat.mdifferentiableWithinAt_of_comp_extChartAt_symm
  rw [hp.mvfderivWithin]
  simpa only [writtenInExtChartAt, extChartAt_self_eq, PartialEquiv.refl_coe,
    modelWithCornersSelf_coe, Function.id_comp] using heqs.fderivWithin_eq hpoint

/-- **The bracket formula** within a subset: evaluated on vector fields `X` and `Y` differentiable
within `s` at `x`, the Lie derivative of a differentiable covariant two-tensor `b` along `V`
satisfies
`(L_V b)_x (X_x, Y_x) = V_x (b (X, Y)) - b_x ([V, X]_x, Y_x) - b_x (X_x, [V, Y]_x)`.
No regularity of `V` is required. -/
theorem mlieDerivBilinWithin_apply_vectorField
    {V X Y : (y : M) → TangentSpace I y}
    {b : (y : M) → TangentSpace I y →L[𝕜] TangentSpace I y →L[𝕜] G}
    {s : Set M} {x : M}
    (hb : MDifferentiableWithinAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b y)) s x)
    (hX : MDifferentiableWithinAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) s x)
    (hY : MDifferentiableWithinAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) s x)
    (hs : UniqueMDiffWithinAt I s x) :
    mlieDerivBilinWithin I V b s x (X x) (Y x) =
      mvfderivWithin I (fun y ↦ b y (X y) (Y y)) s x (V x) -
        b x (mlieBracketWithin I V X s x) (Y x) -
        b x (X x) (mlieBracketWithin I V Y s x) := by
  let X' : E → E := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm X (range I)
  let Y' : E → E := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm Y (range I)
  have hb' := differentiableWithinAt_inChartAtBilin hb
  have hX' : DifferentiableWithinAt 𝕜 X' ((extChartAt I x).symm ⁻¹' s ∩ range I)
      (extChartAt I x x) := hX.differentiableWithinAt_mpullbackWithin_extChartAt_symm
  have hY' : DifferentiableWithinAt 𝕜 Y' ((extChartAt I x).symm ⁻¹' s ∩ range I)
      (extChartAt I x x) := hY.differentiableWithinAt_mpullbackWithin_extChartAt_symm
  have hflat := lieDerivBilinWithin_apply_vectorField (E := E)
    (V := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
    hs hb' hX' hY'
  have hXx : X' (extChartAt I x x) = X x := VectorField.mpullbackWithin_extChartAt_symm_self X x
  have hYx : Y' (extChartAt I x x) = Y x := VectorField.mpullbackWithin_extChartAt_symm_self Y x
  rw [mlieDerivBilinWithin_def]
  erw [← hXx, ← hYx, hflat]
  rw [fderivWithin_inChartAtBilin_apply_mpullbackWithin b X Y hb' hX' hY',
    VectorField.mpullbackWithin_extChartAt_symm_self, inChartAtBilin_extChartAt_self]
  simp only [X', Y', hXx, hYx, VectorField.lieBracketWithin_mpullbackWithin_extChartAt_symm]
  rfl

/-- **The bracket formula**: evaluated on differentiable vector fields `X` and `Y`, the Lie
derivative of a differentiable covariant two-tensor `b` along `V` satisfies
`(L_V b)_x (X_x, Y_x) = V_x (b (X, Y)) - b_x ([V, X]_x, Y_x) - b_x (X_x, [V, Y]_x)`. -/
theorem mlieDerivBilin_apply_vectorField
    {V X Y : (y : M) → TangentSpace I y}
    {b : (y : M) → TangentSpace I y →L[𝕜] TangentSpace I y →L[𝕜] G} {x : M}
    (hb : MDifferentiableAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G))
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b y)) x)
    (hX : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    (hY : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x) :
    mlieDerivBilin I V b x (X x) (Y x) =
      mvfderiv I (fun y ↦ b y (X y) (Y y)) x (V x) -
        b x (mlieBracket I V X x) (Y x) -
        b x (X x) (mlieBracket I V Y x) := by
  simpa only [mlieDerivBilinWithin_univ, mvfderivWithin_univ, mlieBracketWithin_univ] using
    mlieDerivBilinWithin_apply_vectorField (V := V) hb.mdifferentiableWithinAt
      hX.mdifferentiableWithinAt hY.mdifferentiableWithinAt (uniqueMDiffWithinAt_univ I)

end LieDeriv

section Regularity

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

omit [CompleteSpace E] in
private theorem mdifferentiableAt_trivializationAt_symm [IsManifold I 2 M] (x₀ : M)
    {y : M} (hy : y ∈ (chartAt H x₀).source) (u : E) :
    MDifferentiableAt I I.tangent
      (T% (fun q ↦ (trivializationAt E (TangentSpace I) x₀).symm q u)) y := by
  let _ : IsManifold I 1 M := IsManifold.of_le one_le_two
  let _ : IsManifold I (1 + 1) M := by simpa only [one_add_one_eq_two] using ‹IsManifold I 2 M›
  set t := trivializationAt E (TangentSpace I) x₀
  have hyb : y ∈ t.baseSet := by simpa [t] using hy
  refine (t.mdifferentiableAt_section_iff I (fun q ↦ t.symm q u) hyb).2 ?_
  exact (mdifferentiableAt_const (c := u)).congr_of_eventuallyEq <| by
    filter_upwards [t.open_baseSet.mem_nhds hyb] with q hq
    exact congrArg Prod.snd (t.apply_mk_symm hq u)

omit [CompleteSpace E] in
private theorem mpullbackWithin_trivializationAt_symm_eventuallyEq [IsManifold I 1 M]
    (x₀ : M) {z : E} (u : E) :
    VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      (fun q ↦ (trivializationAt E (TangentSpace I) x₀).symm q u) (extChartAt I x₀).target
      =ᶠ[𝓝[(extChartAt I x₀).target] z] fun ζ ↦ (u : TangentSpace 𝓘(𝕜, E) ζ) := by
  filter_upwards [self_mem_nhdsWithin] with ζ hζt
  simp only [VectorField.mpullbackWithin_apply,
    mfderivWithin_congr_set (extChartAt_target_eventuallyEqSet_of_mem hζt)]
  have h := VectorField.mpullbackWithin_extChartAt_symm_apply
    (fun q ↦ (trivializationAt E (TangentSpace I) x₀).symm q u) ((extChartAt I x₀).map_target hζt)
  rw [(extChartAt I x₀).right_inv hζt] at h
  have hζb : (extChartAt I x₀).symm ζ ∈
      (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet := by
    simpa [extChartAt_source] using (extChartAt I x₀).map_target hζt
  exact h.trans (congrArg Prod.snd (Trivialization.apply_mk_symm _ hζb u))

/-- In the preferred chart at `x₀`, the Lie bracket of a differentiable vector field `V` with the
constant-coordinate frame vector field `q ↦ (trivializationAt E (TangentSpace I) x₀).symm q u` is
minus the pushforward of the chart derivative of `V` in direction `u`. -/
private theorem mlieBracket_trivializationAt_symm_eq [IsManifold I (minSmoothness 𝕜 2) M]
    {V : (x : M) → TangentSpace I x} (x₀ : M) {z : E}
    (hz : z ∈ (extChartAt I x₀).target)
    (hV : MDifferentiableAt I I.tangent (T% V) ((extChartAt I x₀).symm z)) (u : E) :
    mlieBracket I V (fun q ↦ (trivializationAt E (TangentSpace I) x₀).symm q u)
        ((extChartAt I x₀).symm z) =
      -mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (range I) z
        (fderivWithin 𝕜 (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I))
          (range I) z u) := by
  let _ : IsManifold I 1 M :=
    IsManifold.of_le ((show (1 : ℕ∞ω) ≤ 2 by norm_num).trans (le_minSmoothness (𝕜 := 𝕜)))
  let _ : IsManifold I 2 M := IsManifold.of_le (le_minSmoothness (𝕜 := 𝕜))
  set σ : (q : M) → TangentSpace I q := fun q ↦ (trivializationAt E (TangentSpace I) x₀).symm q u
  have hy_src : (extChartAt I x₀).symm z ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hz
  have hσ_diff : MDifferentiableAt I I.tangent (T% σ) ((extChartAt I x₀).symm z) :=
    mdifferentiableAt_trivializationAt_symm x₀ (by simpa [extChartAt_source] using hy_src) u
  have ht_eq : (extChartAt I x₀).target =ᶠ[𝓝 z] range I :=
    extChartAt_target_eventuallyEqSet_of_mem hz
  have hu_t : UniqueMDiffOn 𝓘(𝕜, E) (extChartAt I x₀).target := by
    simpa using (uniqueMDiffOn_univ (I := I)).uniqueDiffOn_target_inter x₀ |>.uniqueMDiffOn
  have hmem : z ∈ closure (interior (extChartAt I x₀).target) := by
    have h := extChartAt_mem_closure_interior (I := I) (s := univ) (x₀ := x₀)
      (x := (extChartAt I x₀).symm z) (by simp) hy_src
    rwa [preimage_univ, univ_inter, (extChartAt I x₀).right_inv hz] at h
  have hpull := VectorField.mpullbackWithin_mlieBracketWithin' (I := 𝓘(𝕜, E)) (I' := I)
    (f := (extChartAt I x₀).symm) (V := V) (W := σ) (x₀ := z)
    (s := (extChartAt I x₀).target) (u := (extChartAt I x₀).target) (t := univ)
    (n := minSmoothness 𝕜 2) hV.mdifferentiableWithinAt hσ_diff.mdifferentiableWithinAt
    hu_t hu_t (contMDiffWithinAt_extChartAt_symm_target x₀ hz) hz le_rfl (by simp) hmem Subset.rfl
  let V₀ : E → E := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I)
  have heqV : VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V
      (extChartAt I x₀).target =ᶠ[𝓝[(extChartAt I x₀).target] z]
      (fun ζ ↦ (V₀ ζ : TangentSpace 𝓘(𝕜, E) ζ)) := by
    filter_upwards [self_mem_nhdsWithin] with ζ hζt
    simp only [V₀, VectorField.mpullbackWithin_apply,
      mfderivWithin_congr_set (extChartAt_target_eventuallyEqSet_of_mem hζt)]
    rfl
  have hpull' : (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm
      (mlieBracket I V σ) (extChartAt I x₀).target z : E) = -(fderivWithin 𝕜 V₀ (range I) z u) := by
    rw [← mlieBracketWithin_univ]
    exact (hpull.trans (Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem heqV
      (mpullbackWithin_trivializationAt_symm_eventuallyEq x₀ u) hz |>.trans
      (congrFun mlieBracketWithin_eq_lieBracketWithin z))).trans (by
        rw [lieBracketWithin_congr_set ht_eq, lieBracketWithin, fderivWithin_const_apply,
          zero_apply, zero_sub])
  rw [VectorField.mpullbackWithin_apply, mfderivWithin_congr_set ht_eq] at hpull'
  have key := congrArg (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (range I) z) hpull'
  rw [(isInvertible_mfderivWithin_extChartAt_symm hz).self_apply_inverse] at key
  exact key.trans ((mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (range I) z).map_neg
    (fderivWithin 𝕜 V₀ (range I) z u : TangentSpace 𝓘(𝕜, E) z))

omit [CompleteSpace E] in
/-- Directional derivative along `V` of the pairing of `b` with constant-coordinate frame fields at
`x₀`, expressed in the chart at `x₀`. -/
private theorem mvfderiv_apply_trivializationAt_symm_eq [IsManifold I 2 M]
    {V : (x : M) → TangentSpace I x}
    {b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G}
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
  let _ : ∀ q : M, IsNormableSpace 𝕜 (TangentSpace I q) := fun q ↦
    (VectorBundle.continuousLinearEquivAt 𝕜 E (TangentSpace I : M → Type _) q).isNormableSpace
  set y := (extChartAt I x₀).symm z
  set B₀ := inChartAtBilin I x₀ b
  set g : M → G := fun q ↦ b q ((trivializationAt E (TangentSpace I) x₀).symm q u)
    ((trivializationAt E (TangentSpace I) x₀).symm q w)
  have hy_chart : y ∈ (chartAt H x₀).source := by
    simpa only [y, extChartAt_source] using (extChartAt I x₀).map_target hz
  have hu_z : UniqueDiffWithinAt 𝕜 (range I) z :=
    I.uniqueDiffOn _ (extChartAt_target_subset_range x₀ hz)
  have hB₀_diff := differentiableWithinAt_inChartAtBilin_of_mem x₀ hz hb
  have hpair_eq : (g ∘ (extChartAt I x₀).symm) =ᶠ[𝓝[range I] z] fun ζ ↦ B₀ ζ u w := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hz] with ζ hζ
    have hζc : (extChartAt I x₀).symm ζ ∈ (chartAt H x₀).source := by
      simpa only [extChartAt_source] using (extChartAt I x₀).map_target hζ
    have hζb : (extChartAt I x₀).symm ζ ∈
        (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet := by simpa using hζc
    simp only [g, Function.comp_apply, B₀, inChartAtBilin_apply]
    rw [← Trivialization.symmL_apply (R := 𝕜) _ hζb, ← Trivialization.symmL_apply (R := 𝕜) _ hζb,
      TangentBundle.symmL_trivializationAt hζc, (extChartAt I x₀).right_inv hζ]
    rfl
  have hpair_mdiff : MDifferentiableAt I 𝓘(𝕜, G) g y := by
    simpa [g, mdifferentiableAt_section] using hb.clm_bundle_apply₂ (F₃ := G) (E₃ := fun _ : M ↦ G)
      (mdifferentiableAt_trivializationAt_symm x₀ hy_chart u)
      (mdifferentiableAt_trivializationAt_symm x₀ hy_chart w)
  let Z : E := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I) z
  have hVy : V y = mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (range I) z Z :=
    ((isInvertible_mfderivWithin_extChartAt_symm hz).self_apply_inverse (V y)).symm
  have hchain := mfderiv_comp_mfderivWithin_of_eq (I := 𝓘(𝕜, E)) (I' := I) (I'' := 𝓘(𝕜, G))
    (f := (extChartAt I x₀).symm) (g := g) (s := range I) hpair_mdiff
    (mdifferentiableWithinAt_extChartAt_symm hz)
    (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.2 hu_z) rfl
  change @Eq (E →L[𝕜] G) _ _ at hchain
  have hchain_apply := congrArg (fun L : E →L[𝕜] G ↦ L Z) hchain
  change _ = (mfderiv% g y) ((mfderiv[range I] (extChartAt I x₀).symm z) Z) at hchain_apply
  change (mfderiv% g y) (V y) = _
  rw [hVy, ← hchain_apply, mfderivWithin_eq_fderivWithin]
  change (fderivWithin 𝕜 (g ∘ (extChartAt I x₀).symm) (range I) z) Z = _
  rw [hpair_eq.fderivWithin_eq (hpair_eq.self_of_nhdsWithin (extChartAt_target_subset_range x₀ hz))]
  exact DFunLike.congr_fun ((((ContinuousLinearMap.apply 𝕜 G w).comp
    (ContinuousLinearMap.apply 𝕜 (E →L[𝕜] G) u)).hasFDerivAt.comp_hasFDerivWithinAt z
      hB₀_diff.hasFDerivWithinAt).fderivWithin hu_z) Z

/-- On `(extChartAt I x₀).target`, reading `mlieDerivBilin I V b` in the hom-bundle trivialization
at `x₀` yields the flat Lie derivative `lieDerivBilinWithin` of `inChartAtBilin I x₀ b` along the
chart pullback of `V` wherever `V` and `b` are differentiable. -/
private theorem trivializationAt_mlieDerivBilin_eq [IsManifold I (minSmoothness 𝕜 2) M]
    {V : (x : M) → TangentSpace I x}
    {b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G}
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
  let _ : IsManifold I 1 M :=
    IsManifold.of_le ((show (1 : ℕ∞ω) ≤ 2 by norm_num).trans (le_minSmoothness (𝕜 := 𝕜)))
  let _ : IsManifold I 2 M := IsManifold.of_le (le_minSmoothness (𝕜 := 𝕜))
  set y := (extChartAt I x₀).symm z
  have hy_chart : y ∈ (chartAt H x₀).source := by
    simpa only [y, extChartAt_source] using (extChartAt I x₀).map_target hz
  have hy_base : y ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet := by
    simpa using hy_chart
  have hsymm_eq (v : E) : (trivializationAt E (TangentSpace I) x₀).symm y v =
      mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (range I) z v := by
    rw [← Trivialization.symmL_apply (R := 𝕜) _ hy_base,
      TangentBundle.symmL_trivializationAt hy_chart, (extChartAt I x₀).right_inv hz]
    rfl
  ext u w
  simp only [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ hy_base hy_base (by simp)]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq]
  rw [mlieDerivBilin_apply_vectorField hb
      (mdifferentiableAt_trivializationAt_symm x₀ hy_chart u)
      (mdifferentiableAt_trivializationAt_symm x₀ hy_chart w),
    mvfderiv_apply_trivializationAt_symm_eq x₀ hz hb u w,
    mlieBracket_trivializationAt_symm_eq x₀ hz hV u,
    mlieBracket_trivializationAt_symm_eq x₀ hz hV w,
    hsymm_eq u, hsymm_eq w, map_neg, neg_apply, map_neg,
    sub_neg_eq_add, sub_neg_eq_add]
  simp only [y, ← inChartAtBilin_apply]
  exact (lieDerivBilinWithin_apply (E := E)
    (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I))
    (inChartAtBilin I x₀ b) (range I) z u w).symm

/-- **`C^m` section regularity of the Lie derivative of covariant two-tensors.** Let `V` and `b`
be `C^n` sections at `x₀` with `m + 1 ≤ n` on a manifold of class `max (minSmoothness 𝕜 2) k`
where `m + 2 ≤ k`. Then `mlieDerivBilin I V b` is a `C^m` section at `x₀`. -/
theorem contMDiffAt_mlieDerivBilin {m n k : ℕ∞ω}
    [IsManifold I (minSmoothness 𝕜 2) M] [IsManifold I k M]
    {V : (x : M) → TangentSpace I x}
    {b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G} {x₀ : M}
    (hk : m + 2 ≤ k) (hmn : m + 1 ≤ n)
    (hV : ContMDiffAt I I.tangent n (T% V) x₀)
    (hb : ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G)) n
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b y)) x₀) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G)) m
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (mlieDerivBilin I V b y)) x₀ := by
  let _ : IsManifold I 1 M :=
    IsManifold.of_le ((show (1 : ℕ∞ω) ≤ 2 by norm_num).trans (le_minSmoothness (𝕜 := 𝕜)))
  let _ : IsManifold I (m + 1 + 1) M :=
    IsManifold.of_le (n := k) (by simpa only [add_assoc, one_add_one_eq_two] using hk)
  let _ : IsManifold I (m + 1) M := IsManifold.of_le (n := m + 1 + 1) le_self_add
  let _ : ∀ y : M, IsNormableSpace 𝕜 (TangentSpace I y) := fun y ↦
    (VectorBundle.continuousLinearEquivAt 𝕜 E (TangentSpace I : M → Type _) y).isNormableSpace
  have hV₁ := hV.of_le hmn; have hb₁ := hb.of_le hmn
  let V₀ : E → E := VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I)
  set B₀ := inChartAtBilin I x₀ b
  have hV₀ : ContDiffWithinAt 𝕜 (m + 1) V₀ (extChartAt I x₀).target (extChartAt I x₀ x₀) := by
    have h := (hV₁.contMDiffWithinAt (s := univ)).contDiffWithinAt_mpullbackWithin_extChartAt_symm
    rw [preimage_univ, univ_inter] at h
    exact h.mono (extChartAt_target_subset_range x₀)
  have hB₀ : ContDiffWithinAt 𝕜 (m + 1) B₀ (extChartAt I x₀).target (extChartAt I x₀ x₀) := by
    have h := contDiffWithinAt_inChartAtBilin (n := m + 1) (s := univ) hb₁.contMDiffWithinAt
    rw [preimage_univ, univ_inter] at h
    exact h.mono (extChartAt_target_subset_range x₀)
  have hu_t : UniqueDiffOn 𝕜 (extChartAt I x₀).target := by
    simpa using (uniqueMDiffOn_univ (I := I)).uniqueDiffOn_target_inter x₀
  have hflat_r : ContDiffWithinAt 𝕜 m (lieDerivBilinWithin V₀ B₀ (range I))
      (range I) (extChartAt I x₀ x₀) := by
    rw [contDiffWithinAt_congr_set
      (extChartAt_target_eventuallyEqSet_of_mem (mem_extChartAt_target x₀)).symm]
    refine (contDiffWithinAt_lieDerivBilinWithin hV₀ hB₀ hu_t
      (mem_extChartAt_target x₀) le_rfl).congr_of_eventuallyEq_of_mem ?_ (mem_extChartAt_target x₀)
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact lieDerivBilinWithin_congr_set (extChartAt_target_eventuallyEqSet_of_mem hz).symm
  have hV_nhds := ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1
    (hV₁.of_le (show (1 : ℕ∞ω) ≤ m + 1 from le_add_self))).mono fun _ hy ↦
    hy.mdifferentiableAt one_ne_zero
  have hb_nhds := ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).1
    (hb₁.of_le (show (1 : ℕ∞ω) ≤ m + 1 from le_add_self))).mono fun _ hy ↦
    hy.mdifferentiableAt one_ne_zero
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

/-- Global `C^m` section regularity of `mlieDerivBilin I V b`. -/
theorem contMDiff_mlieDerivBilin {m n k : ℕ∞ω}
    [IsManifold I (minSmoothness 𝕜 2) M] [IsManifold I k M]
    {V : (x : M) → TangentSpace I x}
    {b : (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] G}
    (hk : m + 2 ≤ k) (hmn : m + 1 ≤ n)
    (hV : ContMDiff I I.tangent n (T% V))
    (hb : ContMDiff I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G)) n
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (b y))) :
    ContMDiff I (I.prod 𝓘(𝕜, E →L[𝕜] E →L[𝕜] G)) m
      (fun y ↦ TotalSpace.mk' (E →L[𝕜] E →L[𝕜] G) y (mlieDerivBilin I V b y)) :=
  fun x₀ ↦ contMDiffAt_mlieDerivBilin hk hmn (hV x₀) (hb x₀)

namespace Manifold

variable (G) in
/-- The Lie derivative along a `C^n` vector field `V`, bundled as a linear map from `C^n` bilinear
sections to `C^m` bilinear sections whenever `m + 1 ≤ n` and `m + 2 ≤ k`. -/
def lieDerivBilinearSection {m n k : ℕ∞ω}
    [IsManifold I (minSmoothness 𝕜 2) M] [IsManifold I k M]
    (hk : m + 2 ≤ k) (hmn : m + 1 ≤ n)
    {V : (x : M) → TangentSpace I x} (hV : ContMDiff I I.tangent n (T% V)) :
    BilinearSection I E (TangentSpace I : M → Type _) G n →ₗ[𝕜]
      BilinearSection I E (TangentSpace I : M → Type _) G m :=
  let _ : IsManifold I 1 M :=
    IsManifold.of_le ((show (1 : ℕ∞ω) ≤ 2 by norm_num).trans (le_minSmoothness (𝕜 := 𝕜)))
  let _ : ∀ y : M, IsNormableSpace 𝕜 (TangentSpace I y) := fun y ↦
    (VectorBundle.continuousLinearEquivAt 𝕜 E (TangentSpace I : M → Type _) y).isNormableSpace
  { toFun b := ⟨mlieDerivBilin I V b, contMDiff_mlieDerivBilin hk hmn hV b.contMDiff⟩
    map_add' b₁ b₂ := by
      ext x v w
      have hb₁ := (b₁.contMDiff x).of_le ((show (1 : ℕ∞ω) ≤ m + 1 from le_add_self).trans hmn)
        |>.mdifferentiableAt one_ne_zero
      have hb₂ := (b₂.contMDiff x).of_le ((show (1 : ℕ∞ω) ≤ m + 1 from le_add_self).trans hmn)
        |>.mdifferentiableAt one_ne_zero
      change mlieDerivBilin I V (⇑b₁ + ⇑b₂) x v w =
        (mlieDerivBilin I V b₁ x + mlieDerivBilin I V b₂ x) v w
      rw [mlieDerivBilin_add hb₁ hb₂]
    map_smul' c b := by
      ext x v w
      change mlieDerivBilin I V (c • ⇑b) x v w = (c • mlieDerivBilin I V b) x v w
      rw [mlieDerivBilin_smul] }

@[simp]
theorem lieDerivBilinearSection_apply {m n k : ℕ∞ω}
    [IsManifold I (minSmoothness 𝕜 2) M] [IsManifold I k M]
    (hk : m + 2 ≤ k) (hmn : m + 1 ≤ n)
    {V : (x : M) → TangentSpace I x} (hV : ContMDiff I I.tangent n (T% V))
    (b : BilinearSection I E (TangentSpace I : M → Type _) G n) (x : M) :
    lieDerivBilinearSection G hk hmn hV b x = mlieDerivBilin I V b x := by
  rfl

theorem lieDerivBilinearSection_mem_symmetric {m n k : ℕ∞ω}
    [IsManifold I (minSmoothness 𝕜 2) M] [IsManifold I k M]
    (hk : m + 2 ≤ k) (hmn : m + 1 ≤ n)
    {V : (x : M) → TangentSpace I x} (hV : ContMDiff I I.tangent n (T% V))
    {b : BilinearSection I E (TangentSpace I : M → Type _) G n}
    (hb : b ∈ symmetricBilinearSections) :
    lieDerivBilinearSection G hk hmn hV b ∈ symmetricBilinearSections :=
  (mem_symmetricBilinearSections _).2 fun x v w ↦
    mlieDerivBilin_symm V ((mem_symmetricBilinearSections b).1 hb) x v w

end Manifold

end Regularity

end TauCeti
