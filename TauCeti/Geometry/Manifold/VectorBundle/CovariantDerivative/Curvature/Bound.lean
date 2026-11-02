/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Smoothness

/-!
# Local bounds for the curvature tensor

Let `∇` be a smooth connection on a finite-rank vector bundle `V` over a manifold `M`, and give
`V` and the tangent bundle of `M` continuous fibre metrics. The curvature tensor of `∇` is
locally bounded: near each point, `‖R(u, v)w‖ ≤ C ‖u‖ ‖v‖ ‖w‖` for a single constant `C`, and
hence the same holds on every compact subset of `M`. No metric compatibility or torsion
hypothesis is needed.

The proof reads the tensor in the trivializations at the point, where it is a continuous family
of trilinear maps on the model fibres (`CovariantDerivative.contMDiff_curvatureTensorCLM`), and
compares the fibre norms with the model norms by Mathlib's `eventually_norm_trivializationAt_lt`
and `eventually_norm_symmL_trivializationAt_lt`. Such bounds feed energy estimates for linear
equations whose coefficients involve curvature, such as the Jacobi equation along a geodesic.

## Main results

* `CovariantDerivative.eventually_norm_curvatureTensor_le`: the curvature tensor is bounded near
  each point.
* `CovariantDerivative.exists_norm_curvatureTensor_le_of_isCompact`: the curvature tensor is
  bounded on each compact set.
-/

public section

open Bundle
open scoped ContDiff Manifold Topology

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContinuousRiemannianBundle F V]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]

open ContinuousLinearMap Filter in
/-- The curvature tensor of a smooth connection is locally bounded for continuous fibre metrics:
near each point, `‖R(u, v)w‖ ≤ C ‖u‖ ‖v‖ ‖w‖` for one constant `C`. -/
theorem eventually_norm_curvatureTensor_le (x₀ : M) :
    ∃ C, ∀ᶠ x in 𝓝 x₀, ∀ (u v : TangentSpace I x) (w : V x),
      ‖cov.curvatureTensor x u v w‖ ≤ C * ‖u‖ * ‖v‖ * ‖w‖ := by
  -- Cache the operator-space instances while elaborating the iterated hom bundle.
  let _ : NormedAddCommGroup (F →L[ℝ] F) := inferInstance
  let _ : NormedSpace ℝ (F →L[ℝ] F) := inferInstance
  let _ : NormedAddCommGroup (E →L[ℝ] F →L[ℝ] F) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] F →L[ℝ] F) := inferInstance
  let _ : ∀ x : M, NormedAddCommGroup (V x →L[ℝ] V x) := fun _ ↦ inferInstance
  let _ : ∀ x : M, NormedSpace ℝ (V x →L[ℝ] V x) := fun _ ↦ inferInstance
  -- The curvature tensor read in the trivializations at `x₀` is continuous at `x₀`.
  let φ : M → E →L[ℝ] E →L[ℝ] F →L[ℝ] F := fun x ↦
    inCoordinates E (TangentSpace I) (E →L[ℝ] F →L[ℝ] F)
      (fun x ↦ TangentSpace I x →L[ℝ] V x →L[ℝ] V x) x₀ x x₀ x (cov.curvatureTensorCLM x)
  have hφ : ContinuousAt φ x₀ := ((continuousAt_hom_bundle (σ := RingHom.id ℝ) _).1
    cov.contMDiff_curvatureTensorCLM.continuous.continuousAt).2
  have hφapply : ∀ x ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet ∩
      (trivializationAt F V x₀).baseSet, ∀ a b c,
      φ x a b c = (trivializationAt F V x₀).continuousLinearMapAt ℝ x
        (cov.curvatureTensor x ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ x a)
          ((trivializationAt E (TangentSpace I : M → Type _) x₀).symmL ℝ x b)
          ((trivializationAt F V x₀).symmL ℝ x c)) := by
    intro x ⟨hx, hxV⟩ a b c
    simp only [φ]
    rw [inCoordinates_apply_eq₂ hx hx (by simp [hxV]),
      Trivialization.linearMapAt_def_of_mem _ (by simp [hxV])]
    simp [hom_trivializationAt_apply, inCoordinates,
      (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL_apply hx]
  -- Compare the fibre norms with the model norms near `x₀`.
  obtain ⟨C₁, hC₁, h₁⟩ := eventually_norm_symmL_trivializationAt_lt F V x₀
  obtain ⟨C₂, hC₂, h₂⟩ := eventually_norm_trivializationAt_lt E (fun x : M ↦ TangentSpace I x) x₀
  obtain ⟨C₃, hC₃, h₃⟩ := eventually_norm_trivializationAt_lt F V x₀
  refine ⟨C₁ * (‖φ x₀‖ + 1) * C₂ * C₂ * C₃, ?_⟩
  filter_upwards [h₁, h₂, h₃, hφ.norm.eventually (gt_mem_nhds (lt_add_one ‖φ x₀‖)),
    ((trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.inter
      (trivializationAt F V x₀).open_baseSet).mem_nhds
      ⟨FiberBundle.mem_baseSet_trivializationAt' x₀, FiberBundle.mem_baseSet_trivializationAt' x₀⟩]
    with x h₁ h₂ h₃ h₄ hx u v w
  set e := trivializationAt E (TangentSpace I : M → Type _) x₀
  set eV := trivializationAt F V x₀
  have hR : cov.curvatureTensor x u v w = eV.symmL ℝ x
      (φ x (e.continuousLinearMapAt ℝ x u) (e.continuousLinearMapAt ℝ x v)
        (eV.continuousLinearMapAt ℝ x w)) := by
    rw [hφapply x hx, e.symmL_continuousLinearMapAt hx.1, e.symmL_continuousLinearMapAt hx.1,
      eV.symmL_continuousLinearMapAt hx.2, eV.symmL_continuousLinearMapAt hx.2]
  have hu : ‖e.continuousLinearMapAt ℝ x u‖ ≤ C₂ * ‖u‖ :=
    (le_opNorm _ u).trans (mul_le_mul_of_nonneg_right h₂.le (norm_nonneg _))
  have hv : ‖e.continuousLinearMapAt ℝ x v‖ ≤ C₂ * ‖v‖ :=
    (le_opNorm _ v).trans (mul_le_mul_of_nonneg_right h₂.le (norm_nonneg _))
  have hw : ‖eV.continuousLinearMapAt ℝ x w‖ ≤ C₃ * ‖w‖ :=
    (le_opNorm _ w).trans (mul_le_mul_of_nonneg_right h₃.le (norm_nonneg _))
  have h₁' := h₁.le
  have h₄' := h₄.le
  have hC₁' := hC₁.le
  have hC₂' := hC₂.le
  have hC₃' := hC₃.le
  rw [hR]
  calc _ ≤ ‖eV.symmL ℝ x‖ * (‖φ x‖ * ‖e.continuousLinearMapAt ℝ x u‖ *
        ‖e.continuousLinearMapAt ℝ x v‖ * ‖eV.continuousLinearMapAt ℝ x w‖) := by
        refine (le_opNorm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (le_opNorm₂ _ _ _)
          (norm_nonneg _))
    _ ≤ C₁ * ((‖φ x₀‖ + 1) * (C₂ * ‖u‖) * (C₂ * ‖v‖) * (C₃ * ‖w‖)) := by gcongr
    _ = _ := by ring

/-- On a compact set, the curvature tensor of a smooth connection is bounded for continuous fibre
metrics: `‖R(u, v)w‖ ≤ C ‖u‖ ‖v‖ ‖w‖` at every point of the set. -/
theorem exists_norm_curvatureTensor_le_of_isCompact {K : Set M} (hK : IsCompact K) :
    ∃ C, ∀ x ∈ K, ∀ (u v : TangentSpace I x) (w : V x),
      ‖cov.curvatureTensor x u v w‖ ≤ C * ‖u‖ * ‖v‖ * ‖w‖ := by
  refine hK.induction_on ⟨0, by simp⟩ (fun _ _ hst ⟨C, hC⟩ ↦ ⟨C, fun x hx ↦ hC x (hst hx)⟩)
    (fun _ _ ⟨C, hC⟩ ⟨C', hC'⟩ ↦ ⟨max C C', fun x hx u v w ↦ ?_⟩) fun x _ ↦ ?_
  · rcases hx with hx | hx
    · exact (hC x hx u v w).trans (by gcongr; exact le_max_left C C')
    · exact (hC' x hx u v w).trans (by gcongr; exact le_max_right C C')
  · obtain ⟨C, hC⟩ := cov.eventually_norm_curvatureTensor_le x
    exact ⟨{y | ∀ (u v : TangentSpace I y) (w : V y),
      ‖cov.curvatureTensor y u v w‖ ≤ C * ‖u‖ * ‖v‖ * ‖w‖}, mem_nhdsWithin_of_mem_nhds hC, C,
      fun _ hy ↦ hy⟩

end CovariantDerivative
