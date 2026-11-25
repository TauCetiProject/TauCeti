/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Smoothness
import TauCeti.Topology.Instances.Matrix
import TauCeti.Topology.VectorBundle.Riemannian.Comparison

/-!
# Bounds for the curvature and Ricci tensors

Let `∇` be a smooth connection on a finite-rank vector bundle `V` over a manifold `M`, and give
`V` and the tangent bundle of `M` continuous fibre metrics. The curvature tensor of `∇` is
locally bounded: near each point, `‖R(u, v)w‖ ≤ C ‖u‖ ‖v‖ ‖w‖` for a single constant `C`, and
hence the same holds on every compact subset of `M`. No metric compatibility or torsion
hypothesis is needed.

For a smooth tangent connection with pointwise positive Ricci curvature, a continuous background
metric gives a uniform positive Ricci lower bound on each compact set. Specializing to the
Levi-Civita connection of a smooth metric supplies the uniform Ricci hypothesis in Bonnet–Myers.

For a compact nonempty subset of a manifold of positive dimension, the difference
`Scal(x) − 2 Ricₓ(v,v)` attains a maximum over the unit tangent vectors based in the subset.
Only continuity of the background metric is needed.

The curvature bound proof reads the tensor as continuous trilinear maps in the trivializations
at the point (`CovariantDerivative.contMDiff_curvatureTensorCLM`), and compares the fibre norms
with the model norms by Mathlib's `eventually_norm_trivializationAt_lt`
and `eventually_norm_symmL_trivializationAt_lt`. Such bounds feed energy estimates for linear
equations whose coefficients involve curvature, such as the Jacobi equation along a geodesic.

## Main results

* `CovariantDerivative.eventually_norm_curvatureTensor_le`: the curvature tensor is bounded near
  each point.
* `CovariantDerivative.exists_norm_curvatureTensor_le_of_isCompact`: the curvature tensor is
  bounded on each compact set.
* `IsCompact.exists_pos_mul_norm_sq_le_ricciTensor`: positive Ricci curvature has a uniform
  positive lower bound on each compact set.
* `CovariantDerivative.exists_pos_mul_norm_sq_le_ricciTensor_of_compactSpace`: the corresponding
  bound on a compact manifold.
* `CovariantDerivative.continuous_ricciTensor_apply_self_tangentBundle`: Ricci curvature is
  continuous as a quadratic function on the tangent bundle.
* `IsCompact.exists_max_scalarCurvature_sub_two_mul_ricciTensor`: the ambient curvature maximum
  in the traced Gauss equation.

The uniform positive Ricci bound proof originated in
[`ColdingMinicozziTheory`](https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/dc053c9/ForTauCeti/Geometry/Manifold/Riemannian/Curvature/Ricci/UniformPositive.lean).
The traced Gauss maximum originated in the same project
([`TotalCurvature/Ambient`](https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/9dcd16306c431e362c8168f08667d5f9da72a2e8/ForTauCeti/Geometry/Manifold/Riemannian/Immersion/MinimalHypersurface/TotalCurvature/Ambient.lean)).
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
  obtain ⟨C₃, _, h₃⟩ := eventually_norm_trivializationAt_lt F V x₀
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

open CovariantDerivative Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Evaluating the Ricci tensor on the tautological tangent vector twice gives a continuous
function on the tangent bundle. -/
theorem CovariantDerivative.continuous_ricciTensor_apply_self_tangentBundle
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    Continuous (fun v : TangentBundle I M ↦ cov.ricciTensor v.proj v.snd v.snd) := by
  have hπ := FiberBundle.continuous_proj E (TangentSpace I : M → Type _)
  have hv : Continuous (fun v : TangentBundle I M ↦ TotalSpace.mk' E v.proj v.snd) :=
    continuous_id
  exact continuous_snd.comp ((Trivial.homeomorphProd M ℝ).continuous.comp
    ((cov.contMDiff_ricciTensor.continuous.comp hπ).clm_bundle_apply₂
      (F₁ := E) (F₂ := E) (E₃ := Trivial M ℝ) hv hv))

variable
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

open Riemannian.Tensor in
private theorem continuous_scalarCurvature_of_continuous_metric
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] : Continuous cov.scalarCurvature := by
  have : IsManifold I (0 + 1) M := by simp only [zero_add]; infer_instance
  rw [continuous_iff_continuousAt]
  intro a
  have hframe (i : Fin (Module.finrank ℝ E)) :
      ContinuousOn (fun x ↦ TotalSpace.mk' E x (chartLocalFrame (I := I) a i x))
        (chartAt H a).source := by
    rw [← TangentBundle.trivializationAt_baseSet (I := I) a]
    exact (contMDiffOn_chartLocalFrame (I := I) (n := 0) a i).continuousOn
  have hgram : ContinuousOn (chartGramMatrix (I := I) a) (chartAt H a).source := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply continuous_matrix
    intro i j
    change Continuous ((chartAt H a).source.domRestrict
      (fun x ↦ chartGramMatrix (I := I) a x i j))
    rw [← continuousOn_iff_continuous_domRestrict]
    simpa only [chartGramMatrix_apply] using (hframe i).inner_bundle (hframe j)
  have hinv (i j : Fin (Module.finrank ℝ E)) :
      ContinuousOn (fun y ↦ chartInvGramMatrix (I := I) a y i j) (chartAt H a).source := by
    intro x hx
    have hdet := (chartGramMatrix_det_pos (I := I) a
      (TangentBundle.trivializationAt_baseSet (I := I) a ▸ hx)).ne'
    have hA := hgram.continuousAt ((chartAt H a).open_source.mem_nhds hx)
    simpa only [chartInvGramMatrix_def] using
      (hA.matrix_inv_apply hdet i j).continuousWithinAt
  have hsum := continuousOn_finsetSum Finset.univ fun i _ ↦
    continuousOn_finsetSum Finset.univ fun j _ ↦
      (hinv i j).mul (cov.contMDiffOn_ricciTensor_chartLocalFrame a i j).continuousOn
  exact (hsum.congr fun x hx ↦ cov.scalarCurvature_eq_sum_chartInvGramMatrix a hx).continuousAt
    ((chartAt H a).open_source.mem_nhds (mem_chart_source H a))

/-- For a smooth tangent connection and a continuous background metric, the expression
`Scal(x) − 2 Ricₓ(v,v)` on unit tangent vectors over a nonempty compact set attains its
maximum, provided the tangent space has positive dimension. -/
theorem IsCompact.exists_max_scalarCurvature_sub_two_mul_ricciTensor
    {K : Set M} (hK : IsCompact K) (hne : K.Nonempty) [Nontrivial E]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞] :
    ∃ (x : M) (v : TangentSpace I x), x ∈ K ∧ ‖v‖ = 1 ∧
      ∀ (y : M) (w : TangentSpace I y), y ∈ K → ‖w‖ = 1 →
        cov.scalarCurvature y - 2 * cov.ricciTensor y w w ≤
          cov.scalarCurvature x - 2 * cov.ricciTensor x v v := by
  let U : Set (TangentBundle I M) := {p | p.proj ∈ K ∧ ‖p.snd‖ = 1}
  have hπ := FiberBundle.continuous_proj E (TangentSpace I : M → Type _)
  have hU : IsCompact U :=
    (hK.norm_le_bundle (F := E) (E := TangentSpace I) 1).of_isClosed_subset
      ((hK.isClosed.preimage hπ).inter
        (isClosed_eq (TauCeti.continuous_norm_bundle E (TangentSpace I)) continuous_const))
      (fun _ hp ↦ ⟨hp.1, hp.2.le⟩)
  obtain ⟨x, hx⟩ := hne
  have : Nontrivial (TangentSpace I x) := inferInstanceAs (Nontrivial E)
  obtain ⟨v, hv⟩ := exists_norm_eq (TangentSpace I x) zero_le_one
  let Q (p : TangentBundle I M) :=
    cov.scalarCurvature p.proj - 2 * cov.ricciTensor p.proj p.snd p.snd
  have hQ : Continuous Q :=
    ((continuous_scalarCurvature_of_continuous_metric cov).comp hπ).sub
      (continuous_const.mul cov.continuous_ricciTensor_apply_self_tangentBundle)
  obtain ⟨p, hp, hmax⟩ := hU.exists_isMaxOn ⟨⟨x, v⟩, hx, hv⟩ hQ.continuousOn
  exact ⟨p.proj, p.snd, hp.1, hp.2, fun y w hy hw ↦
    hmax (show (⟨y, w⟩ : TangentBundle I M) ∈ U from ⟨hy, hw⟩)⟩

/-- A compact set with positive Ricci tensor for a smooth tangent connection has a uniform
bound `k ‖v‖² ≤ Ric(v,v)` with `k > 0`, measured in a continuous background metric. -/
theorem IsCompact.exists_pos_mul_norm_sq_le_ricciTensor
    {K : Set M} (hK : IsCompact K)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (hpos : ∀ (x : M), x ∈ K → ∀ (v : TangentSpace I x), v ≠ 0 →
      0 < cov.ricciTensor x v v) :
    ∃ k > 0, ∀ (x : M), x ∈ K → ∀ (v : TangentSpace I x),
      k * ‖v‖ ^ 2 ≤ cov.ricciTensor x v v := by
  have hcont : Continuous (fun x : M ↦
      TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x
        (cov.ricciTensor x).toContinuousBilinearMap) :=
    cov.contMDiff_ricciTensor.continuous
  obtain ⟨k, hk, hle⟩ := hK.exists_pos_forall_mul_norm_sq_le_bundle
    (b := id) hcont.continuousOn
      (fun x hx v hv ↦ by
        simpa only [LinearMap.toContinuousBilinearMap_apply] using hpos x hx v hv)
  exact ⟨k, hk, fun x hx v ↦ by
    simpa only [LinearMap.toContinuousBilinearMap_apply] using hle x hx v⟩

/-- Pointwise positive Ricci curvature of a smooth tangent connection on a compact manifold
has a uniform positive bound measured in a continuous background metric. -/
theorem CovariantDerivative.exists_pos_mul_norm_sq_le_ricciTensor_of_compactSpace
    [CompactSpace M] (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < cov.ricciTensor x v v) :
    ∃ k > 0, ∀ (x : M) (v : TangentSpace I x),
      k * ‖v‖ ^ 2 ≤ cov.ricciTensor x v v := by
  obtain ⟨k, hk, hle⟩ := isCompact_univ.exists_pos_mul_norm_sq_le_ricciTensor cov
    (fun x _ v hv ↦ hpos x v hv)
  exact ⟨k, hk, fun x v ↦ hle x (mem_univ x) v⟩
