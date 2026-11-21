/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Isotropic
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Sectional
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Riemann
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Smoothness
import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt

/-!
# The pointwise `(0, 4)` curvature tensor as a continuous four-tensor

Pairing the `(1, 3)` curvature tensor with the fibre inner product via `r ![u, v, z, w] =
⟪R(u, v)w, z⟫` defines `CovariantDerivative.curvatureFourTensor cov x`. Its contractions match
`ricciTensor` and `scalarCurvature`, diagonal pairings recover `sectionalCurvature`, and for a
metric-compatible torsion-free connection it lies in `algebraicCurvatureSubmodule`. Local `C^0`
Gram–Schmidt frames give continuity of `‖curvatureFourTensor ·‖`, `sectionalMin`, `sectionalMax`,
and `pic2Min`.

## Main definitions & statements

* `curvatureFourTensor`, `IsMetricCompatible.algebraicCurvature`, `ricci_curvatureFourTensor`,
  `scalar_curvatureFourTensor`, `sectionalCurvature_eq_curvatureFourTensor_div`,
  `IsMetricCompatible.isAlgebraicCurvature_curvatureFourTensor`,
  `continuous_norm_curvatureFourTensor`, `continuous_sectionalMin_curvatureFourTensor`,
  `continuous_sectionalMax_curvatureFourTensor`, `continuous_pic2Min_curvatureFourTensor`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer (2018), Chapters 7–8.
-/

public section

open Bundle Filter Set TauCeti TauCeti.FourTensor
open scoped ContDiff InnerProductSpace Manifold Matrix Topology

noncomputable section

namespace CovariantDerivative

section FourTensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov ∞]

/-- The pointwise `(0, 4)` curvature tensor `r ![u, v, z, w] = ⟪R(u, v)w, z⟫`. -/
def curvatureFourTensor (x : M) : FourTensor (TangentSpace I x) :=
  ofLinearMap₄ <| LinearMap.mk₂ ℝ (fun u v ↦ (cov.riemannCurvatureTensor x u v).flip)
    (fun _ _ _ ↦ by ext; simp) (fun _ _ _ ↦ by ext; simp)
    (fun _ _ _ ↦ by ext; simp) (fun _ _ _ ↦ by ext; simp)

/-- `curvatureFourTensor` agrees with `riemannCurvatureTensor` with the last two slots swapped. -/
theorem curvatureFourTensor_eq_riemannCurvatureTensor (x : M) (u v z w : TangentSpace I x) :
    cov.curvatureFourTensor x ![u, v, z, w] = cov.riemannCurvatureTensor x u v w z := by
  simp [curvatureFourTensor]

/-- Evaluation of `curvatureFourTensor` on `![u, v, z, w]`. -/
@[simp]
theorem curvatureFourTensor_apply (x : M) (u v z w : TangentSpace I x) :
    cov.curvatureFourTensor x ![u, v, z, w] = inner ℝ (cov.curvatureTensor x u v w) z := by
  rw [cov.curvatureFourTensor_eq_riemannCurvatureTensor, cov.riemannCurvatureTensor_apply]

/-- The algebraic Ricci contraction of `curvatureFourTensor` is `ricciTensor`. -/
@[simp]
theorem ricci_curvatureFourTensor (x : M) :
    ricci (cov.curvatureFourTensor x) = cov.ricciTensor x := by
  ext u v; let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [ricci_apply_orthonormalBasis b, cov.ricciTensor_eq_sum_riemannCurvatureTensor x b]
  simp [cov.curvatureFourTensor_eq_riemannCurvatureTensor]

/-- The algebraic scalar contraction of `curvatureFourTensor` is `scalarCurvature`. -/
@[simp]
theorem scalar_curvatureFourTensor (x : M) :
    scalar (cov.curvatureFourTensor x) = cov.scalarCurvature x := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [scalar_apply_orthonormalBasis b, cov.scalarCurvature_eq_sum_riemannCurvatureTensor x b]
  simp [cov.curvatureFourTensor_eq_riemannCurvatureTensor]

section Continuity

variable [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)]

private theorem exists_continuousAt_pullback_curvatureFourTensor (x₀ : M) :
    let V₀ := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
    ∃ Φ : M → FourTensor V₀, ContinuousAt Φ x₀ ∧
      ∀ᶠ y in 𝓝 x₀, ∃ L : V₀ ≃ₗᵢ[ℝ] TangentSpace I y,
        Φ y = (cov.curvatureFourTensor y).compContinuousLinearMap fun _ ↦
          (L : V₀ →L[ℝ] TangentSpace I y) := by
  classical
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  let _ : ContMDiffVectorBundle 0 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  set n := Module.finrank ℝ E; let V₀ := EuclideanSpace ℝ (Fin n)
  let b₀ := EuclideanSpace.basisFun (Fin n) ℝ; let c := Module.finBasis ℝ E
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  let sec (k : Fin n) (y : M) : TangentSpace I y :=
    if hy : y ∈ e.baseSet then e.orthonormalBasis c ⟨y, hy⟩ k else 0
  let basisTensor (i : Fin 4 → Fin n) : FourTensor V₀ :=
    (ContinuousMultilinearMap.mkPiRing ℝ (Fin 4) (1 : ℝ)).compContinuousLinearMap
      fun s ↦ innerSL ℝ (b₀ (i s))
  let coeff (i : Fin 4 → Fin n) (y : M) : ℝ :=
    inner ℝ (cov.curvatureTensor y (sec (i 0) y) (sec (i 1) y) (sec (i 3) y)) (sec (i 2) y)
  refine ⟨fun y ↦ ∑ i : Fin 4 → Fin n, coeff i y • basisTensor i,
    tendsto_finsetSum Finset.univ fun i _ ↦ ?_, ?_⟩
  · have hsec (k : Fin n) :
        ContMDiffWithinAt I I.tangent 0 (fun y ↦ TotalSpace.mk' E y (sec k y)) e.baseSet x₀ :=
      e.contMDiffOn_orthonormalBasis c k x₀ hx₀
    have hR := cov.contMDiffWithinAt_curvatureTensor (F := E) (V := TangentSpace I)
      (by simp : (0 : ℕ∞ω) ≤ ∞) (hsec (i 0)) (hsec (i 1)) (hsec (i 3))
    have hc : ContinuousAt (coeff i) x₀ :=
      (continuousWithinAt_iff_continuousAt (e.open_baseSet.mem_nhds hx₀)).1
        (hR.inner_bundle (IB := I) (F := E) (E := fun y : M ↦ TangentSpace I y)
          (b := fun y : M ↦ y) (h := (inferInstance : IsContMDiffRiemannianBundle I 0 E
            (fun y : M ↦ TangentSpace I y))) (hsec (i 2))).continuousWithinAt
    exact hc.smul continuousAt_const
  · filter_upwards [e.open_baseSet.mem_nhds hx₀] with y hy
    let d := e.orthonormalBasis c ⟨y, hy⟩
    refine ⟨d.repr.symm, ?_⟩; ext m
    have hm : m = fun s ↦ ∑ k : Fin n, ⟪b₀ k, m s⟫_ℝ • b₀ k :=
      funext fun s ↦ (b₀.sum_repr' (m s)).symm
    conv_rhs => rw [hm]
    rw [(cov.curvatureFourTensor y).compContinuousLinearMap
      (fun _ ↦ (d.repr.symm : V₀ →L[ℝ] TangentSpace I y)) |>.map_sum, sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [ContinuousMultilinearMap.map_smul_univ]
    have hsec_eq (k : Fin n) : d.repr.symm (b₀ k) = sec k y := by simp [sec, hy, d, b₀]
    have htuple : (fun s : Fin 4 ↦ sec (i s) y) =
        ![sec (i 0) y, sec (i 1) y, sec (i 2) y, sec (i 3) y] := by funext s; fin_cases s <;> rfl
    simp [basisTensor, coeff, ContinuousMultilinearMap.mkPiRing_apply, hsec_eq, htuple, mul_comm]

private theorem continuous_of_pullback_invariant
    (F₀ : FourTensor (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) → ℝ)
    (F : ∀ x : M, FourTensor (TangentSpace I x) → ℝ) (hcont : Continuous F₀)
    (hinv : ∀ (y : M) (L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃ₗᵢ[ℝ] TangentSpace I y),
      F₀ ((cov.curvatureFourTensor y).compContinuousLinearMap
        fun _ ↦ (L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] TangentSpace I y)) =
        F y (cov.curvatureFourTensor y)) :
    Continuous fun x : M ↦ F x (cov.curvatureFourTensor x) :=
  continuous_iff_continuousAt.2 fun x₀ ↦ by
    obtain ⟨Φ, hΦ, heq⟩ := cov.exists_continuousAt_pullback_curvatureFourTensor x₀
    exact (hcont.continuousAt.comp hΦ).congr_of_eventuallyEq
      (heq.mono fun y ⟨L, hL⟩ ↦ ((congrArg F₀ hL).trans (hinv y L)).symm)

/-- The operator norm of `curvatureFourTensor` is continuous across `M`. -/
theorem continuous_norm_curvatureFourTensor :
    Continuous fun x : M ↦ ‖cov.curvatureFourTensor x‖ :=
  cov.continuous_of_pullback_invariant (fun r ↦ ‖r‖) (fun _ r ↦ ‖r‖) continuous_norm fun _ _ ↦
    ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv _ _

/-- `sectionalMin ∘ curvatureFourTensor` is continuous on `M`. -/
theorem continuous_sectionalMin_curvatureFourTensor :
    Continuous fun x : M ↦ sectionalMin (cov.curvatureFourTensor x) :=
  cov.continuous_of_pullback_invariant sectionalMin (fun _ ↦ sectionalMin) continuous_sectionalMin
    fun _ L ↦ sectionalMin_compContinuousLinearMap_linearIsometryEquiv L _

/-- `sectionalMax ∘ curvatureFourTensor` is continuous on `M`. -/
theorem continuous_sectionalMax_curvatureFourTensor :
    Continuous fun x : M ↦ sectionalMax (cov.curvatureFourTensor x) :=
  cov.continuous_of_pullback_invariant sectionalMax (fun _ ↦ sectionalMax) continuous_sectionalMax
    fun _ L ↦ sectionalMax_compContinuousLinearMap_linearIsometryEquiv L _

/-- `pic2Min ∘ curvatureFourTensor` is continuous on `M`. -/
theorem continuous_pic2Min_curvatureFourTensor :
    Continuous fun x : M ↦ pic2Min (cov.curvatureFourTensor x) :=
  cov.continuous_of_pullback_invariant pic2Min (fun _ ↦ pic2Min) continuous_pic2Min
    fun _ L ↦ pic2Min_compContinuousLinearMap_linearIsometryEquiv L _

end Continuity

section MetricCompatible

variable [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]

/-- Sectional curvature expressed through `curvatureFourTensor`. -/
theorem sectionalCurvature_eq_curvatureFourTensor_div
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (x : M) (u v : TangentSpace I x) :
    cov.sectionalCurvature hcov x u v =
      cov.curvatureFourTensor x ![u, v, u, v] / (Matrix.gram ℝ ![u, v]).det := by
  rw [cov.sectionalCurvature_apply, cov.curvatureFourTensor_apply]

/-- On an orthonormal pair, sectional curvature equals `curvatureFourTensor x ![u, v, u, v]`. -/
theorem sectionalCurvature_eq_curvatureFourTensor_of_orthonormal
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (x : M) {u v : TangentSpace I x} (huv : Orthonormal ℝ ![u, v]) :
    cov.sectionalCurvature hcov x u v = cov.curvatureFourTensor x ![u, v, u, v] := by
  rw [cov.sectionalCurvature_eq_of_orthonormal hcov x u v huv, cov.curvatureFourTensor_apply]

/-- For a metric-compatible torsion-free connection, `curvatureFourTensor x` satisfies the
algebraic curvature symmetries. -/
theorem IsMetricCompatible.isAlgebraicCurvature_curvatureFourTensor
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) (x : M) : IsAlgebraicCurvature (cov.curvatureFourTensor x) where
  antisymm_first u v z w := by
    simpa only [cov.curvatureFourTensor_eq_riemannCurvatureTensor] using
      cov.riemannCurvatureTensor_antisymm_first x u v w z
  antisymm_last u v z w := by
    simpa only [cov.curvatureFourTensor_eq_riemannCurvatureTensor] using
      hcov.riemannCurvatureTensor_antisymm_last cov x u v w z
  swap_pairs u v z w := by
    simp only [cov.curvatureFourTensor_eq_riemannCurvatureTensor]
    rw [hcov.riemannCurvatureTensor_swap_pairs cov ht x u v w z,
      cov.riemannCurvatureTensor_antisymm_first x w z u v,
      hcov.riemannCurvatureTensor_antisymm_last cov x z w u v, neg_neg]
  cyclic_eq_zero u v z w := by
    simp only [cov.curvatureFourTensor_eq_riemannCurvatureTensor]
    linarith [cov.riemannCurvatureTensor_cyclic_eq_zero ht x u v z w,
      hcov.riemannCurvatureTensor_antisymm_last cov x u v w z,
      hcov.riemannCurvatureTensor_antisymm_last cov x v z w u,
      hcov.riemannCurvatureTensor_antisymm_last cov x z u w v]

/-- `curvatureFourTensor x` bundled in `algebraicCurvatureSubmodule (TangentSpace I x)`. -/
def IsMetricCompatible.algebraicCurvature
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) (x : M) : algebraicCurvatureSubmodule (TangentSpace I x) :=
  ⟨cov.curvatureFourTensor x, mem_algebraicCurvatureSubmodule.2
    (hcov.isAlgebraicCurvature_curvatureFourTensor cov ht x)⟩

/-- Coercion of `IsMetricCompatible.algebraicCurvature` to `FourTensor`. -/
@[simp]
theorem IsMetricCompatible.coe_algebraicCurvature
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) (x : M) :
    (hcov.algebraicCurvature cov ht x).val = cov.curvatureFourTensor x := (rfl)

end MetricCompatible

end FourTensor

end CovariantDerivative
