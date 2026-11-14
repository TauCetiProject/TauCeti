/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.QuarterPinching
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Riemann
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Smoothness
import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt

/-!
# Pointwise quarter-pinched sectional curvature and the PIC2 cone on Riemannian manifolds

Pairing the pointwise `(1, 3)` curvature tensor of a smooth connection on a Riemannian manifold
with the fibre inner product via `r(u, v, z, w) = ⟪R(u, v)w, z⟫` defines
`CovariantDerivative.curvatureFourTensor cov x : TauCeti.FourTensor (TangentSpace I x)`. Its Ricci
and scalar contractions agree with `ricciTensor` and `scalarCurvature`, and for a metric-compatible
torsion-free connection it lies in `algebraicCurvatureSubmodule (TangentSpace I x)`.

Reading `curvatureFourTensor` in a local Gram–Schmidt orthonormal frame shows that its operator
norm, `sectionalMin`, `sectionalMax`, and `pic2Min` vary continuously on `M` whenever the
Riemannian bundle is `C^0` (without assuming metric compatibility or vanishing torsion).

When a metric-compatible torsion-free connection is pointwise strictly quarter-pinched
(`CovariantDerivative.IsPointwiseQuarterPinched`) in dimension at least two, its algebraic
curvature tensor at each point lies in `interior PIC2`. On a compact manifold, continuity upgrades
pointwise strict quarter pinching to uniform positive sectional and `pic2Expression` bounds, a
uniform pinching factor `< 4`, and a compact convex `O(n)`-invariant subset of `interior PIC2` on
the Euclidean model space containing all isometric frame pullbacks of the manifold's curvature.

## Main definitions

* `CovariantDerivative.curvatureFourTensor`,
  `CovariantDerivative.IsMetricCompatible.algebraicCurvature`.
* `CovariantDerivative.IsQuarterPinchedAt`, `CovariantDerivative.IsPointwiseQuarterPinched`.

## Main statements

* `CovariantDerivative.ricci_curvatureFourTensor`, `CovariantDerivative.scalar_curvatureFourTensor`.
* `CovariantDerivative.continuous_norm_curvatureFourTensor`,
  `CovariantDerivative.continuous_sectionalMin_curvatureFourTensor`,
  `CovariantDerivative.continuous_sectionalMax_curvatureFourTensor`,
  `CovariantDerivative.continuous_pic2Min_curvatureFourTensor`.
* `CovariantDerivative.IsQuarterPinchedAt.mem_interior_isPIC2FourFrame`.
* `CovariantDerivative.IsPointwiseQuarterPinched.exists_pos_and_lt_four_sectionalCurvature`,
  `CovariantDerivative.IsPointwiseQuarterPinched.exists_pos_le_pic2Expression`, and
  `CovariantDerivative.IsPointwiseQuarterPinched.exists_isCompact_convex_subset_interior`.

## References

* S. Brendle and R. Schoen, *Manifolds with `1/4`-pinched curvature are space forms*, J. Amer.
  Math. Soc. 22 (2009), 287–307.
* S. Brendle, *Ricci Flow and the Sphere Theorem*, GSM 111, AMS (2010).
-/

public section

open Bundle Filter Set
open scoped ContDiff InnerProductSpace Manifold Matrix Topology

noncomputable section

namespace CovariantDerivative

section FourTensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov ∞]

/-- The pointwise `(0, 4)` curvature tensor packaged as a continuous four-tensor in the convention
`r ![u, v, z, w] = ⟪R(u, v)w, z⟫`. -/
def curvatureFourTensor (x : M) : TauCeti.FourTensor (TangentSpace I x) :=
  TauCeti.FourTensor.ofLinearMap₄ <|
    LinearMap.mk₂ ℝ (fun u v ↦ (cov.riemannCurvatureTensor x u v).flip)
      (fun _ _ _ ↦ by ext; simp) (fun _ _ _ ↦ by ext; simp)
      (fun _ _ _ ↦ by ext; simp) (fun _ _ _ ↦ by ext; simp)

/-- `curvatureFourTensor` agrees with `riemannCurvatureTensor` with the last two slots swapped. -/
theorem curvatureFourTensor_eq_riemannCurvatureTensor (x : M) (u v z w : TangentSpace I x) :
    cov.curvatureFourTensor x ![u, v, z, w] = cov.riemannCurvatureTensor x u v w z := by
  simp [curvatureFourTensor]

/-- Evaluation of `curvatureFourTensor` on a four-tuple `![u, v, z, w]`. -/
@[simp]
theorem curvatureFourTensor_apply (x : M) (u v z w : TangentSpace I x) :
    cov.curvatureFourTensor x ![u, v, z, w] = inner ℝ (cov.curvatureTensor x u v w) z := by
  rw [cov.curvatureFourTensor_eq_riemannCurvatureTensor, cov.riemannCurvatureTensor_apply]

/-- The algebraic Ricci contraction of `curvatureFourTensor` is `ricciTensor`. -/
@[simp]
theorem ricci_curvatureFourTensor (x : M) :
    TauCeti.FourTensor.ricci (cov.curvatureFourTensor x) = cov.ricciTensor x := by
  ext u v
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [TauCeti.FourTensor.ricci_apply_orthonormalBasis b,
    cov.ricciTensor_eq_sum_riemannCurvatureTensor x b]
  simp [cov.curvatureFourTensor_eq_riemannCurvatureTensor]

/-- The algebraic scalar contraction of `curvatureFourTensor` is `scalarCurvature`. -/
@[simp]
theorem scalar_curvatureFourTensor (x : M) :
    TauCeti.FourTensor.scalar (cov.curvatureFourTensor x) = cov.scalarCurvature x := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [TauCeti.FourTensor.scalar_apply_orthonormalBasis b,
    cov.scalarCurvature_eq_sum_riemannCurvatureTensor x b]
  simp [cov.curvatureFourTensor_eq_riemannCurvatureTensor]

section Continuity

variable [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)]

private theorem exists_continuousAt_pullback_curvatureFourTensor (x₀ : M) :
    ∃ Φ : M → TauCeti.FourTensor (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
      ContinuousAt Φ x₀ ∧
        ∀ᶠ y in 𝓝 x₀, ∃ L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃ₗᵢ[ℝ] TangentSpace I y,
          Φ y = (cov.curvatureFourTensor y).compContinuousLinearMap
            fun _ ↦ (L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] TangentSpace I y) := by
  classical
  have : IsManifold I (0 + 1) M := by simpa using (inferInstance : IsManifold I 1 M)
  let _ : ContMDiffVectorBundle 0 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  set n := Module.finrank ℝ E
  let V₀ := EuclideanSpace ℝ (Fin n)
  let b₀ := EuclideanSpace.basisFun (Fin n) ℝ
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  let c := Module.finBasis ℝ E
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  let sec (k : Fin n) (y : M) : TangentSpace I y :=
    if hy : y ∈ e.baseSet then e.orthonormalBasis c ⟨y, hy⟩ k else 0
  let basisTensor (i : Fin 4 → Fin n) : TauCeti.FourTensor V₀ :=
    (ContinuousMultilinearMap.mkPiRing ℝ (Fin 4) (1 : ℝ)).compContinuousLinearMap
      fun s ↦ innerSL ℝ (b₀ (i s))
  let coeff (i : Fin 4 → Fin n) (y : M) : ℝ :=
    inner ℝ (cov.curvatureTensor y (sec (i 0) y) (sec (i 1) y) (sec (i 3) y)) (sec (i 2) y)
  refine ⟨fun y ↦ ∑ i : Fin 4 → Fin n, coeff i y • basisTensor i, ?_, ?_⟩
  · refine tendsto_finsetSum Finset.univ fun i _ ↦ ?_
    have hsec (k : Fin n) :
        ContMDiffWithinAt I I.tangent 0 (fun y ↦ TotalSpace.mk' E y (sec k y)) e.baseSet x₀ :=
      e.contMDiffOn_orthonormalBasis c k x₀ hx₀
    have hR := cov.contMDiffWithinAt_curvatureTensor (F := E) (V := TangentSpace I)
      (by simp : (0 : ℕ∞ω) ≤ ∞) (hsec (i 0)) (hsec (i 1)) (hsec (i 3))
    have hc : ContinuousAt (coeff i) x₀ :=
      (continuousWithinAt_iff_continuousAt (e.open_baseSet.mem_nhds hx₀)).1
        (hR.inner_bundle (IB := I) (F := E) (E := fun y : M ↦ TangentSpace I y)
          (b := fun y : M ↦ y)
          (h := (inferInstance : IsContMDiffRiemannianBundle I 0 E
            (fun y : M ↦ TangentSpace I y))) (hsec (i 2))).continuousWithinAt
    exact hc.smul continuousAt_const
  · filter_upwards [e.open_baseSet.mem_nhds hx₀] with y hy
    let d := e.orthonormalBasis c ⟨y, hy⟩
    refine ⟨d.repr.symm, ?_⟩
    ext m
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
    (F₀ : TauCeti.FourTensor (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) → ℝ)
    (F : ∀ x : M, TauCeti.FourTensor (TangentSpace I x) → ℝ) (hcont : Continuous F₀)
    (hinv : ∀ (y : M) (L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃ₗᵢ[ℝ] TangentSpace I y),
      F₀ ((cov.curvatureFourTensor y).compContinuousLinearMap
        fun _ ↦ (L : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ] TangentSpace I y)) =
        F y (cov.curvatureFourTensor y)) :
    Continuous fun x : M ↦ F x (cov.curvatureFourTensor x) := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦ ?_
  obtain ⟨Φ, hΦ, heq⟩ := cov.exists_continuousAt_pullback_curvatureFourTensor x₀
  exact (hcont.continuousAt.comp hΦ).congr_of_eventuallyEq
    (heq.mono fun y ⟨L, hL⟩ ↦ ((congrArg F₀ hL).trans (hinv y L)).symm)

/-- The operator norm of `curvatureFourTensor` is continuous across `M`. -/
theorem continuous_norm_curvatureFourTensor :
    Continuous fun x : M ↦ ‖cov.curvatureFourTensor x‖ :=
  cov.continuous_of_pullback_invariant (fun r ↦ ‖r‖) (fun _ r ↦ ‖r‖) continuous_norm fun _ _ ↦
    ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv _ _

/-- The minimum sectional curvature `sectionalMin ∘ curvatureFourTensor` is continuous on `M`. -/
theorem continuous_sectionalMin_curvatureFourTensor :
    Continuous fun x : M ↦ TauCeti.FourTensor.sectionalMin (cov.curvatureFourTensor x) :=
  cov.continuous_of_pullback_invariant TauCeti.FourTensor.sectionalMin
    (fun _ ↦ TauCeti.FourTensor.sectionalMin) TauCeti.FourTensor.continuous_sectionalMin fun _ L ↦
      TauCeti.FourTensor.sectionalMin_compContinuousLinearMap_linearIsometryEquiv L _

/-- The maximum sectional curvature `sectionalMax ∘ curvatureFourTensor` is continuous on `M`. -/
theorem continuous_sectionalMax_curvatureFourTensor :
    Continuous fun x : M ↦ TauCeti.FourTensor.sectionalMax (cov.curvatureFourTensor x) :=
  cov.continuous_of_pullback_invariant TauCeti.FourTensor.sectionalMax
    (fun _ ↦ TauCeti.FourTensor.sectionalMax) TauCeti.FourTensor.continuous_sectionalMax fun _ L ↦
      TauCeti.FourTensor.sectionalMax_compContinuousLinearMap_linearIsometryEquiv L _

/-- The `PIC2` minimum functional `pic2Min ∘ curvatureFourTensor` is continuous on `M`. -/
theorem continuous_pic2Min_curvatureFourTensor :
    Continuous fun x : M ↦ TauCeti.FourTensor.pic2Min (cov.curvatureFourTensor x) :=
  cov.continuous_of_pullback_invariant TauCeti.FourTensor.pic2Min
    (fun _ ↦ TauCeti.FourTensor.pic2Min) TauCeti.FourTensor.continuous_pic2Min fun _ L ↦
      TauCeti.FourTensor.pic2Min_compContinuousLinearMap_linearIsometryEquiv L _

end Continuity

section QuarterPinching

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
    (ht : cov.torsion = 0) (x : M) :
    TauCeti.FourTensor.IsAlgebraicCurvature (cov.curvatureFourTensor x) where
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
    (ht : cov.torsion = 0) (x : M) :
    TauCeti.FourTensor.algebraicCurvatureSubmodule (TangentSpace I x) :=
  ⟨cov.curvatureFourTensor x, TauCeti.FourTensor.mem_algebraicCurvatureSubmodule.2
    (hcov.isAlgebraicCurvature_curvatureFourTensor cov ht x)⟩

/-- Coercion of `IsMetricCompatible.algebraicCurvature` to `FourTensor`. -/
@[simp]
theorem IsMetricCompatible.coe_algebraicCurvature
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) (x : M) :
    (hcov.algebraicCurvature cov ht x).1 = cov.curvatureFourTensor x := (rfl)

/-- A metric-compatible connection is strictly quarter-pinched at `x` if every tangent two-plane at
`x` has positive sectional curvature strictly less than four times that of every other tangent
two-plane at `x`. -/
def IsQuarterPinchedAt
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (x : M) : Prop :=
  ∀ u v u' v' : TangentSpace I x, LinearIndependent ℝ ![u, v] → LinearIndependent ℝ ![u', v'] →
    0 < cov.sectionalCurvature hcov x u v ∧
      cov.sectionalCurvature hcov x u v < 4 * cov.sectionalCurvature hcov x u' v'

/-- Pointwise unfolding of `IsQuarterPinchedAt`. -/
theorem isQuarterPinchedAt_iff
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (x : M) : cov.IsQuarterPinchedAt hcov x ↔
      ∀ u v u' v' : TangentSpace I x,
        LinearIndependent ℝ ![u, v] → LinearIndependent ℝ ![u', v'] →
          0 < cov.sectionalCurvature hcov x u v ∧
            cov.sectionalCurvature hcov x u v < 4 * cov.sectionalCurvature hcov x u' v' := Iff.rfl

/-- Strict sectional curvature bounds `0 < a`, `b < 4 * a` at `x` imply `IsQuarterPinchedAt`. -/
theorem isQuarterPinchedAt_of_sectionalCurvature_mem_Icc
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (x : M) {a b : ℝ} (ha : 0 < a) (hab : b < 4 * a)
    (hsec : ∀ u v : TangentSpace I x, LinearIndependent ℝ ![u, v] →
      cov.sectionalCurvature hcov x u v ∈ Icc a b) :
    cov.IsQuarterPinchedAt hcov x := fun u v u' v' huv huv' ↦
  ⟨ha.trans_le (hsec u v huv).1,
    (hsec u v huv).2.trans_lt (hab.trans_le (by linarith [(hsec u' v' huv').1]))⟩

/-- A connection is pointwise strictly quarter-pinched when `IsQuarterPinchedAt` holds at every
point of `M`. -/
def IsPointwiseQuarterPinched
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov) :
    Prop :=
  ∀ x : M, cov.IsQuarterPinchedAt hcov x

/-- Pointwise characterization of `IsPointwiseQuarterPinched`. -/
theorem isPointwiseQuarterPinched_iff
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov) :
    cov.IsPointwiseQuarterPinched hcov ↔ ∀ x : M, cov.IsQuarterPinchedAt hcov x := Iff.rfl

variable {cov} in
/-- Specialize `IsPointwiseQuarterPinched` to a point `x : M`. -/
theorem IsPointwiseQuarterPinched.isQuarterPinchedAt
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov}
    (h : cov.IsPointwiseQuarterPinched hcov) (x : M) : cov.IsQuarterPinchedAt hcov x := h x

variable {cov} in
/-- Weak quarter pinching at `x` implies `IsPIC2FourFrame (cov.curvatureFourTensor x)`. -/
theorem IsMetricCompatible.isPIC2FourFrame_curvatureFourTensor_of_sectionalCurvature_mem_Icc
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) (x : M) {a b : ℝ} (ha : 0 ≤ a) (hab : b ≤ 4 * a)
    (hsec : ∀ u v : TangentSpace I x, LinearIndependent ℝ ![u, v] →
      cov.sectionalCurvature hcov x u v ∈ Icc a b) :
    TauCeti.FourTensor.IsPIC2FourFrame (cov.curvatureFourTensor x) :=
  (hcov.isAlgebraicCurvature_curvatureFourTensor cov ht x).isPIC2FourFrame_of_weak_quarterPinching
    ha hab fun u v huv ↦ by
      rw [← cov.sectionalCurvature_eq_curvatureFourTensor_of_orthonormal hcov x huv]
      exact mem_Icc.1 (hsec u v huv.linearIndependent)

variable {cov} in
/-- In dimension at least two, strict quarter pinching at `x` implies `0 < sectionalMin`,
`sectionalMax < 4 * sectionalMin`, and places `algebraicCurvature` in `interior PIC2`. -/
theorem IsQuarterPinchedAt.mem_interior_isPIC2FourFrame
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov}
    {x : M} (hp : cov.IsQuarterPinchedAt hcov x) (ht : cov.torsion = 0)
    (hn : 2 ≤ Module.finrank ℝ E) :
    0 < TauCeti.FourTensor.sectionalMin (cov.curvatureFourTensor x) ∧
      TauCeti.FourTensor.sectionalMax (cov.curvatureFourTensor x) <
        4 * TauCeti.FourTensor.sectionalMin (cov.curvatureFourTensor x) ∧
      hcov.algebraicCurvature cov ht x ∈
        interior {q | TauCeti.FourTensor.IsPIC2FourFrame q.1} :=
  TauCeti.FourTensor.mem_interior_isPIC2FourFrame_of_quarterPinched
    (by simpa using hn) (hcov.algebraicCurvature cov ht x) fun u v u' v' huv huv' ↦ by
      simpa only [IsMetricCompatible.coe_algebraicCurvature,
        ← cov.sectionalCurvature_eq_curvatureFourTensor_div hcov x] using hp u v u' v' huv huv'

section Compact

variable {cov} [CompactSpace M]

/-- On a compact manifold of dimension at least two, pointwise strict quarter pinching yields a
uniform positive sectional lower bound `a > 0` and a uniform pinching factor `θ < 4`. -/
theorem IsPointwiseQuarterPinched.exists_pos_and_lt_four_sectionalCurvature
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov}
    (hp : cov.IsPointwiseQuarterPinched hcov) (ht : cov.torsion = 0)
    (hn : 2 ≤ Module.finrank ℝ E) :
    ∃ a > 0, ∃ θ < (4 : ℝ), ∀ (x : M) (u v u' v' : TangentSpace I x),
      LinearIndependent ℝ ![u, v] → LinearIndependent ℝ ![u', v'] →
        a ≤ cov.sectionalCurvature hcov x u v ∧
          cov.sectionalCurvature hcov x u v ≤ θ * cov.sectionalCurvature hcov x u' v' := by
  rcases isEmpty_or_nonempty M with hE | hNE
  · exact ⟨1, one_pos, 1, by norm_num, fun x ↦ hE.elim x⟩
  · let smin (x : M) := TauCeti.FourTensor.sectionalMin (cov.curvatureFourTensor x)
    let smax (x : M) := TauCeti.FourTensor.sectionalMax (cov.curvatureFourTensor x)
    have hpos (x : M) : 0 < smin x := ((hp x).mem_interior_isPIC2FourFrame ht hn).1
    have hlt (x : M) : smax x / smin x < 4 :=
      (div_lt_iff₀ (hpos x)).2 ((hp x).mem_interior_isPIC2FourFrame ht hn).2.1
    obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty
      cov.continuous_sectionalMin_curvatureFourTensor.continuousOn
    have hcont_div : Continuous fun x : M ↦ smax x / smin x :=
      cov.continuous_sectionalMax_curvatureFourTensor.div
        cov.continuous_sectionalMin_curvatureFourTensor fun x ↦ (hpos x).ne'
    obtain ⟨x₁, -, hx₁⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hcont_div.continuousOn
    refine ⟨smin x₀, hpos x₀, smax x₁ / smin x₁, hlt x₁, fun x u v u' v' huv huv' ↦ ?_⟩
    have hr := hcov.isAlgebraicCurvature_curvatureFourTensor cov ht x
    have hmin_le {w z : TangentSpace I x} (hwz : LinearIndependent ℝ ![w, z]) :
        smin x ≤ cov.sectionalCurvature hcov x w z := by
      rw [cov.sectionalCurvature_eq_curvatureFourTensor_div hcov x]
      exact (le_div_iff₀ (Matrix.posDef_gram_of_linearIndependent hwz).det_pos).2
        (hr.sectionalMin_mul_det_gram_le_and_le_sectionalMax w z).1
    have hle_max : cov.sectionalCurvature hcov x u v ≤ smax x := by
      rw [cov.sectionalCurvature_eq_curvatureFourTensor_div hcov x]
      exact (div_le_iff₀ (Matrix.posDef_gram_of_linearIndependent huv).det_pos).2
        (hr.sectionalMin_mul_det_gram_le_and_le_sectionalMax u v).2
    have hθ_ge : 0 ≤ smax x₁ / smin x₁ := div_nonneg
      ((hpos x₁).le.trans (TauCeti.FourTensor.sectionalMin_le_sectionalMax (by simpa using hn) _))
      (hpos x₁).le
    refine ⟨(isMinOn_iff.1 hx₀ x (mem_univ x)).trans (hmin_le huv), hle_max.trans ?_⟩
    calc smax x = (smax x / smin x) * smin x := (div_mul_cancel₀ _ (hpos x).ne').symm
      _ ≤ (smax x₁ / smin x₁) * smin x :=
          mul_le_mul_of_nonneg_right (isMaxOn_iff.1 hx₁ x (mem_univ x)) (hpos x).le
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmin_le huv') hθ_ge

/-- On a compact manifold of dimension at least two, pointwise strict quarter pinching yields a
uniform positive margin `ε > 0` below `pic2Expression` across all points and orthonormal
four-frames. -/
theorem IsPointwiseQuarterPinched.exists_pos_le_pic2Expression
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov}
    (hp : cov.IsPointwiseQuarterPinched hcov) (ht : cov.torsion = 0)
    (hn : 2 ≤ Module.finrank ℝ E) :
    ∃ ε > 0, ∀ (x : M) (f : Fin 4 → TangentSpace I x), Orthonormal ℝ f →
      ∀ l ∈ Icc (-1 : ℝ) 1, ∀ m ∈ Icc (-1 : ℝ) 1,
        ε ≤ TauCeti.FourTensor.pic2Expression (cov.curvatureFourTensor x) f l m := by
  rcases isEmpty_or_nonempty M with hE | hNE
  · exact ⟨1, one_pos, fun x ↦ hE.elim x⟩
  · by_cases hn4 : 4 ≤ Module.finrank ℝ E
    · obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty
        cov.continuous_pic2Min_curvatureFourTensor.continuousOn
      have hpos : 0 < TauCeti.FourTensor.pic2Min (cov.curvatureFourTensor x₀) :=
        (TauCeti.FourTensor.mem_interior_isPIC2FourFrame_iff_pic2Min_pos (by simpa using hn4)).1
          ((hp x₀).mem_interior_isPIC2FourFrame ht hn).2.2
      exact ⟨TauCeti.FourTensor.pic2Min (cov.curvatureFourTensor x₀), hpos,
        fun x _ hf _ hl _ hm ↦ (isMinOn_iff.1 hx₀ x (mem_univ x)).trans
          (TauCeti.FourTensor.pic2Min_le_pic2Expression _ hf hl hm)⟩
    · refine ⟨1, one_pos, fun x f hf ↦ ?_⟩
      have hcard := hf.linearIndependent.fintype_card_le_finrank
      rw [Fintype.card_fin, TauCeti.finrank_tangentSpace] at hcard; omega

/-- On a compact pointwise strictly quarter-pinched manifold of dimension at least two, all
isometric pullbacks of the manifold's curvature tensors to the Euclidean model space lie inside a
single compact convex `O(n)`-invariant subset of `interior PIC2`. -/
theorem IsPointwiseQuarterPinched.exists_isCompact_convex_subset_interior
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov}
    (hp : cov.IsPointwiseQuarterPinched hcov) (ht : cov.torsion = 0)
    (hn : 2 ≤ Module.finrank ℝ E) :
    let V₀ := EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
    ∃ K : Set (TauCeti.FourTensor.algebraicCurvatureSubmodule V₀),
      IsCompact K ∧ Convex ℝ K ∧
      (∀ (e : V₀ ≃ₗᵢ[ℝ] V₀) (q : TauCeti.FourTensor.algebraicCurvatureSubmodule V₀),
        q ∈ K → TauCeti.FourTensor.algebraicCurvatureLinearIsometryEquiv e q ∈ K) ∧
      K ⊆ interior {q | TauCeti.FourTensor.IsPIC2FourFrame q.1} ∧
      ∀ (x : M) (e : V₀ ≃ₗᵢ[ℝ] TangentSpace I x),
        TauCeti.FourTensor.algebraicCurvatureLinearIsometryEquiv e
          (hcov.algebraicCurvature cov ht x) ∈ K := by
  intro V₀
  rcases isEmpty_or_nonempty M with hE | hNE
  · exact ⟨∅, isCompact_empty, convex_empty, fun _ _ h ↦ h.elim, empty_subset _,
      fun x ↦ hE.elim x⟩
  · obtain ⟨ε, hε, hpic⟩ := hp.exists_pos_le_pic2Expression ht hn
    obtain ⟨x₁, -, hx₁⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
      cov.continuous_norm_curvatureFourTensor.continuousOn
    set R := ‖cov.curvatureFourTensor x₁‖
    let B : Set (TauCeti.FourTensor.algebraicCurvatureSubmodule V₀) :=
      Subtype.val ⁻¹' Metric.closedBall (0 : TauCeti.FourTensor V₀) R
    have hB_cpt : IsCompact B :=
      TauCeti.FourTensor.isClosed_algebraicCurvatureSubmodule.isClosedEmbedding_subtypeVal
        |>.isCompact_preimage (isCompact_closedBall (0 : TauCeti.FourTensor V₀) R)
    have hB_conv : Convex ℝ B := fun q₁ h₁ q₂ h₂ a b ha hb hab ↦ by
      simpa only [B, mem_preimage, Submodule.coe_add, Submodule.coe_smul_of_tower] using
        (convex_closedBall (0 : TauCeti.FourTensor V₀) R) h₁ h₂ ha hb hab
    let P : Set (TauCeti.FourTensor.algebraicCurvatureSubmodule V₀) :=
      {q | ∀ f : Fin 4 → V₀, Orthonormal ℝ f → ∀ l ∈ Icc (-1 : ℝ) 1, ∀ m ∈ Icc (-1 : ℝ) 1,
        ε ≤ TauCeti.FourTensor.pic2Expression q.1 f l m}
    have hP_closed : IsClosed P := by
      have hP_eq : P = ⋂ (f : Fin 4 → V₀) (_ : Orthonormal ℝ f) (l : ℝ) (_ : l ∈ Icc (-1 : ℝ) 1)
          (m : ℝ) (_ : m ∈ Icc (-1 : ℝ) 1),
            {q | ε ≤ TauCeti.FourTensor.pic2Expression q.1 f l m} := by
        ext q; simp only [P, mem_ofPred_eq, mem_iInter]
      rw [hP_eq]
      exact isClosed_iInter fun f ↦ isClosed_iInter fun _ ↦ isClosed_iInter fun l ↦
        isClosed_iInter fun _ ↦ isClosed_iInter fun m ↦ isClosed_iInter fun _ ↦
          isClosed_le continuous_const (TauCeti.FourTensor.continuous_pic2Expression.comp
            (continuous_subtype_val.prodMk (continuous_const (y := (f, l, m)))))
    have hP_conv : Convex ℝ P := fun q₁ h₁ q₂ h₂ a b ha hb hab f hf l hl m hm ↦ by
      change ε ≤ TauCeti.FourTensor.pic2Expression (a • q₁.1 + b • q₂.1) f l m
      rw [TauCeti.FourTensor.pic2Expression_add, TauCeti.FourTensor.pic2Expression_smul,
        TauCeti.FourTensor.pic2Expression_smul]
      nlinarith [h₁ f hf l hl m hm, h₂ f hf l hl m hm]
    refine ⟨B ∩ P, hB_cpt.inter_right hP_closed, hB_conv.inter hP_conv,
      fun e q ⟨hqB, hqP⟩ ↦ ⟨?_, ?_⟩,
      fun q ⟨_, hqP⟩ ↦ TauCeti.FourTensor.mem_interior_isPIC2FourFrame_of_exists_pos_le hε hqP,
      fun x e ↦ ⟨?_, ?_⟩⟩
    · simp only [B, mem_preimage, Metric.mem_closedBall, dist_zero_right,
        TauCeti.FourTensor.coe_algebraicCurvatureLinearIsometryEquiv,
        ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv] at hqB ⊢
      exact hqB
    · intro f hf l hl m hm
      rw [TauCeti.FourTensor.coe_algebraicCurvatureLinearIsometryEquiv,
        TauCeti.FourTensor.pic2Expression_compContinuousLinearMap]
      exact hqP (e ∘ f) (e.toLinearIsometry.orthonormal_comp_iff.2 hf) l hl m hm
    · simp only [B, mem_preimage, Metric.mem_closedBall, dist_zero_right,
        TauCeti.FourTensor.coe_algebraicCurvatureLinearIsometryEquiv,
        IsMetricCompatible.coe_algebraicCurvature,
        ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv]
      exact isMaxOn_iff.1 hx₁ x (mem_univ x)
    · intro f hf l hl m hm
      rw [TauCeti.FourTensor.coe_algebraicCurvatureLinearIsometryEquiv,
        IsMetricCompatible.coe_algebraicCurvature,
        TauCeti.FourTensor.pic2Expression_compContinuousLinearMap]
      exact hpic x (e ∘ f) (e.toLinearIsometry.orthonormal_comp_iff.2 hf) l hl m hm

end Compact

end QuarterPinching

end FourTensor

end CovariantDerivative
