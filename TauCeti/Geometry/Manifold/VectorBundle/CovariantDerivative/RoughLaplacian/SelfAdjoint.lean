/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.FormOperator
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.SobolevH1
import TauCeti.Analysis.InnerProductSpace.LaxMilgram
import TauCeti.LinearAlgebra.LinearPMap.Basic

/-!
# The rough Laplacian as a self-adjoint operator on `L²` sections

Let `V` be a smooth real vector bundle of finite rank with a smooth fibre metric over a compact
manifold `M` with a smooth Riemannian metric, and let `∇` be a smooth connection on `V`, with the
Sobolev space `H¹(V)` of `∇` (`CovariantDerivative.SobolevH1`), its value map
`J : H¹(V) → L²(V)` and its energy form `Q`, the continuous extension of `∫ ⟪∇σ, ∇τ⟫ dV` from smooth
sections. This file realizes the rough Laplacian `∇*∇` as an unbounded operator on `L²(V)`, the
partial linear map `CovariantDerivative.SobolevH1.roughLaplacian ∇`. A pair `(f, g)` lies on its
graph exactly when

`f = J w` for some `w ∈ H¹(V)` with `Q(w, v) = ⟪g, J v⟫_{L²}` for every `v ∈ H¹(V)`,

that is, when `∇*∇ f = g` weakly (`CovariantDerivative.SobolevH1.mem_graph_roughLaplacian_iff`).
It is the operator of the form `Q` (`IsCoercive.formOperator`): the `H¹` inner product is the
shifted form `Q + ⟪J ·, J ·⟫_{L²}`, which is coercive, so `1 + ∇*∇` is the inverse of its
Lax–Milgram solution operator.

* `∇*∇` is self-adjoint (`CovariantDerivative.SobolevH1.isSelfAdjoint_roughLaplacian`) and
  nonnegative (`CovariantDerivative.SobolevH1.inner_roughLaplacian_self_nonneg`), since `Q` is
  symmetric and nonnegative, and `-1` lies in its resolvent set
  (`CovariantDerivative.SobolevH1.neg_one_mem_resolventSet_roughLaplacian`): the operator
  `1 + ∇*∇` is invertible on `L²(V)`.
* Its eigenvectors are the values of the weak eigensections
  (`CovariantDerivative.SobolevH1.exists_roughLaplacian_apply_eq_smul_iff`).
* The domain is the maximal weak domain `{J w | v ↦ Q(w, v) is L²-bounded}`
  (`CovariantDerivative.SobolevH1.mem_domain_roughLaplacian_iff`).
* When `M` has no boundary and `∇` is compatible with the metric, the smooth sections lie in the
  domain, where the operator is the rough Laplacian `-tr_g ∇²` built with the Levi-Civita
  connection (`CovariantDerivative.SobolevH1.mem_graph_roughLaplacian_toLp_ofSmooth`,
  `CovariantDerivative.SobolevH1.roughLaplacian_toLp_ofSmooth`). So this operator is a
  self-adjoint extension of the formally self-adjoint operator `∇*∇` on smooth sections.

Here `∇*` is the adjoint of `∇` for the fibre metrics and the Riemannian volume, so the operator is
defined for every smooth connection; for a metric connection, when `M` has no boundary, it agrees on
smooth sections with the negative trace `-tr_g ∇²` of `CovariantDerivative.roughLaplacian`. It is
the analogue for sections of a bundle of the scalar operator
`TauCeti.Manifold.SobolevH1.negLaplacian`.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Chapter VI, §2 (the representation
  theorems for closed semibounded forms).
* H. B. Lawson, Jr. and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter III, §2 (Sobolev spaces of sections defined through a connection).
-/

public section

open Bundle MeasureTheory TauCeti
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace CovariantDerivative.SobolevH1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [IsContMDiffRiemannianBundle I ∞ F V] [IsContinuousRiemannianBundle F V]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {cov : CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]

/-- A smooth metric on the tangent bundle is continuous. -/
local instance instIsContinuousRiemannianBundleTangentSpaceRoughLaplacianSelfAdjoint :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun x : M ↦ TangentSpace I x)

variable (cov) in
/-- **The rough Laplacian** `∇*∇` of a smooth connection `∇` on a bundle over a compact
manifold, as an unbounded operator on `L²(V)`: the operator of the energy form `Q` along the value
map `H¹(V) → L²(V)`. Its graph consists of the pairs `(J w, g)` with `Q(w, v) = ⟪g, J v⟫_{L²}` for
every `v ∈ H¹(V)` (`CovariantDerivative.SobolevH1.mem_graph_roughLaplacian_iff`). For a metric
connection on a bundle over a closed manifold (`[I.Boundaryless]`) it extends
`CovariantDerivative.smoothRoughLaplacian` with the Levi-Civita connection
(`CovariantDerivative.SobolevH1.roughLaplacian_toLp_ofSmooth`). -/
def roughLaplacian :
    LpSection ℝ F V 2 (riemannianVolume I M) →ₗ.[ℝ] LpSection ℝ F V 2 (riemannianVolume I M) :=
  isCoercive_innerSL.formOperator (toLp cov) 1

/-- The `H¹` inner product is the energy form shifted by the `L²` inner product. -/
private theorem inner_eq_energyForm_add (w v : cov.SobolevH1) :
    innerSL ℝ w v = energyForm w v + 1 * ⟪toLp cov w, toLp cov v⟫_ℝ := by
  rw [energyForm_apply, innerSL_apply_apply]
  ring

variable [T2Space M] [ContMDiffVectorBundle ∞ F V I]

/-- **The graph of the rough Laplacian.** `(f, g)` lies on the graph of `∇*∇` exactly when `f` is
the value of some `w ∈ H¹(V)` with `Q(w, v) = ⟪g, J v⟫_{L²}` for every `v ∈ H¹(V)`, that is, when
`∇*∇ f = g` weakly. -/
theorem mem_graph_roughLaplacian_iff {f g : LpSection ℝ F V 2 (riemannianVolume I M)} :
    (f, g) ∈ (roughLaplacian cov).graph ↔
      ∃ w : cov.SobolevH1, toLp cov w = f ∧ ∀ v, energyForm w v = ⟪g, toLp cov v⟫_ℝ :=
  isCoercive_innerSL.mem_graph_formOperator_iff denseRange_toLp inner_eq_energyForm_add

/-- **The domain of the rough Laplacian** is the maximal weak domain: `f` lies in it exactly when
`f` is the value of some `w ∈ H¹(V)` for which `v ↦ Q(w, v)` is bounded by a multiple of the `L²`
norm of `v`. -/
theorem mem_domain_roughLaplacian_iff {f : LpSection ℝ F V 2 (riemannianVolume I M)} :
    f ∈ (roughLaplacian cov).domain ↔
      ∃ w : cov.SobolevH1, toLp cov w = f ∧ ∃ C : ℝ, ∀ v, |energyForm w v| ≤ C * ‖toLp cov v‖ :=
  isCoercive_innerSL.mem_domain_formOperator_iff denseRange_toLp inner_eq_energyForm_add

/-- Every element `f` of the domain is the value of some `w ∈ H¹(V)` with
`Q(w, v) = ⟪∇*∇ f, J v⟫_{L²}` for every `v ∈ H¹(V)`. -/
theorem exists_energyForm_eq_inner_roughLaplacian (f : (roughLaplacian cov).domain) :
    ∃ w : cov.SobolevH1, toLp cov w = f ∧
      ∀ v, energyForm w v = ⟪roughLaplacian cov f, toLp cov v⟫_ℝ :=
  mem_graph_roughLaplacian_iff.1 ((roughLaplacian cov).mem_graph f)

/-- **The rough Laplacian is self-adjoint.** -/
theorem isSelfAdjoint_roughLaplacian : IsSelfAdjoint (roughLaplacian cov) :=
  isCoercive_innerSL.isSelfAdjoint_formOperator denseRange_toLp inner_eq_energyForm_add
    energyForm_comm

/-- **The rough Laplacian is nonnegative**: `⟪∇*∇ f, f⟫_{L²} ≥ 0` for every `f` in its domain. -/
theorem inner_roughLaplacian_self_nonneg (f : (roughLaplacian cov).domain) :
    0 ≤ ⟪roughLaplacian cov f, (f : LpSection ℝ F V 2 (riemannianVolume I M))⟫_ℝ := by
  obtain ⟨w, hw, hQ⟩ := exists_energyForm_eq_inner_roughLaplacian f
  rw [← hw, ← hQ]
  exact energyForm_self_nonneg w

/-- **`1 + ∇*∇` is invertible**: `-1` lies in the resolvent set of the rough Laplacian. -/
theorem neg_one_mem_resolventSet_roughLaplacian : -1 ∈ (roughLaplacian cov).resolventSet :=
  isCoercive_innerSL.neg_mem_resolventSet_formOperator denseRange_toLp

/-- **The eigenvectors of the rough Laplacian are the weak eigensections.** `f` lies in the domain
of `∇*∇` with `∇*∇ f = μ f` exactly when `f` is the value of some `w ∈ H¹(V)` with
`Q(w, v) = μ ⟪J w, J v⟫_{L²}` for every `v ∈ H¹(V)`. -/
theorem exists_roughLaplacian_apply_eq_smul_iff {μ : ℝ}
    {f : LpSection ℝ F V 2 (riemannianVolume I M)} :
    (∃ hf : f ∈ (roughLaplacian cov).domain, roughLaplacian cov ⟨f, hf⟩ = μ • f) ↔
      ∃ w : cov.SobolevH1, toLp cov w = f ∧
        ∀ v, energyForm w v = μ * ⟪toLp cov w, toLp cov v⟫_ℝ := by
  rw [LinearPMap.exists_apply_eq_iff_mem_graph, mem_graph_roughLaplacian_iff]
  refine exists_congr fun w ↦ and_congr_right fun hw ↦ forall_congr' fun v ↦ ?_
  rw [hw, real_inner_smul_left]

/-! ### Smooth sections -/

section Smooth

variable [I.Boundaryless]

/-- **The rough Laplacian on smooth sections.** For a metric connection `∇` on a bundle over a
closed manifold, the value of every smooth section `u` lies in the domain of the rough Laplacian,
where its image is the value of `∇*∇ u = -tr_g ∇²u`, built with the Levi-Civita connection. -/
theorem mem_graph_roughLaplacian_toLp_ofSmooth (hcov : cov.IsMetricCompatible)
    (u : Cₛ^∞⟮I; F, V⟯) :
    (toLp cov (ofSmooth cov u),
        toLp cov (ofSmooth cov (cov.smoothRoughLaplacian (leviCivitaConnection I M) u))) ∈
      (roughLaplacian cov).graph := by
  refine mem_graph_roughLaplacian_iff.2 ⟨ofSmooth cov u, rfl, fun v ↦ ?_⟩
  rw [energyForm_comm, energyForm_ofSmooth_right hcov, real_inner_comm]

/-- For a metric connection on a bundle over a closed manifold, the value of every smooth section
lies in the domain of the rough Laplacian. -/
theorem toLp_ofSmooth_mem_domain_roughLaplacian (hcov : cov.IsMetricCompatible)
    (u : Cₛ^∞⟮I; F, V⟯) : toLp cov (ofSmooth cov u) ∈ (roughLaplacian cov).domain :=
  LinearPMap.mem_domain_of_mem_graph (mem_graph_roughLaplacian_toLp_ofSmooth hcov u)

/-- For a metric connection on a bundle over a closed manifold, the rough Laplacian of the value of
a smooth section `u` is the value of `∇*∇ u`, built with the Levi-Civita connection. -/
theorem roughLaplacian_toLp_ofSmooth (hcov : cov.IsMetricCompatible) (u : Cₛ^∞⟮I; F, V⟯) :
    roughLaplacian cov
        ⟨toLp cov (ofSmooth cov u), toLp_ofSmooth_mem_domain_roughLaplacian hcov u⟩ =
      toLp cov (ofSmooth cov (cov.smoothRoughLaplacian (leviCivitaConnection I M) u)) :=
  (roughLaplacian cov).mem_graph_snd_inj (LinearPMap.mem_graph _ _)
    (mem_graph_roughLaplacian_toLp_ofSmooth hcov u) rfl

end Smooth

end CovariantDerivative.SobolevH1
