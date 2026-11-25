/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Convex
public import Mathlib.MeasureTheory.Group.Arithmetic
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Dirac
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# The push-forward action on probability measures

An action of `M` on a measurable space `X` by measurable maps (`MeasurableConstSMul M X`) induces
an action of `M` on `ProbabilityMeasure X` by push-forward, `g • μ = μ.map (g • ·)`, so that
`(g • μ) s = μ (g⁻¹ • s)` for measurable `s` when `M` is a group.

This action is affine (`MeasureTheory.ProbabilityMeasure.smul_convexComb`), and when `X` is a
topological space with its Borel σ-algebra on which each `x ↦ g • x` is continuous, each
`μ ↦ g • μ` is continuous for the weak topology. For a group this makes each `μ ↦ g • μ` an affine
homeomorphism of `ProbabilityMeasure X` (Mathlib's `Homeomorph.smul`). For example, a group
acting on a subshift by shifts acts on its probability measures; invariant measures are the fixed
points of this action (`MeasureTheory.ProbabilityMeasure.smulInvariantMeasure_iff_forall_smul_eq`),
so they form a weakly closed set
(`MeasureTheory.ProbabilityMeasure.isClosed_setOf_smulInvariantMeasure`).

## Main declarations

* `MeasureTheory.ProbabilityMeasure.instMulActionPushforward`: the push-forward action.
* `MeasureTheory.ProbabilityMeasure.smul_apply`: evaluation on a measurable set.
* `MeasureTheory.ProbabilityMeasure.instContinuousConstSMulPushforward`: continuity for the weak
  topology.
* `MeasureTheory.ProbabilityMeasure.smul_convexComb`: the action is affine.
* `MeasureTheory.ProbabilityMeasure.smul_diracProba`: the action moves point masses.
* `MeasureTheory.ProbabilityMeasure.isClosed_setOf_smulInvariantMeasure`: the invariant
  probability measures are weakly closed.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal Pointwise

namespace MeasureTheory.ProbabilityMeasure

variable {M X : Type*} [MeasurableSpace X]

section SMul

variable [SMul M X]

/-- The action on probability measures by push-forward along `x ↦ g • x`. -/
instance instSMulPushforward : SMul M (ProbabilityMeasure X) where
  smul g μ := μ.map (g • ·)

/-- The underlying measure of `g • μ` is the push-forward of `μ` along `x ↦ g • x`. -/
@[simp]
theorem toMeasure_smul (g : M) (μ : ProbabilityMeasure X) :
    ((g • μ : ProbabilityMeasure X) : Measure X) = (μ : Measure X).map (g • ·) :=
  (rfl)

/-- The action on probability measures is push-forward along `x ↦ g • x`. -/
theorem smul_eq_map (g : M) (μ : ProbabilityMeasure X) : g • μ = μ.map (g • ·) :=
  (rfl)

/-- The push-forward action is continuous in the measure for the weak topology, when each
`x ↦ g • x` is continuous and `X` carries its Borel σ-algebra. -/
instance instContinuousConstSMulPushforward [TopologicalSpace X] [BorelSpace X]
    [ContinuousConstSMul M X] : ContinuousConstSMul M (ProbabilityMeasure X) where
  continuous_const_smul g := continuous_map (continuous_const_smul g)

variable [MeasurableConstSMul M X]

/-- The mass of a measurable set under `g • μ` is the mass of its preimage under `x ↦ g • x`. -/
@[simp]
theorem smul_apply (g : M) (μ : ProbabilityMeasure X) {s : Set X} (hs : MeasurableSet s) :
    (g • μ) s = μ ((g • ·) ⁻¹' s) :=
  map_apply μ (measurable_const_smul g).aemeasurable hs

/-- **The action is affine.** Acting on a convex combination of probability measures gives the
convex combination of the translates. -/
@[simp]
theorem smul_convexComb (g : M) {a b : ℝ≥0∞} (hab : a + b = 1) (P Q : ProbabilityMeasure X) :
    g • convexComb hab P Q = convexComb hab (g • P) (g • Q) :=
  map_convexComb (measurable_const_smul g) hab P Q

/-- The action moves point masses along the action on `X`. -/
@[simp]
theorem smul_diracProba (g : M) (x : X) : g • diracProba x = diracProba (g • x) :=
  map_diracProba (measurable_const_smul g) x

/-- A probability measure is invariant under the action on `X` iff it is a fixed point of the
push-forward action. -/
theorem smulInvariantMeasure_iff_forall_smul_eq (μ : ProbabilityMeasure X) :
    SMulInvariantMeasure M X μ ↔ ∀ g : M, g • μ = μ := by
  refine ⟨fun _ g => toMeasure_injective (measurePreserving_smul g (μ : Measure X)).map_eq,
    fun h => ⟨fun g s hs => ?_⟩⟩
  rw [← Measure.map_apply (measurable_const_smul g) hs, ← toMeasure_smul, h g]

/-- **The invariant probability measures are weakly closed**, for an action by continuous maps on
a Borel space whose closed sets have continuous outer approximations, such as a pseudo-metrisable
space. -/
theorem isClosed_setOf_smulInvariantMeasure [TopologicalSpace X] [BorelSpace X]
    [HasOuterApproxClosed X] [ContinuousConstSMul M X] :
    IsClosed {μ : ProbabilityMeasure X | SMulInvariantMeasure M X μ} := by
  simp_rw [smulInvariantMeasure_iff_forall_smul_eq, Set.ofPred_forall]
  exact isClosed_iInter fun g => isClosed_eq (continuous_const_smul g) continuous_id

end SMul

/-- **The push-forward action.** A monoid acting on `X` by measurable maps acts on the
probability measures on `X` by push-forward. -/
instance instMulActionPushforward [Monoid M] [MulAction M X] [MeasurableConstSMul M X] :
    MulAction M (ProbabilityMeasure X) where
  one_smul μ := toMeasure_injective <| by
    simp only [toMeasure_smul, one_smul]
    exact Measure.map_id
  mul_smul g h μ := toMeasure_injective <| by
    simp only [toMeasure_smul]
    rw [Measure.map_map (measurable_const_smul g) (measurable_const_smul h)]
    simp only [Function.comp_def, mul_smul]

/-- For a group action, the mass of a measurable set under `g • μ` is the mass of its translate
by `g⁻¹`. -/
theorem smul_apply_eq_inv_smul [Group M] [MulAction M X] [MeasurableConstSMul M X] (g : M)
    (μ : ProbabilityMeasure X) {s : Set X} (hs : MeasurableSet s) :
    (g • μ) s = μ (g⁻¹ • s) := by
  rw [smul_apply g μ hs, Set.preimage_smul]

end MeasureTheory.ProbabilityMeasure
