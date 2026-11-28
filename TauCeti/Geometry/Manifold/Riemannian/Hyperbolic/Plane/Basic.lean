/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Metric
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Minimizing
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Polarization
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.Geometry.Manifold.MFDeriv.Opens
import TauCeti.Geometry.Manifold.IsManifold.Basic
import all TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Basic

/-!
# The hyperbolic plane with its Riemannian distance

The upper half-plane model `TauCeti.UpperHalfSpace ℝ` of the hyperbolic plane is the open
half-plane `{(x, y) | 0 < y}` of `ℝ × ℝ` with the metric `(dx² + dy²) / y²`. Its topology is that
of the half-plane, and it carries no distance.

`TauCeti.HyperbolicPlane` is a copy of it, with the same charts, analytic manifold structure and
hyperbolic metric, whose metric space structure is the Riemannian distance, given by
`TauCeti.MetricSpace.ofRiemannianMetric`. It satisfies `IsRiemannianManifold`, so the theory of
Riemannian manifolds with a distance applies to it. All the data except the distance are
definitionally those of the upper half-plane model.

The distance is complete, since the isometries of the upper half-plane act transitively, so the
closed balls are compact. The sectional curvature is `-1`, so the Gaussian curvature
`K = Scal / 2` is `-1`. The hyperbolic plane is contractible, hence simply connected.

## Main definitions

* `TauCeti.HyperbolicPlane`: the hyperbolic plane with its Riemannian distance.
* `TauCeti.HyperbolicPlane.toUpperHalfSpace`: its identification with the upper half-plane model.

## Main statements

* `TauCeti.HyperbolicPlane.instIsRiemannianManifold`: the distance is the Riemannian distance.
* `TauCeti.HyperbolicPlane.instCompleteSpace`, `TauCeti.HyperbolicPlane.instProperSpace`:
  completeness and properness.
* `TauCeti.HyperbolicPlane.hasConstantSectionalCurvature`: the sectional curvature is `-1`.
* `TauCeti.HyperbolicPlane.scalarCurvature_eq`: the scalar curvature is `-2`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 3 (the upper half-space model) and Chapter 6 (the Riemannian distance).
-/

@[expose] public section

open Bundle CovariantDerivative Manifold Metric Set
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace TauCeti

open TauCeti.Manifold

/-- The hyperbolic plane: the upper half-plane `{(x, y) | 0 < y}` of `ℝ × ℝ` with the metric
`(dx² + dy²) / y²`, to be equipped with the Riemannian distance of that metric. -/
def HyperbolicPlane : Type :=
  UpperHalfSpace ℝ

namespace HyperbolicPlane

local notation "P" => WithLp 2 (ℝ × ℝ)
local notation "J" => 𝓘(ℝ, WithLp 2 (ℝ × ℝ))

/-- The identification of the hyperbolic plane with the upper half-plane model. -/
def toUpperHalfSpace : HyperbolicPlane ≃ UpperHalfSpace ℝ :=
  Equiv.refl _

/-- The Riemannian distance of the hyperbolic metric. -/
instance instMetricSpace : MetricSpace HyperbolicPlane :=
  (MetricSpace.ofRiemannianMetric J (UpperHalfSpace ℝ) : MetricSpace (UpperHalfSpace ℝ))

instance instChartedSpace : ChartedSpace P HyperbolicPlane :=
  inferInstanceAs (ChartedSpace P (UpperHalfSpace ℝ))

instance instIsManifold : IsManifold J ω HyperbolicPlane :=
  inferInstanceAs (IsManifold J ω (UpperHalfSpace ℝ))

/-- The hyperbolic metric `(dx² + dy²) / y²`. -/
instance instRiemannianBundle :
    RiemannianBundle (fun x : HyperbolicPlane ↦ TangentSpace J x) :=
  inferInstanceAs (RiemannianBundle (fun x : UpperHalfSpace ℝ ↦ TangentSpace J x))

instance instIsContMDiffRiemannianBundle :
    IsContMDiffRiemannianBundle J ω P (fun x : HyperbolicPlane ↦ TangentSpace J x) :=
  inferInstanceAs (IsContMDiffRiemannianBundle J ω P
    (fun x : UpperHalfSpace ℝ ↦ TangentSpace J x))

instance instIsContinuousRiemannianBundle :
    IsContinuousRiemannianBundle P (fun x : HyperbolicPlane ↦ TangentSpace J x) :=
  inferInstanceAs (IsContinuousRiemannianBundle P
    (fun x : UpperHalfSpace ℝ ↦ TangentSpace J x))

/-- **The hyperbolic plane is a Riemannian manifold**: its distance is the Riemannian distance of
the hyperbolic metric. -/
instance instIsRiemannianManifold : IsRiemannianManifold J HyperbolicPlane :=
  ⟨fun _ _ ↦ rfl⟩

/-- The Riemannian distance of the hyperbolic plane is complete. -/
instance instCompleteSpace : CompleteSpace HyperbolicPlane :=
  UpperHalfSpace.completeSpace_of_riemannianMetric

/-- The closed balls of the hyperbolic plane are compact. -/
instance instProperSpace : ProperSpace HyperbolicPlane :=
  properSpace_of_completeSpace J

instance instContractibleSpace : ContractibleSpace HyperbolicPlane :=
  inferInstanceAs (ContractibleSpace (UpperHalfSpace ℝ))

instance instSimplyConnectedSpace : SimplyConnectedSpace HyperbolicPlane :=
  inferInstance

instance instSecondCountableTopology : SecondCountableTopology HyperbolicPlane :=
  inferInstanceAs (SecondCountableTopology (upperHalfSpaceOpens ℝ))

instance instMeasurableSpace : MeasurableSpace HyperbolicPlane :=
  borel _

instance instBorelSpace : BorelSpace HyperbolicPlane :=
  ⟨rfl⟩

/-! ### Coordinates -/

/-- A point of the hyperbolic plane, as a point `(x, y)` of `ℝ × ℝ`. -/
@[coe]
def toProd (z : HyperbolicPlane) : P :=
  (toUpperHalfSpace z : P)

instance : CoeOut HyperbolicPlane P :=
  ⟨toProd⟩

/-- The height `y` of a point `(x, y)` of the hyperbolic plane. -/
def height (z : HyperbolicPlane) : ℝ :=
  (z : P).snd

@[simp]
theorem _root_.TauCeti.UpperHalfSpace.height_toUpperHalfSpace (z : HyperbolicPlane) :
    UpperHalfSpace.height (toUpperHalfSpace z) = height z :=
  (UpperHalfSpace.snd_coe _).symm

theorem height_pos (z : HyperbolicPlane) : 0 < height z :=
  UpperHalfSpace.height_pos (toUpperHalfSpace z)

/-- The point of the hyperbolic plane represented by a point of `ℝ × ℝ` of positive height. -/
def mk (p : P) (hp : 0 < p.snd) : HyperbolicPlane :=
  toUpperHalfSpace.symm (UpperHalfSpace.mk p hp)

@[simp]
theorem coe_mk (p : P) (hp : 0 < p.snd) : (mk p hp : P) = p :=
  UpperHalfSpace.coe_mk p hp

@[simp]
theorem height_mk (p : P) (hp : 0 < p.snd) : height (mk p hp) = p.snd := by
  rw [height, coe_mk]

theorem coe_injective : Function.Injective ((↑) : HyperbolicPlane → P) :=
  UpperHalfSpace.coe_injective

@[ext]
theorem ext {z w : HyperbolicPlane} (h : (z : P) = w) : z = w :=
  coe_injective h

/-- The charts of the hyperbolic plane are the inclusion into `ℝ × ℝ`. -/
@[simp]
theorem chartAt_apply (z w : HyperbolicPlane) : chartAt P z w = w := by
  change chartAt P (show upperHalfSpaceOpens ℝ from z) (show upperHalfSpaceOpens ℝ from w) = _
  simp
  rfl

/-- The extended charts of the hyperbolic plane are the inclusion into `ℝ × ℝ`. -/
theorem extChartAt_apply (z w : HyperbolicPlane) : extChartAt J z w = w := by
  simp

/-- The charts of the hyperbolic plane are defined everywhere. -/
@[simp]
theorem chartAt_source (z : HyperbolicPlane) : (chartAt P z).source = univ := by
  have h (y : upperHalfSpaceOpens ℝ) : (chartAt P y).source = univ := by
    simp [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_def]
  exact h z

/-- The inclusion of the hyperbolic plane into `ℝ × ℝ` is analytic. -/
theorem contMDiff_coe : ContMDiff J J ω ((↑) : HyperbolicPlane → P) :=
  UpperHalfSpace.contMDiff_coe

/-- A curve of the hyperbolic plane is `Cⁿ` when its trace in `ℝ × ℝ` is. -/
theorem contMDiff_mk {n : ℕ∞ω} {f : ℝ → P} (hf : ContDiff ℝ n f) (h : ∀ t, 0 < (f t).snd) :
    ContMDiff 𝓘(ℝ) J n (fun t ↦ mk (f t) (h t)) :=
  UpperHalfSpace.contMDiff_coe_comp_iff.mp (hf.contMDiff.congr fun t ↦ (coe_mk (f t) (h t)).symm)

/-- A map into the hyperbolic plane is `Cⁿ` on a set when its composite with the inclusion into
`ℝ × ℝ` is. -/
theorem contMDiffOn_coe_comp_iff {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {n : ℕ∞ω} {f : M → HyperbolicPlane} {s : Set M} :
    ContMDiffOn I J n (fun x ↦ (f x : P)) s ↔ ContMDiffOn I J n f s :=
  ContMDiffOn.subtypeVal_comp_iff (upperHalfSpaceOpens ℝ) f s

/-- The inclusion of the hyperbolic plane into `ℝ × ℝ` is a topological embedding. -/
theorem isEmbedding_coe : Topology.IsEmbedding ((↑) : HyperbolicPlane → P) :=
  Topology.IsEmbedding.subtypeVal

theorem continuous_coe : Continuous ((↑) : HyperbolicPlane → P) :=
  isEmbedding_coe.continuous

/-- The image of the hyperbolic plane in `ℝ × ℝ` is the open upper half-plane. -/
theorem range_coe : range ((↑) : HyperbolicPlane → P) = {p | 0 < p.snd} :=
  Subtype.range_val

/-- The hyperbolic inner product of two tangent vectors at `z` is their Euclidean inner product
divided by the square of the height of `z`. -/
theorem inner_def (z : HyperbolicPlane) (v w : TangentSpace J z) :
    ⟪v, w⟫_ℝ = ⟪tangentSpaceCastModel J z v, tangentSpaceCastModel J z w⟫_ℝ / height z ^ 2 :=
  UpperHalfSpace.inner_def (toUpperHalfSpace z) v w

/-- The hyperbolic norm of a tangent vector at `z` is its Euclidean norm divided by the height
of `z`. -/
theorem norm_def (z : HyperbolicPlane) (v : TangentSpace J z) :
    ‖v‖ = ‖tangentSpaceCastModel J z v‖ / height z :=
  UpperHalfSpace.norm_def (toUpperHalfSpace z) v

/-- The differential of the inclusion of the hyperbolic plane into `ℝ × ℝ` is the identity of
`ℝ × ℝ`. -/
theorem mfderiv_coe (z : HyperbolicPlane) (v : TangentSpace J z) :
    mfderiv J J ((↑) : HyperbolicPlane → P) z v = tangentSpaceCastModel J z v := by
  have h := TauCeti.Manifold.mfderiv_subtype_val (I := J) (show upperHalfSpaceOpens ℝ from z)
  exact (congrArg (fun L ↦ L v) h).trans
    (TauCeti.Manifold.tangentSpaceOpenEquiv_apply (I := J) _ v)

/-- The differential of a map from a normed space into the hyperbolic plane is the derivative of
the map of `ℝ × ℝ` it traces. -/
theorem tangentSpaceCastModel_mfderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → HyperbolicPlane} {x : F} {L : F →L[ℝ] P}
    (h : HasFDerivAt (fun y ↦ (f y : P)) L x) (v : F) :
    tangentSpaceCastModel J (f x) (mfderiv 𝓘(ℝ, F) J f x v) = L v := by
  have h1 : mfderiv 𝓘(ℝ, F) J ((Subtype.val : upperHalfSpaceOpens ℝ → P) ∘ f) x v =
      mfderiv 𝓘(ℝ, F) J f x v :=
    mfderiv_subtype_val_comp_apply _
  change (mfderiv 𝓘(ℝ, F) J (fun y ↦ (f y : P)) x v) = _ at h1
  rw [mfderiv_eq_fderiv, h.fderiv] at h1
  exact h1.symm

/-- The velocity of a curve of the hyperbolic plane is the velocity of the curve of `ℝ × ℝ` it
traces. -/
theorem tangentSpaceCastModel_curveVelocity {γ : ℝ → HyperbolicPlane} {t : ℝ} {v : P}
    (h : HasDerivAt (fun s ↦ (γ s : P)) v t) :
    tangentSpaceCastModel J (γ t) (curveVelocity J γ t) = v := by
  rw [curveVelocity_apply]
  refine (tangentSpaceCastModel_mfderiv h.hasFDerivAt 1).trans ?_
  simp

local notation "∇" => leviCivitaConnection J HyperbolicPlane

/-- **The hyperbolic plane has constant sectional curvature `-1`.** -/
theorem hasConstantSectionalCurvature :
    ∇.HasConstantSectionalCurvature (isMetricCompatible_leviCivitaConnection J) (-1) :=
  UpperHalfSpace.hasConstantSectionalCurvature

/-- The tangent planes of the hyperbolic plane have dimension `2`. -/
theorem finrank_tangentSpace (x : HyperbolicPlane) :
    Module.finrank ℝ (TangentSpace J x) = 2 := by
  rw [TauCeti.finrank_tangentSpace, (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).finrank_eq,
    Module.finrank_prod, Module.finrank_self]

/-- The scalar curvature of the hyperbolic plane is `-2`: its Gaussian curvature `Scal / 2` is
`-1`. -/
theorem scalarCurvature_eq (x : HyperbolicPlane) : ∇.scalarCurvature x = -2 := by
  rw [(hasConstantSectionalCurvature.hasSectionalCurvatureAt x).scalarCurvature_eq,
    finrank_tangentSpace]
  norm_num

end HyperbolicPlane

end TauCeti
