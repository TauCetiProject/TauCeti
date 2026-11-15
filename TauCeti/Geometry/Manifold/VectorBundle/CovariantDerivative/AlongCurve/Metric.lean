/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Pullback
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.TangentCone.Basic

/-!
# Metric compatibility along a curve

This file proves the product rule for a metric-compatible covariant derivative acting on tangent
fields along a curve:

`(d/dt) ⟪V, W⟫ = ⟪D V / dt, W⟫ + ⟪V, D W / dt⟫`.

The product rule is first proved for an arbitrary pointwise bilinear pairing `b` of tangent
vectors, neither symmetric nor nondegenerate, which pairs differentiable vector fields to
differentiable functions and satisfies the ambient product rule
`v (b(Y, Z)) = b(∇_v Y, Z) + b(Y, ∇_v Z)` at the current point of the curve. Fields pulled back from
differentiable vector fields satisfy it by the chain rule. A differentiable field along the curve
is locally a finite linear combination of pullbacks of smooth local-frame fields; the additive and
scalar Leibniz laws of `CovariantDerivative.alongCurveWithin` finish the argument. The
Riemannian product rule is the specialization to the inner product, using Mathlib's ambient
`CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq`; metrics of other signatures specialize
the same theorem.

## Main results

* `CovariantDerivative.hasDerivWithinAt_apply_alongCurveWithin`: the within-set product rule for
  a pointwise bilinear pairing satisfying the ambient product rule.
* `CovariantDerivative.IsMetricCompatible.hasDerivWithinAt_inner_alongCurveWithin`: the
  within-set metric product rule for two differentiable tangent fields along a differentiable
  real curve.
* `CovariantDerivative.IsMetricCompatible.differentiableWithinAt_inner` and
  `CovariantDerivative.IsMetricCompatible.derivWithin_inner_alongCurveWithin`: its two principal
  consequences.
* `CovariantDerivative.IsMetricCompatible.hasDerivAt_inner_alongCurve`: the unrestricted form,
  with `CovariantDerivative.IsMetricCompatible.differentiableAt_inner` and
  `CovariantDerivative.IsMetricCompatible.deriv_inner_alongCurve` as consequences.
* `CovariantDerivative.IsMetricCompatible.inner_alongCurveWithin_self_eq_zero_of_eventually_norm_eq`
  and `CovariantDerivative.IsMetricCompatible.inner_alongCurve_self_eq_zero_of_eventually_norm_eq`:
  a field of locally constant length is orthogonal to its covariant derivative.
* `CovariantDerivative.IsMetricCompatible.inner_eq_of_alongCurveWithin_eq_zero`: parallel fields
  along a curve have constant inner product.
* `CovariantDerivative.IsMetricCompatible.eq_of_alongCurveWithin_eq_zero` and
  `CovariantDerivative.IsMetricCompatible.eq_of_alongCurve_eq_zero`: parallel fields that agree at
  one parameter agree on the whole preconnected parameter set.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 2, Proposition 3.2.
* The proof organization is adapted from
  `DoCarmoLib/Riemannian/Connection/MetricCompatibilityAlong.lean` in the Apache-2.0
  [`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture)
  repository, revision `24f32e4d600878bfaac6bc2f2f9324175571c321`, replacing its custom connection
  and metric APIs with Mathlib's `CovariantDerivative.IsMetricCompatible` and Tau Ceti's
  moving-chart derivative.
-/

public section

open Bundle Filter Function
open scoped Manifold Topology

noncomputable section

namespace CovariantDerivative

open TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  {cov : _root_.CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  {γ : ℝ → M} {s : Set ℝ} {t : ℝ}

section Pairing

/-- The within-set product-rule statement for a pointwise bilinear pairing `B` at one parameter,
packaged for the local-frame induction. The pairing is only linear, so that exchanging its
arguments by `LinearMap.flip` stays within the same kind of pairing. -/
private abbrev HasPairingProductRuleWithinAt
    (B : (x : M) → TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (V W : ∀ r, TangentSpace I (γ r)) : Prop :=
  HasDerivWithinAt (fun r ↦ B (γ r) (V r) (W r))
    (B (γ t) (alongCurveWithin cov γ V s t) (W t) +
      B (γ t) (V t) (alongCurveWithin cov γ W s t)) s t

section Linear

variable {B : (x : M) → TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ}

/-- Exchanging the two fields of the product rule flips the pairing. -/
private lemma HasPairingProductRuleWithinAt.flip
    {V W : ∀ r, TangentSpace I (γ r)}
    (h : HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t) B V W) :
    HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t) (fun x ↦ (B x).flip) W V := by
  dsimp only [HasPairingProductRuleWithinAt] at h ⊢
  simp only [LinearMap.flip_apply]
  rw [add_comm]
  exact h

/-- The product rule for the flipped pairing gives the product rule for the original pairing with
its fields exchanged. -/
private lemma HasPairingProductRuleWithinAt.of_flip
    {V W : ∀ r, TangentSpace I (γ r)}
    (h : HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t) (fun x ↦ (B x).flip) W V) :
    HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t) B V W := by
  simpa only [LinearMap.flip_flip] using h.flip

/-- The product rule is additive in its first field. -/
private lemma HasPairingProductRuleWithinAt.add_left
    {V V' W : ∀ r, TangentSpace I (γ r)}
    (hV : HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t) B V W)
    (hV' : HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t) B V' W)
    (hcoordV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hcoordV' : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V' (γ t)) s t) :
    HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t) B
      (fun r ↦ V r + V' r) W := by
  dsimp only [HasPairingProductRuleWithinAt] at hV hV' ⊢
  simp only [map_add, LinearMap.add_apply]
  refine (hV.add hV').congr_deriv ?_
  rw [alongCurveWithin_add cov γ V V' s hcoordV hcoordV']
  simp only [map_add, LinearMap.add_apply]
  ring

/-- The product rule is preserved by multiplying its first field by a differentiable scalar. -/
private lemma HasPairingProductRuleWithinAt.smul_left
    {V W : ∀ r, TangentSpace I (γ r)} {f : ℝ → ℝ}
    (hV : HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t) B V W)
    (hf : DifferentiableWithinAt ℝ f s t)
    (hcoordV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t) :
    HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t) B
      (fun r ↦ f r • V r) W := by
  dsimp only [HasPairingProductRuleWithinAt] at hV ⊢
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  refine (hf.hasDerivWithinAt.mul hV).congr_deriv ?_
  rw [alongCurveWithin_smul cov γ V f s hf hcoordV]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- The product rule is preserved by multiplying its second field by a differentiable scalar. -/
private lemma HasPairingProductRuleWithinAt.smul_right
    {V W : ∀ r, TangentSpace I (γ r)} {f : ℝ → ℝ}
    (hW : HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t) B V W)
    (hf : DifferentiableWithinAt ℝ f s t)
    (hcoordW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t) :
    HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t) B V
      (fun r ↦ f r • W r) :=
  (hW.flip.smul_left hf hcoordW).of_flip

/-- The product rule is preserved by a finite sum in its first field. -/
private lemma HasPairingProductRuleWithinAt.finsetSum_left
    {ι : Type*} {A : Finset ι} {U : ι → ∀ r, TangentSpace I (γ r)}
    {W : ∀ r, TangentSpace I (γ r)}
    (hU : ∀ i ∈ A,
      HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t) B (U i) W)
    (hcoordU : ∀ i ∈ A,
      DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (U i) (γ t)) s t) :
    HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t) B
      (fun r ↦ ∑ i ∈ A, U i r) W := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      simpa [HasPairingProductRuleWithinAt] using
        (hasDerivWithinAt_const (x := t) (s := s) (c := (0 : ℝ)))
  | @insert a A ha ih =>
      have ha_rule := hU a (Finset.mem_insert_self a A)
      have hA_rule := ih (fun i hi ↦ hU i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hcoordU i (Finset.mem_insert_of_mem hi))
      have hsum := ha_rule.add_left hA_rule
        (hcoordU a (Finset.mem_insert_self a A))
        (differentiableWithinAt_sectionCoord_sum γ
          (fun i hi ↦ hcoordU i (Finset.mem_insert_of_mem hi)))
      simpa only [Finset.sum_insert ha, Pi.add_apply] using hsum

/-- The product rule is preserved by a finite sum in its second field. -/
private lemma HasPairingProductRuleWithinAt.finsetSum_right
    {ι : Type*} {A : Finset ι} {V : ∀ r, TangentSpace I (γ r)}
    {U : ι → ∀ r, TangentSpace I (γ r)}
    (hU : ∀ i ∈ A,
      HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t) B V (U i))
    (hcoordU : ∀ i ∈ A,
      DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (U i) (γ t)) s t) :
    HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t) B V
      (fun r ↦ ∑ i ∈ A, U i r) :=
  (HasPairingProductRuleWithinAt.finsetSum_left
    (hU := fun i hi ↦ (hU i hi).flip) hcoordU).of_flip

/-- The product rule transfers along fields that agree near `t` within `s` and at `t`. -/
private lemma HasPairingProductRuleWithinAt.congr_of_eventuallyEq
    {V V' W W' : ∀ r, TangentSpace I (γ r)}
    (h : HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t) B V W)
    (hV : V =ᶠ[𝓝[s] t] V') (hW : W =ᶠ[𝓝[s] t] W') (hVt : V t = V' t) (hWt : W t = W' t) :
    HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t) B V' W' := by
  dsimp only [HasPairingProductRuleWithinAt] at h ⊢
  have hpair : (fun r ↦ B (γ r) (V r) (W r)) =ᶠ[𝓝[s] t] fun r ↦ B (γ r) (V' r) (W' r) := by
    filter_upwards [hV, hW] with r hVr hWr
    rw [hVr, hWr]
  refine (h.congr_of_eventuallyEq hpair.symm (by rw [hVt, hWt])).congr_deriv ?_
  rw [alongCurveWithin_congr cov γ V hV hVt, alongCurveWithin_congr cov γ W hW hWt, hVt, hWt]

end Linear

variable {b : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}

/-- The product rule along a curve for fields pulled back from ambient differentiable vector
fields. -/
private theorem hasPairingProductRuleWithinAt_pullback
    (hdiff : ∀ ⦃Y Z : Π x : M, TangentSpace I x⦄, MDiffAt (T% Y) (γ t) →
      MDiffAt (T% Z) (γ t) → MDiffAt (fun y ↦ b y (Y y) (Z y)) (γ t))
    (hcompat : ∀ ⦃Y Z : Π x : M, TangentSpace I x⦄, MDiffAt (T% Y) (γ t) →
      MDiffAt (T% Z) (γ t) → ∀ v : TangentSpace I (γ t),
        mvfderiv I (fun y ↦ b y (Y y) (Z y)) (γ t) v =
          b (γ t) (cov Y (γ t) v) (Z (γ t)) + b (γ t) (Y (γ t)) (cov Z (γ t) v))
    (hu : UniqueDiffWithinAt ℝ s t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    {X Y : (x : M) → TangentSpace I x}
    (hX : MDiffAt (T% X) (γ t)) (hY : MDiffAt (T% Y) (γ t)) :
    HasPairingProductRuleWithinAt (cov := cov) (γ := γ) (s := s) (t := t)
      (fun x ↦ (b x).toLinearMap₁₂) (fun r ↦ X (γ r)) (fun r ↦ Y (γ r)) := by
  have hchain := hasDerivWithinAt_comp_curve (hdiff hX hY)
    (hasMFDerivWithinAt_curveVelocityWithin hγ)
  rw [hcompat hX hY] at hchain
  dsimp only [HasPairingProductRuleWithinAt]
  rw [alongCurveWithin_pullback_curveVelocityWithin cov γ X hu hγ hX,
    alongCurveWithin_pullback_curveVelocityWithin cov γ Y hu hγ hY]
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]
  -- The chain-rule result uses a definitionally equal real normed-space instance.
  convert hchain using 1
  rfl

/-- The product rule along a curve for two fields that are finite combinations, with coefficients
differentiable within `s` at `t`, of pullbacks of vector fields `X i` that are differentiable at
`γ t` and whose pullbacks have differentiable coordinate readings. -/
private theorem hasPairingProductRuleWithinAt_frameSum
    (hdiff : ∀ ⦃Y Z : Π x : M, TangentSpace I x⦄, MDiffAt (T% Y) (γ t) →
      MDiffAt (T% Z) (γ t) → MDiffAt (fun y ↦ b y (Y y) (Z y)) (γ t))
    (hcompat : ∀ ⦃Y Z : Π x : M, TangentSpace I x⦄, MDiffAt (T% Y) (γ t) →
      MDiffAt (T% Z) (γ t) → ∀ v : TangentSpace I (γ t),
        mvfderiv I (fun y ↦ b y (Y y) (Z y)) (γ t) v =
          b (γ t) (cov Y (γ t) v) (Z (γ t)) + b (γ t) (Y (γ t)) (cov Z (γ t) v))
    (hu : UniqueDiffWithinAt ℝ s t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    {ι : Type*} [Fintype ι] {X : ι → (x : M) → TangentSpace I x}
    (hframe : ∀ i, MDiffAt (T% (X i)) (γ t))
    (hcoordX : ∀ i, DifferentiableWithinAt ℝ
      (sectionCoord (F := E) γ (fun r ↦ X i (γ r)) (γ t)) s t)
    {aV aW : ι → ℝ → ℝ} (haV : ∀ i, DifferentiableWithinAt ℝ (aV i) s t)
    (haW : ∀ i, DifferentiableWithinAt ℝ (aW i) s t) :
    HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t)
      (fun x ↦ (b x).toLinearMap₁₂)
      (fun r ↦ ∑ i, aV i r • X i (γ r)) (fun r ↦ ∑ j, aW j r • X j (γ r)) := by
  have hcoordTerm {a : ι → ℝ → ℝ} (ha : ∀ i, DifferentiableWithinAt ℝ (a i) s t) (i : ι) :
      DifferentiableWithinAt ℝ
        (sectionCoord (F := E) γ (fun r ↦ a i r • X i (γ r)) (γ t)) s t := by
    rw [sectionCoord_smul]
    exact (ha i).smul (hcoordX i)
  have hterm (i j : ι) : HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t)
      (fun x ↦ (b x).toLinearMap₁₂) (fun r ↦ aV i r • X i (γ r))
      (fun r ↦ aW j r • X j (γ r)) :=
    ((hasPairingProductRuleWithinAt_pullback hdiff hcompat hu hγ (hframe i)
      (hframe j)).smul_left (haV i) (hcoordX i)).smul_right (haW j) (hcoordX j)
  refine HasPairingProductRuleWithinAt.finsetSum_left (A := Finset.univ) ?_
    fun i _ ↦ hcoordTerm haV i
  exact fun i _ ↦ HasPairingProductRuleWithinAt.finsetSum_right
    (A := Finset.univ) (fun j _ ↦ hterm i j) fun j _ ↦ hcoordTerm haW j

/-- **The product rule along a curve** for a pointwise bilinear pairing `b` of tangent vectors.
Suppose that `b` pairs vector fields differentiable at `γ t` to a function differentiable at
`γ t`, and that the covariant derivative satisfies the ambient product rule
`v (b(Y, Z)) = b(∇_v Y, Z) + b(Y, ∇_v Z)` there. Then for two tangent fields along `γ` whose
coordinate readings are differentiable within `s` at `t`,
`(d/dt) b(V, W) = b(D V / dt, W) + b(V, D W / dt)` within `s` at `t`.

Neither symmetry nor nondegeneracy of `b` is needed. -/
theorem hasDerivWithinAt_apply_alongCurveWithin
    (hdiff : ∀ ⦃Y Z : Π x : M, TangentSpace I x⦄, MDiffAt (T% Y) (γ t) →
      MDiffAt (T% Z) (γ t) → MDiffAt (fun y ↦ b y (Y y) (Z y)) (γ t))
    (hcompat : ∀ ⦃Y Z : Π x : M, TangentSpace I x⦄, MDiffAt (T% Y) (γ t) →
      MDiffAt (T% Z) (γ t) → ∀ v : TangentSpace I (γ t),
        mvfderiv I (fun y ↦ b y (Y y) (Z y)) (γ t) v =
          b (γ t) (cov Y (γ t) v) (Z (γ t)) + b (γ t) (Y (γ t)) (cov Z (γ t) v))
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t) :
    HasDerivWithinAt (fun r ↦ b (γ r) (V r) (W r))
      (b (γ t) (alongCurveWithin cov γ V s t) (W t) +
        b (γ t) (V t) (alongCurveWithin cov γ W s t)) s t := by
  by_cases hu : UniqueDiffWithinAt ℝ s t
  swap
  · -- Without unique derivatives, every function has every derivative.
    exact hasDerivWithinAt_iff_hasFDerivWithinAt.2 (.of_not_accPt (mt AccPt.uniqueDiffWithinAt hu))
  -- Expand both fields in a smooth local frame around the point of the curve.
  let e := trivializationAt E (TangentSpace I) (γ t)
  let β := Module.finBasis ℝ E
  have hbase : γ t ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  have hnear : ∀ᶠ r in 𝓝[s] t, γ r ∈ e.baseSet :=
    hγ.continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hbase)
  have hcoord (a : ∀ r, TangentSpace I (γ r))
      (ha : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ a (γ t)) s t) (i : Fin _) :
      DifferentiableWithinAt ℝ
        (fun r ↦ β.coord i (sectionCoord (F := E) γ a (γ t) r)) s t :=
    (LinearMap.toContinuousLinearMap (β.coord i)).differentiableAt.comp_differentiableWithinAt t ha
  have hframe (i : Fin (Module.finrank ℝ E)) : MDiffAt (T% (e.localFrame β i)) (γ t) :=
    (((e.isLocalFrameOn_localFrame_baseSet I 1 β).contMDiffOn i).mdifferentiableOn
      one_ne_zero).mdifferentiableAt (e.open_baseSet.mem_nhds hbase)
  have hcoordX (i : Fin (Module.finrank ℝ E)) : DifferentiableWithinAt ℝ
      (sectionCoord (F := E) γ (fun r ↦ e.localFrame β i (γ r)) (γ t)) s t :=
    differentiableWithinAt_sectionCoord γ (fun r ↦ e.localFrame β i (γ r))
      ((hframe i).comp_mdifferentiableWithinAt t hγ) hbase
  have hsum := hasPairingProductRuleWithinAt_frameSum (cov := cov) hdiff hcompat hu hγ hframe
    hcoordX (hcoord V hV) (hcoord W hW)
  simp only [β.coord_apply] at hsum
  have hexp (Q : ∀ r, TangentSpace I (γ r)) (r : ℝ) (hr : γ r ∈ e.baseSet) :
      ∑ i, β.repr (sectionCoord (F := E) γ Q (γ t) r) i • e.localFrame β i (γ r) = Q r := by
    rw [sectionCoord_apply]
    exact (β.eq_sum_repr_continuousLinearMapAt_smul_localFrame hr (Q r)).symm
  refine HasPairingProductRuleWithinAt.congr_of_eventuallyEq hsum ?_ ?_ (hexp V t hbase)
    (hexp W t hbase)
  · filter_upwards [hnear] with r hr using hexp V r hr
  · filter_upwards [hnear] with r hr using hexp W r hr

end Pairing

section Riemannian

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The within-set product rule for a metric-compatible covariant derivative acting on two
differentiable tangent fields along a differentiable real curve. -/
theorem IsMetricCompatible.hasDerivWithinAt_inner_alongCurveWithin
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t) :
    HasDerivWithinAt (fun r ↦ inner ℝ (V r) (W r))
      (inner ℝ (alongCurveWithin cov γ V s t) (W t) +
        inner ℝ (V t) (alongCurveWithin cov γ W s t)) s t := by
  have hdiff : ∀ ⦃Y Z : Π x : M, TangentSpace I x⦄, MDiffAt (T% Y) (γ t) →
      MDiffAt (T% Z) (γ t) → MDiffAt (fun y ↦ innerSL ℝ (Y y) (Z y)) (γ t) := by
    intro Y Z hY hZ
    simp only [innerSL_apply_apply]
    exact MDifferentiableAt.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x)
      (b := id) hY hZ
  have hcompat : ∀ ⦃Y Z : Π x : M, TangentSpace I x⦄, MDiffAt (T% Y) (γ t) →
      MDiffAt (T% Z) (γ t) → ∀ v : TangentSpace I (γ t),
        mvfderiv I (fun y ↦ innerSL ℝ (Y y) (Z y)) (γ t) v =
          innerSL ℝ (cov Y (γ t) v) (Z (γ t)) + innerSL ℝ (Y (γ t)) (cov Z (γ t) v) := by
    intro Y Z hY hZ v
    simp only [innerSL_apply_apply]
    simpa only [FiberBundle.extend_apply_self] using
      hcov.mvfderiv_inner_eq (FiberBundle.extend E v) hY hZ
  -- `innerSL ℝ v w` unfolds to `inner ℝ v w` (`innerSL_apply_apply` is proved by `rfl`), but
  -- `simp` does not rewrite it under the instances found for `TangentSpace I (γ r)`.
  exact hasDerivWithinAt_apply_alongCurveWithin hdiff hcompat hγ hV hW

/-- The fibrewise inner product of two differentiable tangent fields along a differentiable curve
is differentiable within the parameter set. -/
theorem IsMetricCompatible.differentiableWithinAt_inner
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t) :
    DifferentiableWithinAt ℝ (fun r ↦ inner ℝ (V r) (W r)) s t :=
  (hcov.hasDerivWithinAt_inner_alongCurveWithin hγ hV hW).differentiableWithinAt

/-- The derivative identity supplied by metric compatibility within a parameter set. -/
theorem IsMetricCompatible.derivWithin_inner_alongCurveWithin
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t) :
    derivWithin (fun r ↦ inner ℝ (V r) (W r)) s t =
      inner ℝ (alongCurveWithin cov γ V s t) (W t) +
        inner ℝ (V t) (alongCurveWithin cov γ W s t) := by
  by_cases hu : UniqueDiffWithinAt ℝ s t
  · exact (hcov.hasDerivWithinAt_inner_alongCurveWithin hγ hV hW).derivWithin hu
  · simp [derivWithin_zero_of_not_uniqueDiffWithinAt hu,
      alongCurveWithin_of_not_uniqueDiffWithinAt cov γ _ hu]

/-- The unrestricted product rule for a metric-compatible covariant derivative acting on two
differentiable tangent fields along a differentiable real curve. -/
theorem IsMetricCompatible.hasDerivAt_inner_alongCurve
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t)
    (hW : DifferentiableAt ℝ (sectionCoord (F := E) γ W (γ t)) t) :
    HasDerivAt (fun r ↦ inner ℝ (V r) (W r))
      (inner ℝ (alongCurve cov γ V t) (W t) +
        inner ℝ (V t) (alongCurve cov γ W t)) t := by
  apply hasDerivWithinAt_univ.mp
  simpa only [alongCurveWithin_univ] using
    hcov.hasDerivWithinAt_inner_alongCurveWithin (s := Set.univ)
      hγ.mdifferentiableWithinAt hV.differentiableWithinAt hW.differentiableWithinAt

/-- The fibrewise inner product of two differentiable tangent fields along a differentiable curve
is differentiable. -/
theorem IsMetricCompatible.differentiableAt_inner
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t)
    (hW : DifferentiableAt ℝ (sectionCoord (F := E) γ W (γ t)) t) :
    DifferentiableAt ℝ (fun r ↦ inner ℝ (V r) (W r)) t :=
  (hcov.hasDerivAt_inner_alongCurve hγ hV hW).differentiableAt

/-- The product rule for a metric-compatible covariant derivative acting on two differentiable
tangent fields along a differentiable real curve. -/
theorem IsMetricCompatible.deriv_inner_alongCurve
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t)
    (hW : DifferentiableAt ℝ (sectionCoord (F := E) γ W (γ t)) t) :
    deriv (fun r ↦ inner ℝ (V r) (W r)) t =
      inner ℝ (alongCurve cov γ V t) (W t) +
        inner ℝ (V t) (alongCurve cov γ W t) :=
  (hcov.hasDerivAt_inner_alongCurve hγ hV hW).deriv

/-- **A field of locally constant length is orthogonal to its covariant derivative.** If a
differentiable tangent field `V` along a differentiable real curve has constant metric length on
the parameter set `s` near `t`, then `D V / dt` is orthogonal to `V` at `t`, for a
metric-compatible covariant derivative. -/
theorem IsMetricCompatible.inner_alongCurveWithin_self_eq_zero_of_eventually_norm_eq
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hu : UniqueDiffWithinAt ℝ s t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    {V : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hnorm : ∀ᶠ r in 𝓝[s] t, ‖V r‖ = ‖V t‖) :
    inner ℝ (alongCurveWithin cov γ V s t) (V t) = 0 := by
  have hconst : HasDerivWithinAt (fun r ↦ inner ℝ (V r) (V r)) 0 s t :=
    (hasDerivWithinAt_const t s (‖V t‖ ^ 2)).congr_of_eventuallyEq
      (hnorm.mono fun r hr ↦ by simp only [real_inner_self_eq_norm_sq, hr])
      (real_inner_self_eq_norm_sq _)
  have h := hu.eq_deriv _ (hcov.hasDerivWithinAt_inner_alongCurveWithin hγ hV hV) hconst
  linarith [real_inner_comm (alongCurveWithin cov γ V s t) (V t)]

/-- **A field of locally constant length is orthogonal to its covariant derivative**, for the
unrestricted covariant derivative along a differentiable real curve. -/
theorem IsMetricCompatible.inner_alongCurve_self_eq_zero_of_eventually_norm_eq
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    {V : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t)
    (hnorm : ∀ᶠ r in 𝓝 t, ‖V r‖ = ‖V t‖) :
    inner ℝ (alongCurve cov γ V t) (V t) = 0 := by
  simpa only [alongCurveWithin_univ] using
    hcov.inner_alongCurveWithin_self_eq_zero_of_eventually_norm_eq uniqueDiffWithinAt_univ
      hγ.mdifferentiableWithinAt hV.differentiableWithinAt (by rwa [nhdsWithin_univ])

/-- **Parallel transport preserves the inner product.** On a preconnected parameter set, two
tangent fields along a differentiable curve that have differentiable coordinate readings and are
parallel, `D V / dt = D W / dt = 0` on `s`, have the same inner product at every two parameters
of `s`. -/
theorem IsMetricCompatible.inner_eq_of_alongCurveWithin_eq_zero
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hconn : IsPreconnected s)
    (hγ : MDifferentiableOn 𝓘(ℝ, ℝ) I γ s) {V W : ∀ r, TangentSpace I (γ r)}
    (hV : ∀ t ∈ s, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : ∀ t ∈ s, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t)
    (hV₀ : ∀ t ∈ s, alongCurveWithin cov γ V s t = 0)
    (hW₀ : ∀ t ∈ s, alongCurveWithin cov γ W s t = 0) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    inner ℝ (V a) (W a) = inner ℝ (V b) (W b) := by
  have hderiv (t : ℝ) (ht : t ∈ s) : HasDerivWithinAt (fun r ↦ inner ℝ (V r) (W r)) 0 s t := by
    simpa only [hV₀ t ht, hW₀ t ht, inner_zero_left, inner_zero_right, add_zero] using
      hcov.hasDerivWithinAt_inner_alongCurveWithin (hγ t ht) (hV t ht) (hW t ht)
  exact IsPreconnected.eq_of_hasDerivWithinAt_zero hconn hderiv ha hb

/-- **Uniqueness of parallel fields.** On a preconnected parameter set, two parallel tangent
fields along a differentiable curve that agree at one parameter agree at every parameter of the
set. -/
theorem IsMetricCompatible.eq_of_alongCurveWithin_eq_zero
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hconn : IsPreconnected s)
    (hγ : MDifferentiableOn 𝓘(ℝ, ℝ) I γ s) {V W : ∀ r, TangentSpace I (γ r)}
    (hV : ∀ t ∈ s, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : ∀ t ∈ s, DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t)
    (hV₀ : ∀ t ∈ s, alongCurveWithin cov γ V s t = 0)
    (hW₀ : ∀ t ∈ s, alongCurveWithin cov γ W s t = 0)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) (hinit : V a = W a) : V b = W b := by
  have hVV := hcov.inner_eq_of_alongCurveWithin_eq_zero hconn hγ hV hV hV₀ hV₀ hb ha
  have hVW := hcov.inner_eq_of_alongCurveWithin_eq_zero hconn hγ hV hW hV₀ hW₀ hb ha
  have hWV := hcov.inner_eq_of_alongCurveWithin_eq_zero hconn hγ hW hV hW₀ hV₀ hb ha
  have hWW := hcov.inner_eq_of_alongCurveWithin_eq_zero hconn hγ hW hW hW₀ hW₀ hb ha
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [inner_sub_left, inner_sub_right, inner_sub_right, hVV, hVW, hWV, hWW, hinit]
  ring

/-- **Uniqueness of parallel fields**, for the unrestricted covariant derivative: two parallel
tangent fields along a differentiable curve that agree at one parameter agree on the whole
preconnected parameter set. -/
theorem IsMetricCompatible.eq_of_alongCurve_eq_zero
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hconn : IsPreconnected s)
    (hγ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) {V W : ∀ r, TangentSpace I (γ r)}
    (hV : ∀ t ∈ s, DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t)
    (hW : ∀ t ∈ s, DifferentiableAt ℝ (sectionCoord (F := E) γ W (γ t)) t)
    (hV₀ : ∀ t ∈ s, alongCurve cov γ V t = 0)
    (hW₀ : ∀ t ∈ s, alongCurve cov γ W t = 0)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) (hinit : V a = W a) : V b = W b := by
  rcases eq_or_ne a b with rfl | hab
  · exact hinit
  have hs := hconn.uniqueDiffOn ha hb hab
  have hγcoord (t : ℝ) (ht : t ∈ s) : DifferentiableAt ℝ (extChartAt I (γ t) ∘ γ) t :=
    ((mdifferentiableAt_extChartAt (I := I) (mem_chart_source H (γ t))).comp t
      (hγ t ht)).differentiableAt
  have hrestrict (Y : ∀ r, TangentSpace I (γ r))
      (hY : ∀ t ∈ s, DifferentiableAt ℝ (sectionCoord (F := E) γ Y (γ t)) t)
      (hY₀ : ∀ t ∈ s, alongCurve cov γ Y t = 0) (t : ℝ) (ht : t ∈ s) :
      alongCurveWithin cov γ Y s t = 0 := by
    rw [alongCurveWithin_subset cov γ Y (Set.subset_univ s) (hs t ht)
      (hY t ht).differentiableWithinAt (hγcoord t ht).differentiableWithinAt,
      alongCurveWithin_univ, hY₀ t ht]
  exact hcov.eq_of_alongCurveWithin_eq_zero hconn
    (fun t ht ↦ (hγ t ht).mdifferentiableWithinAt)
    (fun t ht ↦ (hV t ht).differentiableWithinAt)
    (fun t ht ↦ (hW t ht).differentiableWithinAt)
    (hrestrict V hV hV₀) (hrestrict W hW hW₀) ha hb hinit

end Riemannian

end CovariantDerivative

end
