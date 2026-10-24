/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Pullback
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

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

omit [FiniteDimensional ℝ E] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- A finite sum of fields with differentiable coordinate readings again has a differentiable
coordinate reading. -/
private lemma differentiableWithinAt_sectionCoord_finsetSum
    {ι : Type*} {A : Finset ι} {U : ι → ∀ r, TangentSpace I (γ r)}
    (hU : ∀ i ∈ A,
      DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (U i) (γ t)) s t) :
    DifferentiableWithinAt ℝ
      (sectionCoord (F := E) γ (fun r ↦ ∑ i ∈ A, U i r) (γ t)) s t := by
  rw [sectionCoord_sum]
  exact DifferentiableWithinAt.fun_sum hU

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
        (differentiableWithinAt_sectionCoord_finsetSum
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
    (hu : UniqueDiffWithinAt ℝ s t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t) :
    HasDerivWithinAt (fun r ↦ b (γ r) (V r) (W r))
      (b (γ t) (alongCurveWithin cov γ V s t) (W t) +
        b (γ t) (V t) (alongCurveWithin cov γ W s t)) s t := by
  classical
  -- Choose a smooth local frame around the point of the curve.
  let e := trivializationAt E (TangentSpace I) (γ t)
  let β := Module.finBasis ℝ E
  let X : Fin (Module.finrank ℝ E) → (x : M) → TangentSpace I x :=
    fun i ↦ e.localFrame β i
  let aV : Fin (Module.finrank ℝ E) → ℝ → ℝ := fun i r ↦
    β.coord i (sectionCoord (F := E) γ V (γ t) r)
  let aW : Fin (Module.finrank ℝ E) → ℝ → ℝ := fun i r ↦
    β.coord i (sectionCoord (F := E) γ W (γ t) r)
  let U : Fin (Module.finrank ℝ E) → ∀ r, TangentSpace I (γ r) :=
    fun i r ↦ aV i r • X i (γ r)
  let Z : Fin (Module.finrank ℝ E) → ∀ r, TangentSpace I (γ r) :=
    fun i r ↦ aW i r • X i (γ r)
  have hbase : γ t ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  have hframe (i : Fin (Module.finrank ℝ E)) : MDiffAt (T% (X i)) (γ t) := by
    exact (((e.isLocalFrameOn_localFrame_baseSet I 1 β).contMDiffOn i).mdifferentiableOn
      one_ne_zero).mdifferentiableAt (e.open_baseSet.mem_nhds hbase)
  -- Coordinate coefficients and pulled-back frame fields are differentiable within the set.
  have haV (i : Fin (Module.finrank ℝ E)) : DifferentiableWithinAt ℝ (aV i) s t := by
    exact (LinearMap.toContinuousLinearMap (β.coord i)).differentiableAt
      |>.comp_differentiableWithinAt t hV
  have haW (i : Fin (Module.finrank ℝ E)) : DifferentiableWithinAt ℝ (aW i) s t := by
    exact (LinearMap.toContinuousLinearMap (β.coord i)).differentiableAt
      |>.comp_differentiableWithinAt t hW
  have hcoordX (i : Fin (Module.finrank ℝ E)) :
      DifferentiableWithinAt ℝ
        (sectionCoord (F := E) γ (fun r ↦ X i (γ r)) (γ t)) s t := by
    exact differentiableWithinAt_sectionCoord γ (fun r ↦ X i (γ r))
      ((hframe i).comp_mdifferentiableWithinAt t hγ) hbase
  have hcoordTerm (a : Fin (Module.finrank ℝ E) → ℝ → ℝ)
      (ha : ∀ i, DifferentiableWithinAt ℝ (a i) s t)
      (i : Fin (Module.finrank ℝ E)) :
      DifferentiableWithinAt ℝ
        (sectionCoord (F := E) γ (fun r ↦ a i r • X i (γ r)) (γ t)) s t := by
    rw [sectionCoord_smul]
    exact (ha i).smul (hcoordX i)
  have hcoordU (i : Fin (Module.finrank ℝ E)) :
      DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (U i) (γ t)) s t :=
    hcoordTerm aV haV i
  have hcoordZ (i : Fin (Module.finrank ℝ E)) :
      DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (Z i) (γ t)) s t :=
    hcoordTerm aW haW i
  -- Apply metric compatibility termwise, then sum both frame expansions.
  have hterm (i j : Fin (Module.finrank ℝ E)) :
      HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t)
        (fun x ↦ (b x).toLinearMap₁₂) (U i) (Z j) :=
    ((hasPairingProductRuleWithinAt_pullback hdiff hcompat hu hγ (hframe i)
      (hframe j)).smul_left (haV i) (hcoordX i)).smul_right (haW j) (hcoordX j)
  have hsum : HasPairingProductRuleWithinAt (cov := cov) (s := s) (t := t)
      (fun x ↦ (b x).toLinearMap₁₂) (fun r ↦ ∑ i, U i r) (fun r ↦ ∑ j, Z j r) := by
    refine HasPairingProductRuleWithinAt.finsetSum_left
      (A := Finset.univ) (U := U) (W := fun r ↦ ∑ j, Z j r) ?_ ?_
    · intro i _
      exact HasPairingProductRuleWithinAt.finsetSum_right
        (A := Finset.univ) (hU := fun j _ ↦ hterm i j) (fun j _ ↦ hcoordZ j)
    · exact fun i _ ↦ hcoordU i
  dsimp only [HasPairingProductRuleWithinAt] at hsum
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply] at hsum
  -- The chosen frame expansion agrees with each original field near `t` and at `t` itself.
  have hnear : ∀ᶠ r in 𝓝[s] t, γ r ∈ e.baseSet :=
    hγ.continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hbase)
  have frameExpansion (Q : ∀ r, TangentSpace I (γ r)) :
      Q =ᶠ[𝓝[s] t] fun r ↦ ∑ i,
        β.repr (sectionCoord (F := E) γ Q (γ t) r) i • X i (γ r) := by
    filter_upwards [hnear] with r hr
    calc
      Q r = e.symmL ℝ (γ r) (sectionCoord (F := E) γ Q (γ t) r) := by
        rw [sectionCoord_apply, e.symmL_continuousLinearMapAt (R := ℝ) hr]
      _ = e.symmL ℝ (γ r)
          (∑ i, β.repr (sectionCoord (F := E) γ Q (γ t) r) i • β i) := by
        rw [β.sum_repr]
      _ = ∑ i, β.repr (sectionCoord (F := E) γ Q (γ t) r) i • X i (γ r) := by
        simp only [map_sum, map_smul, X, symmL_basis_eq_localFrame β hr]
  have frameExpansionAt (Q : ∀ r, TangentSpace I (γ r)) :
      Q t = ∑ i, β.repr (sectionCoord (F := E) γ Q (γ t) t) i • X i (γ t) := by
    calc
      Q t = e.symmL ℝ (γ t) (sectionCoord (F := E) γ Q (γ t) t) := by
        rw [sectionCoord_apply, e.symmL_continuousLinearMapAt (R := ℝ) hbase]
      _ = e.symmL ℝ (γ t)
          (∑ i, β.repr (sectionCoord (F := E) γ Q (γ t) t) i • β i) := by
        rw [β.sum_repr]
      _ = ∑ i, β.repr (sectionCoord (F := E) γ Q (γ t) t) i • X i (γ t) := by
        simp only [map_sum, map_smul, X, symmL_basis_eq_localFrame β hbase]
  have hVsum : V =ᶠ[𝓝[s] t] fun r ↦ ∑ i, U i r := by
    simpa only [U, aV, β.coord_apply] using frameExpansion V
  have hWsum : W =ᶠ[𝓝[s] t] fun r ↦ ∑ i, Z i r := by
    simpa only [Z, aW, β.coord_apply] using frameExpansion W
  have hVt : V t = ∑ i, U i t := by
    simpa only [U, aV, β.coord_apply] using frameExpansionAt V
  have hWt : W t = ∑ i, Z i t := by
    simpa only [Z, aW, β.coord_apply] using frameExpansionAt W
  have hpair : (fun r ↦ b (γ r) (V r) (W r)) =ᶠ[𝓝[s] t]
      fun r ↦ b (γ r) (∑ i, U i r) (∑ j, Z j r) := by
    filter_upwards [hVsum, hWsum] with r hVr hWr
    rw [hVr, hWr]
    rfl
  have hDV : alongCurveWithin cov γ V s t =
      alongCurveWithin cov γ (fun r ↦ ∑ i, U i r) s t :=
    alongCurveWithin_congr cov γ V hVsum hVt
  have hDW : alongCurveWithin cov γ W s t =
      alongCurveWithin cov γ (fun r ↦ ∑ i, Z i r) s t :=
    alongCurveWithin_congr cov γ W hWsum hWt
  have hpairAt : b (γ t) (V t) (W t) = b (γ t) (∑ i, U i t) (∑ j, Z j t) := by
    rw [hVt, hWt]
  refine (hsum.congr_of_eventuallyEq hpair hpairAt).congr_deriv ?_
  rw [hDV, hDW, hVt, hWt]

end Pairing

section Riemannian

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

/-- The within-set product rule for a metric-compatible covariant derivative acting on two
differentiable tangent fields along a differentiable real curve. -/
theorem IsMetricCompatible.hasDerivWithinAt_inner_alongCurveWithin
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hu : UniqueDiffWithinAt ℝ s t)
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
  exact hasDerivWithinAt_apply_alongCurveWithin hdiff hcompat hu hγ hV hW

/-- The fibrewise inner product of two differentiable tangent fields along a differentiable curve
is differentiable within the parameter set. -/
theorem IsMetricCompatible.differentiableWithinAt_inner
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hu : UniqueDiffWithinAt ℝ s t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t) :
    DifferentiableWithinAt ℝ (fun r ↦ inner ℝ (V r) (W r)) s t :=
  (hcov.hasDerivWithinAt_inner_alongCurveWithin hu hγ hV hW).differentiableWithinAt

/-- The derivative identity supplied by metric compatibility within a parameter set. -/
theorem IsMetricCompatible.derivWithin_inner_alongCurveWithin
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hu : UniqueDiffWithinAt ℝ s t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t) :
    derivWithin (fun r ↦ inner ℝ (V r) (W r)) s t =
      inner ℝ (alongCurveWithin cov γ V s t) (W t) +
        inner ℝ (V t) (alongCurveWithin cov γ W s t) :=
  (hcov.hasDerivWithinAt_inner_alongCurveWithin hu hγ hV hW).derivWithin hu

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
    hcov.hasDerivWithinAt_inner_alongCurveWithin uniqueDiffWithinAt_univ
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

end Riemannian

end CovariantDerivative

end
