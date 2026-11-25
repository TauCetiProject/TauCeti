/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongMap.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Metric compatibility along a map

For a map `f : N → M` and a metric-compatible covariant derivative `∇` on `TM`, this file proves
the product rule for covariant differentiation of tangent fields along `f`
(`CovariantDerivative.alongMap`):

`v ⟪V, W⟫ = ⟪∇_v V, W⟫ + ⟪V, ∇_v W⟫` for `v ∈ T_x N`.

As for curves (`CovariantDerivative.hasDerivWithinAt_apply_alongCurveWithin`), the product rule is
first proved for an arbitrary pointwise continuous bilinear pairing `b` of tangent vectors which
pairs differentiable vector fields to differentiable functions and satisfies the ambient product
rule `v (b(Y, Z)) = b(∇_v Y, Z) + b(Y, ∇_v Z)` at `f x`. Fields pulled back from differentiable
vector fields satisfy it by the chain rule and `CovariantDerivative.alongMap_pullback`. A field
along `f` with differentiable coordinate reading is near `x` a finite combination of pullbacks of
smooth local-frame fields, with differentiable coefficients, and the additive and scalar Leibniz
laws of `CovariantDerivative.alongMap` finish the argument. The Riemannian product rule is the
specialization to the inner product, using Mathlib's ambient
`CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq`.

## Main results

* `CovariantDerivative.mvfderiv_apply_alongMap`: the product rule along a map for a pointwise
  bilinear pairing satisfying the ambient product rule, with
  `CovariantDerivative.mdifferentiableAt_apply_alongMap`.
* `CovariantDerivative.IsMetricCompatible.mvfderiv_inner_alongMap`: the metric product rule for
  two tangent fields along a differentiable map with differentiable coordinate readings, with
  `CovariantDerivative.IsMetricCompatible.mdifferentiableAt_inner_alongMap`.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 2, Proposition 3.2 (the case of curves).
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
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
  {f : N → M} {x : N}

section Pairing

section Linear

variable {b : (z : M) → TangentSpace I z →ₗ[ℝ] TangentSpace I z →ₗ[ℝ] ℝ}

/-- The product rule along `f` at `x` for a pointwise bilinear pairing `b`, packaged for the
local-frame induction: `b(V, W)` is differentiable at `x`, with derivative
`v ↦ b(∇_v V, W) + b(V, ∇_v W)`. -/
private def HasPairingProductRuleAt
    (cov : _root_.CovariantDerivative I E (fun x : M ↦ TangentSpace I x)) (f : N → M) (x : N)
    (b : (z : M) → TangentSpace I z →ₗ[ℝ] TangentSpace I z →ₗ[ℝ] ℝ)
    (V W : ∀ y, TangentSpace I (f y)) : Prop :=
  MDifferentiableAt J 𝓘(ℝ, ℝ) (fun y ↦ b (f y) (V y) (W y)) x ∧
    ∀ v : TangentSpace J x, mvfderiv J (fun y ↦ b (f y) (V y) (W y)) x v =
      b (f x) (cov.alongMap J f V x v) (W x) + b (f x) (V x) (cov.alongMap J f W x v)

/-- Exchanging the two fields of the product rule flips the pairing. -/
private lemma HasPairingProductRuleAt.flip {V W : ∀ y, TangentSpace I (f y)}
    (h : HasPairingProductRuleAt (J := J) cov f x b V W) :
    HasPairingProductRuleAt (J := J) cov f x (fun z ↦ (b z).flip) W V := by
  obtain ⟨hd, hD⟩ := h
  refine ⟨by simpa only [LinearMap.flip_apply] using hd, fun v ↦ ?_⟩
  simp only [LinearMap.flip_apply]
  rw [hD v, add_comm]

/-- The product rule for the flipped pairing gives the product rule with the fields exchanged. -/
private lemma HasPairingProductRuleAt.of_flip {V W : ∀ y, TangentSpace I (f y)}
    (h : HasPairingProductRuleAt (J := J) cov f x (fun z ↦ (b z).flip) W V) :
    HasPairingProductRuleAt (J := J) cov f x b V W := by
  simpa only [LinearMap.flip_flip] using h.flip

/-- The product rule is additive in its first field. -/
private lemma HasPairingProductRuleAt.add_left {V V' W : ∀ y, TangentSpace I (f y)}
    (hV : HasPairingProductRuleAt (J := J) cov f x b V W)
    (hV' : HasPairingProductRuleAt (J := J) cov f x b V' W)
    (hcV : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f V (f x)) x)
    (hcV' : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f V' (f x)) x) :
    HasPairingProductRuleAt (J := J) cov f x b (fun y ↦ V y + V' y) W := by
  obtain ⟨hd, hD⟩ := hV
  obtain ⟨hd', hD'⟩ := hV'
  have hfun : (fun y ↦ b (f y) (V y + V' y) (W y)) =
      (fun y ↦ b (f y) (V y) (W y)) + fun y ↦ b (f y) (V' y) (W y) := by
    ext y
    simp
  refine ⟨by rw [hfun]; exact hd.add hd', fun v ↦ ?_⟩
  rw [hfun, mvfderiv_add hd hd']
  simp only [FunLike.coe_add, Pi.add_apply]
  rw [hD v, hD' v, alongMap_fun_add cov f V V' hcV hcV']
  simp only [FunLike.coe_add, Pi.add_apply, map_add, LinearMap.add_apply]
  ring

/-- The product rule is preserved by multiplying its first field by a differentiable scalar. -/
private lemma HasPairingProductRuleAt.smul_left {V W : ∀ y, TangentSpace I (f y)} {g : N → ℝ}
    (hV : HasPairingProductRuleAt (J := J) cov f x b V W)
    (hg : MDifferentiableAt J 𝓘(ℝ, ℝ) g x)
    (hcV : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f V (f x)) x) :
    HasPairingProductRuleAt (J := J) cov f x b (fun y ↦ g y • V y) W := by
  obtain ⟨hd, hD⟩ := hV
  have hfun : (fun y ↦ b (f y) (g y • V y) (W y)) = g • fun y ↦ b (f y) (V y) (W y) := by
    ext y
    simp
  refine ⟨by rw [hfun]; exact hg.smul hd, fun v ↦ ?_⟩
  rw [hfun, mvfderiv_smul hg hd]
  simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [hD v, alongMap_fun_smul cov f V g hg hcV]
  simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply]
  ring

/-- The product rule is preserved by multiplying its second field by a differentiable scalar. -/
private lemma HasPairingProductRuleAt.smul_right {V W : ∀ y, TangentSpace I (f y)} {g : N → ℝ}
    (hW : HasPairingProductRuleAt (J := J) cov f x b V W)
    (hg : MDifferentiableAt J 𝓘(ℝ, ℝ) g x)
    (hcW : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f W (f x)) x) :
    HasPairingProductRuleAt (J := J) cov f x b V (fun y ↦ g y • W y) :=
  (hW.flip.smul_left hg hcW).of_flip

/-- The zero field satisfies the product rule. -/
private lemma hasPairingProductRuleAt_zero_left {W : ∀ y, TangentSpace I (f y)} :
    HasPairingProductRuleAt (J := J) cov f x b (fun _ ↦ 0) W := by
  refine ⟨by simpa using mdifferentiableAt_const, fun v ↦ ?_⟩
  simp only [map_zero, LinearMap.zero_apply, alongMap_fun_zero]
  rw [mvfderiv_const (0 : ℝ)]
  simp

/-- The product rule is preserved by a finite sum in its first field. -/
private lemma HasPairingProductRuleAt.finsetSum_left
    {ι : Type*} {A : Finset ι} {U : ι → ∀ y, TangentSpace I (f y)}
    {W : ∀ y, TangentSpace I (f y)}
    (hU : ∀ i ∈ A, HasPairingProductRuleAt (J := J) cov f x b (U i) W)
    (hcU : ∀ i ∈ A, MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f (U i) (f x)) x) :
    HasPairingProductRuleAt (J := J) cov f x b (fun y ↦ ∑ i ∈ A, U i y) W := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using hasPairingProductRuleAt_zero_left (J := J) (cov := cov) (b := b)
  | @insert a A ha ih =>
      have hA := ih (fun i hi ↦ hU i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hcU i (Finset.mem_insert_of_mem hi))
      have hsum := (hU a (Finset.mem_insert_self a A)).add_left hA
        (hcU a (Finset.mem_insert_self a A)) (by
          rw [sectionCoord_fun_sum]
          have := MDifferentiableAt.sum fun i hi ↦ hcU i (Finset.mem_insert_of_mem hi)
          rwa [Finset.sum_fn] at this)
      simpa only [Finset.sum_insert ha] using hsum

/-- The product rule is preserved by a finite sum in its second field. -/
private lemma HasPairingProductRuleAt.finsetSum_right
    {ι : Type*} {A : Finset ι} {V : ∀ y, TangentSpace I (f y)}
    {U : ι → ∀ y, TangentSpace I (f y)}
    (hU : ∀ i ∈ A, HasPairingProductRuleAt (J := J) cov f x b V (U i))
    (hcU : ∀ i ∈ A, MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f (U i) (f x)) x) :
    HasPairingProductRuleAt (J := J) cov f x b V (fun y ↦ ∑ i ∈ A, U i y) :=
  (HasPairingProductRuleAt.finsetSum_left (hU := fun i hi ↦ (hU i hi).flip) hcU).of_flip

/-- The product rule transfers along fields that agree near `x`. -/
private lemma HasPairingProductRuleAt.congr_of_eventuallyEq
    {V V' W W' : ∀ y, TangentSpace I (f y)}
    (h : HasPairingProductRuleAt (J := J) cov f x b V W)
    (hV : ∀ᶠ y in 𝓝 x, V y = V' y) (hW : ∀ᶠ y in 𝓝 x, W y = W' y) :
    HasPairingProductRuleAt (J := J) cov f x b V' W' := by
  obtain ⟨hd, hD⟩ := h
  have hpair : (fun y ↦ b (f y) (V' y) (W' y)) =ᶠ[𝓝 x] fun y ↦ b (f y) (V y) (W y) := by
    filter_upwards [hV, hW] with y hVy hWy
    rw [hVy, hWy]
  refine ⟨hd.congr_of_eventuallyEq hpair, fun v ↦ ?_⟩
  rw [hpair.mvfderiv_eq, hD v, alongMap_congr cov f V hV, alongMap_congr cov f W hW,
    hV.self_of_nhds, hW.self_of_nhds]

end Linear

variable {b : (z : M) → TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ}

/-- The product rule along `f` for fields pulled back from ambient differentiable vector
fields. -/
private theorem hasPairingProductRuleAt_pullback
    (hdiff : ∀ ⦃Y Z : Π z : M, TangentSpace I z⦄, MDiffAt (T% Y) (f x) →
      MDiffAt (T% Z) (f x) → MDiffAt (fun z ↦ b z (Y z) (Z z)) (f x))
    (hcompat : ∀ ⦃Y Z : Π z : M, TangentSpace I z⦄, MDiffAt (T% Y) (f x) →
      MDiffAt (T% Z) (f x) → ∀ v : TangentSpace I (f x),
        mvfderiv I (fun z ↦ b z (Y z) (Z z)) (f x) v =
          b (f x) (cov Y (f x) v) (Z (f x)) + b (f x) (Y (f x)) (cov Z (f x) v))
    (hf : MDifferentiableAt J I f x)
    {X Y : (z : M) → TangentSpace I z}
    (hX : MDiffAt (T% X) (f x)) (hY : MDiffAt (T% Y) (f x)) :
    HasPairingProductRuleAt (J := J) cov f x (fun z ↦ (b z).toLinearMap₁₂) (fun y ↦ X (f y))
      (fun y ↦ Y (f y)) := by
  refine ⟨(hdiff hX hY).comp x hf, fun v ↦ ?_⟩
  change mvfderiv J ((fun z ↦ b z (X z) (Y z)) ∘ f) x v = _
  rw [mvfderiv_comp_apply x (hdiff hX hY) hf v, hcompat hX hY, alongMap_pullback cov f hf hX,
    alongMap_pullback cov f hf hY]
  rfl

/-- The product rule along `f` at `x` for a pairing `b` satisfying the ambient product rule, for
two fields along `f` with differentiable coordinate readings. -/
private theorem hasPairingProductRuleAt
    (hdiff : ∀ ⦃Y Z : Π z : M, TangentSpace I z⦄, MDiffAt (T% Y) (f x) →
      MDiffAt (T% Z) (f x) → MDiffAt (fun z ↦ b z (Y z) (Z z)) (f x))
    (hcompat : ∀ ⦃Y Z : Π z : M, TangentSpace I z⦄, MDiffAt (T% Y) (f x) →
      MDiffAt (T% Z) (f x) → ∀ v : TangentSpace I (f x),
        mvfderiv I (fun z ↦ b z (Y z) (Z z)) (f x) v =
          b (f x) (cov Y (f x) v) (Z (f x)) + b (f x) (Y (f x)) (cov Z (f x) v))
    (hf : MDifferentiableAt J I f x) {V W : ∀ y, TangentSpace I (f y)}
    (hV : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f V (f x)) x)
    (hW : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f W (f x)) x) :
    HasPairingProductRuleAt (J := J) cov f x (fun z ↦ (b z).toLinearMap₁₂) V W := by
  -- Expand both fields in a smooth local frame around `f x`.
  let e := trivializationAt E (TangentSpace I) (f x)
  let β := Module.finBasis ℝ E
  have hbase : f x ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (f x)
  have hnear : ∀ᶠ y in 𝓝 x, f y ∈ e.baseSet :=
    hf.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hbase)
  have hframe (i : Fin (Module.finrank ℝ E)) : MDiffAt (T% (e.localFrame β i)) (f x) :=
    (((e.isLocalFrameOn_localFrame_baseSet I 1 β).contMDiffOn i).mdifferentiableOn
      one_ne_zero).mdifferentiableAt (e.open_baseSet.mem_nhds hbase)
  have hcX (i : Fin (Module.finrank ℝ E)) : MDifferentiableAt J 𝓘(ℝ, E)
      (sectionCoord ℝ (F := E) f (fun y ↦ e.localFrame β i (f y)) (f x)) x :=
    mdifferentiableAt_sectionCoord f (fun y ↦ e.localFrame β i (f y))
      ((hframe i).comp x hf) hbase
  have hcoeff (Q : ∀ y, TangentSpace I (f y))
      (hQ : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f Q (f x)) x) (i : Fin _) :
      MDifferentiableAt J 𝓘(ℝ, ℝ)
        (fun y ↦ β.coord i (sectionCoord ℝ (F := E) f Q (f x) y)) x :=
    (LinearMap.toContinuousLinearMap (β.coord i)).differentiableAt.comp_mdifferentiableAt hQ
  have hcTerm (Q : ∀ y, TangentSpace I (f y))
      (hQ : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f Q (f x)) x) (i : Fin _) :
      MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f
        (fun y ↦ β.coord i (sectionCoord ℝ (F := E) f Q (f x) y) • e.localFrame β i (f y))
        (f x)) x := by
    rw [sectionCoord_fun_smul]
    exact (hcoeff Q hQ i).smul (hcX i)
  have hterm (i j : Fin (Module.finrank ℝ E)) :
      HasPairingProductRuleAt (J := J) cov f x (fun z ↦ (b z).toLinearMap₁₂)
        (fun y ↦ β.coord i (sectionCoord ℝ (F := E) f V (f x) y) • e.localFrame β i (f y))
        (fun y ↦ β.coord j (sectionCoord ℝ (F := E) f W (f x) y) • e.localFrame β j (f y)) :=
    ((hasPairingProductRuleAt_pullback hdiff hcompat hf (hframe i) (hframe j)).smul_left
      (hcoeff V hV i) (hcX i)).smul_right (hcoeff W hW j) (hcX j)
  have hsum := HasPairingProductRuleAt.finsetSum_left (A := Finset.univ)
    (fun i _ ↦ HasPairingProductRuleAt.finsetSum_right (A := Finset.univ)
      (fun j _ ↦ hterm i j) fun j _ ↦ hcTerm W hW j) fun i _ ↦ hcTerm V hV i
  have hexp (Q : ∀ y, TangentSpace I (f y)) (y : N) (hy : f y ∈ e.baseSet) :
      ∑ i, β.coord i (sectionCoord ℝ (F := E) f Q (f x) y) • e.localFrame β i (f y) = Q y := by
    simp only [β.coord_apply, sectionCoord_apply]
    exact (β.eq_sum_repr_continuousLinearMapAt_smul_localFrame hy (Q y)).symm
  refine hsum.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hnear] with y hy using hexp V y hy
  · filter_upwards [hnear] with y hy using hexp W y hy

/-- **The product rule along a map**, differentiability part: for a pointwise bilinear pairing `b`
that pairs vector fields differentiable at `f x` to a function differentiable at `f x`, and for a
map `f` differentiable at `x`, `b(V, W)` is differentiable at `x` for any two fields `V`, `W` along
`f` whose coordinate readings are differentiable at `x`. -/
theorem mdifferentiableAt_apply_alongMap
    (hdiff : ∀ ⦃Y Z : Π z : M, TangentSpace I z⦄, MDiffAt (T% Y) (f x) →
      MDiffAt (T% Z) (f x) → MDiffAt (fun z ↦ b z (Y z) (Z z)) (f x))
    (hcompat : ∀ ⦃Y Z : Π z : M, TangentSpace I z⦄, MDiffAt (T% Y) (f x) →
      MDiffAt (T% Z) (f x) → ∀ v : TangentSpace I (f x),
        mvfderiv I (fun z ↦ b z (Y z) (Z z)) (f x) v =
          b (f x) (cov Y (f x) v) (Z (f x)) + b (f x) (Y (f x)) (cov Z (f x) v))
    (hf : MDifferentiableAt J I f x) {V W : ∀ y, TangentSpace I (f y)}
    (hV : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f V (f x)) x)
    (hW : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f W (f x)) x) :
    MDifferentiableAt J 𝓘(ℝ, ℝ) (fun y ↦ b (f y) (V y) (W y)) x :=
  (hasPairingProductRuleAt hdiff hcompat hf hV hW).1

/-- **The product rule along a map.** Let `b` be a pointwise bilinear pairing of tangent vectors
that pairs vector fields differentiable at `f x` to a function differentiable at `f x`, such that
the covariant derivative satisfies the ambient product rule
`v (b(Y, Z)) = b(∇_v Y, Z) + b(Y, ∇_v Z)` there. Then for a map `f` differentiable at `x` and two
fields `V`, `W` along `f` whose coordinate readings are differentiable at `x`,
`v (b(V, W)) = b(∇_v V, W) + b(V, ∇_v W)` for every `v ∈ T_x N`, with `∇_v` covariant
differentiation along `f`. Neither symmetry nor nondegeneracy of `b` is needed. -/
theorem mvfderiv_apply_alongMap
    (hdiff : ∀ ⦃Y Z : Π z : M, TangentSpace I z⦄, MDiffAt (T% Y) (f x) →
      MDiffAt (T% Z) (f x) → MDiffAt (fun z ↦ b z (Y z) (Z z)) (f x))
    (hcompat : ∀ ⦃Y Z : Π z : M, TangentSpace I z⦄, MDiffAt (T% Y) (f x) →
      MDiffAt (T% Z) (f x) → ∀ v : TangentSpace I (f x),
        mvfderiv I (fun z ↦ b z (Y z) (Z z)) (f x) v =
          b (f x) (cov Y (f x) v) (Z (f x)) + b (f x) (Y (f x)) (cov Z (f x) v))
    (hf : MDifferentiableAt J I f x) {V W : ∀ y, TangentSpace I (f y)}
    (hV : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f V (f x)) x)
    (hW : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f W (f x)) x)
    (v : TangentSpace J x) :
    mvfderiv J (fun y ↦ b (f y) (V y) (W y)) x v =
      b (f x) (cov.alongMap J f V x v) (W x) + b (f x) (V x) (cov.alongMap J f W x v) :=
  (hasPairingProductRuleAt hdiff hcompat hf hV hW).2 v

end Pairing


section Riemannian

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

omit [FiniteDimensional ℝ E] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- Inner products of vector fields differentiable at a point are differentiable there. -/
private theorem mdifferentiableAt_innerSL {z : M} {Y Z : Π z : M, TangentSpace I z}
    (hY : MDiffAt (T% Y) z) (hZ : MDiffAt (T% Z) z) :
    MDiffAt (fun y ↦ innerSL ℝ (Y y) (Z y)) z := by
  simp only [innerSL_apply_apply]
  exact MDifferentiableAt.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x)
    (b := id) hY hZ

/-- The ambient product rule for `innerSL` supplied by metric compatibility. -/
private theorem IsMetricCompatible.mvfderiv_innerSL
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {z : M} {Y Z : Π z : M, TangentSpace I z}
    (hY : MDiffAt (T% Y) z) (hZ : MDiffAt (T% Z) z) (v : TangentSpace I z) :
    mvfderiv I (fun y ↦ innerSL ℝ (Y y) (Z y)) z v =
      innerSL ℝ (cov Y z v) (Z z) + innerSL ℝ (Y z) (cov Z z v) := by
  simp only [innerSL_apply_apply]
  simpa only [FiberBundle.extend_apply_self] using
    hcov.mvfderiv_inner_eq (FiberBundle.extend E v) hY hZ

/-- For a metric-compatible covariant derivative, the inner product of two tangent fields along a
map `f` differentiable at `x`, with coordinate readings differentiable at `x`, is differentiable
at `x`. -/
theorem IsMetricCompatible.mdifferentiableAt_inner_alongMap
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (hf : MDifferentiableAt J I f x) {V W : ∀ y, TangentSpace I (f y)}
    (hV : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f V (f x)) x)
    (hW : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f W (f x)) x) :
    MDifferentiableAt J 𝓘(ℝ, ℝ) (fun y ↦ inner ℝ (V y) (W y)) x :=
  mdifferentiableAt_apply_alongMap (cov := cov) (b := fun _ ↦ innerSL ℝ)
    (fun _ _ hY hZ ↦ mdifferentiableAt_innerSL hY hZ)
    (fun _ _ hY hZ v ↦ hcov.mvfderiv_innerSL hY hZ v) hf hV hW

/-- **Metric compatibility along a map.** For a metric-compatible covariant derivative `∇` on
`TM`, a map `f` differentiable at `x`, and two tangent fields `V`, `W` along `f` whose coordinate
readings are differentiable at `x`, `v ⟪V, W⟫ = ⟪∇_v V, W⟫ + ⟪V, ∇_v W⟫` for every `v ∈ T_x N`,
with `∇_v` covariant differentiation along `f`. -/
theorem IsMetricCompatible.mvfderiv_inner_alongMap
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (hf : MDifferentiableAt J I f x) {V W : ∀ y, TangentSpace I (f y)}
    (hV : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f V (f x)) x)
    (hW : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f W (f x)) x)
    (v : TangentSpace J x) :
    mvfderiv J (fun y ↦ inner ℝ (V y) (W y)) x v =
      inner ℝ (cov.alongMap J f V x v) (W x) + inner ℝ (V x) (cov.alongMap J f W x v) :=
  mvfderiv_apply_alongMap (cov := cov) (b := fun _ ↦ innerSL ℝ)
    (fun _ _ hY hZ ↦ mdifferentiableAt_innerSL hY hZ)
    (fun _ _ hY hZ v ↦ hcov.mvfderiv_innerSL hY hZ v) hf hV hW v

end Riemannian

end CovariantDerivative
