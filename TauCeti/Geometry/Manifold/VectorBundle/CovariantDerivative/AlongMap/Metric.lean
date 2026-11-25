/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongMap.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

/-!
# Metric compatibility along a map

For a map `f : N → M` and a metric-compatible covariant derivative `∇` on a Riemannian vector
bundle `B → M`, this file proves the product rule for covariant differentiation of sections of `B`
along `f` (`CovariantDerivative.alongMap`):

`v ⟪V, W⟫ = ⟪∇_v V, W⟫ + ⟪V, ∇_v W⟫` for `v ∈ T_x N`.

As for curves (`CovariantDerivative.hasDerivWithinAt_apply_alongCurveWithin`), the product rule is
first proved for an arbitrary pointwise continuous bilinear pairing `b` of fibre vectors of `B`
which pairs differentiable sections to differentiable functions and satisfies the ambient product
rule `v (b(Y, Z)) = b(∇_v Y, Z) + b(Y, ∇_v Z)` at `f x`. Fields pulled back from differentiable
sections satisfy it by the chain rule and `CovariantDerivative.alongMap_pullback`. A field
along `f` with differentiable coordinate reading is near `x` a finite combination of pullbacks of
smooth local-frame sections, with differentiable coefficients, and the additive and scalar Leibniz
laws of `CovariantDerivative.alongMap` finish the argument. The Riemannian product rule is the
specialization to the inner product, using Mathlib's ambient product rule
`CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq` at a constant direction field.
Differentiability of the pairing needs no covariant derivative and is proved in
`SectionAlongMap/Pairing.lean`. The tangent bundle case is `B := TangentSpace I`.

## Main results

* `CovariantDerivative.mvfderiv_apply_alongMap`: the product rule along a map for a pointwise
  bilinear pairing satisfying the ambient product rule.
* `CovariantDerivative.IsMetricCompatible.mvfderiv_inner_alongMap`: the metric product rule for
  two sections of a Riemannian bundle along a differentiable map with differentiable coordinate
  readings.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 2, Proposition 3.2 (the case of curves).
* The proof organization is adapted, via `AlongCurve/Metric.lean`, from
  `DoCarmoLib/Riemannian/Connection/MetricCompatibilityAlong.lean` in the Apache-2.0
  [`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture)
  repository, revision `24f32e4d600878bfaac6bc2f2f9324175571c321`.
-/

public section

open Bundle Filter Function
open scoped Manifold Topology

noncomputable section

namespace CovariantDerivative

open TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀] [FiniteDimensional ℝ F₀]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
  {f : N → M} {x : N}

section Pairing

variable {B : M → Type*} [TopologicalSpace (TotalSpace F₀ B)]
  [∀ x, AddCommGroup (B x)] [∀ x, Module ℝ (B x)] [∀ x, TopologicalSpace (B x)]
  [∀ x, IsTopologicalAddGroup (B x)] [∀ x, ContinuousSMul ℝ (B x)]
  [FiberBundle F₀ B] [VectorBundle ℝ F₀ B] [ContMDiffVectorBundle 1 F₀ B I]
  {cov : _root_.CovariantDerivative I F₀ B}

section Linear

variable {b : (z : M) → B z →ₗ[ℝ] B z →ₗ[ℝ] ℝ}

/-- The product rule along `f` at `x` for a pointwise bilinear pairing `b`, packaged for the
local-frame induction: `b(V, W)` is differentiable at `x`, with derivative
`v ↦ b(∇_v V, W) + b(V, ∇_v W)`. -/
private def HasPairingProductRuleAt
    (cov : _root_.CovariantDerivative I F₀ B) (f : N → M) (x : N)
    (b : (z : M) → B z →ₗ[ℝ] B z →ₗ[ℝ] ℝ)
    (V W : ∀ y, B (f y)) : Prop :=
  MDifferentiableAt J 𝓘(ℝ, ℝ) (fun y ↦ b (f y) (V y) (W y)) x ∧
    ∀ v : TangentSpace J x, mvfderiv J (fun y ↦ b (f y) (V y) (W y)) x v =
      b (f x) (cov.alongMap J f V x v) (W x) + b (f x) (V x) (cov.alongMap J f W x v)

/-- Exchanging the two fields of the product rule flips the pairing. -/
private lemma HasPairingProductRuleAt.flip {V W : ∀ y, B (f y)}
    (h : HasPairingProductRuleAt (J := J) cov f x b V W) :
    HasPairingProductRuleAt (J := J) cov f x (fun z ↦ (b z).flip) W V := by
  obtain ⟨hd, hD⟩ := h
  refine ⟨by simpa only [LinearMap.flip_apply] using hd, fun v ↦ ?_⟩
  simp only [LinearMap.flip_apply]
  rw [hD v, add_comm]

/-- The product rule for the flipped pairing gives the product rule with the fields exchanged. -/
private lemma HasPairingProductRuleAt.of_flip {V W : ∀ y, B (f y)}
    (h : HasPairingProductRuleAt (J := J) cov f x (fun z ↦ (b z).flip) W V) :
    HasPairingProductRuleAt (J := J) cov f x b V W := by
  simpa only [LinearMap.flip_flip] using h.flip

/-- The product rule is additive in its first field. -/
private lemma HasPairingProductRuleAt.add_left {V V' W : ∀ y, B (f y)}
    (hV : HasPairingProductRuleAt (J := J) cov f x b V W)
    (hV' : HasPairingProductRuleAt (J := J) cov f x b V' W)
    (hcV : MDifferentiableAt J 𝓘(ℝ, F₀) (sectionCoord ℝ (F := F₀) f V (f x)) x)
    (hcV' : MDifferentiableAt J 𝓘(ℝ, F₀) (sectionCoord ℝ (F := F₀) f V' (f x)) x) :
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
private lemma HasPairingProductRuleAt.smul_left {V W : ∀ y, B (f y)} {g : N → ℝ}
    (hV : HasPairingProductRuleAt (J := J) cov f x b V W)
    (hg : MDifferentiableAt J 𝓘(ℝ, ℝ) g x)
    (hcV : MDifferentiableAt J 𝓘(ℝ, F₀) (sectionCoord ℝ (F := F₀) f V (f x)) x) :
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
private lemma HasPairingProductRuleAt.smul_right {V W : ∀ y, B (f y)} {g : N → ℝ}
    (hW : HasPairingProductRuleAt (J := J) cov f x b V W)
    (hg : MDifferentiableAt J 𝓘(ℝ, ℝ) g x)
    (hcW : MDifferentiableAt J 𝓘(ℝ, F₀) (sectionCoord ℝ (F := F₀) f W (f x)) x) :
    HasPairingProductRuleAt (J := J) cov f x b V (fun y ↦ g y • W y) :=
  (hW.flip.smul_left hg hcW).of_flip

/-- The zero field satisfies the product rule. -/
private lemma hasPairingProductRuleAt_zero_left {W : ∀ y, B (f y)} :
    HasPairingProductRuleAt (J := J) cov f x b (fun _ ↦ 0) W := by
  refine ⟨by simpa using mdifferentiableAt_const, fun v ↦ ?_⟩
  simp only [map_zero, LinearMap.zero_apply, alongMap_fun_zero]
  rw [mvfderiv_const (0 : ℝ)]
  simp

/-- The product rule is preserved by a finite sum in its first field. -/
private lemma HasPairingProductRuleAt.finsetSum_left
    {ι : Type*} {A : Finset ι} {U : ι → ∀ y, B (f y)}
    {W : ∀ y, B (f y)}
    (hU : ∀ i ∈ A, HasPairingProductRuleAt (J := J) cov f x b (U i) W)
    (hcU : ∀ i ∈ A, MDifferentiableAt J 𝓘(ℝ, F₀) (sectionCoord ℝ (F := F₀) f (U i) (f x)) x) :
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
    {ι : Type*} {A : Finset ι} {V : ∀ y, B (f y)}
    {U : ι → ∀ y, B (f y)}
    (hU : ∀ i ∈ A, HasPairingProductRuleAt (J := J) cov f x b V (U i))
    (hcU : ∀ i ∈ A, MDifferentiableAt J 𝓘(ℝ, F₀) (sectionCoord ℝ (F := F₀) f (U i) (f x)) x) :
    HasPairingProductRuleAt (J := J) cov f x b V (fun y ↦ ∑ i ∈ A, U i y) :=
  (HasPairingProductRuleAt.finsetSum_left (hU := fun i hi ↦ (hU i hi).flip) hcU).of_flip

/-- The product rule transfers along fields that agree near `x`. -/
private lemma HasPairingProductRuleAt.congr_of_eventuallyEq
    {V V' W W' : ∀ y, B (f y)}
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

variable {b : (z : M) → B z →L[ℝ] B z →L[ℝ] ℝ}

/-- The product rule along `f` for fields pulled back from ambient differentiable vector
fields. -/
private theorem hasPairingProductRuleAt_pullback
    (hdiff : ∀ ⦃Y Z : Π z : M, B z⦄, MDiffAt (T% Y) (f x) →
      MDiffAt (T% Z) (f x) → MDiffAt (fun z ↦ b z (Y z) (Z z)) (f x))
    (hcompat : ∀ ⦃Y Z : Π z : M, B z⦄, MDiffAt (T% Y) (f x) →
      MDiffAt (T% Z) (f x) → ∀ v : TangentSpace I (f x),
        mvfderiv I (fun z ↦ b z (Y z) (Z z)) (f x) v =
          b (f x) (cov Y (f x) v) (Z (f x)) + b (f x) (Y (f x)) (cov Z (f x) v))
    (hf : MDifferentiableAt J I f x)
    {X Y : (z : M) → B z}
    (hX : MDiffAt (T% X) (f x)) (hY : MDiffAt (T% Y) (f x)) :
    HasPairingProductRuleAt (J := J) cov f x (fun z ↦ (b z).toLinearMap₁₂) (fun y ↦ X (f y))
      (fun y ↦ Y (f y)) := by
  refine ⟨(hdiff hX hY).comp x hf, fun v ↦ ?_⟩
  have hcomp := mvfderiv_comp_apply x (hdiff hX hY) hf v
  simp only [Function.comp_def] at hcomp
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]
  rw [hcomp, hcompat hX hY, alongMap_pullback cov f hf hX, alongMap_pullback cov f hf hY]
  simp only [ContinuousLinearMap.comp_apply]

/-- The product rule along `f` at `x` for a pairing `b` satisfying the ambient product rule, for
two fields along `f` with differentiable coordinate readings. -/
private theorem hasPairingProductRuleAt
    (hdiff : ∀ ⦃Y Z : Π z : M, B z⦄, MDiffAt (T% Y) (f x) →
      MDiffAt (T% Z) (f x) → MDiffAt (fun z ↦ b z (Y z) (Z z)) (f x))
    (hcompat : ∀ ⦃Y Z : Π z : M, B z⦄, MDiffAt (T% Y) (f x) →
      MDiffAt (T% Z) (f x) → ∀ v : TangentSpace I (f x),
        mvfderiv I (fun z ↦ b z (Y z) (Z z)) (f x) v =
          b (f x) (cov Y (f x) v) (Z (f x)) + b (f x) (Y (f x)) (cov Z (f x) v))
    (hf : MDifferentiableAt J I f x) {V W : ∀ y, B (f y)}
    (hV : MDifferentiableAt J 𝓘(ℝ, F₀) (sectionCoord ℝ (F := F₀) f V (f x)) x)
    (hW : MDifferentiableAt J 𝓘(ℝ, F₀) (sectionCoord ℝ (F := F₀) f W (f x)) x) :
    HasPairingProductRuleAt (J := J) cov f x (fun z ↦ (b z).toLinearMap₁₂) V W := by
  -- Expand both fields in a smooth local frame around `f x`.
  let e := trivializationAt F₀ B (f x)
  let β := Module.finBasis ℝ F₀
  have hframe (i : Fin (Module.finrank ℝ F₀)) : MDiffAt (T% (e.localFrame β i)) (f x) :=
    (contMDiffAt_localFrame_of_mem 1 _ β i
      (FiberBundle.mem_baseSet_trivializationAt F₀ B (f x))).mdifferentiableAt one_ne_zero
  have hcX (i : Fin (Module.finrank ℝ F₀)) : MDifferentiableAt J 𝓘(ℝ, F₀)
      (sectionCoord ℝ (F := F₀) f (fun y ↦ e.localFrame β i (f y)) (f x)) x :=
    mdifferentiableAt_sectionCoord f (fun y ↦ e.localFrame β i (f y)) ((hframe i).comp x hf)
      (FiberBundle.mem_baseSet_trivializationAt F₀ B (f x))
  have hcTerm (Q : ∀ y, B (f y))
      (hQ : MDifferentiableAt J 𝓘(ℝ, F₀) (sectionCoord ℝ (F := F₀) f Q (f x)) x) (i : Fin _) :
      MDifferentiableAt J 𝓘(ℝ, F₀) (sectionCoord ℝ (F := F₀) f
        (fun y ↦ β.coord i (sectionCoord ℝ (F := F₀) f Q (f x) y) • e.localFrame β i (f y))
        (f x)) x := by
    rw [sectionCoord_fun_smul]
    exact (mdifferentiableAt_repr_sectionCoord f Q β hQ i).smul (hcX i)
  have hterm (i j : Fin (Module.finrank ℝ F₀)) :
      HasPairingProductRuleAt (J := J) cov f x (fun z ↦ (b z).toLinearMap₁₂)
        (fun y ↦ β.coord i (sectionCoord ℝ (F := F₀) f V (f x) y) • e.localFrame β i (f y))
        (fun y ↦ β.coord j (sectionCoord ℝ (F := F₀) f W (f x) y) • e.localFrame β j (f y)) :=
    ((hasPairingProductRuleAt_pullback hdiff hcompat hf (hframe i) (hframe j)).smul_left
      (mdifferentiableAt_repr_sectionCoord f V β hV i) (hcX i)).smul_right
      (mdifferentiableAt_repr_sectionCoord f W β hW j) (hcX j)
  have hsum := HasPairingProductRuleAt.finsetSum_left (A := Finset.univ)
    (fun i _ ↦ HasPairingProductRuleAt.finsetSum_right (A := Finset.univ)
      (fun j _ ↦ hterm i j) fun j _ ↦ hcTerm W hW j) fun i _ ↦ hcTerm V hV i
  have hexp (Q : ∀ y, B (f y)) : ∀ᶠ y in 𝓝 x,
      ∑ i, β.coord i (sectionCoord ℝ (F := F₀) f Q (f x) y) • e.localFrame β i (f y) = Q y :=
    (eventually_eq_sum_repr_sectionCoord_smul_localFrame f Q β hf.continuousAt
      (FiberBundle.mem_baseSet_trivializationAt F₀ B (f x))).mono fun _ hy ↦ by
        simp only [Module.Basis.coord_apply]
        exact hy.symm
  exact hsum.congr_of_eventuallyEq (hexp V) (hexp W)

/-- **The product rule along a map.** Let `b` be a pointwise bilinear pairing of fibre vectors
of `B` that pairs sections differentiable at `f x` to a function differentiable at `f x`, such that
the covariant derivative satisfies the ambient product rule
`v (b(Y, Z)) = b(∇_v Y, Z) + b(Y, ∇_v Z)` there. Then for a map `f` differentiable at `x` and two
fields `V`, `W` along `f` whose coordinate readings are differentiable at `x`,
`v (b(V, W)) = b(∇_v V, W) + b(V, ∇_v W)` for every `v ∈ T_x N`, with `∇_v` covariant
differentiation along `f`. Neither symmetry nor nondegeneracy of `b` is needed. -/
theorem mvfderiv_apply_alongMap
    (hdiff : ∀ ⦃Y Z : Π z : M, B z⦄, MDiffAt (T% Y) (f x) →
      MDiffAt (T% Z) (f x) → MDiffAt (fun z ↦ b z (Y z) (Z z)) (f x))
    (hcompat : ∀ ⦃Y Z : Π z : M, B z⦄, MDiffAt (T% Y) (f x) →
      MDiffAt (T% Z) (f x) → ∀ v : TangentSpace I (f x),
        mvfderiv I (fun z ↦ b z (Y z) (Z z)) (f x) v =
          b (f x) (cov Y (f x) v) (Z (f x)) + b (f x) (Y (f x)) (cov Z (f x) v))
    (hf : MDifferentiableAt J I f x) {V W : ∀ y, B (f y)}
    (hV : MDifferentiableAt J 𝓘(ℝ, F₀) (sectionCoord ℝ (F := F₀) f V (f x)) x)
    (hW : MDifferentiableAt J 𝓘(ℝ, F₀) (sectionCoord ℝ (F := F₀) f W (f x)) x)
    (v : TangentSpace J x) :
    mvfderiv J (fun y ↦ b (f y) (V y) (W y)) x v =
      b (f x) (cov.alongMap J f V x v) (W x) + b (f x) (V x) (cov.alongMap J f W x v) :=
  (hasPairingProductRuleAt hdiff hcompat hf hV hW).2 v

end Pairing

section Riemannian

variable {B : M → Type*} [TopologicalSpace (TotalSpace F₀ B)]
  [∀ x, NormedAddCommGroup (B x)] [∀ x, InnerProductSpace ℝ (B x)]
  [FiberBundle F₀ B] [VectorBundle ℝ F₀ B] [ContMDiffVectorBundle 1 F₀ B I]
  [IsContMDiffRiemannianBundle I 1 F₀ B]
  {cov : _root_.CovariantDerivative I F₀ B}

/-- **Metric compatibility along a map.** For a metric-compatible covariant derivative `∇` on
a Riemannian bundle `B`, a map `f` differentiable at `x`, and two sections `V`, `W` of `B` along `f`
whose coordinate readings are differentiable at `x`, `v ⟪V, W⟫ = ⟪∇_v V, W⟫ + ⟪V, ∇_v W⟫` for every
`v ∈ T_x N`, with `∇_v` covariant differentiation along `f`. -/
theorem IsMetricCompatible.mvfderiv_inner_alongMap
    (hcov : cov.IsMetricCompatible)
    (hf : MDifferentiableAt J I f x) {V W : ∀ y, B (f y)}
    (hV : MDifferentiableAt J 𝓘(ℝ, F₀) (sectionCoord ℝ (F := F₀) f V (f x)) x)
    (hW : MDifferentiableAt J 𝓘(ℝ, F₀) (sectionCoord ℝ (F := F₀) f W (f x)) x)
    (v : TangentSpace J x) :
    mvfderiv J (fun y ↦ inner ℝ (V y) (W y)) x v =
      inner ℝ (cov.alongMap J f V x v) (W x) + inner ℝ (V x) (cov.alongMap J f W x v) := by
  have hdiff : ∀ ⦃Y Z : Π z : M, B z⦄, MDiffAt (T% Y) (f x) →
      MDiffAt (T% Z) (f x) → MDiffAt (fun z ↦ innerSL ℝ (Y z) (Z z)) (f x) := by
    intro Y Z hY hZ
    simp only [innerSL_apply_apply]
    exact MDifferentiableAt.inner_bundle (IB := I) (F := F₀) (E := B)
      (b := id) hY hZ
  have hcompat : ∀ ⦃Y Z : Π z : M, B z⦄, MDiffAt (T% Y) (f x) →
      MDiffAt (T% Z) (f x) → ∀ w : TangentSpace I (f x),
        mvfderiv I (fun z ↦ innerSL ℝ (Y z) (Z z)) (f x) w =
          innerSL ℝ (cov Y (f x) w) (Z (f x)) + innerSL ℝ (Y (f x)) (cov Z (f x) w) := by
    intro Y Z hY hZ w
    simp only [innerSL_apply_apply]
    exact hcov.mvfderiv_inner_eq (fun _ ↦ w) hY hZ
  -- `innerSL ℝ v w` unfolds to `inner ℝ v w` (`innerSL_apply_apply` is proved by `rfl`).
  exact mvfderiv_apply_alongMap hdiff hcompat hf hV hW v

end Riemannian

end CovariantDerivative
