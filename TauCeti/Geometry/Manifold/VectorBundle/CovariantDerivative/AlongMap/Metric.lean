/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongMap.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Basic

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
specialization to the inner product, using the ambient directional product rule
`CovariantDerivative.IsMetricCompatible.mvfderiv_inner_apply`. Differentiability of the pairing
needs no covariant derivative: it uses only the same local-frame expansion.

## Main results

* `CovariantDerivative.mvfderiv_apply_alongMap`: the product rule along a map for a pointwise
  bilinear pairing satisfying the ambient product rule.
* `CovariantDerivative.mdifferentiableAt_apply_alongMap`: such a pairing of two fields along a
  map with differentiable coordinate readings is differentiable.
* `CovariantDerivative.IsMetricCompatible.mvfderiv_inner_alongMap`: the metric product rule for
  two tangent fields along a differentiable map with differentiable coordinate readings.
* `CovariantDerivative.mdifferentiableAt_inner_alongMap`: the inner product of two such fields
  is differentiable.

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

/-- The fields of the canonical local frame of `TM` around `z` are differentiable at `z`. -/
private lemma mdifferentiableAt_localFrame (z : M) (i : Fin (Module.finrank ℝ E)) :
    MDiffAt (T% ((trivializationAt E (TangentSpace I) z).localFrame (Module.finBasis ℝ E) i)) z :=
  ((((trivializationAt E (TangentSpace I) z).isLocalFrameOn_localFrame_baseSet I 1
    (Module.finBasis ℝ E)).contMDiffOn i).mdifferentiableOn one_ne_zero).mdifferentiableAt
    ((trivializationAt E (TangentSpace I) z).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) z))

omit [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- The basis coordinates of a coordinate reading differentiable at `x` are differentiable
at `x`. -/
private lemma mdifferentiableAt_coord_sectionCoord {Q : ∀ y, TangentSpace I (f y)}
    (hQ : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f Q (f x)) x)
    (i : Fin (Module.finrank ℝ E)) :
    MDifferentiableAt J 𝓘(ℝ, ℝ)
      (fun y ↦ (Module.finBasis ℝ E).coord i (sectionCoord ℝ (F := E) f Q (f x) y)) x :=
  (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)).differentiableAt
    |>.comp_mdifferentiableAt hQ

omit [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- Near `x`, a field along a map continuous at `x` is the combination of the pulled-back
local-frame fields around `f x`, with the basis coordinates of its coordinate reading as
coefficients. -/
private lemma eventually_sum_coord_smul_localFrame (hf : ContinuousAt f x)
    (Q : ∀ y, TangentSpace I (f y)) :
    ∀ᶠ y in 𝓝 x, ∑ i, (Module.finBasis ℝ E).coord i (sectionCoord ℝ (F := E) f Q (f x) y) •
      (trivializationAt E (TangentSpace I) (f x)).localFrame (Module.finBasis ℝ E) i (f y) =
        Q y := by
  let e := trivializationAt E (TangentSpace I) (f x)
  filter_upwards [hf.preimage_mem_nhds (e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (f x)))] with y hy
  simp only [(Module.finBasis ℝ E).coord_apply, sectionCoord_apply]
  exact ((Module.finBasis ℝ E).eq_sum_repr_continuousLinearMapAt_smul_localFrame hy (Q y)).symm

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
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]
  rw [show (fun y ↦ b (f y) (X (f y)) (Y (f y))) = (fun z ↦ b z (X z) (Y z)) ∘ f from rfl,
    mvfderiv_comp_apply x (hdiff hX hY) hf v, hcompat hX hY, alongMap_pullback cov f hf hX,
    alongMap_pullback cov f hf hY]
  simp only [ContinuousLinearMap.comp_apply]

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
  have hcX (i : Fin (Module.finrank ℝ E)) : MDifferentiableAt J 𝓘(ℝ, E)
      (sectionCoord ℝ (F := E) f (fun y ↦ e.localFrame β i (f y)) (f x)) x :=
    mdifferentiableAt_sectionCoord f (fun y ↦ e.localFrame β i (f y))
      ((mdifferentiableAt_localFrame (f x) i).comp x hf)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (f x))
  have hcTerm (Q : ∀ y, TangentSpace I (f y))
      (hQ : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f Q (f x)) x) (i : Fin _) :
      MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f
        (fun y ↦ β.coord i (sectionCoord ℝ (F := E) f Q (f x) y) • e.localFrame β i (f y))
        (f x)) x := by
    rw [sectionCoord_fun_smul]
    exact (mdifferentiableAt_coord_sectionCoord hQ i).smul (hcX i)
  have hterm (i j : Fin (Module.finrank ℝ E)) :
      HasPairingProductRuleAt (J := J) cov f x (fun z ↦ (b z).toLinearMap₁₂)
        (fun y ↦ β.coord i (sectionCoord ℝ (F := E) f V (f x) y) • e.localFrame β i (f y))
        (fun y ↦ β.coord j (sectionCoord ℝ (F := E) f W (f x) y) • e.localFrame β j (f y)) :=
    ((hasPairingProductRuleAt_pullback hdiff hcompat hf (mdifferentiableAt_localFrame (f x) i)
      (mdifferentiableAt_localFrame (f x) j)).smul_left
      (mdifferentiableAt_coord_sectionCoord hV i) (hcX i)).smul_right
      (mdifferentiableAt_coord_sectionCoord hW j) (hcX j)
  have hsum := HasPairingProductRuleAt.finsetSum_left (A := Finset.univ)
    (fun i _ ↦ HasPairingProductRuleAt.finsetSum_right (A := Finset.univ)
      (fun j _ ↦ hterm i j) fun j _ ↦ hcTerm W hW j) fun i _ ↦ hcTerm V hV i
  exact hsum.congr_of_eventuallyEq (eventually_sum_coord_smul_localFrame hf.continuousAt V)
    (eventually_sum_coord_smul_localFrame hf.continuousAt W)

/-- **The product rule along a map**, differentiability part: for a pointwise bilinear pairing `b`
that pairs vector fields differentiable at `f x` to a function differentiable at `f x`, and for a
map `f` differentiable at `x`, `b(V, W)` is differentiable at `x` for any two fields `V`, `W` along
`f` whose coordinate readings are differentiable at `x`. No covariant derivative is involved. -/
theorem mdifferentiableAt_apply_alongMap
    (hdiff : ∀ ⦃Y Z : Π z : M, TangentSpace I z⦄, MDiffAt (T% Y) (f x) →
      MDiffAt (T% Z) (f x) → MDiffAt (fun z ↦ b z (Y z) (Z z)) (f x))
    (hf : MDifferentiableAt J I f x) {V W : ∀ y, TangentSpace I (f y)}
    (hV : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f V (f x)) x)
    (hW : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f W (f x)) x) :
    MDifferentiableAt J 𝓘(ℝ, ℝ) (fun y ↦ b (f y) (V y) (W y)) x := by
  -- Expand both fields in a smooth local frame around `f x`.
  have hsum : MDifferentiableAt J 𝓘(ℝ, ℝ) (∑ j, ∑ i, fun y ↦
      (Module.finBasis ℝ E).coord j (sectionCoord ℝ (F := E) f W (f x) y) •
        (Module.finBasis ℝ E).coord i (sectionCoord ℝ (F := E) f V (f x) y) •
          b (f y)
            ((trivializationAt E (TangentSpace I) (f x)).localFrame (Module.finBasis ℝ E) i (f y))
            ((trivializationAt E (TangentSpace I) (f x)).localFrame (Module.finBasis ℝ E) j (f y)))
      x :=
    MDifferentiableAt.sum fun j _ ↦ MDifferentiableAt.sum fun i _ ↦
      (mdifferentiableAt_coord_sectionCoord hW j).smul
        ((mdifferentiableAt_coord_sectionCoord hV i).smul
          ((hdiff (mdifferentiableAt_localFrame (f x) i)
            (mdifferentiableAt_localFrame (f x) j)).comp x hf))
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [eventually_sum_coord_smul_localFrame hf.continuousAt V,
    eventually_sum_coord_smul_localFrame hf.continuousAt W] with y hVy hWy
  rw [← hVy, ← hWy]
  simp only [map_sum, map_smul, FunLike.coe_sum, FunLike.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

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

omit [FiniteDimensional ℝ E] in
/-- The inner product of two tangent fields along a map `f` differentiable at `x`, with
coordinate readings differentiable at `x`, is differentiable at `x`. -/
theorem mdifferentiableAt_inner_alongMap
    (hf : MDifferentiableAt J I f x) {V W : ∀ y, TangentSpace I (f y)}
    (hV : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f V (f x)) x)
    (hW : MDifferentiableAt J 𝓘(ℝ, E) (sectionCoord ℝ (F := E) f W (f x)) x) :
    MDifferentiableAt J 𝓘(ℝ, ℝ) (fun y ↦ inner ℝ (V y) (W y)) x := by
  have hbase := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (f x)
  exact MDifferentiableAt.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x)
    (b := f) ((mdifferentiableAt_sectionCoord_iff f V hf hbase).1 hV)
    ((mdifferentiableAt_sectionCoord_iff f W hf hbase).1 hW)

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
      inner ℝ (cov.alongMap J f V x v) (W x) + inner ℝ (V x) (cov.alongMap J f W x v) := by
  have hdiff : ∀ ⦃Y Z : Π z : M, TangentSpace I z⦄, MDiffAt (T% Y) (f x) →
      MDiffAt (T% Z) (f x) → MDiffAt (fun z ↦ innerSL ℝ (Y z) (Z z)) (f x) := by
    intro Y Z hY hZ
    simp only [innerSL_apply_apply]
    exact MDifferentiableAt.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x)
      (b := id) hY hZ
  have hcompat : ∀ ⦃Y Z : Π z : M, TangentSpace I z⦄, MDiffAt (T% Y) (f x) →
      MDiffAt (T% Z) (f x) → ∀ w : TangentSpace I (f x),
        mvfderiv I (fun z ↦ innerSL ℝ (Y z) (Z z)) (f x) w =
          innerSL ℝ (cov Y (f x) w) (Z (f x)) + innerSL ℝ (Y (f x)) (cov Z (f x) w) := by
    intro Y Z hY hZ w
    simp only [innerSL_apply_apply]
    exact hcov.mvfderiv_inner_apply hY hZ w
  -- `innerSL ℝ v w` unfolds to `inner ℝ v w` (`innerSL_apply_apply` is proved by `rfl`).
  exact mvfderiv_apply_alongMap hdiff hcompat hf hV hW v

end Riemannian

end CovariantDerivative
