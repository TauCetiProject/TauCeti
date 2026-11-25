/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Differentiability of pairings of sections along a map

For a map `f : N → M` differentiable at `x` and two sections `V`, `W` of a vector bundle `B → M`
along `f` whose coordinate readings are differentiable at `x`, this file shows that pairing `V`
and `W` gives a function differentiable at `x`. Near `x`, each field is a finite combination of
pullbacks of smooth local-frame sections around `f x`, with differentiable coefficients. So a
pointwise continuous bilinear pairing which pairs differentiable sections to differentiable
functions pairs `V` and `W` to a differentiable function. For the inner product of a Riemannian
bundle this follows directly from Mathlib's `MDifferentiableAt.inner_bundle`. No covariant
derivative is involved.

## Main results

* `TauCeti.Manifold.mdifferentiableAt_apply_of_mdifferentiableAt_sectionCoord`: a pairing that
  preserves differentiability of sections, applied to two fields along a differentiable map with
  differentiable coordinate readings, is differentiable.
* `TauCeti.Manifold.mdifferentiableAt_inner_of_mdifferentiableAt_sectionCoord`: the inner
  product of two such fields of a Riemannian bundle is differentiable.

## References

* The local-frame expansion argument is adapted, via
  `CovariantDerivative/AlongCurve/Metric.lean`, from
  `DoCarmoLib/Riemannian/Connection/MetricCompatibilityAlong.lean` in the Apache-2.0
  [`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture)
  repository, revision `24f32e4d600878bfaac6bc2f2f9324175571c321`.
-/

public section

open Bundle Filter
open scoped Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
  {f : N → M} {x : N}

section Pairing

variable [FiniteDimensional ℝ F₀] {B : M → Type*} [TopologicalSpace (TotalSpace F₀ B)]
  [∀ x, AddCommGroup (B x)] [∀ x, Module ℝ (B x)] [∀ x, TopologicalSpace (B x)]
  [FiberBundle F₀ B] [VectorBundle ℝ F₀ B] [ContMDiffVectorBundle 1 F₀ B I]
  {b : (z : M) → B z →L[ℝ] B z →L[ℝ] ℝ}

/-- For a pointwise continuous bilinear pairing `b` of fibre vectors of `B` that pairs sections
differentiable at `f x` to a function differentiable at `f x`, and for a map `f` differentiable at
`x`, `b(V, W)` is differentiable at `x` for any two fields `V`, `W` along `f` whose coordinate
readings are differentiable at `x`. -/
theorem mdifferentiableAt_apply_of_mdifferentiableAt_sectionCoord
    (hdiff : ∀ ⦃Y Z : Π z : M, B z⦄, MDiffAt (T% Y) (f x) →
      MDiffAt (T% Z) (f x) → MDiffAt (fun z ↦ b z (Y z) (Z z)) (f x))
    (hf : MDifferentiableAt J I f x) {V W : ∀ y, B (f y)}
    (hV : MDifferentiableAt J 𝓘(ℝ, F₀) (sectionCoord ℝ (F := F₀) f V (f x)) x)
    (hW : MDifferentiableAt J 𝓘(ℝ, F₀) (sectionCoord ℝ (F := F₀) f W (f x)) x) :
    MDifferentiableAt J 𝓘(ℝ, ℝ) (fun y ↦ b (f y) (V y) (W y)) x := by
  -- Expand both fields in a smooth local frame around `f x`.
  have hframe (i : Fin (Module.finrank ℝ F₀)) :
      MDiffAt (T% ((trivializationAt F₀ B (f x)).localFrame (Module.finBasis ℝ F₀) i)) (f x) :=
    (contMDiffAt_localFrame_of_mem 1 _ _ i
      (FiberBundle.mem_baseSet_trivializationAt F₀ B (f x))).mdifferentiableAt one_ne_zero
  have hsum : MDifferentiableAt J 𝓘(ℝ, ℝ) (∑ j, ∑ i, fun y ↦
      (Module.finBasis ℝ F₀).coord j (sectionCoord ℝ (F := F₀) f W (f x) y) •
        (Module.finBasis ℝ F₀).coord i (sectionCoord ℝ (F := F₀) f V (f x) y) •
          b (f y)
            ((trivializationAt F₀ B (f x)).localFrame (Module.finBasis ℝ F₀) i (f y))
            ((trivializationAt F₀ B (f x)).localFrame (Module.finBasis ℝ F₀) j (f y)))
      x :=
    MDifferentiableAt.sum fun j _ ↦ MDifferentiableAt.sum fun i _ ↦
      (mdifferentiableAt_repr_sectionCoord f W (Module.finBasis ℝ F₀) hW j).smul
        ((mdifferentiableAt_repr_sectionCoord f V (Module.finBasis ℝ F₀) hV i).smul
          ((hdiff (hframe i) (hframe j)).comp x hf))
  refine hsum.congr_of_eventuallyEq ?_
  have hbase := FiberBundle.mem_baseSet_trivializationAt F₀ B (f x)
  filter_upwards [eventually_eq_sum_repr_sectionCoord_smul_localFrame f V (Module.finBasis ℝ F₀)
    hf.continuousAt hbase, eventually_eq_sum_repr_sectionCoord_smul_localFrame f W
    (Module.finBasis ℝ F₀) hf.continuousAt hbase] with y hVy hWy
  rw [hVy, hWy]
  simp only [map_sum, map_smul, FunLike.coe_sum, FunLike.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Module.Basis.coord_apply]

end Pairing

section Riemannian

variable {B : M → Type*} [TopologicalSpace (TotalSpace F₀ B)]
  [∀ x, NormedAddCommGroup (B x)] [∀ x, InnerProductSpace ℝ (B x)]
  [FiberBundle F₀ B] [VectorBundle ℝ F₀ B] [ContMDiffVectorBundle 1 F₀ B I]
  [IsContMDiffRiemannianBundle I 1 F₀ B]

/-- The inner product of two sections along a map `f` differentiable at `x`, with
coordinate readings differentiable at `x`, is differentiable at `x`. -/
theorem mdifferentiableAt_inner_of_mdifferentiableAt_sectionCoord
    (hf : MDifferentiableAt J I f x) {V W : ∀ y, B (f y)}
    (hV : MDifferentiableAt J 𝓘(ℝ, F₀) (sectionCoord ℝ (F := F₀) f V (f x)) x)
    (hW : MDifferentiableAt J 𝓘(ℝ, F₀) (sectionCoord ℝ (F := F₀) f W (f x)) x) :
    MDifferentiableAt J 𝓘(ℝ, ℝ) (fun y ↦ inner ℝ (V y) (W y)) x := by
  have hbase := FiberBundle.mem_baseSet_trivializationAt F₀ B (f x)
  exact MDifferentiableAt.inner_bundle (IB := I) (F := F₀) (E := B)
    (b := f) ((mdifferentiableAt_sectionCoord_iff f V hf hbase).1 hV)
    ((mdifferentiableAt_sectionCoord_iff f W hf hbase).1 hW)

end Riemannian

end TauCeti.Manifold
