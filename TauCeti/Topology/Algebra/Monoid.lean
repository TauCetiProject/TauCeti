/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.CompactOpen

/-!
# Continuous maps on a topological magma, and the coordinate embeddings of a product

Continuous-map constructions that use the multiplication of a topological magma, next to
Mathlib's `ContinuousMap.mulLeft` and `ContinuousMap.mulRight`, and the convergence of the
coordinate embeddings `Pi.mulSingle` of a product of pointed topological spaces, next to Mathlib's
`continuous_mulSingle`.

## Main definitions

* `ContinuousMap.compSwapShearMulRight`: the family `x ↦ (y ↦ Ψ y (y * x))` attached to a
  two-variable continuous map `Ψ`, that is, `Ψ` precomposed with the coordinate swap followed by
  the shear `(a, b) ↦ (a, a * b)` of `Homeomorph.shearMulRight`, with
  `ContinuousMap.compSwapShearMulRight_apply_apply` its pointwise formula.

## Main results

* `TauCeti.tendsto_mulSingle_cofinite`: in a product `∀ i, M i` of pointed topological spaces, the
  elements `Pi.mulSingle i (x i)` supported at a single coordinate tend to `1` along the cofinite
  filter on the index type.
-/

public section

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X] [Mul X] [ContinuousMul X] [LocallyCompactSpace X]
  {Z : Type*} [TopologicalSpace Z]

/-- The family `x ↦ (y ↦ Ψ y (y * x))` attached to a two-variable continuous map `Ψ`: the
uncurried `Ψ` precomposed with the coordinate swap `(x, y) ↦ (y, x)` followed by the shear
`(a, b) ↦ (a, a * b)` of `Homeomorph.shearMulRight`, curried again. Local compactness makes
evaluation continuous, which is what makes the family jointly continuous. -/
noncomputable def compSwapShearMulRight (Ψ : C(X, C(X, Z))) : C(X, C(X, Z)) :=
  curry ⟨fun p : X × X => Ψ p.2 (p.2 * p.1),
    continuous_eval.comp ((Ψ.continuous.comp continuous_snd).prodMk
      (continuous_snd.mul continuous_fst))⟩

@[simp]
theorem compSwapShearMulRight_apply_apply (Ψ : C(X, C(X, Z))) (x y : X) :
    compSwapShearMulRight Ψ x y = Ψ y (y * x) := (rfl)

end ContinuousMap

namespace TauCeti

open Filter Topology

variable {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, One (M i)]
  [∀ i, TopologicalSpace (M i)]

/-- **The coordinate embeddings of a product tend to `1` along the cofinite filter.** For any
family `x`, the element `Pi.mulSingle i (x i)` of the product, supported at the single coordinate
`i`, tends to `1` as `i` leaves every finite set. -/
@[to_additive /-- **The coordinate embeddings of a product tend to `0` along the cofinite
filter.** For any family `x`, the element `Pi.single i (x i)` of the product, supported at the
single coordinate `i`, tends to `0` as `i` leaves every finite set. -/]
theorem tendsto_mulSingle_cofinite (x : ∀ i, M i) :
    Tendsto (fun i ↦ Pi.mulSingle i (x i)) cofinite (𝓝 1) := by
  -- coordinatewise: the `j`-th coordinate of `Pi.mulSingle i (x i)` is `1` as soon as `i ≠ j`
  rw [tendsto_pi_nhds]
  intro j
  refine tendsto_const_nhds.congr' ((eventually_cofinite_ne j).mono fun i hij ↦ ?_)
  exact (Pi.mulSingle_eq_of_ne hij.symm (x i)).symm

end TauCeti
