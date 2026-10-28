/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Basic

/-!
# Alternating pullbacks and postcompositions

The underlying continuous multilinear map of an alternating pullback is the
multilinear pullback. This identity allows consumers to move between the two APIs
without unfolding their implementations.

Postcomposing a continuous alternating map with the identity continuous linear map
leaves it unchanged.

Pullback along a continuous linear map is linear, and postcomposition with a continuous linear
map that is semilinear for an additional scalar action is semilinear, over any scalars acting on
the codomain compatibly with the base ring. For instance, complex-valued real alternating forms
form a complex vector space, and these operations are complex-linear or conjugate-linear.

## Main declarations

* `ContinuousAlternatingMap.compContinuousLinearMapLinear`: pullback as a linear map over the
  scalars of the codomain.
* `ContinuousLinearMap.compContinuousAlternatingMapSemilinear`: postcomposition with a semilinear
  map as a semilinear map of alternating maps.
-/

public section

namespace ContinuousAlternatingMap

/-- Taking the underlying multilinear map commutes with continuous linear pullback. -/
@[simp] theorem toContinuousMultilinearMap_compContinuousLinearMap
    {R E F G ι : Type*} [Semiring R]
    [AddCommMonoid E] [Module R E] [TopologicalSpace E]
    [AddCommMonoid F] [Module R F] [TopologicalSpace F]
    [AddCommMonoid G] [Module R G] [TopologicalSpace G]
    (φ : F [⋀^ι]→L[R] G) (f : E →L[R] F) :
    (φ.compContinuousLinearMap f).toContinuousMultilinearMap =
      φ.toContinuousMultilinearMap.compContinuousLinearMap (fun _ ↦ f) := (rfl)

variable {A S M M' N ι : Type*} [Semiring A] [Semiring S]
  [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  [AddCommMonoid M'] [Module A M'] [TopologicalSpace M']
  [AddCommMonoid N] [Module A N] [TopologicalSpace N] [ContinuousAdd N]
  [Module S N] [ContinuousConstSMul S N] [SMulCommClass A S N]

variable (S) in
/-- `ContinuousAlternatingMap.compContinuousLinearMap` as a linear map over any scalars acting on
the codomain. This generalizes Mathlib's `ContinuousAlternatingMap.compContinuousLinearMapₗ`,
which is linear over the base ring only. -/
def compContinuousLinearMapLinear (f : M →L[A] M') :
    (M' [⋀^ι]→L[A] N) →ₗ[S] M [⋀^ι]→L[A] N where
  toFun g := g.compContinuousLinearMap f
  map_add' g g' := by ext; simp
  map_smul' c g := by ext; simp

@[simp]
theorem compContinuousLinearMapLinear_apply (f : M →L[A] M') (g : M' [⋀^ι]→L[A] N) :
    compContinuousLinearMapLinear S f g = g.compContinuousLinearMap f :=
  (rfl)

end ContinuousAlternatingMap

namespace ContinuousLinearMap

/-- Postcomposing a continuous alternating map with the identity leaves it unchanged. -/
@[simp] theorem id_compContinuousAlternatingMap
    {R E F ι : Type*} [Semiring R]
    [AddCommMonoid E] [Module R E] [TopologicalSpace E]
    [AddCommMonoid F] [Module R F] [TopologicalSpace F]
    (f : E [⋀^ι]→L[R] F) :
    (ContinuousLinearMap.id R F).compContinuousAlternatingMap f = f := by
  ext; simp

variable {A S S₂ M N N' ι : Type*} [Semiring A] [Semiring S] [Semiring S₂]
  [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  [AddCommMonoid N] [Module A N] [TopologicalSpace N] [ContinuousAdd N]
  [Module S N] [ContinuousConstSMul S N] [SMulCommClass A S N]
  [AddCommMonoid N'] [Module A N'] [TopologicalSpace N'] [ContinuousAdd N']
  [Module S₂ N'] [ContinuousConstSMul S₂ N'] [SMulCommClass A S₂ N']

/-- Postcomposition with a continuous linear map `L` that is `σ`-semilinear for additional
scalar actions on its domain and codomain, as a `σ`-semilinear map of alternating maps. -/
def compContinuousAlternatingMapSemilinear {σ : S →+* S₂} (L : N →L[A] N')
    (hL : ∀ (c : S) x, L (c • x) = σ c • L x) :
    (M [⋀^ι]→L[A] N) →ₛₗ[σ] M [⋀^ι]→L[A] N' where
  toFun ω := L.compContinuousAlternatingMap ω
  map_add' ω ω' := by ext; simp
  map_smul' c ω := by ext; simp [hL]

@[simp]
theorem compContinuousAlternatingMapSemilinear_apply {σ : S →+* S₂} (L : N →L[A] N')
    (hL : ∀ (c : S) x, L (c • x) = σ c • L x) (ω : M [⋀^ι]→L[A] N) :
    compContinuousAlternatingMapSemilinear L hL ω = L.compContinuousAlternatingMap ω :=
  (rfl)

end ContinuousLinearMap
