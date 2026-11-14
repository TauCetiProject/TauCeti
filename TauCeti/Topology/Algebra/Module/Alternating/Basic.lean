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
* `ContinuousAlternatingMap.eq_zero_iff_forall_apply_fin_one`: an alternating map of one vector
  vanishes exactly when it vanishes on every vector.
* `ContinuousAlternatingMap.compContinuousLinearMap_compContinuousLinearMap`: pulling back along
  `A` and then along `B` is pulling back along `A.comp B`.
* `ContinuousAlternatingMap.compContinuousLinearMap_apply_vecCons_two`: the pullback of a map of
  two vectors along `L`, evaluated on `(u, w)`, is the map evaluated on `(L u, L w)`.
* `ContinuousAlternatingMap.compContinuousLinearMap_fst_add_compContinuousLinearMap_snd_apply`:
  the sum `ω₁ ∘ pr₁ + ω₂ ∘ pr₂` of pullbacks of maps of two vectors to `E × F` evaluates
  componentwise.
* `ContinuousAlternatingMap.map_linearDependent`: an alternating map vanishes on linearly
  dependent families.
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

/-- A continuous alternating map of one vector vanishes exactly when it vanishes on every
vector. -/
theorem eq_zero_iff_forall_apply_fin_one {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    (α : M [⋀^Fin 1]→L[R] N) : α = 0 ↔ ∀ v, α ![v] = 0 := by
  refine ⟨fun h v ↦ by simp [h], fun h ↦ ?_⟩
  ext w
  obtain ⟨v, rfl⟩ : ∃ v, w = ![v] := ⟨w 0, funext fun i ↦ by rw [Fin.fin_one_eq_zero i]; rfl⟩
  exact h v

section CompComp

variable {R M M' M'' F ι : Type*} [Semiring R]
  [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [AddCommMonoid M'] [Module R M'] [TopologicalSpace M']
  [AddCommMonoid M''] [Module R M''] [TopologicalSpace M'']
  [AddCommMonoid F] [Module R F] [TopologicalSpace F]

/-- Pulling a form back along `A` and then along `B` is pulling it back along `A.comp B`. -/
@[simp]
theorem compContinuousLinearMap_compContinuousLinearMap (a : M'' [⋀^ι]→L[R] F)
    (A : M →L[R] M'') (B : M' →L[R] M) :
    (a.compContinuousLinearMap A).compContinuousLinearMap B =
      a.compContinuousLinearMap (A.comp B) :=
  rfl

end CompComp

/-- The pullback of a two-form along a continuous linear map, evaluated on `(u, w)`, is the form
evaluated on `(L u, L w)`. -/
theorem compContinuousLinearMap_apply_vecCons_two {R M M' N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M] [AddCommMonoid M'] [Module R M']
    [TopologicalSpace M'] [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    (a : M [⋀^Fin 2]→L[R] N) (L : M' →L[R] M) (u w : M') :
    a.compContinuousLinearMap L ![u, w] = a ![L u, L w] := by
  rw [compContinuousLinearMap_apply]
  congr 1
  funext i
  match i with | 0 | 1 => rfl

/-- The sum `ω₁ ∘ pr₁ + ω₂ ∘ pr₂` of the pullbacks of alternating maps of two vectors on `E` and
`F` to `E × F` evaluates componentwise. -/
theorem compContinuousLinearMap_fst_add_compContinuousLinearMap_snd_apply {R E F G : Type*}
    [Semiring R] [AddCommMonoid E] [Module R E] [TopologicalSpace E] [AddCommMonoid F]
    [Module R F] [TopologicalSpace F] [AddCommMonoid G] [Module R G] [TopologicalSpace G]
    [ContinuousAdd G] (ω₁ : E [⋀^Fin 2]→L[R] G) (ω₂ : F [⋀^Fin 2]→L[R] G) (x y : E × F) :
    (ω₁.compContinuousLinearMap (.fst R E F) + ω₂.compContinuousLinearMap (.snd R E F)) ![x, y] =
      ω₁ ![x.1, y.1] + ω₂ ![x.2, y.2] := by
  simp only [add_apply, compContinuousLinearMap_apply_vecCons_two, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd']

/-- A continuous alternating map vanishes on a linearly dependent family. -/
theorem map_linearDependent {R M N ι : Type*} [Ring R] [IsDomain R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [AddCommGroup N] [Module R N] [TopologicalSpace N]
    [Module.IsTorsionFree R N] (f : M [⋀^ι]→L[R] N) (v : ι → M) (h : ¬LinearIndependent R v) :
    f v = 0 := by
  rw [← coe_toAlternatingMap]
  exact f.toAlternatingMap.map_linearDependent v h

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
