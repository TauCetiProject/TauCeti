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

The two-form `pr₁^* ω₁ + pr₂^* ω₂` on `V × W` pairs `p` with `q` to `ω₁(p.1, q.1) + ω₂(p.2, q.2)`.

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
* `ContinuousAlternatingMap.apply_vecCons_swap`: an alternating map of two vectors changes sign
  when they are exchanged.
* `ContinuousAlternatingMap.apply_vecCons_eq_sum_repr`,
  `ContinuousAlternatingMap.apply_vecCons_eq_sum_repr_fin_four`: a two-form in the coordinates of
  a basis, and its six-term form on a four-dimensional space.
* `ContinuousAlternatingMap.compContinuousLinearMap_compContinuousLinearMap`: pulling back along
  `A` and then along `B` is pulling back along `A.comp B`.
* `ContinuousAlternatingMap.compContinuousLinearMap_fst_add_snd_apply`: the two-form
  `pr₁^* ω₁ + pr₂^* ω₂` on a product evaluated on two vectors.
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

/-- A continuous alternating map of two vectors changes sign when they are exchanged. -/
theorem apply_vecCons_swap {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommGroup N] [Module R N] [TopologicalSpace N]
    (f : M [⋀^Fin 2]→L[R] N) (v w : M) : f ![w, v] = -f ![v, w] := by
  simpa using f.map_swap ![v, w] (i := 0) (j := 1) Fin.zero_ne_one

section Coordinates

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [AddCommMonoid N] [Module R N] [TopologicalSpace N]

/-- **A two-form in coordinates.** In the coordinates of a basis `b`, a two-form `ω` is
`ω(u, v) = ∑ᵢ ∑ⱼ uᵢ vⱼ ω(bᵢ, bⱼ)`. -/
theorem apply_vecCons_eq_sum_repr {ι : Type*} [Fintype ι] (b : Module.Basis ι R M)
    (ω : M [⋀^Fin 2]→L[R] N) (u v : M) :
    ω ![u, v] = ∑ i, ∑ j, (b.repr u i * b.repr v j) • ω ![b i, b j] := by
  -- `ω` is linear in each argument (`MultilinearMap.toLinearMap`), so expand both in `b`.
  have h (m : Fin 2 → M) (k : Fin 2) (x : M) :
      ω (Function.update m k x) = ∑ i, b.repr x i • ω (Function.update m k (b i)) := by
    simpa [b.sum_repr] using
      _root_.map_sum (ω.toMultilinearMap.toLinearMap m k) (fun i ↦ b.repr x i • b i) Finset.univ
  have h₀ (x y z : M) : Function.update ![x, y] 0 z = ![z, y] := by
    ext k; fin_cases k <;> simp
  have h₁ (x y z : M) : Function.update ![x, y] 1 z = ![x, z] := by
    ext k; fin_cases k <;> simp
  have hu := h ![u, v] 0 u
  have hv (x : M) := h ![x, v] 1 v
  simp only [h₀, h₁] at hu hv
  simp only [hu, hv, Finset.smul_sum, smul_smul]

end Coordinates

section FinFour

variable {R M N : Type*} [Ring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N]

/-- **A two-form on a four-dimensional space in coordinates.** In the coordinates of a basis `b`
indexed by `Fin 4`, a two-form `ω` is `ω(u, v) = ∑_{i < j} (uᵢ vⱼ - uⱼ vᵢ) ω(bᵢ, bⱼ)`. -/
theorem apply_vecCons_eq_sum_repr_fin_four (b : Module.Basis (Fin 4) R M)
    (ω : M [⋀^Fin 2]→L[R] N) (u v : M) :
    ω ![u, v] =
      (b.repr u 0 * b.repr v 1 - b.repr u 1 * b.repr v 0) • ω ![b 0, b 1] +
      (b.repr u 0 * b.repr v 2 - b.repr u 2 * b.repr v 0) • ω ![b 0, b 2] +
      (b.repr u 0 * b.repr v 3 - b.repr u 3 * b.repr v 0) • ω ![b 0, b 3] +
      (b.repr u 1 * b.repr v 2 - b.repr u 2 * b.repr v 1) • ω ![b 1, b 2] +
      (b.repr u 1 * b.repr v 3 - b.repr u 3 * b.repr v 1) • ω ![b 1, b 3] +
      (b.repr u 2 * b.repr v 3 - b.repr u 3 * b.repr v 2) • ω ![b 2, b 3] := by
  have hzero : ∀ i, ω ![b i, b i] = 0 := fun i ↦
    ω.map_eq_zero_of_eq ![b i, b i] (i := 0) (j := 1) rfl Fin.zero_ne_one
  rw [apply_vecCons_eq_sum_repr b]
  simp only [Fin.sum_univ_four, hzero, smul_zero, apply_vecCons_swap ω (b 0) (b 1),
    apply_vecCons_swap ω (b 0) (b 2), apply_vecCons_swap ω (b 0) (b 3),
    apply_vecCons_swap ω (b 1) (b 2), apply_vecCons_swap ω (b 1) (b 3),
    apply_vecCons_swap ω (b 2) (b 3), smul_neg, sub_smul]
  abel

end FinFour

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

section Prod

variable {R V W N : Type*} [Semiring R]
  [AddCommMonoid V] [Module R V] [TopologicalSpace V]
  [AddCommMonoid W] [Module R W] [TopologicalSpace W]
  [AddCommMonoid N] [Module R N] [TopologicalSpace N] [ContinuousAdd N]

/-- The two-form `pr₁^* ω₁ + pr₂^* ω₂` on `V × W` pairs `p` with `q` to
`ω₁(p.1, q.1) + ω₂(p.2, q.2)`. -/
theorem compContinuousLinearMap_fst_add_snd_apply (ω₁ : V [⋀^Fin 2]→L[R] N)
    (ω₂ : W [⋀^Fin 2]→L[R] N) (p q : V × W) :
    (ω₁.compContinuousLinearMap (ContinuousLinearMap.fst R V W) +
        ω₂.compContinuousLinearMap (ContinuousLinearMap.snd R V W)) ![p, q] =
      ω₁ ![p.1, q.1] + ω₂ ![p.2, q.2] := by
  have h₁ : Prod.fst ∘ ![p, q] = ![p.1, q.1] := by ext i; fin_cases i <;> rfl
  have h₂ : Prod.snd ∘ ![p, q] = ![p.2, q.2] := by ext i; fin_cases i <;> rfl
  simp [h₁, h₂]

end Prod

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
