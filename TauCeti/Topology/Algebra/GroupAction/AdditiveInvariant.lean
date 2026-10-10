/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Module.PUnit
public import Mathlib.Topology.Algebra.MulAction

/-!
# Additive invariants of finite discrete monoid actions

Fix a natural number `p` and a monoid `G` with a topology. Consider finite discrete additive
commutative groups with a continuous distributive `G`-action whose elements are killed by a power
of `p`. An additive-monoid-valued invariant that is additive on every equivariant short exact
sequence is preserved by equivariant additive equivalences. If the target has left cancellation,
the invariant also vanishes on subsingleton objects. This applies, in particular, to
natural-number-valued lengths and integer-valued Euler characteristics.

## Main results

* `TauCeti.invariant_eq_zero_of_subsingleton`: an additive invariant vanishes on a subsingleton
  object.
* `TauCeti.invariant_eq_of_equiv`: an additive invariant is constant on equivariant additive
  equivalence classes.
-/

public section

universe u v w

namespace TauCeti

variable {p : ℕ} {G : Type v} [Monoid G] [TopologicalSpace G]
  {R : Type w} [AddMonoid R]

variable
  (I : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [DistribMulAction G A] [ContinuousSMul G A] [Finite A],
    (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) → R)
  (hExact : ∀ {A B C : Type u}
    [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A]
    [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B] [ContinuousSMul G B] [Finite B]
    [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C] [ContinuousSMul G C] [Finite C]
    (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0)
    (hB : ∀ b : B, ∃ k : ℕ, p ^ k • b = 0)
    (hC : ∀ c : C, ∃ k : ℕ, p ^ k • c = 0)
    (f : A →+ B) (q : B →+ C),
    (∀ (g : G) (a : A), f (g • a) = g • f a) →
    (∀ (g : G) (b : B), q (g • b) = g • q b) →
    Function.Injective f → Function.Surjective q →
    f.range = q.ker → I B hB = I A hA + I C hC)

include hExact in
/-- An invariant with values in a left-cancellative additive monoid that is additive on
equivariant short exact sequences vanishes on a subsingleton module. -/
theorem invariant_eq_zero_of_subsingleton [IsLeftCancelAdd R] {A : Type u}
    [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Subsingleton A]
    (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) : I A hA = 0 := by
  have h := hExact hA hA hA 0 0
    (by intro g a; simp) (by intro g a; simp)
    (Function.injective_of_subsingleton _)
    (Function.surjective_to_subsingleton _)
    (Subsingleton.elim _ _)
  exact left_eq_add.mp h

include hExact in
/-- An additive-monoid-valued invariant additive on equivariant short exact sequences takes
the same value on equivariantly isomorphic modules. -/
theorem invariant_eq_of_equiv {A B : Type u}
    [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A]
    [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B] [ContinuousSMul G B] [Finite B]
    (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0)
    (hB : ∀ b : B, ∃ k : ℕ, p ^ k • b = 0)
    (e : A ≃+ B) (he : ∀ (g : G) (a : A), e (g • a) = g • e a) :
    I A hA = I B hB := by
  have _ : ContinuousSMul G PUnit.{u + 1} := ⟨continuous_of_const fun _ _ ↦ rfl⟩
  have hZ : ∀ z : PUnit.{u + 1}, ∃ k : ℕ, p ^ k • z = 0 := fun _ ↦ ⟨0, rfl⟩
  have hid := hExact hA hA hZ (AddMonoidHom.id A) 0
    (by intro g a; rfl) (by intro _ _; simp) Function.injective_id
    (Function.surjective_to_subsingleton _)
    (by rw [AddMonoidHom.range_eq_top.mpr Function.surjective_id, AddMonoidHom.ker_zero])
  have h := hExact hA hB hZ e.toAddMonoidHom 0 he
    (by intro _ _; simp) e.injective
    (Function.surjective_to_subsingleton _)
    (by rw [AddMonoidHom.range_eq_top.mpr e.surjective, AddMonoidHom.ker_zero])
  exact hid.trans h.symm

end TauCeti
