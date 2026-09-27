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
# Additive invariants of finite discrete group actions

Fix a natural number `p` and a group `G` with a topology. Consider finite discrete additive
commutative groups with a continuous distributive `G`-action whose elements are killed by a power
of `p`. An integer-valued invariant additive on every equivariant short exact sequence vanishes
on subsingleton objects and is preserved by equivariant additive equivalences.

## Main results

* `TauCeti.invariant_eq_zero_of_subsingleton`: an additive invariant vanishes on a subsingleton
  object.
* `TauCeti.invariant_eq_of_equiv`: an additive invariant is constant on equivariant additive
  equivalence classes.
-/

public section

universe u v

namespace TauCeti

variable {p : ℕ} {G : Type v} [Group G] [TopologicalSpace G]

variable
  (I : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [DistribMulAction G A] [ContinuousSMul G A] [Finite A],
    (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) → ℤ)
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
/-- An invariant additive on equivariant short exact sequences vanishes on a subsingleton
module. -/
theorem invariant_eq_zero_of_subsingleton {A : Type u}
    [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A] [Subsingleton A]
    (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) : I A hA = 0 := by
  have h := hExact hA hA hA 0 0
    (by intro g a; simp) (by intro g a; simp)
    (fun _ _ _ ↦ Subsingleton.elim _ _)
    (fun a ↦ ⟨0, Subsingleton.elim _ _⟩)
    (by
      ext a
      constructor
      · intro _
        rfl
      · intro _
        exact ⟨0, Subsingleton.elim _ _⟩)
  omega

include hExact in
/-- An invariant additive on equivariant short exact sequences takes the same value on
equivariantly isomorphic modules. -/
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
  have h := hExact hA hB hZ e.toAddMonoidHom 0 he
    (by intro g b; simp) e.injective
    (fun z ↦ ⟨0, Subsingleton.elim _ _⟩)
    (by
      ext b
      constructor
      · intro _
        rfl
      · intro _
        exact e.surjective b)
  rw [invariant_eq_zero_of_subsingleton I hExact hZ, add_zero] at h
  exact h.symm

end TauCeti
