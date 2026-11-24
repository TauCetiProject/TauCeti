/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Module.PUnit
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Topology.Algebra.MulAction
public import TauCeti.Topology.Algebra.GroupAction.QuotientAddGroup

/-!
# Additive invariants of finite discrete monoid actions

Fix a natural number `p` and a monoid `G` with a topology. Consider finite discrete additive
commutative groups with a continuous distributive `G`-action that are additive `p`-groups
(`IsAddPGroup p`: every element is killed by a power of `p`). An invariant with values in a type
with addition that is additive on every equivariant short exact sequence is preserved by
equivariant additive equivalences. If zero is an identity and addition is left cancellative, the
invariant also vanishes on subsingleton objects. This applies, in particular, to
natural-number-valued lengths and integer-valued Euler characteristics.

## Main results

* `TauCeti.invariant_eq_zero_of_subsingleton`: an additive invariant vanishes on a subsingleton
  object.
* `TauCeti.invariant_eq_of_equiv`: an additive invariant is constant on equivariant additive
  equivalence classes.
* `TauCeti.invariant_addSubgroup_eq_of_eq_top`: an additive invariant does not distinguish a
  `G`-stable additive subgroup equal to `⊤` from the whole object.
-/

public section

universe u v w

namespace TauCeti

variable {p : ℕ} {G : Type v} [Monoid G] [TopologicalSpace G] {R : Type w}

variable
  (I : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [DistribMulAction G A] [ContinuousSMul G A] [Finite A],
    IsAddPGroup p A → R)

section Add

variable [Add R]
  (hExact : ∀ {A B C : Type u}
    [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A]
    [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B] [ContinuousSMul G B] [Finite B]
    [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C] [ContinuousSMul G C] [Finite C]
    (hA : IsAddPGroup p A) (hB : IsAddPGroup p B) (hC : IsAddPGroup p C)
    (f : A →+ B) (q : B →+ C),
    (∀ (g : G) (a : A), f (g • a) = g • f a) →
    (∀ (g : G) (b : B), q (g • b) = g • q b) →
    Function.Injective f → Function.Surjective q →
    f.range = q.ker → I B hB = I A hA + I C hC)

include hExact in
/-- An invariant with values in a type with addition that is additive on equivariant short
exact sequences takes the same value on equivariantly isomorphic modules. -/
theorem invariant_eq_of_equiv {A B : Type u}
    [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A]
    [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B] [ContinuousSMul G B] [Finite B]
    (hA : IsAddPGroup p A) (e : A ≃+ B) (he : ∀ (g : G) (a : A), e (g • a) = g • e a) :
    I A hA = I B (hA.of_equiv e) := by
  have _ : ContinuousSMul G PUnit.{u + 1} := ⟨continuous_of_const fun _ _ ↦ rfl⟩
  -- Both `A` and `B` are extensions of the zero module by `A`, through `id` and through `e`.
  have hZ := IsAddPGroup.of_subsingleton p PUnit.{u + 1}
  have hid := hExact hA hA hZ (AddMonoidHom.id A) 0 (fun _ _ ↦ rfl)
    (fun _ _ ↦ Subsingleton.elim _ _) Function.injective_id
    (Function.surjective_to_subsingleton _)
    (by rw [AddMonoidHom.range_eq_top.mpr Function.surjective_id, AddMonoidHom.ker_zero])
  have h := hExact hA (hA.of_equiv e) hZ e.toAddMonoidHom 0 he
    (fun _ _ ↦ Subsingleton.elim _ _) e.injective (Function.surjective_to_subsingleton _)
    (by rw [AddMonoidHom.range_eq_top.mpr e.surjective, AddMonoidHom.ker_zero])
  exact hid.trans h.symm

include hExact in
/-- An invariant does not distinguish a `G`-stable additive subgroup equal to `⊤` from the whole
module. -/
theorem invariant_addSubgroup_eq_of_eq_top {M : Type u}
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
    (hM : IsAddPGroup p M) (N : AddSubgroup M) (htop : N = ⊤) :
    haveI hN : ∀ g : G, ∀ x ∈ N, g • x ∈ N := fun g x _ ↦ htop ▸ AddSubgroup.mem_top (g • x)
    letI := N.restrictDistribMulAction hN
    letI := N.restrictDistribMulAction_continuousSMul hN
    I N (hM.to_addSubgroup N) = I M hM := by
  subst htop
  have hN : ∀ g : G, ∀ x ∈ (⊤ : AddSubgroup M), g • x ∈ (⊤ : AddSubgroup M) :=
    fun g x _ ↦ AddSubgroup.mem_top (g • x)
  let := (⊤ : AddSubgroup M).restrictDistribMulAction hN
  let := (⊤ : AddSubgroup M).restrictDistribMulAction_continuousSMul hN
  exact invariant_eq_of_equiv I hExact _ AddSubgroup.topEquiv fun g x ↦ by
    simp only [AddSubgroup.topEquiv_apply, AddSubgroup.restrictDistribMulAction_coe_smul]

end Add

section AddZeroClass

variable [AddZeroClass R]
  (hExact : ∀ {A B C : Type u}
    [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A]
    [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B] [ContinuousSMul G B] [Finite B]
    [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C] [ContinuousSMul G C] [Finite C]
    (hA : IsAddPGroup p A) (hB : IsAddPGroup p B) (hC : IsAddPGroup p C)
    (f : A →+ B) (q : B →+ C),
    (∀ (g : G) (a : A), f (g • a) = g • f a) →
    (∀ (g : G) (b : B), q (g • b) = g • q b) →
    Function.Injective f → Function.Surjective q →
    f.range = q.ker → I B hB = I A hA + I C hC)

include hExact in
/-- An invariant with values in a type whose addition has zero as an identity and left
cancellation, additive on equivariant short exact sequences, vanishes on a subsingleton module. -/
theorem invariant_eq_zero_of_subsingleton [IsLeftCancelAdd R] {A : Type u}
    [AddCommGroup A] [TopologicalSpace A] [DistribMulAction G A] [Subsingleton A] :
    haveI : ContinuousSMul G A := ⟨continuous_of_const fun _ _ ↦ Subsingleton.elim _ _⟩
    I A (.of_subsingleton p A) = 0 := by
  have : ContinuousSMul G A := ⟨continuous_of_const fun _ _ ↦ Subsingleton.elim _ _⟩
  have hA := IsAddPGroup.of_subsingleton p A
  have h := hExact hA hA hA 0 0 (fun _ _ ↦ Subsingleton.elim _ _)
    (fun _ _ ↦ Subsingleton.elim _ _) (Function.injective_of_subsingleton _)
    (Function.surjective_to_subsingleton _) (Subsingleton.elim _ _)
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

end AddZeroClass

end TauCeti
