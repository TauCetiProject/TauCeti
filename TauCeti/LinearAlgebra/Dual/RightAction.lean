/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# The dual of a right module as a left module

For a right module `N` over a semiring `A` whose right action commutes with a base commutative
semiring `k`, the duality `D = Hom_k(-, k)` turns `N` into a *left* `A`-module: a scalar `a` acts on
a functional `φ` by precomposition with multiplication by `a`, `(a • φ) x = φ (x * a)`.
Precomposition reverses composition, which is exactly what exchanges the two sides.

This file records that action as the ring homomorphism `TauCeti.dualRightAction`.

On the other side, a semiring `A` with a `k`-module structure commuting with left multiplication
acts on the right of the dual of its left regular module by
`(ψ · c) b = ψ (c * b)`, which Mathlib writes as the domain action `DomMulAct.mk c • ψ`. A map
`A → Module.Dual k A` that is equivariant for the right `A`-actions is determined by its value at
`1`; this is `TauCeti.apply_apply_eq_apply_one_mul`.

## Main definitions

* `TauCeti.dualRightAction`: the left action of `A` on the `k`-dual of a right `A`-module, as a ring
  homomorphism into the `k`-linear endomorphisms of the dual.

## Main results

* `TauCeti.apply_apply_eq_apply_one_mul`: a map from `A` to its dual that is equivariant for the
  right `A`-actions is determined by its value at `1`; additivity is not assumed.
* `LinearEquiv.isScalarTower_of_dual_regular`: a left `A`-module identified with the dual of the
  right regular module, with action `(a • φ) x = φ (x * a)`, has compatible actions of `k` and `A`.

## Implementation notes

The action is deliberately *not* installed as a `Module A (Module.Dual k N)` instance: the
underlying type of `Module.Dual k N` is a type of linear maps, which already carries the
codomain-scaling `Module` instances of `Mathlib.Algebra.Module.LinearMap.Defs`, and a second
`Module` structure matching every dual would make instance search on those types depend on an
undetermined right-module structure.  A consumer that wants the left module structure on one
particular dual builds it with `Module.compHom`, which pins the right-module structure being
dualized.
-/

public section

namespace TauCeti

universe u v w

variable (k : Type u) (N : Type w) {A : Type v} [CommSemiring k] [Semiring A] [AddCommMonoid N]
  [Module k N] [Module Aᵐᵒᵖ N] [SMulCommClass Aᵐᵒᵖ k N]

/-- The **duality** `D = Hom_k(-, k)` turns a right `A`-module `N` into a left `A`-module: the
scalar `a` sends a functional `φ` to `x ↦ φ (x * a)`.  This records that action as a ring
homomorphism from `A` to the `k`-linear endomorphisms of `Module.Dual k N`.

Precomposition reverses composition, which is exactly what makes a *right* action on `N` into a
*left* action on its dual; the hypothesis `SMulCommClass Aᵐᵒᵖ k N` is what makes multiplication by
`a` a `k`-linear endomorphism of `N` in the first place. -/
def dualRightAction : A →+* Module.End k (Module.Dual k N) where
  toFun a := (Module.toModuleEnd k N (MulOpposite.op a)).dualMap
  map_one' := by ext φ x; simp
  map_mul' a b := by ext φ x; simp [mul_smul]
  map_zero' := by ext φ x; simp
  map_add' a b := by ext φ x; simp [add_smul]

@[simp]
theorem dualRightAction_apply_apply (a : A) (φ : Module.Dual k N) (x : N) :
    dualRightAction k N a φ x = φ (MulOpposite.op a • x) :=
  (rfl)

section DomMulAct

variable {k} [Module k A] [SMulCommClass k A A]

/-- A map from `A` to its dual that is equivariant for the right `A`-actions, using the action
`DomMulAct.mk c • ψ = ψ (c * ·)` on the dual, is determined by its value at `1`. The map need not
be additive. -/
theorem apply_apply_eq_apply_one_mul {e : A → Module.Dual k A}
    (he : ∀ a c : A, e (a * c) = DomMulAct.mk c • e a) (a b : A) : e a b = e 1 (a * b) := by
  simpa using LinearMap.congr_fun (he 1 a) b

end DomMulAct

end TauCeti

namespace LinearEquiv

variable {k A Q : Type*} [CommSemiring k] [Semiring A] [Algebra k A] [AddCommMonoid Q]
  [Module A Q] [Module k Q]

/-- A left `A`-module identified with the dual of the right regular module, with action
`(a • φ) x = φ (x * a)`, has compatible actions of `k` and `A`. -/
theorem isScalarTower_of_dual_regular (e : Q ≃ₗ[k] Module.Dual k A)
    (he : ∀ (a : A) (q : Q) (x : A), e (a • q) x = e q (x * a)) :
    IsScalarTower k A Q :=
  IsScalarTower.of_algebraMap_smul fun c q => e.injective <| LinearMap.ext fun x => by
    simp [he, ← Algebra.commutes, ← Algebra.smul_def]

end LinearEquiv
