/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Order.DirectedInverseSystem

/-!
# Composites of a sequence of ⋆-algebra homomorphisms

A sequence of ⋆-algebra homomorphisms `f n : A n →⋆ₐ[R] A (n + 1)` determines, for `i ≤ j`, the
composite `A i →⋆ₐ[R] A j` of `f i, …, f (j - 1)`. These composites form a directed system over
`ℕ`, which is how sequential inductive limits are usually presented. This is the ⋆-algebra
homomorphism version of Mathlib's `FirstOrder.Language.DirectedSystem.natLERec` and
`FirstOrder.Language.DirectedSystem.natLERec.directedSystem` (`Mathlib.ModelTheory.DirectLimit`),
whose construction through `Nat.leRecOn` it follows.

## Main definitions

* `StarAlgHom.natLERec f i j h`: the composite `A i →⋆ₐ[R] A j` of the maps `f k` for
  `i ≤ k < j`.

## Main statements

* `StarAlgHom.natLERec_self_succ`: the composite from a stage to the next one is `f`.
* `StarAlgHom.natLERec_comp`: the composites compose.
* `StarAlgHom.natLERec.directedSystem`: the composites form a directed system.
* `StarAlgHom.natLERec_injective`: the composites of injective maps are injective.
-/

public section

namespace StarAlgHom

variable {R : Type*} {A : ℕ → Type*} [CommSemiring R] [∀ n, Semiring (A n)]
  [∀ n, Algebra R (A n)] [∀ n, Star (A n)] (f : ∀ n, A n →⋆ₐ[R] A (n + 1))

/-- For a sequence of ⋆-algebra homomorphisms `f n : A n → A (n + 1)` and `i ≤ j`, the composite
`A i → A j` of the maps `f k` for `i ≤ k < j`. -/
def natLERec (i j : ℕ) (h : i ≤ j) : A i →⋆ₐ[R] A j :=
  Nat.leRecOn h (fun {k} g ↦ (f k).comp g) (StarAlgHom.id R _)

/-- The composite from a stage to itself is the identity. -/
@[simp]
theorem natLERec_self (i : ℕ) : natLERec f i i le_rfl = StarAlgHom.id R _ :=
  Nat.leRecOn_self _

/-- The composite to the stage after `k` is `f k` after the composite to `k`. -/
theorem natLERec_succ {i k : ℕ} (h : i ≤ k) :
    natLERec f i (k + 1) (h.trans k.le_succ) = (f k).comp (natLERec f i k h) :=
  Nat.leRecOn_succ h _

/-- The composite from a stage to the next one is the map `f` at that stage. -/
@[simp]
theorem natLERec_self_succ (n : ℕ) (h : n ≤ n + 1) : natLERec f n (n + 1) h = f n := by
  rw [natLERec_succ f le_rfl, natLERec_self, StarAlgHom.comp_id]

/-- The composites compose. -/
theorem natLERec_comp {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (natLERec f j k hjk).comp (natLERec f i j hij) = natLERec f i k (hij.trans hjk) := by
  induction k, hjk using Nat.le_induction with
  | base => rw [natLERec_self, StarAlgHom.id_comp]
  | succ k hjk ih => rw [natLERec_succ f hjk, natLERec_succ f (hij.trans hjk),
      StarAlgHom.comp_assoc, ih]

/-- The composites of a sequence of ⋆-algebra homomorphisms form a directed system. -/
instance natLERec.directedSystem : DirectedSystem A fun i j h ↦ natLERec f i j h where
  map_self i a := by rw [natLERec_self, StarAlgHom.coe_id, id_eq]
  map_map k j i hij hjk a := by rw [← natLERec_comp f hij hjk, StarAlgHom.comp_apply]

variable {f} in
/-- The composites of injective ⋆-algebra homomorphisms are injective. -/
theorem natLERec_injective (hf : ∀ n, Function.Injective (f n)) (i j : ℕ) (h : i ≤ j) :
    Function.Injective (natLERec f i j h) := by
  induction j, h using Nat.le_induction with
  | base => rw [natLERec_self]; exact Function.injective_id
  | succ k hik ih => rw [natLERec_succ f hik]; exact (hf k).comp ih

end StarAlgHom
