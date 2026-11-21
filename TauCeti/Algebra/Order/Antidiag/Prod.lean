/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.Order.Sub.Unbundled.Basic

/-!
# Antidiagonals as fibres, and initial intervals under ordered subtraction

In a canonically ordered additive type `α` with ordered subtraction and locally finite initial
segments, pairs `(b, c) : α × α` with `b + c = a` are parametrized by `b ∈ Finset.Iic a` via
`c = a - b`. `Finset.sigmaIicEquivProd` packages the resulting bijection `(Σ a : α, Iic a) ≃ α × α`,
serving as the `Finset.Iic` counterpart of `Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd` for
types such as `ι → ℕ` that carry no `Finset.HasAntidiagonal` instance.

For a type with an addition and antidiagonals, `Finset.antidiagonal n` is the fibre over `n` of the
addition map `α × α → α` (`Finset.fiberEquivAntidiagonal`), as a type.

## Main definitions

* `Finset.fiberEquivAntidiagonal`: the equivalence between the fibre of the addition map over `n`
  and `Finset.antidiagonal n`.

* `Finset.sigmaIicEquivProd`: the equivalence `(Σ a : α, Iic a) ≃ α × α` sending `(a, b)` to
  `(b, a - b)` and `(b, c)` to `(b + c, b)`.
-/

public section

namespace Finset

section FiberEquivAntidiagonal

variable {α : Type*} [Add α] [HasAntidiagonal α]

-- The body is exposed so that the underlying pair of `fiberEquivAntidiagonal n x` is `x` by
-- definition, which reindexing coproducts along it uses.
/-- The fibre over `n` of the addition map `α × α → α` is `Finset.antidiagonal n`. -/
@[expose]
def fiberEquivAntidiagonal (n : α) :
    ((fun x : α × α ↦ x.1 + x.2) ⁻¹' {n}) ≃ antidiagonal n :=
  Equiv.subtypeEquivRight fun x ↦ by simp

/-- `Finset.fiberEquivAntidiagonal n` does not change the underlying pair. -/
@[simp]
lemma coe_fiberEquivAntidiagonal_apply (n : α) (x : (fun x : α × α ↦ x.1 + x.2) ⁻¹' {n}) :
    (fiberEquivAntidiagonal n x : α × α) = x :=
  (rfl)

end FiberEquivAntidiagonal

variable {α : Type*} [AddCommSemigroup α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] [AddLeftReflectLE α] [LocallyFiniteOrderBot α]

/-- Bijection between the sigma type `Σ a, Iic a` of pairs `(a, b)` with `b ≤ a` and `α × α`,
sending `(a, b)` to `(b, a - b)` and `(b, c)` to `(b + c, b)`. -/
def sigmaIicEquivProd : (Σ a : α, Iic a) ≃ α × α where
  toFun x := (x.2.val, x.1 - x.2.val)
  invFun p := ⟨p.1 + p.2, ⟨p.1, mem_Iic.2 le_self_add⟩⟩
  left_inv := by
    rintro ⟨a, b, hb⟩
    exact Sigma.subtype_ext (add_tsub_cancel_of_le (mem_Iic.1 hb)) rfl
  right_inv p := by
    ext <;> simp

@[simp]
theorem sigmaIicEquivProd_apply (x : Σ a : α, Iic a) :
    sigmaIicEquivProd x = (x.2.val, x.1 - x.2.val) := (rfl)

@[simp]
theorem sigmaIicEquivProd_symm_apply (p : α × α) :
    sigmaIicEquivProd.symm p = ⟨p.1 + p.2, ⟨p.1, mem_Iic.2 le_self_add⟩⟩ := (rfl)

end Finset
