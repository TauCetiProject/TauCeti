/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The cyclic quotient of an algebra

For a (not necessarily unital or associative) ring `A` which is a module over a ring `k`, the
**commutator submodule** of `A` is the `k`-span of the additive commutators `x * y - y * x`.  The
quotient by this submodule is the **cyclic quotient**

```text
A / [A, A].
```

Its elements are cyclic classes.  For a path algebra `kQ`, a potential for the three-dimensional
Ginzburg construction is naturally a cyclic class rather than a chosen representative in `kQ`.
This file provides the quotient and its elementary universal property; cyclic derivatives of a path
algebra are descended to it in `TauCeti.RepresentationTheory.Quiver.PathAlgebra.Cyclic.Derivative`.

## Main definitions

* `TauCeti.commutatorSubmodule`: the span of additive commutators in `A`.
* `TauCeti.cyclicQuotient`: the quotient `A / [A, A]`.

## Main results

* `TauCeti.neg_mem_commutatorSubmodule`, `TauCeti.zsmul_mem_commutatorSubmodule` and
  `TauCeti.neg_one_pow_mul_mem_commutatorSubmodule`: the commutator submodule is closed under
  negation, under integer multiples and under multiplication by signs, even over a semiring of
  scalars.
* `TauCeti.mul_mem_commutatorSubmodule_comm`: a product is a sum of commutators exactly when its
  rotation is.
* `TauCeti.commutatorSubmodule_le_iff`: the commutator submodule lies in a submodule exactly
  when every additive commutator `x * y - y * x` does.
* `TauCeti.commutatorSubmodule_le_ker_iff`: a linear map kills the commutator submodule exactly
  when it takes equal values on `x * y` and `y * x`.
* `TauCeti.map_mem_commutatorSubmodule`: a multiplicative `k`-linear map carries the commutator
  submodule over `k` into the commutator submodule over `k` of its target.
* `TauCeti.map_mem_commutatorSubmodule_of_ringHom`: when `k` acts on `A` associatively and
  centrally, a non-unital ring homomorphism carries the commutator submodule over `k` into the
  commutator submodule of its target over any semiring of scalars acting on the target.

The trace criterion for nonvanishing cyclic classes, which needs matrices, is
`TauCeti.trace_map_eq_zero_of_mem_commutatorSubmodule` in
`TauCeti.LinearAlgebra.Matrix.Trace.CyclicQuotient`.

## References

* J.-L. Loday, *Cyclic Homology*, Section 1.1, for the identification
  `HH₀(A) = A / [A, A]`.
-/

public section

namespace TauCeti

variable (k : Type*) (A : Type*) [NonUnitalNonAssocRing A]

section Semiring

variable [Semiring k] [Module k A]

/-- The `k`-submodule of `A` spanned by the additive commutators `x * y - y * x`. -/
def commutatorSubmodule : Submodule k A :=
  Submodule.span k (Set.range fun p : A × A => p.1 * p.2 - p.2 * p.1)

/-- Every additive commutator belongs to the commutator submodule. -/
@[simp]
theorem mul_sub_mul_mem_commutatorSubmodule (x y : A) :
    x * y - y * x ∈ commutatorSubmodule k A :=
  Submodule.subset_span ⟨(x, y), rfl⟩

variable {k A} in
/-- The commutator submodule lies in a submodule `S` exactly when every additive commutator
`x * y - y * x` lies in `S`. -/
theorem commutatorSubmodule_le_iff {S : Submodule k A} :
    commutatorSubmodule k A ≤ S ↔ ∀ x y : A, x * y - y * x ∈ S := by
  rw [commutatorSubmodule, Submodule.span_le, Set.range_subset_iff, Prod.forall]
  simp only [SetLike.mem_coe]

variable {k A} in
/-- The commutator submodule is closed under negation even when `k` is only a semiring: the
negative of a commutator `x * y - y * x` is the commutator `y * x - x * y`. -/
theorem neg_mem_commutatorSubmodule {x : A} (hx : x ∈ commutatorSubmodule k A) :
    -x ∈ commutatorSubmodule k A := by
  -- negation, as a `k`-linear map, sends each spanning commutator to a commutator
  have hle : commutatorSubmodule k A ≤ (commutatorSubmodule k A).comap (-LinearMap.id) :=
    commutatorSubmodule_le_iff.2 fun x y => by simp
  simpa using hle hx

variable {k A} in
/-- The commutator submodule is closed under integer multiples even when `k` is only a
semiring. -/
theorem zsmul_mem_commutatorSubmodule {x : A} (hx : x ∈ commutatorSubmodule k A) (n : ℤ) :
    n • x ∈ commutatorSubmodule k A := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using nsmul_mem hx m
  · simpa using neg_mem_commutatorSubmodule (nsmul_mem hx m)

variable {k} in
/-- The commutator submodule is closed under multiplication by a sign `(-1) ^ e`, even when `k` is
only a semiring. -/
theorem neg_one_pow_mul_mem_commutatorSubmodule {B : Type*} [Ring B] [Module k B] {x : B}
    (hx : x ∈ commutatorSubmodule k B) (e : ℕ) : (-1 : B) ^ e * x ∈ commutatorSubmodule k B := by
  rcases neg_one_pow_eq_or B e with h | h
  · simpa [h] using hx
  · simpa [h] using neg_mem_commutatorSubmodule hx

variable {k A} in
/-- **Rotation**: a product lies in the commutator submodule exactly when the product of its
factors in the other order does, since the two differ by the commutator `x * y - y * x`. -/
theorem mul_mem_commutatorSubmodule_comm {x y : A} :
    x * y ∈ commutatorSubmodule k A ↔ y * x ∈ commutatorSubmodule k A := by
  constructor <;> intro h
  · simpa using add_mem h (mul_sub_mul_mem_commutatorSubmodule k A y x)
  · simpa using add_mem h (mul_sub_mul_mem_commutatorSubmodule k A x y)

variable {k A} in
/-- A linear map kills the commutator submodule exactly when it is invariant under exchanging the
two factors of a product.  The target need only be an additive monoid. -/
theorem commutatorSubmodule_le_ker_iff {M : Type*} [AddCommMonoid M] [Module k M]
    (f : A →ₗ[k] M) :
    commutatorSubmodule k A ≤ LinearMap.ker f ↔ ∀ x y : A, f (x * y) = f (y * x) := by
  refine commutatorSubmodule_le_iff.trans (forall₂_congr fun x y => ?_)
  rw [LinearMap.mem_ker]
  constructor <;> intro h
  · rw [← sub_add_cancel (x * y) (y * x), map_add, h, zero_add]
  · rw [sub_eq_add_neg, map_add, h, ← map_add, add_neg_cancel, map_zero]

variable {k A} in
/-- A multiplicative linear map, such as an algebra homomorphism, carries the commutator submodule
into the commutator submodule. -/
theorem map_mem_commutatorSubmodule {B F : Type*} [NonUnitalNonAssocRing B] [Module k B]
    [FunLike F A B] [MulHomClass F A B] [LinearMapClass F k A B] (f : F) {x : A}
    (hx : x ∈ commutatorSubmodule k A) : f x ∈ commutatorSubmodule k B := by
  have hle : commutatorSubmodule k A ≤ (commutatorSubmodule k B).comap (f : A →ₗ[k] B) :=
    commutatorSubmodule_le_iff.2 fun x y => by simp
  exact hle hx

variable {k A} in
/-- A non-unital ring homomorphism carries the commutator submodule over `k` into the commutator
submodule over any semiring `l`, whenever `k` acts associatively and centrally on `A`: each scalar
multiple `r • (a * b - b * a) = (r • a) * b - b * (r • a)` is itself a commutator. -/
theorem map_mem_commutatorSubmodule_of_ringHom {l B F : Type*} [Semiring l]
    [NonUnitalNonAssocRing B] [IsScalarTower k A A] [SMulCommClass k A A] [Module l B]
    [FunLike F A B] [NonUnitalRingHomClass F A B] (f : F) {x : A}
    (hx : x ∈ commutatorSubmodule k A) : f x ∈ commutatorSubmodule l B := by
  suffices ∀ r : k, f (r • x) ∈ commutatorSubmodule l B by simpa using this 1
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hz
    intro r
    have hr : r • (a * b - b * a) = (r • a) * b - b * (r • a) := by
      rw [smul_sub, smul_mul_assoc, mul_smul_comm]
    rw [hr, map_sub, map_mul, map_mul]
    exact mul_sub_mul_mem_commutatorSubmodule l B (f (r • a)) (f b)
  | zero => intro _; simp
  | add y z _ _ hy hz => intro r; rw [smul_add, map_add]; exact add_mem (hy r) (hz r)
  | smul s y _ hy => intro r; rw [smul_smul]; exact hy (r * s)

end Semiring

/-- The **cyclic quotient** `A / [A, A]`.  Its elements are cyclic classes; for a path algebra,
cyclic derivatives, and hence the three-dimensional Ginzburg differential, depend only on such a
class. -/
abbrev cyclicQuotient [Ring k] [Module k A] := A ⧸ commutatorSubmodule k A

end TauCeti
