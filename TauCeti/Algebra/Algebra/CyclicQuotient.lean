/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
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
* `TauCeti.commutatorSubmodule_le_ker_iff`: a linear map kills the commutator submodule exactly
  when it takes equal values on `x * y` and `y * x`.
* `TauCeti.map_mem_commutatorSubmodule` and `TauCeti.map_mem_commutatorSubmodule_of_ringHom`: a
  multiplicative linear map, and also any non-unital ring homomorphism from a ring whose scalar
  action commutes with multiplication, carries commutators to commutators.
* `TauCeti.trace_map_eq_zero_of_mem_commutatorSubmodule`: the trace of a matrix representation,
  with entries in any commutative ring that is a module over the scalars, vanishes on the
  commutator submodule.  A representation in which an element has nonzero trace therefore shows
  that its cyclic class is nonzero.

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
theorem mul_sub_mul_mem_commutatorSubmodule (x y : A) :
    x * y - y * x ∈ commutatorSubmodule k A :=
  Submodule.subset_span ⟨(x, y), rfl⟩

variable {k A} in
/-- The commutator submodule is closed under negation even when `k` is only a semiring: the
negative of a commutator `x * y - y * x` is the commutator `y * x - x * y`. -/
theorem neg_mem_commutatorSubmodule {x : A} (hx : x ∈ commutatorSubmodule k A) :
    -x ∈ commutatorSubmodule k A := by
  -- negation, as a `k`-linear map, sends each spanning commutator to a commutator
  suffices commutatorSubmodule k A ≤ (commutatorSubmodule k A).comap (-LinearMap.id) by
    simpa using this hx
  refine Submodule.span_le.2 (Set.range_subset_iff.2 fun p => ?_)
  simpa using mul_sub_mul_mem_commutatorSubmodule k A p.2 p.1

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
two factors of a product. -/
theorem commutatorSubmodule_le_ker_iff {M : Type*} [AddCommGroup M] [Module k M]
    (f : A →ₗ[k] M) :
    commutatorSubmodule k A ≤ LinearMap.ker f ↔ ∀ x y : A, f (x * y) = f (y * x) := by
  rw [commutatorSubmodule, Submodule.span_le, Set.range_subset_iff]
  simp only [Prod.forall, SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero]

variable {k A} in
/-- A multiplicative linear map, such as an algebra homomorphism, carries the commutator submodule
into the commutator submodule. -/
theorem map_mem_commutatorSubmodule {B F : Type*} [NonUnitalNonAssocRing B] [Module k B]
    [FunLike F A B] [MulHomClass F A B] [LinearMapClass F k A B] (f : F) {x : A}
    (hx : x ∈ commutatorSubmodule k A) : f x ∈ commutatorSubmodule k B := by
  have hle : commutatorSubmodule k A ≤ (commutatorSubmodule k B).comap (f : A →ₗ[k] B) := by
    rw [commutatorSubmodule, Submodule.span_le, Set.range_subset_iff]
    rintro ⟨x, y⟩
    simpa using mul_sub_mul_mem_commutatorSubmodule k B (f x) (f y)
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

variable {k A} in
/-- **The trace of a matrix representation kills commutators**: if `f` is a multiplicative
`k`-linear map to square matrices over a (not necessarily unital or associative) commutative ring
`R` which is a `k`-module, then the trace of `f x` vanishes for every `x` in the commutator
submodule. -/
theorem trace_map_eq_zero_of_mem_commutatorSubmodule {n R F : Type*} [Fintype n]
    [NonUnitalNonAssocCommRing R] [Module k R] [FunLike F A (Matrix n n R)]
    [MulHomClass F A (Matrix n n R)] [LinearMapClass F k A (Matrix n n R)] (f : F) {x : A}
    (hx : x ∈ commutatorSubmodule k A) : (f x).trace = 0 :=
  (commutatorSubmodule_le_ker_iff (Matrix.traceLinearMap n k R)).2
    (fun X Y => Matrix.trace_mul_comm X Y) (map_mem_commutatorSubmodule f hx)

end Semiring

/-- The **cyclic quotient** `A / [A, A]`.  Its elements are cyclic classes; for a path algebra,
cyclic derivatives, and hence the three-dimensional Ginzburg differential, depend only on such a
class. -/
abbrev cyclicQuotient [Ring k] [Module k A] := A ⧸ commutatorSubmodule k A

end TauCeti
