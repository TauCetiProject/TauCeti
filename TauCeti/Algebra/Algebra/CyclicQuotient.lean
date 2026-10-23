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

* `TauCeti.commutatorSubmodule_le_ker_iff`: a linear map kills the commutator submodule exactly
  when it takes equal values on `x * y` and `y * x`.

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
/-- A linear map kills the commutator submodule exactly when it is invariant under exchanging the
two factors of a product. -/
theorem commutatorSubmodule_le_ker_iff {M : Type*} [AddCommGroup M] [Module k M]
    (f : A →ₗ[k] M) :
    commutatorSubmodule k A ≤ LinearMap.ker f ↔ ∀ x y : A, f (x * y) = f (y * x) := by
  rw [commutatorSubmodule, Submodule.span_le, Set.range_subset_iff]
  constructor
  · intro h x y
    have hzero := LinearMap.mem_ker.1 (h (x, y))
    rwa [map_sub, sub_eq_zero] at hzero
  · intro h p
    apply LinearMap.mem_ker.2
    rw [map_sub, h, sub_self]

end Semiring

/-- The **cyclic quotient** `A / [A, A]`.  Its elements are cyclic classes; for a path algebra,
cyclic derivatives, and hence the three-dimensional Ginzburg differential, depend only on such a
class. -/
abbrev cyclicQuotient [Ring k] [Module k A] := A ⧸ commutatorSubmodule k A

end TauCeti
