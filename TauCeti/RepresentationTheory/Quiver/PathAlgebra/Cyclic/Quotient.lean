/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic

/-!
# The cyclic quotient of a path algebra

For a quiver `Q` over a commutative ring `k`, the **commutator submodule** of its path algebra is
the `k`-span of the additive commutators `x * y - y * x`.  The quotient by this submodule is the
**cyclic quotient**

```text
kQ / [kQ, kQ].
```

Its elements are cyclic classes.  In particular, a potential for the three-dimensional Ginzburg
construction is naturally a cyclic class rather than a chosen representative in `kQ`.  This file
provides the quotient and its elementary universal property; cyclic derivatives are descended to
it in `TauCeti.RepresentationTheory.Quiver.PathAlgebra.Cyclic.Derivative`.

## Main definitions

* `TauCeti.PathAlgebra.commutatorSubmodule`: the span of additive commutators in a path algebra.
* `TauCeti.PathAlgebra.cyclicQuotient`: the quotient `kQ / [kQ, kQ]`.

## Main results

* `TauCeti.PathAlgebra.commutatorSubmodule_le_ker_iff`: a linear map kills the commutator
  submodule exactly when it takes equal values on `x * y` and `y * x`.

## References

* J.-L. Loday, *Cyclic Homology*, Section 1.1, for the identification
  `HH₀(A) = A / [A, A]`.
-/

public section

namespace TauCeti

namespace PathAlgebra

universe u v w

variable (k : Type w) [CommRing k] (Q : Type u) [Quiver.{v} Q]

/-- The `k`-submodule of the path algebra `kQ` spanned by the additive commutators
`x * y - y * x`. -/
noncomputable def commutatorSubmodule : Submodule k (pathAlgebra k Q) :=
  Submodule.span k (Set.range fun p : pathAlgebra k Q × pathAlgebra k Q =>
    p.1 * p.2 - p.2 * p.1)

/-- Every additive commutator belongs to the commutator submodule. -/
theorem mul_sub_mul_mem_commutatorSubmodule (x y : pathAlgebra k Q) :
    x * y - y * x ∈ commutatorSubmodule k Q :=
  Submodule.subset_span ⟨(x, y), rfl⟩

/-- A linear map kills the commutator submodule exactly when it is invariant under exchanging the
two factors of a product. -/
theorem commutatorSubmodule_le_ker_iff {M : Type*} [AddCommGroup M] [Module k M]
    (f : pathAlgebra k Q →ₗ[k] M) :
    commutatorSubmodule k Q ≤ LinearMap.ker f ↔
      ∀ x y : pathAlgebra k Q, f (x * y) = f (y * x) := by
  rw [commutatorSubmodule, Submodule.span_le, Set.range_subset_iff]
  constructor
  · intro h x y
    have hzero := LinearMap.mem_ker.1 (h (x, y))
    rwa [map_sub, sub_eq_zero] at hzero
  · intro h p
    apply LinearMap.mem_ker.2
    rw [map_sub, h, sub_self]

/-- The **cyclic quotient** `kQ / [kQ, kQ]` of a path algebra.  Its elements are cyclic classes;
cyclic derivatives, and hence the three-dimensional Ginzburg differential, depend only on such a
class. -/
abbrev cyclicQuotient := pathAlgebra k Q ⧸ commutatorSubmodule k Q

end PathAlgebra

end TauCeti
