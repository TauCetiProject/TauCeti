/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective

/-!
# Projectivity along a tower of scalars

If `S` is a projective `R`-module and `M` is a projective `S`-module, compatibly with the
`R`-actions, then `M` is a projective `R`-module: `M` is a direct summand of a free `S`-module,
which is a direct sum of copies of the projective `R`-module `S`.

No commutativity is assumed, and `S` need not be an `R`-algebra: it suffices that `R` acts on `S`
compatibly with multiplication on the left. This is the situation of a subring that is not central,
for instance the group algebra `A[H]` of a subgroup acting on `A[G]` by left multiplication, and is
how a projective `A[G]`-module is restricted to a projective `A[H]`-module.

## Main results

* `Module.Projective.trans`: projectivity is transitive along a scalar tower.
-/

public section

namespace Module.Projective

variable {R S M : Type*} [Semiring R] [Semiring S] [Module R S] [IsScalarTower R S S]
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- **Projectivity is transitive along a scalar tower.** A projective module over a ring `S` that is
itself projective as a left `R`-module is projective over `R`. -/
theorem trans [Module.Projective R S] [Module.Projective S M] : Module.Projective R M := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective S M›
  have : Module.Projective R (M →₀ S) :=
    .of_equiv' (finsuppLequivDFinsupp (M := S) R).symm
  refine .of_split (s.restrictScalars R) ((Finsupp.linearCombination S id).restrictScalars R) ?_
  ext x
  exact DFunLike.congr_fun hs x

end Module.Projective
