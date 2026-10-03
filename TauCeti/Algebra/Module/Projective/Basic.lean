/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Projectivity along a tower of scalars

A projective module over an `R`-algebra `A` that is itself projective over `R` is projective over
`R`: it is a direct summand of a free `A`-module, which is a direct sum of copies of `A`. This is
the projective counterpart of `Module.Finite.trans`; for instance, a projective module over the
group algebra `R[G]` of a group is projective over `R`.

## Main results

* `Module.Projective.trans`: projectivity is transitive along `R → A`.
-/

public section

/-- **Projectivity is transitive.** A projective module over an `R`-algebra `A` that is projective
over `R` is projective over `R`. -/
theorem Module.Projective.trans {R : Type*} (A P : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] [AddCommMonoid P] [Module R P] [Module A P] [IsScalarTower R A P]
    [Module.Projective R A] [Module.Projective A P] : Module.Projective R P := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective A P›
  -- `P` is a direct summand of `P →₀ A`, a direct sum of copies of `A`.
  have : Module.Projective R (P →₀ A) := .of_equiv (finsuppLequivDFinsupp R).symm
  exact .of_split (s.restrictScalars R) ((Finsupp.linearCombination A id).restrictScalars R)
    (LinearMap.ext fun x ↦ congr($hs x))
