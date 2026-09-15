/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Derivation
public import TauCeti.Algebra.Lie.F4.ShortRoot.QuotientCoordinates

/-!
# The numbered simple root generators of type F4 differentiate the multiplication

The Lie algebra of type `F₄` acts on its twenty-six-dimensional module by derivations of the
invariant symmetric multiplication; equivalently, that multiplication is a morphism of modules from
the symmetric square. This file records that for the eight numbered simple root generators, over
the integers.

A generator carries each weight vector of the basis to a multiple of a weight vector, and each
product of two weight vectors is a combination of at most two of them, so the derivation equation
of a generator is a finite family of relations between the structure constants of the
multiplication and the coefficients of the generator, one for each pair of a column of the
multiplication and a matrix entry. Those relations are what
`TauCeti.F4ShortRoot.isDerivation_rootMatrix_of_entries` asks for, and they are the same family for
all eight generators, and the four numbered raising generators are treated in
`TauCeti.Algebra.Lie.F4.ShortRoot.RaisingDerivation`, the four lowering ones in
`TauCeti.Algebra.Lie.F4.ShortRoot.LoweringDerivation`.

## Main results

* `TauCeti.F4ShortRoot.isDerivation_rootMatrix_of_entries`: the derivation property of a numbered
  simple root generator, reduced to its entrywise form.

## References

* N. Jacobson, *Exceptional Lie Algebras*, Lecture Notes in Pure and Applied Mathematics **1**,
  Marcel Dekker (1971), §I.4.
-/

public section

open Matrix

namespace TauCeti.F4ShortRoot

/-- **The derivation equations of a numbered simple root generator, entry by entry.** The `(p, q)`
entry of the equation on the `c`th column relates the structure constants of the multiplication at
the target of the generator to the structure constants at its source. -/
theorem isDerivation_rootMatrix_of_entries (k : Fin 4 ⊕ Fin 4)
    (h : ∀ c : Fin 26, ∀ p : Fin 26 × Fin 26,
      (if p.1 = rootStepTarget k (multTargetOne c p.2) then
            rootStepCoeff k (multTargetOne c p.2) else 0) * multCoeffOne c p.2 +
          (if p.1 = rootStepTarget k (multTargetTwo c p.2) then
            rootStepCoeff k (multTargetTwo c p.2) else 0) * multCoeffTwo c p.2 -
          ((if p.1 = multTargetOne c (rootStepTarget k p.2) then
                multCoeffOne c (rootStepTarget k p.2) else 0) +
              (if p.1 = multTargetTwo c (rootStepTarget k p.2) then
                multCoeffTwo c (rootStepTarget k p.2) else 0)) * rootStepCoeff k p.2 =
        rootStepCoeff k c *
          ((if p.1 = multTargetOne (rootStepTarget k c) p.2 then
              multCoeffOne (rootStepTarget k c) p.2 else 0) +
            (if p.1 = multTargetTwo (rootStepTarget k c) p.2 then
              multCoeffTwo (rootStepTarget k c) p.2 else 0))) :
    IsDerivation (rootMatrix k) := by
  rw [isDerivation_int_iff]
  intro c
  rw [Matrix.IsStep.sum_smul (isStep_rootMatrix k)]
  ext p q
  rw [Matrix.sub_apply,
    Matrix.IsDoubleStep.mul_apply (isDoubleStep_multiplicationOperator c) (rootMatrix k) p q,
    Matrix.IsStep.mul_apply (isStep_rootMatrix k) (multiplicationOperator c) p q,
    Matrix.smul_apply, smul_eq_mul, (isStep_rootMatrix k).apply, (isStep_rootMatrix k).apply,
    multiplicationOperator_apply, multiplicationOperator_apply]
  exact h c (p, q)

end TauCeti.F4ShortRoot
