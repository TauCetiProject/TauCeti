/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Zero

import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# The roots of a characteristic polynomial in an extension field

The *characteristic roots* of an endomorphism `f` of a free module of finite rank over `R` are
the roots of its characteristic polynomial in a field `L` over `R`, counted with multiplicity:
the multiset `f.charpoly.aroots L`. They are the eigenvalues of `f` after extension of scalars
to `L`, and the multiplicity of a root `μ` is the dimension of the maximal generalized eigenspace
of `f ⊗ L` at `μ`, so it does not see whether `f ⊗ L` is semisimple. Over an algebraically closed
field there are exactly as many characteristic roots as the rank of the module.

This is the multiset of eigenvalues with multiplicities in the sense of Deligne, through which
the weights of a Frobenius module are defined.

## Main results

* `LinearMap.card_aroots_charpoly`: over an algebraically closed field, the number of
  characteristic roots, counted with multiplicity, is the rank of the module.
* `LinearMap.finrank_maxGenEigenspace_baseChange_eq`: the multiplicity of a characteristic root
  `μ ∈ L` is the dimension of the maximal generalized eigenspace of `f ⊗ L` at `μ`.
* `Module.End.hasEigenvalue_baseChange_iff`: the eigenvalues of `f ⊗ L` are the characteristic
  roots of `f` in `L`.

## References

* P. Deligne, *La conjecture de Weil. I*, Publ. Math. IHÉS 43 (1974), §2, (2.6).
-/

public section

open Module Polynomial

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M] (f : Module.End R M) {L : Type*} [Field L] [Algebra R L]

namespace LinearMap

/-- Over an algebraically closed field `Ω`, the characteristic polynomial of an endomorphism of a
free module of rank `d` has exactly `d` roots, counted with multiplicity. -/
theorem card_aroots_charpoly (Ω : Type*) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] :
    (f.charpoly.aroots Ω).card = finrank R M := by
  have := (algebraMap R Ω).domain_nontrivial
  rw [IsAlgClosed.card_aroots_eq_natDegree_of_isUnit_leadingCoeff
    (by simp [f.charpoly_monic.leadingCoeff]), f.charpoly_natDegree]

/-- The multiplicity of `μ` as a root in a field `L` of the characteristic polynomial of `f` is
the dimension of the maximal generalized eigenspace at `μ` of the extension of scalars `f ⊗ L`. -/
theorem finrank_maxGenEigenspace_baseChange_eq [DecidableEq L] (μ : L) :
    finrank L (Module.End.maxGenEigenspace (f.baseChange L) μ) =
      (f.charpoly.aroots L).count μ := by
  rw [finrank_maxGenEigenspace_eq, charpoly_baseChange, aroots_def, count_roots]

end LinearMap

namespace Module.End

/-- The eigenvalues of the extension of scalars `f ⊗ L` are the roots in `L` of the
characteristic polynomial of `f`. -/
theorem hasEigenvalue_baseChange_iff {μ : L} :
    HasEigenvalue (f.baseChange L) μ ↔ μ ∈ f.charpoly.aroots L := by
  rw [hasEigenvalue_iff_isRoot_charpoly, LinearMap.charpoly_baseChange, aroots_def,
    mem_roots ((f.charpoly_monic.map _).ne_zero)]

end Module.End
