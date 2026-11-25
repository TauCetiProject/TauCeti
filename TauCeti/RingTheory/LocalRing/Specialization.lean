/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Module
public import TauCeti.LinearAlgebra.TensorProduct.Range
import TauCeti.LinearAlgebra.Submodule.Compl

/-!
# Ranks of split images under specialization over a local ring

Let `R` be a local ring, for instance the ring of rational functions in a parameter `t` that are
regular at a point `τ`. Its residue field is the field of coefficients specialized at `t = τ`, and
when `R` is a domain its fraction field is the field of generic coefficients. A linear map `f`
between finite free `R`-modules extends to both fields, and its two ranks can differ:
multiplication by `t - τ` on `R` has rank one generically and rank zero at `τ`. Specialization
only bounds the rank of `f` above by its generic rank.

The two ranks agree when the range of `f` is a direct summand of the target. Then the range is a
direct summand of a finite flat module, hence finite free over the local ring `R`
(`Submodule.finite_free_of_isCompl`), and its extension of scalars to a nontrivial commutative
`R`-algebra `A` is the range of `f.baseChange A`, of the same rank
(`LinearMap.finrank_range_baseChange_of_isComplemented`). In particular, an idempotent
endomorphism `E` of a finite flat `R`-module `L` has the same rank after extension of scalars to
every nontrivial commutative `R`-algebra (`LinearMap.IsIdempotentElem.finrank_range_baseChange`),
and when `R` is a domain its ranks over the fraction field and over the residue field agree. This
is the constancy of dimension behind specialization arguments, such as Goodman–Wenzl's
classification of the tensor ideals of the Temperley–Lieb category, where `E(x) = e x f` for
idempotents `e` and `f` of a generic algebra that can be evaluated at `τ`. That `E` is an
endomorphism of the lattice `L` is essential: the map `x ↦ e x f` need not preserve the span of an
arbitrary set of diagrams, and the dimensions of `e L f` before and after specialization can then
differ.

For a map `f` from a finite free `R`-module into a finite flat `R`-module whose range is a direct
summand, injectivity is also insensitive to specialization: for every nontrivial commutative
`R`-algebra `A`, `f.baseChange A` is injective exactly when `f` is
(`LinearMap.baseChange_injective_iff_of_isComplemented_of_isLocalRing`). So when `R` is a domain, a
map that is injective generically stays injective at `τ`.

## Main results

* `LinearMap.IsIdempotentElem.finrank_range_baseChange`: the rank of an idempotent endomorphism of
  a finite flat module over a local ring does not change under extension of scalars to a
  nontrivial commutative algebra.
* `LinearMap.IsIdempotentElem.finrank_range_baseChange_fractionRing_eq_residueField`: its ranks
  over the total ring of fractions (the fraction field, for a local domain) and over the residue
  field agree.
* `LinearMap.baseChange_injective_iff_of_isComplemented_of_isLocalRing`: a linear map from a
  finite free module into a finite flat module over a local ring, with complemented range, is
  injective after extension of scalars to a nontrivial commutative algebra if and only if it is
  injective.

## References

* F. M. Goodman and H. Wenzl, *Ideals in the Temperley–Lieb category*, appendix to
  M. H. Freedman, *A magnetic model with a possible Chern–Simons phase*, Comm. Math. Phys. 234
  (2003), 129–183, Section 1.
-/

public section

open Module

namespace LinearMap

variable {R M N : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Flat R N]

/-- **Constancy of dimension.** An idempotent endomorphism `E` of a finite flat module over a
local ring `R` has the same rank after extension of scalars to every nontrivial commutative
`R`-algebra `A`. -/
theorem IsIdempotentElem.finrank_range_baseChange {E : Module.End R N} (hE : IsIdempotentElem E)
    (A : Type*) [CommSemiring A] [Nontrivial A] [Algebra R A] :
    finrank A (range (E.baseChange A)) = finrank R (range E) := by
  have := (Submodule.finite_free_of_isCompl _ (IsIdempotentElem.isCompl hE)).2
  exact E.finrank_range_baseChange_of_isComplemented ⟨_, IsIdempotentElem.isCompl hE⟩ A

/-- **The generic and the special rank of an idempotent agree.** An idempotent endomorphism of a
finite flat module over a local ring `R` has the same rank over the total ring of fractions
`FractionRing R`, which is the fraction field when `R` is a domain, and over the residue field of
`R`. -/
theorem IsIdempotentElem.finrank_range_baseChange_fractionRing_eq_residueField
    {E : Module.End R N} (hE : IsIdempotentElem E) :
    finrank (FractionRing R) (range (E.baseChange (FractionRing R))) =
      finrank (IsLocalRing.ResidueField R) (range (E.baseChange (IsLocalRing.ResidueField R))) := by
  rw [IsIdempotentElem.finrank_range_baseChange hE, IsIdempotentElem.finrank_range_baseChange hE]

/-- **Injectivity of a map with split range is insensitive to specialization.** A linear map
`f` from a finite free module into a finite flat module over a local ring `R`, whose range is
a direct summand, is injective after extension of scalars to a nontrivial commutative `R`-algebra
`A` if and only if it is injective. So when `R` is a domain, `f` is injective over the fraction
field of `R` exactly when it is injective over the residue field. -/
theorem baseChange_injective_iff_of_isComplemented_of_isLocalRing [Module.Finite R M]
    [Module.Free R M] (f : M →ₗ[R] N) (hf : IsComplemented (range f)) (A : Type*)
    [CommSemiring A] [Nontrivial A] [Algebra R A] :
    Function.Injective (f.baseChange A) ↔ Function.Injective f := by
  obtain ⟨q, hq⟩ := hf
  have := (Submodule.finite_free_of_isCompl _ hq).2
  exact f.baseChange_injective_iff_of_isComplemented ⟨q, hq⟩ A

end LinearMap
