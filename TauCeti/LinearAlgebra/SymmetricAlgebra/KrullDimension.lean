/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.KrullDimension.Polynomial
import TauCeti.RingTheory.KrullDimension.FiniteType

/-!
# Krull dimension of the symmetric algebra of a finite-dimensional vector space

Let `M` be a finite-dimensional vector space over a field `k`. A basis of `M` identifies the
symmetric algebra `Sym M` with a polynomial ring over `k` in `finrank k M` variables
(`SymmetricAlgebra.equivMvPolynomial`). Transporting the corresponding facts about polynomial rings,
`Sym M` has Krull dimension `finrank k M`, and so does the local ring at each of its maximal ideals.
In particular this applies to the irrelevant ideal of elements with zero constant term, the ideal of
the origin when `M = V*`, so the local ring of the affine space `V` at the origin has dimension
`dim V`.

## Main results

* `TauCeti.SymmetricAlgebra.ringKrullDim_eq_finrank`: `Sym M` has Krull dimension `finrank k M`.
* `TauCeti.SymmetricAlgebra.height_eq_finrank_of_isMaximal`: every maximal ideal of `Sym M` has
  height `finrank k M`.
-/

public section

namespace TauCeti.SymmetricAlgebra

variable (k M : Type*) [Field k] [AddCommGroup M] [Module k M] [FiniteDimensional k M]

/-- The symmetric algebra of a finite-dimensional vector space has Krull dimension the dimension of
the space. -/
theorem ringKrullDim_eq_finrank :
    ringKrullDim (SymmetricAlgebra k M) = Module.finrank k M := by
  let b := Module.Free.chooseBasis k M
  rw [ringKrullDim_eq_of_ringEquiv (SymmetricAlgebra.equivMvPolynomial b).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    zero_add, Module.finrank_eq_nat_card_basis b]

variable {k M} in
/-- Every maximal ideal of the symmetric algebra of a finite-dimensional vector space has height
the dimension of the space. -/
theorem height_eq_finrank_of_isMaximal (P : Ideal (SymmetricAlgebra k M)) [P.IsMaximal] :
    P.height = Module.finrank k M := by
  let b := Module.Free.chooseBasis k M
  let e := (SymmetricAlgebra.equivMvPolynomial b).toRingEquiv
  have : (P.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
  rw [← e.height_map P, MvPolynomial.height_eq_natCard_of_isMaximal,
    Module.finrank_eq_nat_card_basis b]

end TauCeti.SymmetricAlgebra
