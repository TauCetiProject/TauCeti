/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normalizer.Connected
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Components

/-!
# The normalizer modulo the centralizer is finite étale

Let `D(X)` be a closed diagonalizable subgroup of a finite-type affine group over an
algebraically closed field. If its scheme normalizer is reduced, the represented quotient
of the normalizer by the scheme centralizer is finite étale. In characteristic zero the
reducedness hypothesis follows from Cartier's theorem.

The quotient coordinate algebra is the coinvariant algebra for the centralizer ideal
inside the normalizer. The result describes the full quotient scheme, including when
the diagonalizable subgroup is nonreduced.

For a maximal torus in a reductive group, identifying the centralizer with the torus
turns this quotient into the Weyl group scheme. That identification is a separate result.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§4.a and 21.1.
* T. A. Springer, *Linear Algebraic Groups*, §7.1.
-/

public section

namespace BialgHom

open TauCeti

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H : FiniteTypeCommHopfAlgCat.{u, u} k} {X : Type u} [CommGroup X]
  (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π)
  [IsReduced (FiniteTypeCommHopfAlgCat.quotient H (normalizerHopfIdeal π hπ))]

/- Normality is supplied by
`BialgHom.isNormal_map_centralizerHopfIdeal_mkBialgHom_normalizerHopfIdeal`.
The containment below uses `Normalizer.Connected`, so the component-coinvariant
theorems apply to the centralizer inside the normalizer. -/
/-- Inside the scheme normalizer, its identity component is contained in the
centralizer. The inequality is reversed on defining ideals. -/
private theorem map_centralizerHopfIdeal_le_identityComponentHopfIdeal :
    (centralizerHopfIdeal π).map
        (Bialgebra.Quotient.mkBialgHom (normalizerHopfIdeal π hπ).toIdeal) ≤
      HopfAlgebra.identityComponentHopfIdeal (k := k)
        (H := FiniteTypeCommHopfAlgCat.quotient H (normalizerHopfIdeal π hπ)) := by
  apply (HopfIdeal.map_le_iff_le_comapOfSurjective
    (CommHopfAlgCat.mkQuotient_surjective H.obj (normalizerHopfIdeal π hπ))).mpr
  intro x hx
  rw [HopfIdeal.mem_comapOfSurjective]
  exact (HopfIdeal.mem_identityComponent _ x).mp
    (centralizerHopfIdeal_le_identityComponent_normalizerHopfIdeal π hπ hx)

/-- The coordinate algebra of the scheme normalizer modulo the scheme centralizer
is finite-dimensional. No reducedness or smoothness of the ambient group is required. -/
theorem moduleFinite_coinvariants_centralizer_normalizer :
    Module.Finite k
      ((centralizerHopfIdeal π).map
        (Bialgebra.Quotient.mkBialgHom (normalizerHopfIdeal π hπ).toIdeal)).coinvariants :=
  FiniteTypeCommHopfAlgCat.moduleFinite_coinvariants_of_le_identityComponentHopfIdeal
    (FiniteTypeCommHopfAlgCat.quotient H (normalizerHopfIdeal π hπ)) _
    (map_centralizerHopfIdeal_le_identityComponentHopfIdeal π hπ)

/-- The represented quotient of the scheme normalizer by the scheme centralizer
is étale, retaining the full subgroup schemes even when `D(X)` is nonreduced. -/
theorem algebraEtale_coinvariants_centralizer_normalizer :
    Algebra.Etale k
      ((centralizerHopfIdeal π).map
        (Bialgebra.Quotient.mkBialgHom (normalizerHopfIdeal π hπ).toIdeal)).coinvariants :=
  FiniteTypeCommHopfAlgCat.algebraEtale_coinvariants_of_le_identityComponentHopfIdeal
    (FiniteTypeCommHopfAlgCat.quotient H (normalizerHopfIdeal π hπ)) _
    (map_centralizerHopfIdeal_le_identityComponentHopfIdeal π hπ)

end BialgHom
