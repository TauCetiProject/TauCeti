/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Coinvariants
public import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.Basic

/-!
# Quotients of general linear groups by faithfully represented reductive groups

Let `G` be an affine group of finite type over a field `k` of characteristic zero, and let
`ρ : G → GLₙ` be a faithful representation, given by a comodule `M` with a basis `b` indexed by
`Fin n`. Faithfulness says that the coordinate morphism `ρ* : O(GLₙ) ⟶ O(G)` is surjective, so
`ρ` identifies `G` with the closed subgroup of `GLₙ` cut out by the kernel of `ρ*`.

When `G` is reductive, the fppf homogeneous quotient `GLₙ/G` is the affine scheme
`Spec O(GLₙ)^G`. Here `O(GLₙ)^G` is the algebra of functions `f` on `GLₙ` invariant under right
translation by `G`, that is, `(id ⊗ ρ*) (Δ f) = f ⊗ 1`
(`TauCeti.HopfIdeal.mem_coinvariants_ker_iff`). The quotient map restricts points of `GLₙ` to
these invariants, and `TauCeti.HopfIdeal.coinvariantsPointsHomEquiv` gives its universal
property. This is the affine direction of Matsushima's criterion applied to the ambient group
`GLₙ`.

## Main declarations

* `TauCeti.Comodule.isIso_fppfHomogeneousQuotientToCoinvariantsPoints_ker_coordinateBialgHom`:
  for a faithful representation of a reductive group in characteristic zero, restriction to the
  invariants identifies `GLₙ/G` with the sheaf of points of `Spec O(GLₙ)^G`.

## References

* Y. Matsushima, *Espaces homogènes de Stein des groupes de Lie complexes*, Nagoya Math. J.
  **16** (1960), 205–218.
* J. S. Milne, *Algebraic Groups* (2017), §5.c and Chapter 12.
-/

public section

open CategoryTheory Module

namespace TauCeti.Comodule

universe u

variable {k H M : Type u} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommMonoid M] [Module k M] [Comodule k H M] {n : ℕ}

/-- **`GLₙ/G` is affine for a faithful reductive representation.** Let `G` be a reductive group
over a field of characteristic zero and `ρ : G → GLₙ` a faithful representation with coordinate
morphism `ρ* : O(GLₙ) ⟶ O(G)`. Restriction to the functions on `GLₙ` invariant under right
translation by `G` identifies the fppf homogeneous quotient `GLₙ/G` with the sheaf of points of
`Spec O(GLₙ)^G`. -/
theorem isIso_fppfHomogeneousQuotientToCoinvariantsPoints_ker_coordinateBialgHom
    (b : Basis (Fin n) k M) (hM : IsFaithful (k := k) (H := H) (V := M))
    (hH : reductiveCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.of k H)) :
    IsIso (HopfIdeal.fppfHomogeneousQuotientToCoinvariantsPoints
      (HopfIdeal.ker (coordinateBialgHom (H := H) b))) :=
  HopfIdeal.isIso_fppfHomogeneousQuotientToCoinvariantsPoints_ker_of_reductive
    (FiniteTypeCommHopfAlgCat.ofHom (coordinateBialgHom (H := H) b))
    ((coordinateBialgHom_surjective_iff_isFaithful b).mpr hM) hH

end TauCeti.Comodule
