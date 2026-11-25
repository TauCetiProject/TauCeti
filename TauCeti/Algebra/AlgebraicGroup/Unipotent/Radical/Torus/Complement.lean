/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.ClosedImmersion
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Diagonalizable.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.SemidirectProduct
import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Connected.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected
import TauCeti.RingTheory.TensorProduct.Reduced

/-!
# Tori as complements to the unipotent radical

Let `G` be a reduced affine group of finite type over an algebraically closed field `k`, with
unipotent radical `R_u(G)`. A reduced closed subgroup `D ⊆ G` whose coordinate algebra is spanned
by its group-like elements, for instance a torus, meets `R_u(G)` trivially (`TauCeti.
FiniteTypeCommHopfAlgCat.sup_unipotentRadicalDefiningIdeal_eq_augmentation_of_groupLikeSpanned`),
so the composite `D → G → G ⧸ R_u(G)` has trivial scheme-theoretic kernel. As `D` is reduced,
this homomorphism is a closed immersion
(`TauCeti.FiniteTypeCommHopfAlgCat.coinvariantsι_comp_mkQuotient_surjective`): in coordinates,
the map from the right coinvariants `O(G ⧸ R_u(G))` to `O(D)` is surjective.

If moreover `G` is connected, a torus `T ⊆ G` is smooth and connected, so `T` maps
isomorphically onto `G ⧸ R_u(G)` as soon as `dim Lie(G ⧸ R_u(G)) ≤ dim Lie(T)`
(`TauCeti.FiniteTypeCommHopfAlgCat.isIso_coinvariantsι_comp_mkQuotient`). Multiplication
`R_u(G) ⋊ T → G` is then an isomorphism
(`TauCeti.FiniteTypeCommHopfAlgCat.isIso_productMapOfNormal_unipotentRadical_of_isIso`).

For a connected group with solvable rational points, `G ⧸ R_u(G)` is a torus
(`TauCeti.FiniteTypeCommHopfAlgCat.torus_coinvariants_unipotentRadical`), and the last statement
is the decomposition `G = G_u ⋊ T` of Milne, Theorem 16.33(d), for every torus `T` of the
dimension of `G ⧸ G_u`. Solvability is not assumed here: the hypotheses force `G ⧸ R_u(G)` to be
isomorphic to the torus `T`.

Coordinate arrows reverse the homomorphisms of represented groups: the subgroup `D` or `T` is the
closed subgroup cut out by a Hopf ideal `I` of `O(G)`, and the composite homomorphism is
represented by `coinvariantsι ≫ mkQuotient G I : O(G ⧸ R_u(G)) ⟶ O(G) ⧸ I`.

## Main declarations

In the `TauCeti.FiniteTypeCommHopfAlgCat` namespace:

* `coinvariantsι_unipotentRadical_comp_mkQuotient_surjective_of_groupLikeSpanned`: a reduced
  closed subgroup of a reduced group whose coordinate algebra is spanned by group-like elements,
  such as a torus, maps to `G ⧸ R_u(G)` by a closed immersion.
* `isIso_coinvariantsι_unipotentRadical_comp_mkQuotient_of_torus`: for connected `G`, a torus
  whose Lie algebra is at least as large as that of `G ⧸ R_u(G)` maps isomorphically onto
  `G ⧸ R_u(G)`.
* `isIso_productMapOfNormal_unipotentRadical_of_torus`: for such a torus `T`, multiplication
  `R_u(G) ⋊ T → G` is an isomorphism.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 16.33, pp. 335–336.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] (G : FiniteTypeCommHopfAlgCat.{u, u} k)

/-- **A reduced diagonalizable closed subgroup of a reduced group maps to the quotient by the
unipotent radical by a closed immersion**, over an algebraically closed field. If the Hopf ideal
`I` cuts out a reduced closed subgroup `D` whose coordinate algebra is spanned by its group-like
elements, for instance a torus, the coordinate map of the composite `D → G → G ⧸ R_u(G)`, from the
right coinvariants to `O(G) ⧸ I`, is surjective. -/
theorem coinvariantsι_unipotentRadical_comp_mkQuotient_surjective_of_groupLikeSpanned
    [IsReduced G] {I : HopfIdeal k G}
    (hI : DiagonalizableGroup.groupLikeSpannedProperty k (quotient G I))
    [IsReduced (quotient G I)] :
    Function.Surjective
      (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal G) ≫
        CommHopfAlgCat.mkQuotient G.obj I).hom :=
  coinvariantsι_comp_mkQuotient_surjective G _ <|
  kernelHopfIdeal_coinvariantsι_unipotentRadical_comp_mkQuotient_eq_augmentation_of_groupLikeSpanned
    G hI

variable [IsReduced G] [ConnectedSpace (PrimeSpectrum G)]

/-- **A torus of a connected group with Lie algebra at least as large as that of `G ⧸ R_u(G)`
maps isomorphically onto `G ⧸ R_u(G)`**, over an algebraically closed field. Here `G` is reduced
and connected, and the Hopf ideal `I` cuts out a torus `T` with
`dim Lie(G ⧸ R_u(G)) ≤ dim Lie(T)`; then the coordinate map of the composite
`T → G → G ⧸ R_u(G)` is an isomorphism. -/
theorem isIso_coinvariantsι_unipotentRadical_comp_mkQuotient_of_torus
    {I : HopfIdeal k G} (hI : torusCommHopfAlgProperty k (quotient G I))
    (hfinrank :
      letI := (isNormal_unipotentRadicalDefiningIdeal G).isHopfSubalgebra_coinvariants.hopfAlgebra
      Module.finrank k
          (Derivation k (CommHopfAlgCat.coinvariants (isNormal_unipotentRadicalDefiningIdeal G))
            (Bialgebra.CounitAlgebra k
              (CommHopfAlgCat.coinvariants (isNormal_unipotentRadicalDefiningIdeal G)) k)) ≤
        Module.finrank k
          (Derivation k (quotient G I) (Bialgebra.CounitAlgebra k (quotient G I) k))) :
    IsIso (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal G) ≫
      CommHopfAlgCat.mkQuotient G.obj I) := by
  have : Algebra.Smooth k G :=
    (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k G.obj)
  exact isIso_coinvariantsι_comp_mkQuotient G
    ((geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k G.obj).mpr inferInstance) _
    (hI.smooth k _) ((hI.geometricallyConnected k _).connectedSpace)
    (kernelHopfIdeal_coinvariantsι_unipotentRadical_comp_mkQuotient_eq_augmentation_of_torus G hI)
    hfinrank

/-- **`G = R_u(G) ⋊ T`** for a reduced connected group `G` over an algebraically closed field
and a torus `T` with Lie algebra at least as large as that of `G ⧸ R_u(G)` (Milne,
Theorem 16.33(d), for connected solvable `G`): if the Hopf ideal `J` cuts out such a torus,
multiplication `R_u(G) ⋊ T → G` is an isomorphism of affine groups. -/
theorem isIso_productMapOfNormal_unipotentRadical_of_torus
    {J : HopfIdeal k G} (hJ : torusCommHopfAlgProperty k (quotient G J))
    (hfinrank :
      letI := (isNormal_unipotentRadicalDefiningIdeal G).isHopfSubalgebra_coinvariants.hopfAlgebra
      Module.finrank k
          (Derivation k (CommHopfAlgCat.coinvariants (isNormal_unipotentRadicalDefiningIdeal G))
            (Bialgebra.CounitAlgebra k
              (CommHopfAlgCat.coinvariants (isNormal_unipotentRadicalDefiningIdeal G)) k)) ≤
        Module.finrank k
          (Derivation k (quotient G J) (Bialgebra.CounitAlgebra k (quotient G J) k))) :
    IsIso (CommHopfAlgCat.productMapOfNormal G.obj (unipotentRadicalDefiningIdeal G) J
      (isNormal_unipotentRadicalDefiningIdeal G)) := by
  have := isIso_coinvariantsι_unipotentRadical_comp_mkQuotient_of_torus G hJ hfinrank
  exact isIso_productMapOfNormal_unipotentRadical_of_isIso G J

end TauCeti.FiniteTypeCommHopfAlgCat
