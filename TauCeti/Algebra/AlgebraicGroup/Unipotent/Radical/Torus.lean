/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.ClosedImmersion
public import TauCeti.Algebra.AlgebraicGroup.Solvable.UnipotentRadical
import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected

/-!
# Tori mapping isomorphically onto the quotient by the unipotent radical

Let `G` be a reduced connected affine group of finite type with solvable points over an
algebraically closed field `k`, and let `T` be a torus in `G`. The quotient `G ⧸ R_u(G)` by the
unipotent radical is a torus (`torus_coinvariants_unipotentRadical`). This file proves that if
the composite `T → G → G ⧸ R_u(G)` has trivial scheme-theoretic kernel, then it is a closed
immersion, and it is an isomorphism as soon as the Lie algebra of `T` has dimension at least that
of `G ⧸ R_u(G)`. The closed-immersion statement holds for any geometrically reduced `G` of finite
type over any field.

This is the closed-immersion step of the decomposition `G = R_u(G) ⋊ T` for a maximal torus `T`
(Milne, Theorem 16.33(d)). It leaves the dimension count: that a maximal torus has the same
dimension as `G ⧸ R_u(G)`.

Coordinate rings reverse arrows: `O(G ⧸ R_u(G))` is the Hopf subalgebra of right coinvariants,
and the composite is the coordinate map `coinvariantsι ≫ mkQuotient G J`, where `J` cuts out `T`.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.surjective_coinvariantsι_unipotentRadical_comp_mkQuotient`:
  a torus meeting `R_u(G)` trivially maps to `G ⧸ R_u(G)` by a closed immersion.
* `TauCeti.FiniteTypeCommHopfAlgCat.isIso_coinvariantsι_unipotentRadical_comp_mkQuotient`:
  if moreover its Lie dimension is at least that of `G ⧸ R_u(G)`, it maps isomorphically onto
  `G ⧸ R_u(G)`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorems 5.34 and 16.33(d).
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), Theorem 10.6.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] (G : FiniteTypeCommHopfAlgCat.{u, u} k)

/-- **A torus meeting the unipotent radical trivially maps to `G ⧸ R_u(G)` by a closed
immersion**, for a geometrically reduced `G` over any field. If the Hopf ideal `J` cuts out a
torus `T` and the composite `T → G → G ⧸ R_u(G)` has trivial kernel, then its coordinate map
`coinvariantsι ≫ mkQuotient G J` is surjective. -/
theorem surjective_coinvariantsι_unipotentRadical_comp_mkQuotient
    [Algebra.IsGeometricallyReduced k G] {J : HopfIdeal k G}
    (hJ : torusCommHopfAlgProperty k (quotient G J))
    (hker : CommHopfAlgCat.kernelHopfIdeal
        (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal G) ≫
          CommHopfAlgCat.mkQuotient G.obj J) =
      HopfIdeal.augmentation k (CommHopfAlgCat.quotient G.obj J)) :
    Function.Surjective
      (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal G) ≫
        CommHopfAlgCat.mkQuotient G.obj J).hom := by
  let hR := isNormal_unipotentRadicalDefiningIdeal G
  let _ := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
  have : Algebra.FiniteType k (CommHopfAlgCat.coinvariants hR) := hR.finiteType_coinvariants
  have : Algebra.IsGeometricallyReduced k (quotient G J) :=
    (torusCommHopfAlgProperty.geometricallyReduced k _ hJ).isGeometricallyReduced
  exact CommHopfAlgCat.surjective_of_kernelHopfIdeal_eq_augmentation _ hker

variable [IsAlgClosed k] [IsReduced G] [ConnectedSpace (PrimeSpectrum G)]
variable [Group.IsSolvable (WithConv (G →ₐ[k] k))]

/-- **A torus meeting the unipotent radical trivially, of Lie dimension at least that of
`G ⧸ R_u(G)`, maps isomorphically onto `G ⧸ R_u(G)`.** If the Hopf ideal `J` cuts out a torus
`T`, the composite `T → G → G ⧸ R_u(G)` has trivial kernel, and the Lie algebra of `T` has
dimension at least that of `G ⧸ R_u(G)`, then the composite is an isomorphism. -/
theorem isIso_coinvariantsι_unipotentRadical_comp_mkQuotient {J : HopfIdeal k G}
    (hJ : torusCommHopfAlgProperty k (quotient G J))
    (hker : CommHopfAlgCat.kernelHopfIdeal
        (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal G) ≫
          CommHopfAlgCat.mkQuotient G.obj J) =
      HopfIdeal.augmentation k (CommHopfAlgCat.quotient G.obj J))
    (hfinrank :
      letI := (isNormal_unipotentRadicalDefiningIdeal G).isHopfSubalgebra_coinvariants.hopfAlgebra
      Module.finrank k
          (Derivation k (CommHopfAlgCat.coinvariants (isNormal_unipotentRadicalDefiningIdeal G))
            (Bialgebra.CounitAlgebra k
              (CommHopfAlgCat.coinvariants (isNormal_unipotentRadicalDefiningIdeal G)) k)) ≤
        Module.finrank k
          (Derivation k (CommHopfAlgCat.quotient G.obj J)
            (Bialgebra.CounitAlgebra k (CommHopfAlgCat.quotient G.obj J) k))) :
    IsIso (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal G) ≫
      CommHopfAlgCat.mkQuotient G.obj J) := by
  let hR := isNormal_unipotentRadicalDefiningIdeal G
  let _ := hR.isHopfSubalgebra_coinvariants.hopfAlgebra
  have : Algebra.FiniteType k (CommHopfAlgCat.coinvariants hR) := hR.finiteType_coinvariants
  have hQ := torus_coinvariants_unipotentRadical G
  exact CommHopfAlgCat.isIso_of_kernelHopfIdeal_eq_augmentation_of_finrank_le _
    (torusCommHopfAlgProperty.smooth k _ hQ)
    (geometricallyConnectedCommHopfAlgProperty.connectedSpace
      (torusCommHopfAlgProperty.geometricallyConnected k _ hQ))
    (torusCommHopfAlgProperty.smooth k _ hJ)
    (geometricallyConnectedCommHopfAlgProperty.connectedSpace
      (torusCommHopfAlgProperty.geometricallyConnected k _ hJ))
    hker hfinrank

end TauCeti.FiniteTypeCommHopfAlgCat
