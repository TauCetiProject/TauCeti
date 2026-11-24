/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.EssentialImage
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Quotient
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Exactness
import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Diagonalizable
import TauCeti.RingTheory.TensorProduct.Reduced

/-!
# Diagonalizable subgroups meet the unipotent radical trivially

Let `G` be a finite-type affine group over an algebraically closed field `k`. The unipotent
radical `R_u(G)` is smooth with unipotent points, so every diagonalizable closed subgroup of it
is trivial (`algebraMap_bijective_of_groupLikeSetSpan_eq_top_of_surjective` in the
`TauCeti.geometricallyUnipotentPointsCommHopfAlgProperty` namespace).
The intersection of a diagonalizable closed subgroup `D` with `R_u(G)` is a closed subgroup of
both, hence diagonalizable and contained in a reduced unipotent group, hence trivial.

In Hopf coordinates, if `D` and `R_u(G)` are cut out by the Hopf ideals `I` and `I_u`, their
intersection is cut out by `I ⊔ I_u`, and the statement is `I ⊔ I_u = augmentation`. This is the
scheme-theoretic statement: it also excludes infinitesimal intersections such as `μₚ`.

The argument uses nothing about `R_u(G)` beyond smoothness and unipotence: it is the
specialisation to `R_u(G)` of
`TauCeti.FiniteTypeCommHopfAlgCat.sup_eq_augmentation_of_groupLikeSpanned_of_smoothUnipotent`,
for any closed subgroup with smooth unipotent coordinate algebra.

Over an algebraically closed field every torus is split, hence diagonalizable, so a torus of `G`
meets `R_u(G)` trivially. When `G` is reduced, the composite `D → G → G ⧸ R_u(G)` therefore has
trivial scheme-theoretic kernel. For a smooth connected solvable group and a maximal torus `T`
this is the first half of the decomposition `G = R_u(G) ⋊ T` (Milne, Theorem 16.33(d)). The two
intersection theorems need no solvability, smoothness or connectedness of `G`; the kernel theorems
assume `G` reduced (over the algebraically closed `k`, equivalently smooth), which identifies the
kernel of `G → G ⧸ R_u(G)` with `R_u(G)`.

## Main declarations

In the `TauCeti.FiniteTypeCommHopfAlgCat` namespace:

* `sup_unipotentRadicalDefiningIdeal_eq_augmentation_of_groupLikeSpanned`: a diagonalizable
  closed subgroup meets the unipotent radical trivially.
* `sup_unipotentRadicalDefiningIdeal_eq_augmentation_of_torus`: a torus meets the unipotent
  radical trivially.
* the `_of_groupLikeSpanned` and `_of_torus` forms of
  `kernelHopfIdeal_coinvariantsι_unipotentRadical_comp_mkQuotient_eq_augmentation`: for reduced
  `G`, a diagonalizable closed subgroup, or a torus, maps to `G ⧸ R_u(G)` with trivial kernel.

## References

* J. S. Milne, *Algebraic Groups* (2017), Corollary 14.18 and Theorem 16.33.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), Theorem 10.6.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] (G : FiniteTypeCommHopfAlgCat.{u, u} k)

/-- **A diagonalizable closed subgroup meets the unipotent radical trivially**, over an
algebraically closed field and scheme-theoretically. If the Hopf ideal `I` cuts out a closed
subgroup whose coordinate algebra is spanned by its group-like elements, then `I` and the defining
ideal of the unipotent radical together generate the augmentation ideal. -/
theorem sup_unipotentRadicalDefiningIdeal_eq_augmentation_of_groupLikeSpanned
    {I : HopfIdeal k G}
    (hI : DiagonalizableGroup.groupLikeSpannedProperty k (quotient G I)) :
    I ⊔ unipotentRadicalDefiningIdeal G = HopfIdeal.augmentation k G :=
  sup_eq_augmentation_of_groupLikeSpanned_of_smoothUnipotent G hI
    (smoothUnipotent_unipotentRadical G)

/-- **A torus meets the unipotent radical trivially**, over an algebraically closed field and
scheme-theoretically: if the Hopf ideal `I` cuts out a torus, then `I` and the defining ideal of
the unipotent radical together generate the augmentation ideal. -/
theorem sup_unipotentRadicalDefiningIdeal_eq_augmentation_of_torus {I : HopfIdeal k G}
    (hI : torusCommHopfAlgProperty k (quotient G I)) :
    I ⊔ unipotentRadicalDefiningIdeal G = HopfIdeal.augmentation k G :=
  sup_unipotentRadicalDefiningIdeal_eq_augmentation_of_groupLikeSpanned G
    ((torusCommHopfAlgProperty.split k _ hI).groupLikeSpanned k _)

/-- **A diagonalizable closed subgroup of a reduced group maps to the quotient by the unipotent
radical with trivial kernel**, over an algebraically closed field and scheme-theoretically. If
the Hopf ideal `I` cuts out a closed subgroup `D` whose coordinate algebra is spanned by its
group-like elements, the coordinate map of the composite `D → G → G ⧸ R_u(G)` has kernel Hopf
ideal the augmentation ideal. Here `O(G ⧸ R_u(G))` is the Hopf subalgebra of right
coinvariants. -/
theorem
kernelHopfIdeal_coinvariantsι_unipotentRadical_comp_mkQuotient_eq_augmentation_of_groupLikeSpanned
    [IsReduced G] {I : HopfIdeal k G}
    (hI : DiagonalizableGroup.groupLikeSpannedProperty k (quotient G I)) :
    CommHopfAlgCat.kernelHopfIdeal
        (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal G) ≫
          CommHopfAlgCat.mkQuotient G.obj I) =
      HopfIdeal.augmentation k (CommHopfAlgCat.quotient G.obj I) := by
  -- The kernel of `O(G ⧸ R_u(G)) → O(G) → O(G) ⧸ I` is the image of `I_u` in `O(G) ⧸ I`.
  rw [CommHopfAlgCat.kernelHopfIdeal_comp,
    CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_eq (isNormal_unipotentRadicalDefiningIdeal G)]
  -- Both sides are images of Hopf ideals of `O(G)` containing `I`, so they agree exactly when their
  -- pullbacks to `O(G)` do: these are `I_u ⊔ I` and the augmentation ideal.
  rw [← HopfIdeal.comapOfSurjective_eq_comapOfSurjective_iff (CommHopfAlgCat.mkQuotient G.obj I).hom
      (CommHopfAlgCat.mkQuotient_surjective G.obj I),
    HopfIdeal.comapOfSurjective_map, HopfIdeal.comapOfSurjective_augmentation, sup_comm]
  have hsup := sup_unipotentRadicalDefiningIdeal_eq_augmentation_of_groupLikeSpanned G hI
  simpa only [CommHopfAlgCat.hom_mkQuotient, HopfIdeal.kerOfSurjective_mkBialgHom] using hsup

/-- **A torus of a reduced group maps to the quotient by the unipotent radical with trivial
kernel**, over an algebraically closed field and scheme-theoretically: if the Hopf ideal `I` cuts
out a torus `T`, the coordinate map of the composite `T → G → G ⧸ R_u(G)` has kernel Hopf ideal the
augmentation ideal. -/
theorem kernelHopfIdeal_coinvariantsι_unipotentRadical_comp_mkQuotient_eq_augmentation_of_torus
    [IsReduced G] {I : HopfIdeal k G} (hI : torusCommHopfAlgProperty k (quotient G I)) :
    CommHopfAlgCat.kernelHopfIdeal
        (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal G) ≫
          CommHopfAlgCat.mkQuotient G.obj I) =
      HopfIdeal.augmentation k (CommHopfAlgCat.quotient G.obj I) :=
  kernelHopfIdeal_coinvariantsι_unipotentRadical_comp_mkQuotient_eq_augmentation_of_groupLikeSpanned
    G ((torusCommHopfAlgProperty.split k _ hI).groupLikeSpanned k _)

end TauCeti.FiniteTypeCommHopfAlgCat
