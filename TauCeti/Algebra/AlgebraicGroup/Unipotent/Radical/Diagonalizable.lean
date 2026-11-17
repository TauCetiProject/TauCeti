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
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.ClosedSubgroup
import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Diagonalizable
import TauCeti.RingTheory.Smooth.GeometricallyReduced
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

Over an algebraically closed field every torus is split, hence diagonalizable, so a torus of `G`
meets `R_u(G)` trivially. When `G` is reduced, the composite `D → G → G ⧸ R_u(G)` therefore has
trivial scheme-theoretic kernel. For a smooth connected solvable group and a maximal torus `T`
this is the first half of the decomposition `G = R_u(G) ⋊ T` (Milne, Theorem 16.33(d)). No
solvability, smoothness or connectedness of `G` is needed here.

## Main declarations

In the `TauCeti.FiniteTypeCommHopfAlgCat` namespace:

* `sup_unipotentRadicalDefiningIdeal_eq_augmentation_of_groupLikeSpanned`: a diagonalizable
  closed subgroup meets the unipotent radical trivially.
* `sup_unipotentRadicalDefiningIdeal_eq_augmentation_of_torus`: a torus meets the unipotent
  radical trivially.
* `kernelHopfIdeal_coinvariantsι_unipotentRadical_comp_mkQuotient_eq_augmentation`: for reduced
  `G`, a diagonalizable closed subgroup maps to `G ⧸ R_u(G)` with trivial kernel.

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
    I ⊔ unipotentRadicalDefiningIdeal G = HopfIdeal.augmentation k G := by
  set U := unipotentRadicalDefiningIdeal G
  have hU := (smoothUnipotentCommHopfAlgProperty_iff k (quotient G U)).mp
    (smoothUnipotent_unipotentRadical G)
  have hgeom : geometricallyUnipotentPointsCommHopfAlgProperty k
      (CommHopfAlgCat.quotient G.obj U) :=
    (geometricallyUnipotentPointsCommHopfAlgProperty_iff k _).mpr hU.2
  let _ : Algebra.Smooth k (CommHopfAlgCat.quotient G.obj U) :=
    (smoothCommHopfAlgProperty_iff _).mp ((smoothCommHopfAlgProperty_iff _).mpr hU.1)
  let _ : IsReduced (CommHopfAlgCat.quotient G.obj U) := isReduced_of_smooth k _
  -- The intersection is a quotient of the diagonalizable subgroup, hence diagonalizable.
  have hK : Subcoalgebra.groupLikeSetSpan (R := k)
      (C := CommHopfAlgCat.quotient G.obj (I ⊔ U)) Set.univ = ⊤ :=
    (DiagonalizableGroup.groupLikeSpannedProperty_iff k _).mp <|
      DiagonalizableGroup.groupLikeSpannedProperty.of_surjective k _ _
        (quotientMapOfLe G (le_sup_left : I ≤ I ⊔ U)) (quotientMapOfLe_surjective G le_sup_left) hI
  -- It is also a closed subgroup of the reduced unipotent group `R_u(G)`, hence trivial.
  have hbij := hgeom.algebraMap_bijective_of_groupLikeSetSpan_eq_top_of_surjective hK
      (toBialgHom (quotientMapOfLe G (le_sup_right : U ≤ I ⊔ U)))
      (quotientMapOfLe_surjective G le_sup_right)
  refine le_antisymm (HopfIdeal.le_augmentation k G _) fun x hx ↦ ?_
  rw [HopfIdeal.mem_augmentation] at hx
  obtain ⟨c, hc⟩ := hbij.2 (toBialgHom (mkQuotient G (I ⊔ U)) x)
  have hcounit := congrArg (Coalgebra.counit (R := k)) hc
  rw [Bialgebra.counit_algebraMap, CoalgHomClass.counit_comp_apply, hx] at hcounit
  rw [← mkQuotient_eq_zero_iff, ← hc, hcounit, map_zero]

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
theorem kernelHopfIdeal_coinvariantsι_unipotentRadical_comp_mkQuotient_eq_augmentation
    [IsReduced G] {I : HopfIdeal k G}
    (hI : DiagonalizableGroup.groupLikeSpannedProperty k (quotient G I)) :
    CommHopfAlgCat.kernelHopfIdeal
        (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal G) ≫
          CommHopfAlgCat.mkQuotient G.obj I) =
      HopfIdeal.augmentation k (CommHopfAlgCat.quotient G.obj I) := by
  rw [CommHopfAlgCat.kernelHopfIdeal_comp,
    CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_eq (isNormal_unipotentRadicalDefiningIdeal G)]
  refine le_antisymm (HopfIdeal.le_augmentation k _ _) fun y hy ↦ ?_
  obtain ⟨x, rfl⟩ := CommHopfAlgCat.mkQuotient_surjective G.obj I y
  rw [HopfIdeal.mem_augmentation, CoalgHomClass.counit_comp_apply] at hy
  have hx : x ∈ I ⊔ unipotentRadicalDefiningIdeal G := by
    rw [sup_unipotentRadicalDefiningIdeal_eq_augmentation_of_groupLikeSpanned G hI]
    exact (HopfIdeal.mem_augmentation k G).mpr hy
  obtain ⟨a, ha, b, hb, rfl⟩ := HopfIdeal.mem_sup.mp hx
  rw [map_add, (CommHopfAlgCat.mkQuotient_eq_zero_iff G.obj I a).mpr ha, zero_add]
  exact HopfIdeal.mem_map_of_mem _ hb

end TauCeti.FiniteTypeCommHopfAlgCat
