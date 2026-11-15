/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Centralizer
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Maximal

/-!
# The centralizer of the diagonal torus in the general linear group

Over every commutative ring `R`, the scheme-theoretic centralizer of the diagonal torus `T` of
`GL_n` is `T` itself. In Hopf coordinates, the centralizer ideal
`BialgHom.centralizerHopfIdeal` of the diagonal-torus coordinate morphism is the diagonal-torus
defining ideal.

The statement is about the closed subgroup scheme, not only about its points over a field. It
holds over every base ring, including `𝔽₂`, where the group of rational diagonal matrices is
trivial and its centralizer in `GL_n(𝔽₂)` is everything.

The generic quotient of the normalizer of a diagonalizable subgroup by its centralizer, in
`TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normalizer.Quotient`, is therefore the
quotient of the normalizer of the diagonal torus of `GL_n` by the torus itself.

## Main declaration

* `TauCeti.GeneralLinear.centralizerHopfIdeal_diagonalTorusCoordinateMap`: **the centralizer of
  the diagonal torus of `GL_n` is the diagonal torus.**

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §16.1.
* SGA 3, Exposé XI, on centralizers of diagonalizable subgroups.
-/

public section

open TensorProduct WithConv

namespace TauCeti.GeneralLinear

universe u w

variable {R : Type u} [CommRing R] {n : ℕ}

/-- A point of `GL_n` killing the centralizer ideal of the diagonal torus is a diagonal matrix,
over every base ring and every value algebra. The public form of this statement is
`centralizerHopfIdeal_diagonalTorusCoordinateMap`. -/
private theorem isDiag_pointsMulEquiv_of_centralizerHopfIdeal_le_ker
    {A : Type w} [CommRing A] [Algebra R A]
    {g : WithConv (coordinateHopfAlgebra R n →ₐ[R] A)}
    (hg : (BialgHom.centralizerHopfIdeal
        (diagonalTorusCoordinateMap (R := R) (N := n)).hom).toIdeal ≤ RingHom.ker g.ofConv) :
    ((pointsMulEquiv n g : Matrix.GeneralLinearGroup (Fin n) A) :
      Matrix (Fin n) (Fin n) A).IsDiag := by
  exact (BialgHom.centralizerHopfIdeal_le_ker_iff_isDiag_of_coordinates
    (diagonalTorusCoordinateMap (R := R) (N := n)).hom
    (fun i ↦ Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1))
    (fun _ _ h ↦ ULift.up_injective
      (Finsupp.single_left_injective one_ne_zero (Multiplicative.ofAdd.injective h)))
    (diagonalTorusCoordinateMap_X (R := R)) g).mp hg

/-- **The centralizer of the diagonal torus of `GL_n` is the diagonal torus**, as closed subgroup
schemes over an arbitrary commutative ring. In coordinates, the centralizer ideal of the
diagonal-torus coordinate morphism equals the diagonal-torus defining ideal. -/
theorem centralizerHopfIdeal_diagonalTorusCoordinateMap :
    BialgHom.centralizerHopfIdeal (diagonalTorusCoordinateMap (R := R) (N := n)).hom =
      diagonalTorusDefiningIdeal R n := by
  -- The centralizer contains the torus; conversely, the quotient by the centralizer ideal is a
  -- diagonal point, so it kills the diagonal-torus ideal.
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rw [diagonalTorusDefiningIdeal_eq_ker]
    exact BialgHom.centralizerHopfIdeal_le_kerOfSurjective _
      (diagonalTorusCoordinateMap_surjective R n)
  let C := BialgHom.centralizerHopfIdeal (diagonalTorusCoordinateMap (R := R) (N := n)).hom
  -- The quotient map by the centralizer ideal is a point killing that ideal, hence diagonal.
  let g : WithConv (coordinateHopfAlgebra R n →ₐ[R] coordinateHopfAlgebra R n ⧸ C.toIdeal) :=
    toConv (Ideal.Quotient.mkₐ R C.toIdeal)
  have hg : C.toIdeal ≤ RingHom.ker g.ofConv := fun y hy ↦ by
    rw [RingHom.mem_ker, ofConv_toConv, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hy
  let A := coordinateHopfAlgebra R n ⧸ C.toIdeal
  have hmem : g ∈ CommHopfAlgCat.quotientPointsSubgroup (coordinateHopfAlgebra R n)
      (diagonalTorusDefiningIdeal R n) (CommAlgCat.of R A) :=
    (mem_quotientPointsSubgroup_diagonalTorusDefiningIdeal_iff R n A g).mpr
      (isDiag_pointsMulEquiv_of_centralizerHopfIdeal_le_ker (A := A) hg)
  have hx0 :=
    (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ (CommAlgCat.of R A) g).mp hmem x hx
  rw [ofConv_toConv, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at hx0
  exact HopfIdeal.mem_toIdeal.mp hx0

end TauCeti.GeneralLinear
