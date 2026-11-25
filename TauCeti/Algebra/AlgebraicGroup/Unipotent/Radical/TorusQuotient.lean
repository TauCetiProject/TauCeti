/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Torus.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.HopfBaseChange
public import TauCeti.RingTheory.Smooth.GeometricallyReduced
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Exactness
import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Recognition
import TauCeti.Algebra.AlgebraicGroup.Torus.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Diagonalizable.Quotient

/-!
# The unipotent radical when the quotient is a torus

Over any field, a connected normal smooth unipotent subgroup of a geometrically reduced group
whose affine quotient is of multiplicative type, for instance a torus, is the unipotent radical
(`TauCeti.FiniteTypeCommHopfAlgCat.
unipotentRadicalDefiningIdeal_eq_of_multiplicativeType_coinvariants`). If `G ⧸ R_u(G)` is a
torus, the formation of `R_u(G)` therefore commutes with every field extension
(`TauCeti.FiniteTypeCommHopfAlgCat.baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_torus`): a
torus stays a torus after extension of scalars, and the image in a group with semisimple geometric
points of the smooth unipotent radical of `G_K` is trivial.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.
    unipotentRadicalDefiningIdeal_eq_of_multiplicativeType_coinvariants`
* `TauCeti.FiniteTypeCommHopfAlgCat.baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_torus`

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 16.33, pp. 335–336.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

universe u

noncomputable section

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- **Uniqueness of the unipotent radical with quotient of multiplicative type.** Over any field, a
connected normal smooth unipotent subgroup of a geometrically reduced group whose affine quotient
is of multiplicative type, for instance a torus, is the unipotent radical. -/
theorem unipotentRadicalDefiningIdeal_eq_of_multiplicativeType_coinvariants
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.IsGeometricallyReduced k H]
    {I : HopfIdeal k H} (hI : HopfIdeal.IsUnipotentRadicalCandidate H I) :
    letI := hI.isNormal.isHopfSubalgebra_coinvariants.hopfAlgebra
    multiplicativeTypeCommHopfAlgProperty k
        ⟨CommHopfAlgCat.coinvariants hI.isNormal,
          (finiteTypeCommHopfAlgProperty_iff _).mpr hI.isNormal.finiteType_coinvariants⟩ →
      unipotentRadicalDefiningIdeal H = I := by
  intro hM
  let D : FiniteTypeCommHopfAlgCat.{u, u} k :=
    ⟨CommHopfAlgCat.coinvariants hI.isNormal,
      (finiteTypeCommHopfAlgProperty_iff _).mpr hI.isNormal.finiteType_coinvariants⟩
  have hker := CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_eq hI.isNormal
  let _ : Algebra.IsGeometricallyReduced k D :=
    Algebra.IsGeometricallyReduced.of_injective
      (CommHopfAlgCat.coinvariantsι hI.isNormal).hom.toAlgHom
      (CommHopfAlgCat.hopfSubalgebraι_injective hI.isNormal.isHopfSubalgebra_coinvariants)
  have hD : geometricallySemisimplePointsCommHopfAlgProperty k D.obj :=
    ((multiplicativeTypeCommHopfAlgProperty_iff_isCocomm_and_geometricallySemisimplePoints D).mp
      hM).2
  rw [unipotentRadicalDefiningIdeal_eq_kernelHopfIdeal_of_geometricallySemisimple H D hD
    (CommHopfAlgCat.coinvariantsι hI.isNormal) (by rwa [hker]), hker]

/-- **Base change of the unipotent radical with torus quotient.** Over any field, if the affine
quotient of a smooth group by its unipotent radical is a torus, then the formation of the unipotent
radical commutes with every field extension `K / k`. -/
theorem baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_torus
    {K : Type u} [Field K] [Algebra k K]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) [Algebra.Smooth k H] :
    letI := (isNormal_unipotentRadicalDefiningIdeal H).isHopfSubalgebra_coinvariants.hopfAlgebra
    torusCommHopfAlgProperty k
        ⟨CommHopfAlgCat.coinvariants (isNormal_unipotentRadicalDefiningIdeal H),
          (finiteTypeCommHopfAlgProperty_iff _).mpr
            (isNormal_unipotentRadicalDefiningIdeal H).finiteType_coinvariants⟩ →
      CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
        unipotentRadicalDefiningIdeal (baseChange (K := K) H) := by
  intro hT
  let hR := isNormal_unipotentRadicalDefiningIdeal H
  have hI := (isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal H).baseChange (K := K)
  refine (unipotentRadicalDefiningIdeal_eq_of_multiplicativeType_coinvariants _ hI ?_).symm
  exact torusCommHopfAlgProperty.multiplicativeType K _ <| (torusCommHopfAlgProperty K).prop_of_iso
    (ObjectProperty.isoMk _ (CommHopfAlgCat.coinvariantsBaseChangeIso (K := K) hR))
    (hT.baseChange K)

end FiniteTypeCommHopfAlgCat

end

end TauCeti
