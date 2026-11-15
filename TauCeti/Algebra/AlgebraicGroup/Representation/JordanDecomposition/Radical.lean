/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.ClosedFactors
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Separation
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Central.Basic

/-!
# The unipotent radical of a commutative affine group

For a reduced connected commutative affine group of finite type over an algebraically closed
field, the closed unipotent Jordan factor is the unipotent radical. Thus the unipotent points
form a smooth connected closed subgroup, rather than merely a subgroup of rational points.
This identifies the unipotent factor in the commutative splitting with the canonical radical
used in the structure theory of connected solvable groups.

The containment theorem also applies without connectedness of the ambient group: every reduced
closed subgroup whose rational points are unipotent lies in the unipotent Jordan factor.
Reducedness of that subgroup is essential, since rational points do not detect infinitesimal
subgroups. Connectedness of the ambient group is used to make its Jordan factor connected.

The construction reuses the regular Jordan projections and closed factors in
`JordanDecomposition.ClosedFactors`, and the universal property of the unipotent radical.

## References

* A. Borel, *Linear Algebraic Groups*, §§4.7 and 11.21.
* T. A. Springer, *Linear Algebraic Groups*, §§2.4 and 3.1.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.HopfAlgebra.Point

universe u

variable (k H : Type u) [Field k] [IsAlgClosed k] [CommRing H]
  [_root_.HopfAlgebra k H] [Algebra.FiniteType k H] [IsReduced H]
  [Coalgebra.IsCocomm k H]

/-- Every reduced closed subgroup consisting of unipotent rational points is contained in the
closed unipotent Jordan factor. The inequality reverses subgroup containment. -/
theorem ker_unipotentPartBialgHom_le_of_isUnipotentPoint
    (J : HopfIdeal k H) [IsReduced (CommHopfAlgCat.quotient
      (_root_.CommHopfAlgCat.of k H) J)]
    (hJ : ∀ g : WithConv (H →ₐ[k] k),
      g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) J
        (CommAlgCat.of k k) → IsUnipotentPoint g) :
    HopfIdeal.ker (unipotentPartBialgHom k H) ≤ J := by
  apply HopfIdeal.le_of_quotientPointsSubgroup_le (K := k)
    (H := _root_.CommHopfAlgCat.of k H)
  intro g hg
  exact (mem_quotientPointsSubgroup_ker_unipotentPartBialgHom_base_iff k H g).mpr
    (hJ g hg)

/-- The closed unipotent Jordan factor of a connected commutative affine group is a connected
normal smooth unipotent subgroup. -/
theorem isUnipotentRadicalCandidate_ker_unipotentPartBialgHom
    (hH : geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k H)) :
    HopfIdeal.IsUnipotentRadicalCandidate (FiniteTypeCommHopfAlgCat.of k H)
      (HopfIdeal.ker (unipotentPartBialgHom k H)) := by
  refine HopfIdeal.IsUnipotentRadicalCandidate.mk ?_ ?_
    (smoothUnipotentCommHopfAlgProperty_unipotentFactor k H)
  · exact ((HopfIdeal.isCentral_bot_iff_isCocomm.mpr inferInstance).mono bot_le).isNormal
  · exact hH.image (_root_.CommHopfAlgCat.ofHom (unipotentPartBialgHom k H))

/-- For a connected commutative affine group, the unipotent radical is exactly the closed
unipotent Jordan factor, scheme-theoretically and in every characteristic. -/
theorem unipotentRadicalDefiningIdeal_eq_ker_unipotentPartBialgHom
    (hH : geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k H)) :
    FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal (FiniteTypeCommHopfAlgCat.of k H) =
      HopfIdeal.ker (unipotentPartBialgHom k H) := by
  let G := FiniteTypeCommHopfAlgCat.of k H
  let J := FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal G
  have hJ := FiniteTypeCommHopfAlgCat.isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal G
  apply le_antisymm
  · exact FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_le G _
      (isUnipotentRadicalCandidate_ker_unipotentPartBialgHom k H hH)
  · let _ : Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient G J) :=
      ((smoothUnipotentCommHopfAlgProperty_iff k _).mp hJ.smoothUnipotent).1
    let _ : IsReduced (CommHopfAlgCat.quotient G.obj J) := isReduced_of_smooth k _
    apply ker_unipotentPartBialgHom_le_of_isUnipotentPoint k H J
    intro g hg
    obtain ⟨q, rfl⟩ := hg
    exact (hJ.smoothUnipotent.isUnipotentPoint q).mapDomain
      (CommHopfAlgCat.mkQuotient G.obj J).hom

/-- The rational points of the unipotent radical of a connected commutative affine group are
exactly the unipotent rational points of the ambient group. -/
@[simp]
theorem mem_quotientPointsSubgroup_unipotentRadical_iff
    (hH : geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k H))
    (g : WithConv (H →ₐ[k] k)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        (FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal
          (FiniteTypeCommHopfAlgCat.of k H)) (CommAlgCat.of k k) ↔
      IsUnipotentPoint g := by
  rw [unipotentRadicalDefiningIdeal_eq_ker_unipotentPartBialgHom k H hH]
  exact mem_quotientPointsSubgroup_ker_unipotentPartBialgHom_base_iff k H g

end TauCeti.HopfAlgebra.Point
