/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.SolvableSubgroup
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Borel conjugacy from a closed projective orbit

Suppose a smooth connected solvable subgroup is the stabilizer of a point in a closed
projective orbit. Then it is a Borel subgroup, and all Borel subgroups are its conjugates.
Indeed every Borel subgroup fixes a point of that orbit, so it is contained in a conjugate
of the stabilizer. Maximality upgrades containment to equality.

This separates the fixed-point argument from the construction of a closed orbit with
solvable stabilizer. Closedness of the orbit is an explicit hypothesis; it does not hold
for the orbit of an arbitrary Chevalley line.

The proof combines `HopfIdeal.exists_conjugate_le_of_isClosed_projectiveOrbit` with
`HopfIdeal.isBorelOverAlgClosed_iff_exists_eq_conjugate`.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §11.1.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 17.6.
-/

public section

open AlgebraicGeometry WithConv

namespace TauCeti.HopfIdeal

universe u

variable {k H M : Type u} [Field k] [IsAlgClosed k]
  [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- If a smooth connected solvable subgroup is the stabilizer of a rational point of a
closed projective orbit, the Borel subgroups are exactly its conjugates. In particular the
stabilizer itself is Borel. Neither smoothness nor connectedness of the ambient group is
needed for this criterion. -/
theorem isBorelOverAlgClosed_iff_exists_eq_conjugate_of_isClosed_projectiveOrbit
    (D : HopfIdeal k H) (hD : IsBorelCandidate k (FiniteTypeCommHopfAlgCat.of k H) D)
    (m : M) (hm : Module.IsUnimodular k m)
    (hclosed : IsClosed (Set.range (Comodule.projectiveOrbitMap (H := H) m hm)))
    (hstab : ∀ a : WithConv (H →ₐ[k] k),
      a ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H) D
          (CommAlgCat.of k k) ↔
        Comodule.projectiveOrbitMap (H := H) m hm (AlgHom.kernelPoint a.ofConv) =
          Comodule.projectiveOrbitMap (H := H) m hm
            (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)))
    (I : HopfIdeal k H) :
    IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) I ↔
      ∃ g : WithConv (H →ₐ[k] k), I = D.conjugate g := by
  apply isBorelOverAlgClosed_iff_exists_eq_conjugate D hD
  intro J hJ
  have hcandidate := ((isBorelOverAlgClosed_iff k
    (FiniteTypeCommHopfAlgCat.of k H) J).mp hJ).2.prop
  let Q := FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) J
  let _ : Algebra.Smooth k Q := (smoothCommHopfAlgProperty_iff _).mp hcandidate.smooth
  let _ : IsReduced Q := isReduced_of_smooth k Q
  let _ : ConnectedSpace (PrimeSpectrum Q) :=
    hcandidate.geometricallyConnected.connectedSpace k Q.obj
  let _ : Group.IsSolvable (WithConv (Q →ₐ[k] AlgebraicClosure k)) :=
    (geometricallySolvablePointsCommHopfAlgProperty_iff _ _).mp hcandidate.geometricallySolvable
  let _ : Group.IsSolvable (WithConv (Q →ₐ[k] k)) :=
    Group.isSolvable_of_isSolvable_injective
      (AlgHom.mapValue_injective (φ := Algebra.ofId k (AlgebraicClosure k))
        (FaithfulSMul.algebraMap_injective k (AlgebraicClosure k)))
  exact exists_conjugate_le_of_isClosed_projectiveOrbit
    (H := FiniteTypeCommHopfAlgCat.of k H) D J m hm hclosed hstab

end TauCeti.HopfIdeal
