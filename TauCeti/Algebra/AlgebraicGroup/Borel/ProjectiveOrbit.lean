/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Borel.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Solvability
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

Without a closed orbit with solvable stabilizer, a group that is not solvable still has a closed
orbit with proper stabilizer. Every Borel candidate then lies in a conjugate of that proper
closed subgroup, which reduces the conjugacy of Borel subgroups to a group of smaller dimension.

## Main declarations

* `TauCeti.HopfIdeal.IsBorelCandidate.exists_conjugate_le`: a Borel candidate lies in a conjugate
  of every closed subgroup whose conjugates contain all reduced connected solvable closed
  subgroups.
* `TauCeti.HopfIdeal.isBorelOverAlgClosed_iff_exists_eq_conjugate_of_isClosed_projectiveOrbit`:
  the stabilizer of a point of a closed projective orbit, if it is a Borel candidate, is a Borel
  subgroup whose conjugates are all the Borel subgroups.
* `TauCeti.HopfIdeal.exists_ne_bot_forall_isBorelCandidate_exists_conjugate_le_of_not_isSolvable`:
  an irreducible group that is not solvable has a proper closed subgroup containing a conjugate of
  every Borel candidate.

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

/-- A Borel candidate lies in a conjugate of `D` as soon as every reduced connected closed
subgroup with solvable rational points does. -/
theorem IsBorelCandidate.exists_conjugate_le {D J : HopfIdeal k H}
    (hJ : IsBorelCandidate k (FiniteTypeCommHopfAlgCat.of k H) J)
    (hD : ∀ (I : HopfIdeal k H)
      [IsReduced (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) I)]
      [ConnectedSpace (PrimeSpectrum
        (FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) I))]
      [Group.IsSolvable (WithConv
        ((FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) I) →ₐ[k] k))],
      ∃ g : WithConv (H →ₐ[k] k), D.conjugate g ≤ I) :
    ∃ g : WithConv (H →ₐ[k] k), D.conjugate g ≤ J := by
  let Q := FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) J
  let _ : Algebra.Smooth k Q := (smoothCommHopfAlgProperty_iff _).mp hJ.smooth
  let _ : IsReduced Q := isReduced_of_smooth k Q
  let _ : ConnectedSpace (PrimeSpectrum Q) :=
    hJ.geometricallyConnected.connectedSpace k Q.obj
  let _ : Group.IsSolvable (WithConv (Q →ₐ[k] AlgebraicClosure k)) :=
    (geometricallySolvablePointsCommHopfAlgProperty_iff _ _).mp hJ.geometricallySolvable
  let _ : Group.IsSolvable (WithConv (Q →ₐ[k] k)) :=
    Group.isSolvable_of_isSolvable_injective
      (AlgHom.mapValue_injective (φ := Algebra.ofId k (AlgebraicClosure k))
        (FaithfulSMul.algebraMap_injective k (AlgebraicClosure k)))
  exact hD J

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
  exact ((isBorelOverAlgClosed_iff k (FiniteTypeCommHopfAlgCat.of k H) J).mp hJ).2.prop
    |>.exists_conjugate_le fun I _ _ _ ↦
      exists_conjugate_le_of_isClosed_projectiveOrbit
        (H := FiniteTypeCommHopfAlgCat.of k H) D I m hm hclosed hstab

/-- An irreducible affine group of finite type over an algebraically closed field whose
rational points do not form a solvable group has a proper closed subgroup containing a conjugate
of every Borel candidate, in particular of every Borel subgroup. -/
theorem exists_ne_bot_forall_isBorelCandidate_exists_conjugate_le_of_not_isSolvable
    [IrreducibleSpace (PrimeSpectrum H)] (hH : ¬ Group.IsSolvable (WithConv (H →ₐ[k] k))) :
    ∃ D : HopfIdeal k H, D ≠ ⊥ ∧ ∀ J : HopfIdeal k H,
      IsBorelCandidate k (FiniteTypeCommHopfAlgCat.of k H) J →
        ∃ g : WithConv (H →ₐ[k] k), D.conjugate g ≤ J := by
  obtain ⟨D, hD, hconj⟩ := exists_ne_bot_forall_exists_conjugate_le_of_not_isSolvable
    (H := FiniteTypeCommHopfAlgCat.of k H) hH
  exact ⟨D, hD, fun J hJ ↦ hJ.exists_conjugate_le fun I _ _ _ ↦ hconj I⟩

end TauCeti.HopfIdeal
