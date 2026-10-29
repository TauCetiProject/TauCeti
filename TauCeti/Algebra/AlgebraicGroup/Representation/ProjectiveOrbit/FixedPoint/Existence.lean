/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.FixedPoint.Basic
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosedOrbit
import TauCeti.Algebra.AlgebraicGroup.Connected.Irreducible

/-!
# Borel fixed points in projective representations

Let a reduced connected solvable affine group of finite type over an algebraically closed
field act on the projective space of a finite-dimensional comodule. Every nonempty closed
subset invariant under rational group translations contains a fixed point. The point is a
rational line, and its orbit morphism is constant on all scheme points of the group.

This is the projective form of the Borel fixed-point theorem used for homogeneous spaces:
once such a space is realized as a closed invariant subset of a projective representation,
a connected solvable subgroup fixes a point. In particular, no fixed-vector assertion is
made: the group may act on the fixed line through a nontrivial character.

The closed-orbit lemma supplies an orbit inside the invariant subset. Connectedness makes
the group irreducible, and the proper--affine argument for closed solvable orbits makes
that orbit a singleton. The two conclusions below express the resulting constant orbit
and the fixed projective point, respectively.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §10.4.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 17.5.
-/

public section

open AlgebraicGeometry WithConv TopologicalSpace

namespace TauCeti.Comodule

universe u

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
  [Group.IsSolvable (WithConv (H →ₐ[k] k))]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- **Borel fixed-point theorem, orbit form.** Every nonempty closed invariant subset
of projective space contains a rational line whose full scheme-point orbit is a singleton. -/
theorem exists_projectiveOrbitMap_eq_identity_of_isClosed_of_isSolvable
    {Z : Set (Proj (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M)))}
    (hZ : IsClosed Z) (hne : Z.Nonempty)
    (hinvariant : ∀ g : WithConv (H →ₐ[k] k),
      Set.MapsTo (projectivePointTranslation (M := M) g).hom Z Z) :
    ∃ (m : M) (hm : Module.IsUnimodular k m),
      projectiveOrbitMap (H := H) m hm
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈ Z ∧
        ∀ x : Spec (.of H), projectiveOrbitMap (H := H) m hm x =
          projectiveOrbitMap (H := H) m hm
            (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) := by
  let _ : IrreducibleSpace (PrimeSpectrum H) :=
    _root_.CommHopfAlgCat.irreducibleSpace_primeSpectrum_of_connectedSpace k
      (_root_.CommHopfAlgCat.of k H)
  obtain ⟨m, hm, hclosed, hsub⟩ :=
    exists_isClosed_range_projectiveOrbitMap_subset_of_isClosed (H := H) hZ hne hinvariant
  exact ⟨m, hm, hsub (Set.mem_range_self _),
    projectiveOrbitMap_eq_identity_of_isClosed_of_isSolvable m hm hclosed⟩

/-- **Borel fixed-point theorem, projective form.** Every nonempty closed invariant subset
of a projective representation of a reduced connected solvable affine group contains a
closed point fixed by every rational group translation. -/
theorem exists_fixed_mem_of_isClosed_of_isSolvable
    {Z : Set (Proj (SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M)))}
    (hZ : IsClosed Z) (hne : Z.Nonempty)
    (hinvariant : ∀ g : WithConv (H →ₐ[k] k),
      Set.MapsTo (projectivePointTranslation (M := M) g).hom Z Z) :
    ∃ x ∈ Z, x ∈ closedPoints _ ∧
      ∀ g : WithConv (H →ₐ[k] k), (projectivePointTranslation (M := M) g).hom x = x := by
  obtain ⟨m, hm, hmem, horbit⟩ :=
    exists_projectiveOrbitMap_eq_identity_of_isClosed_of_isSolvable (H := H) hZ hne hinvariant
  refine ⟨_, hmem,
    (ProjectiveSpectrum.mem_closedPoints_iff_exists_projectiveOrbitMap_eq (H := H) _).mpr
      ⟨m, hm, rfl⟩, fun g ↦ ?_⟩
  have htranslation :=
    projectivePointTranslation_projectiveOrbitMap_kernelPoint g 1 m hm
  rw [mul_one] at htranslation
  simp only [AlgHom.convOne_def, Algebra.ofId_self, AlgHom.id_comp] at htranslation
  exact htranslation.trans (horbit (AlgHom.kernelPoint g.ofConv))

end TauCeti.Comodule
