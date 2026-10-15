/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.AffineChart
public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Closed projective orbits of connected solvable groups

A closed projective orbit of a reduced connected solvable affine group over an algebraically
closed field consists of one point. This is the proper--affine step in the Borel fixed-point
argument.

Lie--Kolchin places the whole orbit in an affine chart. Its orbit scheme is therefore affine:
the closed orbit immersion factors as a closed immersion into that chart. On the other hand it
is proper, being closed in projective space, so its structural morphism is finite. The orbit
scheme is connected as a continuous image of the connected group scheme. A finite scheme over
an algebraically closed field has discrete underlying space, hence this connected orbit scheme
has only one point.

The conclusion applies to every scheme point of the group, not only to its rational points.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §10.4.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 17.5.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.Comodule

universe u

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
  [Group.IsSolvable (WithConv (H →ₐ[k] k))]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- The scheme of a closed projective orbit of a reduced connected solvable affine group is
affine. -/
theorem isAffine_projectiveOrbitScheme_of_isClosed_of_isSolvable
    (m : M) (hm : Module.IsUnimodular k m)
    (hclosed : IsClosed (Set.range (projectiveOrbitMap (H := H) m hm))) :
    IsAffine (projectiveOrbitScheme (H := H) m hm) := by
  let i := projectiveOrbitι (H := H) m hm
  let _ : IsClosedImmersion i := IsClosedImmersion.of_isPreimmersion i (by
    simpa only [i, range_projectiveOrbitι] using hclosed)
  obtain ⟨φ, hφ, horbit⟩ :=
    exists_isAffineOpen_range_projectiveOrbitMap_subset_of_isSolvable (H := H) m hm
  let U : (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M))).Opens :=
    Proj.basicOpen (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M))
      (SymmetricAlgebra.ι k (Module.Dual k M) φ)
  have hiU : Set.range i ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    simpa only [i, U, range_projectiveOrbitι] using horbit
  let j := IsOpenImmersion.lift U.ι i hiU
  let _ : IsClosedImmersion j := by
    change IsClosedImmersion (IsOpenImmersion.lift U.ι i hiU)
    exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (IsOpenImmersion.isPullback_lift_id i U.ι hiU).flip inferInstance
  have hU : IsAffineOpen U := by
    simpa only [U] using hφ
  let _ : IsAffine U := hU
  exact isAffine_of_isAffineHom j

/-- The structural morphism of a closed projective orbit of a reduced connected solvable affine
group is finite. -/
theorem isFinite_projectiveOrbitToSpec_of_isClosed_of_isSolvable
    (m : M) (hm : Module.IsUnimodular k m)
    (hclosed : IsClosed (Set.range (projectiveOrbitMap (H := H) m hm))) :
    IsFinite (projectiveOrbitToSpec (H := H) m hm) := by
  let i := projectiveOrbitι (H := H) m hm
  let _ : IsClosedImmersion i := IsClosedImmersion.of_isPreimmersion i (by
    simpa only [i, range_projectiveOrbitι] using hclosed)
  let _ : IsAffine (projectiveOrbitScheme (H := H) m hm) :=
    isAffine_projectiveOrbitScheme_of_isClosed_of_isSolvable m hm hclosed
  let _ : IsProper (projectiveOrbitToSpec (H := H) m hm) := by
    rw [projectiveOrbitToSpec_def]
    infer_instance
  exact IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩

/-- The scheme of a closed projective orbit of a reduced connected solvable affine group has at
most one point. -/
theorem subsingleton_projectiveOrbitScheme_of_isClosed_of_isSolvable
    (m : M) (hm : Module.IsUnimodular k m)
    (hclosed : IsClosed (Set.range (projectiveOrbitMap (H := H) m hm))) :
    Subsingleton (projectiveOrbitScheme (H := H) m hm) := by
  let _ : IsFinite (projectiveOrbitToSpec (H := H) m hm) :=
    isFinite_projectiveOrbitToSpec_of_isClosed_of_isSolvable m hm hclosed
  let _ : ConnectedSpace (Spec (.of H)) :=
    inferInstanceAs (ConnectedSpace (PrimeSpectrum H))
  let _ : ConnectedSpace (projectiveOrbitScheme (H := H) m hm) :=
    (toProjectiveOrbit (H := H) m hm).surjective.connectedSpace
      (toProjectiveOrbit (H := H) m hm).continuous
  have hpreimage :
      projectiveOrbitToSpec (H := H) m hm ⁻¹' {IsLocalRing.closedPoint k} = Set.univ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  let _ : Finite (projectiveOrbitScheme (H := H) m hm) :=
    Finite.of_finite_univ (hpreimage ▸
      (projectiveOrbitToSpec (H := H) m hm).finite_preimage_singleton
        (IsLocalRing.closedPoint k))
  exact subsingleton_of_preconnected_totallyDisconnected

/-- If a projective orbit of a reduced connected solvable affine group is closed, then every
scheme point of the group has the same image as the identity point. -/
theorem projectiveOrbitMap_eq_identity_of_isClosed_of_isSolvable
    (m : M) (hm : Module.IsUnimodular k m)
    (hclosed : IsClosed (Set.range (projectiveOrbitMap (H := H) m hm)))
    (x : Spec (.of H)) :
    projectiveOrbitMap (H := H) m hm x =
      projectiveOrbitMap (H := H) m hm
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) := by
  let _ : Subsingleton (projectiveOrbitScheme (H := H) m hm) :=
    subsingleton_projectiveOrbitScheme_of_isClosed_of_isSolvable m hm hclosed
  have hpoint :
      toProjectiveOrbit (H := H) m hm x =
        toProjectiveOrbit (H := H) m hm
          (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) :=
    Subsingleton.elim _ _
  have hi := congrArg (fun y ↦ projectiveOrbitι (H := H) m hm y) hpoint
  simpa only [← Scheme.Hom.comp_apply, toProjectiveOrbit_projectiveOrbitι] using hi

/-- A closed projective orbit of a reduced connected solvable affine group is the singleton
containing the identity image. -/
theorem range_projectiveOrbitMap_eq_singleton_of_isClosed_of_isSolvable
    (m : M) (hm : Module.IsUnimodular k m)
    (hclosed : IsClosed (Set.range (projectiveOrbitMap (H := H) m hm))) :
    Set.range (projectiveOrbitMap (H := H) m hm) =
      {projectiveOrbitMap (H := H) m hm
        (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact Set.mem_singleton_iff.mpr
      (projectiveOrbitMap_eq_identity_of_isClosed_of_isSolvable m hm hclosed x)
  · rintro rfl
    exact Set.mem_range_self _

/-- Every rational point of a reduced connected solvable affine group preserves the line of a
vector whose projective orbit is closed. -/
theorem map_span_eq_span_of_isClosed_range_projectiveOrbitMap_of_isSolvable
    (m : M) (hm : Module.IsUnimodular k m)
    (hclosed : IsClosed (Set.range (projectiveOrbitMap (H := H) m hm)))
    (g : WithConv (H →ₐ[k] k)) :
    (k ∙ m).map (basePointsRepresentation M g) = k ∙ m :=
  (projectiveOrbitMap_kernelPoint_eq_one_iff m hm g).mp
    (projectiveOrbitMap_eq_identity_of_isClosed_of_isSolvable m hm hclosed
      (AlgHom.kernelPoint g.ofConv))

end TauCeti.Comodule
