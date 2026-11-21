/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Torus
public import TauCeti.Geometry.Lie.Adjoint.Representation.Basic
public import TauCeti.RepresentationTheory.BaseChange
import TauCeti.RepresentationTheory.Continuous.Basic

/-!
# The zero weight of the maximal-torus adjoint action

For a maximal torus `T` in a compact finite-dimensional real Lie group `G`, the invariant subspace
of the restricted adjoint representation is `Lie(T)`. Indeed, fixed derivations are exactly the
Lie algebra of the centralizer, and that centralizer has Lie algebra `Lie(T)`.

The same identification survives extension to any commutative real algebra. In particular,
complexification identifies the trivial-character weight space with the actual complexified toral
Lie algebra inside the complexified ambient Lie algebra. The conclusion uses `Submodule.baseChange`;
Mathlib's `Submodule.toBaseChange.toLinearEquiv` identifies it with the tensor product of the toral
Lie algebra. Connectedness of `G` is not assumed. The scalar-extension theorem applies to
the possibly infinite acting group `T`.

## Main results

* `TauCeti.Lie.IsMaximalTorus.invariants_adjoint`: real adjoint invariants are the toral
  Lie algebra.
* `TauCeti.Lie.IsMaximalTorus.invariants_adjoint_baseChange`: invariants after scalar extension
  are the scalar-extended toral Lie algebra.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter V, § 1 (The Adjoint Representation and Groups of Rank 1), Definitions (1.1) and (1.3),
  and § 2 (Roots and Weyl Chambers), Proposition (2.3)(i), p.189.
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped ContDiff Manifold

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [CompactSpace G]

/-- The adjoint action restricted to a maximal torus has its Lie algebra as invariant subspace. -/
theorem IsMaximalTorus.invariants_adjoint {T : Subgroup G} (hT : IsMaximalTorus T) :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    Representation.invariants
      ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.comp T.subtype :
        Representation ℝ T (LeftInvariantDerivation I G)) =
      (lieSubalgebraOfSubgroup (I := I) T).toSubmodule := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  ext X
  rw [Representation.mem_invariants]
  have heval (k : T) :
      ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.comp T.subtype :
        Representation ℝ T (LeftInvariantDerivation I G)) k X = Ad (I := I) (k : G) X :=
    (ContRepresentation.toRepresentation_apply _ (k : G) X).trans
      (continuousAdjointRepresentation_apply (I := I) (k : G) X)
  simp_rw [heval]
  have hfixed := mem_lieSubalgebraOfSubgroup_centralizer_iff (I := I) T X
  dsimp only at hfixed
  rw [← hfixed, hT.lieSubalgebraOfSubgroup_centralizer, LieSubalgebra.mem_toSubmodule]

/-- After scalar extension, the torus adjoint invariants are the extended toral Lie algebra.
For complex scalars this is the zero-weight space of the complexified adjoint action. -/
theorem IsMaximalTorus.invariants_adjoint_baseChange {T : Subgroup G} (hT : IsMaximalTorus T)
    (A : Type*) [CommRing A] [Algebra ℝ A] :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    Representation.invariants (Representation.baseChange A
      ((continuousAdjointRepresentation (I := I) (G := G)).toRepresentation.comp T.subtype :
        Representation ℝ T (LeftInvariantDerivation I G))) =
      (lieSubalgebraOfSubgroup (I := I) T).toSubmodule.baseChange A := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  dsimp only
  rw [← Representation.invariants_baseChange, hT.invariants_adjoint]

end TauCeti.Lie
