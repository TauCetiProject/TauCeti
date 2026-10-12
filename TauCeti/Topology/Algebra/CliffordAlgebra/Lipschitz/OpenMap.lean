/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Lipschitz.Action
public import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.Closed
public import TauCeti.Topology.Algebra.Group.Units
public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.CliffordGroup
public import Mathlib.Topology.Algebra.Group.OpenMapping
import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Generators
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# The vector representation of the Lipschitz group is open

For a nondegenerate quadratic form on a finite-dimensional space over a Hausdorff topological
field in which `2` is invertible, Mathlib's Lipschitz group is closed in the units of the Clifford
algebra. When `V` is nontrivial it is the classical Clifford group of units whose twisted
conjugation preserves the vectors, and each of these conditions is closed; when `V` is trivial it
is the trivial subgroup (although then every unit preserves the zero vector space), which is
closed as a point. Over a locally compact σ-compact field, such as
`ℝ` or `ℚ_p`, the Lipschitz group is therefore σ-compact, while the orthogonal group is locally
compact and Hausdorff. The open mapping theorem for topological groups then shows that the
surjective continuous vector representation `lipschitzToOrthogonal` is an open map.

Openness is what lets a property of Lipschitz elements that is open in the Clifford algebra
descend to an open subset of the orthogonal group; the spinor kernel is the main example.

## Main results

* `CliffordAlgebra.isClosed_lipschitzGroup`: the Lipschitz group is closed in the units of the
  Clifford algebra.
* `CliffordAlgebra.sigmaCompactSpace_lipschitzGroup`: over a σ-compact field it is σ-compact.
* `CliffordAlgebra.isOpenMap_lipschitzToOrthogonal`: over a locally compact σ-compact field the
  vector representation onto the orthogonal group is an open map.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
-/

public section

open Set

namespace CliffordAlgebra

open TauCeti

variable {K V : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
  [Invertible (2 : K)] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (Q : QuadraticForm K V)

/-- The Lipschitz group of a nondegenerate quadratic form on a finite-dimensional space over a
Hausdorff topological field in which `2` is invertible is closed in the units of the Clifford
algebra with its module topology. -/
theorem isClosed_lipschitzGroup (hQ : Q.Nondegenerate) :
    IsClosed (lipschitzGroup Q : Set (CliffordAlgebra Q)ˣ) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [lipschitzGroup_eq_bot, Subgroup.coe_bot]
    exact isClosed_singleton
  · have h : (lipschitzGroup Q : Set (CliffordAlgebra Q)ˣ) =
        ⋂ m, (fun x : (CliffordAlgebra Q)ˣ => involute (Q := Q) ↑x * ι Q m * ↑x⁻¹) ⁻¹'
          (LinearMap.range (ι Q) : Set (CliffordAlgebra Q)) := by
      ext x
      simp only [SetLike.mem_coe,
        mem_lipschitzGroup_iff_involute_act_ι_mem_range_ι Q hQ hQ.exists_isUnit, mem_iInter,
        mem_preimage]
    rw [h]
    exact isClosed_iInter fun m => (Submodule.isClosed_of_isModuleTopology _).preimage
      ((((continuous_involute Q).comp Units.continuous_val).mul continuous_const).mul
        Units.continuous_coe_inv)

/-- Over a Hausdorff σ-compact topological field in which `2` is invertible, the Lipschitz group
of a nondegenerate quadratic form on a finite-dimensional space is σ-compact, being closed in the
units of the σ-compact Clifford algebra. -/
theorem sigmaCompactSpace_lipschitzGroup [SigmaCompactSpace K] (hQ : Q.Nondegenerate) :
    SigmaCompactSpace (lipschitzGroup Q) :=
  (isClosed_lipschitzGroup Q hQ).sigmaCompactSpace

/-- **The vector representation is open.** For a nondegenerate quadratic form on a
finite-dimensional space over a Hausdorff, locally compact and σ-compact topological field in
which `2` is invertible, the twisted-conjugation homomorphism from the Lipschitz group onto the
orthogonal group is an open map for the canonical subgroup topologies. -/
theorem isOpenMap_lipschitzToOrthogonal [LocallyCompactSpace K] [SigmaCompactSpace K]
    (hQ : Q.Nondegenerate) : IsOpenMap (lipschitzToOrthogonal Q) := by
  let _ : TopologicalSpace V := moduleTopology K V
  have : IsModuleTopology K V := ⟨rfl⟩
  have := sigmaCompactSpace_lipschitzGroup Q hQ
  exact (lipschitzToOrthogonal Q).isOpenMap_of_sigmaCompact
    (lipschitzToOrthogonal_surjective Q hQ) (continuous_lipschitzToOrthogonal Q)

end CliffordAlgebra
