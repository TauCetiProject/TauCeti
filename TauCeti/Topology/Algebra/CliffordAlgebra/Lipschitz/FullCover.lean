/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.FullCover
public import TauCeti.Topology.Algebra.CliffordAlgebra.Lipschitz.Norm
public import TauCeti.Topology.Algebra.CliffordAlgebra.Lipschitz.OpenMap
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Closed
public import Mathlib.Topology.Covering.Quotient
import TauCeti.Topology.Algebra.CliffordAlgebra.Pin.Basic
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# The normalized Clifford full cover is a covering of the orthogonal group

The normalized full Clifford cover `CliffordAlgebra.cliffordFullCover Q` is the subgroup of the
Lipschitz group on which the reverse Clifford norm is `1` or `-1`. This file studies it with the
subspace topology inherited from the units of the Clifford algebra.

On a finite-dimensional space over a Hausdorff topological field the reverse norm is continuous,
so the full cover is closed in the Lipschitz group. For a nondegenerate form it is therefore a
closed subgroup of the Clifford units, and the Spin group, with its subspace topology from the
Clifford algebra, is in turn a closed subgroup of the full cover. The action of the full cover on
the quadratic space, the restriction of the twisted-conjugation action of the Lipschitz group, is
continuous.

An element of the full cover acting trivially is a scalar `r` whose norm `r ^ 2` is `±1`, so
`r ^ 4 = 1`: the kernel of the action is finite over every field
(`CliffordAlgebra.finite_ker_cliffordFullCoverToOrthogonal`). When every element of the field
is a square up to sign, as over `ℝ` (`IsRealClosed.isSquare_or_isSquare_neg`) or `ℂ`, the action is
onto the orthogonal group (`CliffordAlgebra.cliffordFullCoverToOrthogonal_surjective`). Over a
locally compact σ-compact field the full cover is σ-compact, being closed in the σ-compact
Lipschitz group, so the open mapping theorem for topological groups makes the surjective action
open. A continuous open surjective homomorphism of topological groups with discrete kernel is a
covering map, so the full cover is a covering of the orthogonal group. Over `ℝ`, in positive
dimension, the kernel is `{±1}` (`CliffordAlgebra.ker_cliffordFullCoverToOrthogonal`), so the
covering is two-sheeted.

## Main results

* `CliffordAlgebra.isClosed_cliffordFullCover`: the full cover is closed in the Lipschitz group.
* `CliffordAlgebra.isClosedEmbedding_cliffordFullCover_val`: the inclusion of the full cover in
  the Clifford units is a closed embedding.
* `CliffordAlgebra.isClosedEmbedding_spinToCliffordFullCover`: the Spin group is a closed
  subgroup of the full cover, with its own topology.
* `CliffordAlgebra.continuous_cliffordFullCoverToOrthogonal`: the action is continuous.
* `CliffordAlgebra.isOpenMap_cliffordFullCoverToOrthogonal`: over a locally compact σ-compact field
  in which every element is a square up to sign, the action is open.
* `CliffordAlgebra.isQuotientCoveringMap_cliffordFullCoverToOrthogonal` and
  `CliffordAlgebra.isCoveringMap_cliffordFullCoverToOrthogonal`: under the same hypotheses the
  action is a covering map, the quotient by its kernel.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, Section 2.
* J. Gallier, *Clifford Algebras, Clifford Groups, and a Generalization of the Quaternions: The
  Pin and Spin Groups*, arXiv:0805.0311v3, Definition 1.6 and Proposition 1.21.
-/

public section

namespace CliffordAlgebra

open TauCeti Topology

variable {K V : Type*} [Field K] [TopologicalSpace K]
  [Invertible (2 : K)] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (Q : QuadraticForm K V)

/-- The action of the normalized full cover on the quadratic space is continuous. -/
@[fun_prop]
theorem continuous_cliffordFullCoverToOrthogonal [IsTopologicalSemiring K] :
    Continuous (cliffordFullCoverToOrthogonal Q) :=
  ((continuous_lipschitzToOrthogonal Q).comp continuous_subtypeVal).congr fun x ↦
    (cliffordFullCoverToOrthogonal_apply Q x).symm

variable [IsTopologicalRing K] [T2Space K]

/-- The normalized full cover is closed in the Lipschitz group: it is the inverse image of the
closed set `{1, -1}` under the continuous reverse Clifford norm. -/
theorem isClosed_cliffordFullCover :
    IsClosed (cliffordFullCover Q : Set (lipschitzGroup Q)) := by
  have h : (cliffordFullCover Q : Set (lipschitzGroup Q)) =
      (fun x => (cliffordNorm Q x : K)) ⁻¹' {1, -1} := by
    ext x
    simp only [SetLike.mem_coe, mem_cliffordFullCover_iff, Set.mem_preimage,
      Set.mem_insert_iff, Set.mem_singleton_iff, Units.ext_iff, Units.val_one, Units.val_neg]
  rw [h]
  exact (Set.toFinite _).isClosed.preimage (Units.continuous_val.comp (continuous_cliffordNorm Q))

/-- The inclusion of the normalized full cover of a nondegenerate quadratic form in the units of
the Clifford algebra is a closed embedding: the full cover is a closed subgroup of the Clifford
units, carrying the subspace topology. -/
theorem isClosedEmbedding_cliffordFullCover_val (hQ : Q.Nondegenerate) :
    IsClosedEmbedding fun x : cliffordFullCover Q =>
      ((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ) :=
  (isClosed_lipschitzGroup Q hQ).isClosedEmbedding_subtypeVal.comp
    (isClosed_cliffordFullCover Q).isClosedEmbedding_subtypeVal

/-- The inclusion of the Spin group of a nondegenerate quadratic form in its normalized full cover
is a closed embedding, for the subspace topology on the Spin group from the Clifford algebra and on
the full cover from the Clifford units. -/
theorem isClosedEmbedding_spinToCliffordFullCover (hQ : Q.Nondegenerate) :
    IsClosedEmbedding (spinToCliffordFullCover Q) := by
  let c : cliffordFullCover Q → CliffordAlgebra Q := fun x ↦
    ((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ)
  have hc : Continuous c :=
    Units.continuous_val.comp (continuous_subtypeVal.comp continuous_subtypeVal)
  have hinj : Function.Injective c := fun x y h ↦ Subtype.ext (Subtype.ext (Units.ext h))
  have hcomp : c ∘ spinToCliffordFullCover Q = Subtype.val := funext fun x ↦ by
    simp [c, spinToLipschitz_apply, coe_pinToLipschitz_apply, coe_spinToPin_apply]
  have hcont : Continuous (spinToCliffordFullCover Q) :=
    continuous_induced_rng.mpr <|
      ((TauCeti.CliffordAlgebra.continuous_pinToLipschitz Q).comp
        (TauCeti.CliffordAlgebra.continuous_spinToPin Q)).congr fun x ↦ by
          simp only [Function.comp_apply, coe_spinToCliffordFullCover_apply, spinToLipschitz_apply]
  have hrange : Set.range (spinToCliffordFullCover Q) = c ⁻¹' (spinGroup Q : Set _) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [Set.mem_preimage, ← Function.comp_apply (f := c), hcomp]
      exact y.property
    · intro hx
      exact ⟨⟨c x, hx⟩, hinj (congrFun hcomp _)⟩
  refine ⟨.of_comp hcont hc ?_, ?_⟩
  · rw [hcomp]
    exact .subtypeVal
  · rw [hrange]
    exact (isClosed_spinGroup Q hQ).preimage hc

/-- The normalized full cover of a nondegenerate quadratic form over a σ-compact field is
σ-compact, being closed in the σ-compact Lipschitz group. -/
theorem sigmaCompactSpace_cliffordFullCover [SigmaCompactSpace K] (hQ : Q.Nondegenerate) :
    SigmaCompactSpace (cliffordFullCover Q) :=
  have := sigmaCompactSpace_lipschitzGroup Q hQ
  (isClosed_cliffordFullCover Q).sigmaCompactSpace

variable [LocallyCompactSpace K] [SigmaCompactSpace K]

/-- **The full-cover action is open.** For a nondegenerate quadratic form on a finite-dimensional
space over a Hausdorff, locally compact and σ-compact topological field in which every element is
a square up to sign, such as `ℝ` or `ℂ`, the action of the normalized full cover on the orthogonal
group is an open map. -/
theorem isOpenMap_cliffordFullCoverToOrthogonal (hQ : Q.Nondegenerate)
    (hK : ∀ a : K, IsSquare a ∨ IsSquare (-a)) :
    IsOpenMap (cliffordFullCoverToOrthogonal Q) := by
  let _ : TopologicalSpace V := moduleTopology K V
  have : IsModuleTopology K V := ⟨rfl⟩
  have := sigmaCompactSpace_cliffordFullCover Q hQ
  exact (cliffordFullCoverToOrthogonal Q).isOpenMap_of_sigmaCompact
    (cliffordFullCoverToOrthogonal_surjective hQ hK) (continuous_cliffordFullCoverToOrthogonal Q)

/-- **The full cover is a covering of the orthogonal group.** For a nondegenerate quadratic form on
a finite-dimensional space over a Hausdorff, locally compact and σ-compact topological field in
which every element is a square up to sign, the action of the normalized full cover onto the
orthogonal group is the quotient covering map associated to the action of its finite kernel. -/
theorem isQuotientCoveringMap_cliffordFullCoverToOrthogonal (hQ : Q.Nondegenerate)
    (hK : ∀ a : K, IsSquare a ∨ IsSquare (-a)) :
    IsQuotientCoveringMap (cliffordFullCoverToOrthogonal Q)
      (cliffordFullCoverToOrthogonal Q).ker :=
  (isOpenMap_cliffordFullCoverToOrthogonal Q hQ hK).isQuotientMap
    (continuous_cliffordFullCoverToOrthogonal Q) (cliffordFullCoverToOrthogonal_surjective hQ hK)
    |>.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
      (finite_ker_cliffordFullCoverToOrthogonal hQ).isDiscrete

/-- **The full cover is a covering map** onto the orthogonal group, for a nondegenerate quadratic
form on a finite-dimensional space over a Hausdorff, locally compact and σ-compact topological
field in which every element is a square up to sign, such as `ℝ` or `ℂ`. -/
theorem isCoveringMap_cliffordFullCoverToOrthogonal (hQ : Q.Nondegenerate)
    (hK : ∀ a : K, IsSquare a ∨ IsSquare (-a)) :
    IsCoveringMap (cliffordFullCoverToOrthogonal Q) :=
  (isQuotientCoveringMap_cliffordFullCoverToOrthogonal Q hQ hK).isCoveringMap

end CliffordAlgebra
