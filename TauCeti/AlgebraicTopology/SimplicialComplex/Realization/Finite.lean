/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Subcomplex
import Mathlib.Data.Fintype.Powerset

/-!
# The topology of finite polyhedra

For a complex with finitely many faces, the weak topology of its realization agrees with
its barycentric-coordinate topology. In particular, the realization is compact and its
coordinate map into `ι → ℝ` is a closed embedding. This permits finite polyhedra, including
finite local models of triangulated manifolds, to be treated as ordinary coordinate subspaces.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (polyhedra and their topology).
-/

public section

noncomputable section

open Set TauCeti.SetLike
open scoped Set.Notation

namespace AbstractSimplicialComplex

variable {ι : Type*}

attribute [local instance] Classical.decEq

variable (K : AbstractSimplicialComplex ι)

/-- A finite subcomplex occupies a compact subset of the weak realization. -/
theorem isCompact_setOf_support_mem {L : PreAbstractSimplicialComplex ι}
    (hL : L ≤ K.toPreAbstractSimplicialComplex) (hfin : L.faces.Finite) :
    IsCompact {x : Realization K | x.1.support ∈ L} := by
  let C : L.faces → Set (Realization K) :=
    fun σ => range (faceInclusion K ⟨σ.1, hL σ.2⟩)
  have : Finite L.faces := hfin.to_subtype
  have heq : {x : Realization K | x.1.support ∈ L} = ⋃ σ, C σ := by
    ext x
    constructor
    · intro hx
      exact mem_iUnion.mpr ⟨⟨x.1.support, hx⟩,
        ⟨⟨x.1, by simpa only [carrier_val] using mem_convexHull_carrier K x⟩,
          Subtype.ext (faceInclusion_val _ _ _)⟩⟩
    · intro hx
      obtain ⟨σ, y, rfl⟩ := mem_iUnion.mp hx
      exact support_faceInclusion_mem hL σ.2 y
  rw [heq]
  exact isCompact_iUnion fun σ => isCompact_range (continuous_faceInclusion K ⟨σ.1, hL σ.2⟩)

/-- The weak realization of a complex with finitely many faces is compact. -/
theorem compactSpace_realization_of_finite_faces (hfin : K.faces.Finite) :
    CompactSpace (Realization K) := by
  have hc := K.isCompact_setOf_support_mem le_rfl hfin
  have heq : {x : Realization K | x.1.support ∈ K.toPreAbstractSimplicialComplex} = univ :=
    Set.eq_univ_of_forall fun x => support_mem K x
  rw [heq] at hc
  exact ⟨hc⟩

/-- The weak realization of a complex on a finite vertex type is compact. -/
instance instCompactSpaceRealization [Finite ι] (K : AbstractSimplicialComplex ι) :
    CompactSpace (Realization K) := by
  let := Fintype.ofFinite ι
  exact K.compactSpace_realization_of_finite_faces (Set.toFinite K.faces)

/-- Barycentric coordinates restrict to a closed embedding on every compact subset of
the weak realization. This applies in particular to compact local chart domains. -/
theorem isClosedEmbedding_realization_coe_restrict {s : Set (Realization K)} (hs : IsCompact s) :
    Topology.IsClosedEmbedding (fun x : s => (x.1.1 : ι → ℝ)) := by
  let : CompactSpace s := isCompact_iff_compactSpace.mp hs
  exact ((continuous_realization_coe K).comp continuous_subtype_val).isClosedEmbedding
    ((injective_realization_coe K).comp Subtype.val_injective)

/-- For a complex with finitely many faces the barycentric-coordinate map is a closed
embedding. Thus the weak topology is exactly the topology inherited from coordinate space. -/
theorem isClosedEmbedding_realization_coe (hfin : K.faces.Finite) :
    Topology.IsClosedEmbedding (fun x : Realization K => (x.1 : ι → ℝ)) := by
  let : CompactSpace (Realization K) := K.compactSpace_realization_of_finite_faces hfin
  exact (continuous_realization_coe K).isClosedEmbedding (injective_realization_coe K)

end AbstractSimplicialComplex
