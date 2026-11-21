/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Subcomplex
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Data.Fintype.Powerset

/-!
# The topology of finite polyhedra

For a complex with finitely many faces, the weak topology of its realization agrees with
its barycentric-coordinate topology. In particular, the realization is compact and its
coordinate map into `ι → ℝ` is a closed embedding, so the realization is homeomorphic to its
coordinate image. This permits finite polyhedra, including finite local models of triangulated
manifolds, to be treated as ordinary coordinate subspaces.

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
    IsCompact {x : Realization K | x.val.support ∈ L} := by
  let C : L.faces → Set (Realization K) :=
    fun σ => range (faceInclusion K ⟨σ.val, hL σ.property⟩)
  have : Finite L.faces := hfin.to_subtype
  have heq : {x : Realization K | x.val.support ∈ L} = ⋃ σ, C σ := by
    ext x
    constructor
    · intro hx
      exact mem_iUnion.mpr ⟨⟨x.val.support, hx⟩,
        ⟨⟨x.val, by simpa only [carrier_val] using mem_convexHull_carrier K x⟩,
          Subtype.ext (faceInclusion_val _ _ _)⟩⟩
    · intro hx
      obtain ⟨σ, y, rfl⟩ := mem_iUnion.mp hx
      exact support_faceInclusion_mem hL σ.property y
  rw [heq]
  exact isCompact_iUnion fun σ => isCompact_range (continuous_faceInclusion K ⟨σ.val,
      hL σ.property⟩)

/-- The weak realization of a complex with finitely many faces is compact. -/
theorem compactSpace_realization_of_finite_faces (hfin : K.faces.Finite) :
    CompactSpace (Realization K) := by
  have hc := K.isCompact_setOf_support_mem le_rfl hfin
  have heq : {x : Realization K | x.val.support ∈ K.toPreAbstractSimplicialComplex} = univ :=
    Set.eq_univ_of_forall fun x => support_mem K x
  rw [heq] at hc
  exact ⟨hc⟩

/-- The weak realization of a complex on a finite vertex type is compact. -/
instance instCompactSpaceRealization [Finite ι] (K : AbstractSimplicialComplex ι) :
    CompactSpace (Realization K) := by
  let := Fintype.ofFinite ι
  exact K.compactSpace_realization_of_finite_faces (Set.toFinite K.faces)

/-- The weak realization of a complex with finitely many faces is compact. -/
instance instCompactSpaceRealizationOfFiniteFace (K : AbstractSimplicialComplex ι)
    [Finite (Face K)] : CompactSpace (Realization K) :=
  K.compactSpace_realization_of_finite_faces (Set.toFinite K.faces)

/-- Barycentric coordinates restrict to a closed embedding on every compact subset of
the weak realization. This applies in particular to compact local chart domains. -/
theorem isClosedEmbedding_realization_coe_restrict {s : Set (Realization K)} (hs : IsCompact s) :
    Topology.IsClosedEmbedding (fun x : s => (x.val.val : ι → ℝ)) := by
  let : CompactSpace s := isCompact_iff_compactSpace.mp hs
  exact ((continuous_realization_coe K).comp continuous_subtypeVal).isClosedEmbedding
    ((injective_realization_coe K).comp Subtype.val_injective)

/-- For a complex with finitely many faces the barycentric-coordinate map is a closed
embedding. Thus the weak topology is exactly the topology inherited from coordinate space. -/
theorem isClosedEmbedding_realization_coe (hfin : K.faces.Finite) :
    Topology.IsClosedEmbedding (fun x : Realization K => (x.val : ι → ℝ)) := by
  let : CompactSpace (Realization K) := K.compactSpace_realization_of_finite_faces hfin
  exact (continuous_realization_coe K).isClosedEmbedding (injective_realization_coe K)

/-- For a complex with finitely many faces, the weak realization is homeomorphic to its image in
coordinate space under the barycentric-coordinate map. -/
def realizationHomeomorphRange (hfin : K.faces.Finite) :
    Realization K ≃ₜ range fun x : Realization K => (x.val : ι → ℝ) :=
  (K.isClosedEmbedding_realization_coe hfin).isEmbedding.toHomeomorph

@[simp]
theorem coe_realizationHomeomorphRange_apply (hfin : K.faces.Finite) (x : Realization K) :
    (K.realizationHomeomorphRange hfin x : ι → ℝ) = x.val :=
  Topology.IsEmbedding.toHomeomorph_apply_coe _ x

@[simp]
theorem coe_realizationHomeomorphRange_symm_apply (hfin : K.faces.Finite)
    (y : range fun x : Realization K => (x.val : ι → ℝ)) :
    (((K.realizationHomeomorphRange hfin).symm y).val : ι → ℝ) = y :=
  congrArg Subtype.val ((K.realizationHomeomorphRange hfin).apply_symm_apply y)

/-- Distances in the coordinate image of `|K|` are distances of barycentric coordinates. -/
theorem dist_eq_norm_realizationHomeomorphRange_symm [Fintype ι] (hfin : K.faces.Finite)
    (p q : range fun x : Realization K => (x.val : ι → ℝ)) :
    dist p q = ‖(((K.realizationHomeomorphRange hfin).symm p).val : ι → ℝ) -
      ((K.realizationHomeomorphRange hfin).symm q).val‖ := by
  rw [Subtype.dist_eq, dist_eq_norm, coe_realizationHomeomorphRange_symm_apply,
    coe_realizationHomeomorphRange_symm_apply]

end AbstractSimplicialComplex
