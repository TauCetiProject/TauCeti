/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Subfield

/-!
# Topology of general linear groups over subfields

If `E` is a closed subfield of a topological field `L`, the range of `GL ι E →* GL ι L`
along `SubringClass.subtype E` is closed in `GL ι L`, being cut out by entrywise membership in `E`.

## Main results

* `Matrix.GeneralLinearGroup.isClosed_range_map_subtype`: if `E` is closed in `L`, the range of
  `Matrix.GeneralLinearGroup.map (SubringClass.subtype E)` is closed in `GL ι L`.
-/

public section

namespace Matrix.GeneralLinearGroup

/-- **Closedness of the subfield general linear group.** If `E` is a closed subfield of a
topological field `L`, then the range of `GL ι E →* GL ι L` is closed in `GL ι L`. -/
theorem isClosed_range_map_subtype {L S ι : Type*} [Field L] [SetLike S L] [SubfieldClass S L]
    [TopologicalSpace L] [Fintype ι] [DecidableEq ι] {E : S} (hE : IsClosed (E : Set L)) :
    IsClosed ((Matrix.GeneralLinearGroup.map (n := ι) (SubringClass.subtype E)).range :
      Set (GL ι L)) := by
  have heq :
      ((Matrix.GeneralLinearGroup.map (n := ι) (SubringClass.subtype E)).range : Set (GL ι L)) =
        ⋂ i, ⋂ j, (fun A : GL ι L ↦ (A : Matrix ι ι L) i j) ⁻¹' (E : Set L) := by
    ext A
    simp only [SetLike.mem_coe, mem_range_map_subtype_iff, Set.mem_iInter, Set.mem_preimage]
  rw [heq]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
    hE.preimage (Units.continuous_val.matrix_elem i j)

end Matrix.GeneralLinearGroup
