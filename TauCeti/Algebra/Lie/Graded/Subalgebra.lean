/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Graded.Hom
public import TauCeti.Algebra.DirectSum.Internal

/-!
# Gradings on homogeneous Lie subalgebras

A Lie subalgebra stable under homogeneous projection inherits the ambient Lie grading.
Its degree-`i` piece is the inverse image of the ambient degree-`i` piece under inclusion.
In particular, zero ambient pieces remain zero, so any restriction on the support of the
grading passes to the subalgebra.

`LieSubalgebra.gradedLieAlgebra` supplies the inherited structure as a local instance.
The decomposition is `TauCeti.DirectSum.Decomposition.restrict`; its projections are computed
by `TauCeti.DirectSum.map_decompose_restrict`, and membership is `Submodule.mem_comap`.

Adapted from `Mei/Algebra/Lie/Graded/Subalgebra.lean` in
[Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`68536122a97fed8e87bc6870b9427151971b9ab2` (Apache 2.0).
-/

public section

namespace LieSubalgebra

variable {ι R L : Type*} [DecidableEq ι] [AddCommMonoid ι]
  [CommRing R] [LieRing L] [LieAlgebra R L]

/-- A homogeneous Lie subalgebra inherits the Lie grading on the inverse images of the
ambient pieces. Use `letI := K.gradedLieAlgebra ℒ hK` to install the grading. -/
@[instance_reducible]
noncomputable def gradedLieAlgebra (K : LieSubalgebra R L)
    (ℒ : ι → Submodule R L) [GradedLieAlgebra ℒ]
    (hK : DirectSum.SetLike.IsHomogeneous ℒ K) :
    GradedLieAlgebra (fun i ↦ (ℒ i).comap K.incl.toLinearMap) where
  toDecomposition := TauCeti.DirectSum.Decomposition.restrict ℒ _ K.incl.toLinearMap
    Subtype.val_injective (fun _ _ ↦ Iff.rfl) (fun i x ↦
      ⟨⟨_, hK i x.property⟩, rfl⟩)
  toGradedBracket := inferInstance

end LieSubalgebra
