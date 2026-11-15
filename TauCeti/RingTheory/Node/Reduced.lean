/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.BranchSequence
public import TauCeti.RingTheory.Smooth.GeometricallyReduced
import Mathlib.LinearAlgebra.TensorProduct.Basis
import TauCeti.RingTheory.Node.BaseChange

/-!
# Reduced coordinate algebras of nodes

Every smoothing `xy = a` over a reduced ring is reduced. Over a field, the case `a = 0`
embeds in the product of its polynomial branch algebras, while for nonzero `a` the algebra
is smooth. The free module structure then detects nilpotents over a reduced base by passing
to all residue fields. The instance `TauCeti.NodeAlgebra.isReduced` thus supplies reducedness
of the standard nodal chart over any reduced base ring.

## References

* The Stacks Project, Section 53.19, *Nodal curves*, Tag 0C46.
-/

public section

noncomputable section

namespace TauCeti.NodeAlgebra

open scoped TensorProduct

private theorem isReduced_of_field {K : Type*} [Field K] (a : K) : IsReduced (NodeAlgebra K a) := by
  by_cases ha : a = 0
  · subst a
    exact isReduced_of_injective (branchMap K) (branchMap_injective K)
  · have : Algebra.IsStandardSmooth K (NodeAlgebra K a) :=
      (isStandardSmoothOfRelativeDimension_of_isUnit a (isUnit_iff_ne_zero.mpr ha)).isStandardSmooth
    exact TauCeti.isReduced_of_smooth K (NodeAlgebra K a)

/-- Every node smoothing over a reduced coefficient ring is reduced. -/
instance isReduced {R : Type*} [CommRing R] [IsReduced R] (a : R) :
    IsReduced (NodeAlgebra R a) := by
  let b := Module.Free.chooseBasis R (NodeAlgebra R a)
  constructor
  intro z hz
  apply b.repr.injective
  ext i
  suffices IsNilpotent (b.repr z i) by simpa using this.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro p hp
  let := hp
  let K := p.ResidueField
  have : IsReduced (NodeAlgebra K (algebraMap R K a)) := isReduced_of_field _
  have : IsReduced (K ⊗[R] NodeAlgebra R a) :=
    isReduced_of_injective (baseChange a) (baseChange a).injective
  have hzK : (1 : K) ⊗ₜ[R] z = 0 :=
    (hz.map (Algebra.TensorProduct.includeRight :
      NodeAlgebra R a →ₐ[R] K ⊗[R] NodeAlgebra R a)).eq_zero
  have hi := congrArg (fun w ↦ (b.baseChange K).repr w i) hzK
  simpa [Module.Basis.baseChange_repr_tmul, Algebra.smul_def,
    ← Ideal.algebraMap_residueField_eq_zero] using hi

end TauCeti.NodeAlgebra
