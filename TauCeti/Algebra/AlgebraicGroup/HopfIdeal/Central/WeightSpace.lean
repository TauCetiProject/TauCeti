/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace

/-!
# Central subgroups have trivial adjoint weights

The Lie algebra of a central closed subgroup is fixed by the adjoint group action, including
in positive characteristic when the subgroup is infinitesimal. Consequently it lies in the
trivial weight space for every homomorphism from a diagonalizable group. Its intersection
with any nontrivial weight space is zero.

This group-level invariance is stronger than belonging to the center of the Lie algebra.
It controls the differential kernel of a central isogeny even when that kernel is not étale.
The proof uses the universal adjoint-invariance characterization in `Center.Tangent`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10 and 21.1.
-/

public section

open TensorProduct

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k] {H : CommHopfAlgCat.{u} k}
  [Module.Finite k (Bialgebra.CotangentSpace k H)]
  {X : Type u} [CommGroup X] {I : HopfIdeal k H}

/-- A tangent vector of a central subgroup has trivial weight under every diagonalizable
subgroup of the ambient group. No smoothness or reducedness is required. -/
theorem IsCentral.mem_adjointWeightSpace_one (hI : I.IsCentral)
    (π : H →ₐc[k] MonoidAlgebra k X)
    {x : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (hx : Derivation.cotangentLinearEquiv (B := k) x ∈ I.lieSubalgebra (B := k)) :
    x ∈ Derivation.adjointWeightSpace π 1 := by
  have hcenter : Derivation.cotangentLinearEquiv (B := k) x ∈
      (CommHopfAlgCat.centerDefiningIdeal H).lieSubalgebra (B := k) := by
    rw [mem_lieSubalgebra_iff] at hx ⊢
    exact fun a ha ↦ hx a ((CommHopfAlgCat.centerDefiningIdeal_le_iff H I).mpr hI ha)
  have hcoact :=
    (CommHopfAlgCat.coact_adjointComodule_eq_tmul_one_iff_mem_lieSubalgebra_centerDefiningIdeal
      H x).mpr hcenter
  rw [Derivation.mem_adjointWeightSpace, hcoact]
  simp [MonoidAlgebra.one_def]

/-- A nontrivial adjoint weight vector in the Lie algebra of a central closed subgroup
vanishes, including for nonreduced central subgroups in positive characteristic. -/
theorem IsCentral.eq_zero_of_mem_adjointWeightSpace (hI : I.IsCentral)
    (π : H →ₐc[k] MonoidAlgebra k X) {α : X} (hα : α ≠ 1)
    {x : Module.Dual k (Bialgebra.CotangentSpace k H)}
    (hx : x ∈ Derivation.adjointWeightSpace π α)
    (hxI : Derivation.cotangentLinearEquiv (B := k) x ∈ I.lieSubalgebra (B := k)) :
    x = 0 := by
  classical
  have hdisj := (Derivation.isInternal_adjointWeightSpace π).submodule_iSupIndep.pairwiseDisjoint hα
  exact (Submodule.disjoint_def.mp hdisj) x hx (hI.mem_adjointWeightSpace_one π hxI)

end TauCeti.HopfIdeal
