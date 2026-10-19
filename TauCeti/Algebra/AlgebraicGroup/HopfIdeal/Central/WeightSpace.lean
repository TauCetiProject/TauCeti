/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Tangent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace

/-!
# Adjoint weight spaces of central subgroups and kernels

The Lie algebra of a central closed subgroup is fixed by the adjoint group action, including
in positive characteristic when the subgroup is infinitesimal. Consequently it lies in the
trivial weight space for every homomorphism from a diagonalizable group. Its intersection
with any nontrivial weight space is zero.

This group-level invariance is stronger than belonging to the center of the Lie algebra.
For homomorphisms with central kernel, the differential is injective on every nontrivial
weight space even when the kernel is infinitesimal. Accordingly every nontrivial source
weight occurs in the target after restriction to the same diagonalizable group. These
conclusions require neither finiteness nor faithful flatness, and do not assert surjectivity
on weight spaces.
The proof uses the universal adjoint-invariance characterization in `Center.Tangent`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10 and 21.1.
-/

public section

open CategoryTheory TensorProduct

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

namespace TauCeti.CommHopfAlgCat

universe u

open Derivation

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{u} k}
  [Module.Finite k (Bialgebra.CotangentSpace k K)]
  {X : Type u} [CommGroup X]

/-- A homomorphism with scheme-theoretically central kernel has injective differential on
every nontrivial adjoint weight space. This applies to inseparable central isogenies: the
kernel may be infinitesimal, and its tangent space contributes only trivial weights.
Neither finiteness nor faithful flatness of the homomorphism is required. -/
theorem injOn_dualCotangentMap_adjointWeightSpace_of_isCentral_kernel
    (f : H ⟶ K) (hcentral : (kernelHopfIdeal f).IsCentral)
    (π : K →ₐc[k] MonoidAlgebra k X) {α : X} (hα : α ≠ 1) :
    Set.InjOn (dualCotangentMap f.hom) (adjointWeightSpace π α) := by
  intro x hx y hy hxy
  apply sub_eq_zero.mp
  apply hcentral.eq_zero_of_mem_adjointWeightSpace π hα (Submodule.sub_mem _ hx hy)
  rw [lieSubalgebra_kernelHopfIdeal, LieIdeal.mem_toLieSubalgebra, LieHom.mem_ker,
    derivationCompLieHom_apply, ← cotangentLinearEquiv_dualCotangentMap]
  simp [map_sub, hxy]

variable [Module.Finite k (Bialgebra.CotangentSpace k H)]

/-- A homomorphism with central kernel preserves every nontrivial adjoint weight occurring
in its source. Both weight sets are indexed by the characters of the same diagonalizable
group, mapped into the target by composition. No separability assumption is needed. -/
theorem nontrivialAdjointWeights_subset_comp_of_isCentral_kernel
    (f : H ⟶ K) (hcentral : (kernelHopfIdeal f).IsCentral)
    (π : K →ₐc[k] MonoidAlgebra k X) :
    nontrivialAdjointWeights π ⊆ nontrivialAdjointWeights (π.comp f.hom) := by
  intro α hα
  rw [mem_nontrivialAdjointWeights] at hα ⊢
  obtain ⟨hα, hspace⟩ := hα
  obtain ⟨x, hx, hxne⟩ := (Submodule.ne_bot_iff _).mp hspace
  refine ⟨hα, (Submodule.ne_bot_iff _).mpr ⟨dualCotangentMap f.hom x,
    f.hom.dualCotangentMap_mem_adjointWeightSpace π α hx, ?_⟩⟩
  intro hzero
  exact hxne ((injOn_dualCotangentMap_adjointWeightSpace_of_isCentral_kernel f hcentral π hα)
    hx (Submodule.zero_mem _) (hzero.trans (map_zero _).symm))

end TauCeti.CommHopfAlgCat
