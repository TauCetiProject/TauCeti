/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Internal
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.Basis

/-!
# The canonical torus coaction on an admissible lattice

A Kostant-stable subgroup lying in the sum of its integral Cartan weight spaces has a
canonical coaction of the integral group algebra of the additive weight group `κ → ℤ`.
For finite `κ`, this is a representation of the split torus with that character lattice.
It does not require a choice of integral weight basis, finite generation, or that the
subgroup span the ambient rational module.

`kostantWeightComodule` integrates the integral weight decomposition. Its character
spaces are exactly `weightSublattice`, not eigenspaces formed by reducing Lie eigenvalues
modulo a prime. The generic comodule base-change and point-action constructions can
therefore specialize this representation while retaining the integral character labels.
No identification with a torus in an independently constructed reductive group is asserted.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §27.1.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.1.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {ι κ V : Type*}
  [AddCommGroup V] [Module ℚ V]
  (e : ι → L) (h : κ → L)
  (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
  (M : AddSubgroup V)
  (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
  (hV : ∀ x : M, (x : V) ∈ ⨆ μ : κ → ℤ, jointWeightSpace h ρ μ)

include e hM hV in
private theorem isInternal_multiplicativeWeights [DecidableEq (Multiplicative (κ → ℤ))] :
    DirectSum.IsInternal fun μ : Multiplicative (κ → ℤ) =>
      weightSublattice h ρ M μ.toAdd := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    ((iSupIndep_weightSublattice h ρ M).comp Multiplicative.toAdd.injective)
  exact (Multiplicative.toAdd.surjective.iSup_comp (weightSublattice h ρ M)).trans
    (iSup_weightSublattice_eq_top e h ρ M hM hV)

/-- The integral diagonalizable-group representation of a Kostant-stable subgroup given by
its Cartan weights. For a finite Cartan index this is a split-torus representation. -/
@[instance_reducible]
noncomputable def kostantWeightComodule :
    Comodule ℤ (MonoidAlgebra ℤ (Multiplicative (κ → ℤ))) M :=
  letI := Classical.decEq (Multiplicative (κ → ℤ))
  (isInternal_multiplicativeWeights e h ρ M hM hV).monoidAlgebraComodule

/-- An integral weight vector coacts by its original integral character.
Supply the weight explicitly when rewriting: the coaction of zero does not determine it. -/
theorem coact_kostantWeightComodule_of_mem {μ : κ → ℤ} {v : M}
    (hv : v ∈ weightSublattice h ρ M μ) :
    letI := kostantWeightComodule e h ρ M hM hV
    Comodule.coact (R := ℤ) (C := MonoidAlgebra ℤ (Multiplicative (κ → ℤ))) v =
      v ⊗ₜ[ℤ] MonoidAlgebra.single (Multiplicative.ofAdd μ) 1 := by
  classical
  exact (isInternal_multiplicativeWeights e h ρ M hM hV).coact_monoidAlgebraComodule_of_mem hv

end TauCeti.UniversalEnvelopingAlgebra
