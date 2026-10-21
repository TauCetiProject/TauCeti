/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace

/-!
# Adjoint weight spaces under separable isogenies

An isogeny between smooth affine groups with étale kernel identifies their Lie algebras.
For any homomorphism from a diagonalizable group into the source, the differential identifies
each adjoint weight space with the corresponding weight space in the target. In particular,
the sets of nontrivial adjoint weights agree when indexed by the characters of that same
diagonalizable group. For maximal tori in reductive groups, this is the comparison of root
spaces used in studying central isogenies and root data.

The coordinate arrow `f : H ⟶ K` represents `Spec K → Spec H`. A homomorphism from a
diagonalizable group to `Spec K` is specified by `π : K →ₐc[k] k[M]`; composing with the isogeny
gives `π.comp f.hom`. Neither maximality nor centrality is required for the weight comparison.
The étale-kernel hypothesis is essential: a Frobenius isogeny can have zero differential.
The comparison therefore applies in any characteristic, without asserting it for inseparable
isogenies.

The Lie equivalence is `IsIsogeny.lieEquivOfEtaleKernel`, transported through cotangent
duality. Weight compatibility uses equivariance over the universal point of the diagonalizable
group, rather than testing just ground-field-valued points.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10 and 21.1.
* T. A. Springer, *Linear Algebraic Groups*, §9.6.
-/

public section

open CategoryTheory Derivation

namespace TauCeti.CommHopfAlgCat.IsIsogeny

universe u

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{u} k}
  [Algebra.Smooth k H] [Algebra.Smooth k K] {f : H ⟶ K}

variable {M : Type u} [CommGroup M]

/-- The differential of a smooth isogeny with étale kernel detects adjoint weight vectors.
Both weights are indexed by the characters of the diagonalizable group in the source. -/
theorem dualCotangentMap_mem_adjointWeightSpace_iff (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal))
    (π : K →ₐc[k] MonoidAlgebra k M) (α : M)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    dualCotangentMap f.hom x ∈ adjointWeightSpace (π.comp f.hom) α ↔
      x ∈ adjointWeightSpace π α :=
  f.hom.dualCotangentMap_mem_adjointWeightSpace_iff_of_injective
    (hf.dualCotangentMap_bijective_of_etaleKernel hker).injective π α x

/-- An isogeny with étale kernel carries each adjoint weight space onto the corresponding
weight space of the target. -/
theorem map_dualCotangentMap_adjointWeightSpace (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal))
    (π : K →ₐc[k] MonoidAlgebra k M) (α : M) :
    (adjointWeightSpace π α).map (dualCotangentMap f.hom) =
      adjointWeightSpace (π.comp f.hom) α :=
  f.hom.map_dualCotangentMap_adjointWeightSpace_of_bijective
    (hf.dualCotangentMap_bijective_of_etaleKernel hker) π α

/-- The differential of an isogeny with étale kernel restricts to an equivalence of each
adjoint weight space. -/
noncomputable def adjointWeightSpaceEquivOfEtaleKernel (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal))
    (π : K →ₐc[k] MonoidAlgebra k M) (α : M) :
    adjointWeightSpace π α ≃ₗ[k] adjointWeightSpace (π.comp f.hom) α :=
  f.hom.adjointWeightSpaceEquivOfBijective
    (hf.dualCotangentMap_bijective_of_etaleKernel hker) π α

/-- On weight vectors the restricted equivalence is the differential. -/
@[simp]
theorem coe_adjointWeightSpaceEquivOfEtaleKernel_apply (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal))
    (π : K →ₐc[k] MonoidAlgebra k M) (α : M) (x : adjointWeightSpace π α) :
    (hf.adjointWeightSpaceEquivOfEtaleKernel hker π α x :
        Module.Dual k (Bialgebra.CotangentSpace k H)) = dualCotangentMap f.hom x := by
  exact f.hom.coe_adjointWeightSpaceEquivOfBijective_apply _ π α x

/-- A smooth isogeny with étale kernel preserves the nontrivial adjoint weights after
restriction to the same diagonalizable group in its source. -/
@[simp]
theorem nontrivialAdjointWeights_comp (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal))
    (π : K →ₐc[k] MonoidAlgebra k M) :
    nontrivialAdjointWeights (π.comp f.hom) = nontrivialAdjointWeights π :=
  f.hom.nontrivialAdjointWeights_comp_of_bijective
    (hf.dualCotangentMap_bijective_of_etaleKernel hker) π

end TauCeti.CommHopfAlgCat.IsIsogeny
