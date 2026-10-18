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

/-- The differential of an isogeny with étale kernel, on cotangent duals. -/
noncomputable def dualCotangentEquivOfEtaleKernel (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal)) :
    Module.Dual k (Bialgebra.CotangentSpace k K) ≃ₗ[k]
      Module.Dual k (Bialgebra.CotangentSpace k H) :=
  (cotangentLinearEquiv (R := k) (A := K) (B := k)).trans
    ((hf.lieEquivOfEtaleKernel hker).toLinearEquiv.trans
      (cotangentLinearEquiv (R := k) (A := H) (B := k)).symm)

/-- The transported equivalence has the canonical differential as its underlying linear map. -/
@[simp]
theorem dualCotangentEquivOfEtaleKernel_toLinearMap (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal)) :
    (hf.dualCotangentEquivOfEtaleKernel hker).toLinearMap = dualCotangentMap f.hom := by
  apply LinearMap.ext
  intro x
  apply (cotangentLinearEquiv (R := k) (A := H) (B := k)).injective
  simp only [dualCotangentEquivOfEtaleKernel, LinearEquiv.trans_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LieEquiv.coe_toLinearEquiv,
    lieEquivOfEtaleKernel_apply, cotangentLinearEquiv_dualCotangentMap]

/-- The cotangent-dual equivalence acts by the differential. Use this for explicit rewriting;
the equivalence itself remains available for cancellation with its inverse. -/
theorem dualCotangentEquivOfEtaleKernel_apply (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    hf.dualCotangentEquivOfEtaleKernel hker x = dualCotangentMap f.hom x :=
  LinearMap.congr_fun (hf.dualCotangentEquivOfEtaleKernel_toLinearMap hker) x

variable {M : Type u} [CommGroup M]

/-- The differential of a smooth isogeny with étale kernel detects adjoint weight vectors.
Both weights are indexed by the characters of the diagonalizable group in the source. -/
theorem dualCotangentMap_mem_adjointWeightSpace_iff (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal))
    (π : K →ₐc[k] MonoidAlgebra k M) (α : M)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    dualCotangentMap f.hom x ∈ adjointWeightSpace (π.comp f.hom) α ↔
      x ∈ adjointWeightSpace π α := by
  apply BialgHom.dualCotangentMap_mem_adjointWeightSpace_iff_of_injective
  rw [← hf.dualCotangentEquivOfEtaleKernel_toLinearMap hker]
  exact (hf.dualCotangentEquivOfEtaleKernel hker).injective

/-- An isogeny with étale kernel carries each adjoint weight space onto the corresponding
weight space of the target. -/
theorem map_dualCotangentMap_adjointWeightSpace (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal))
    (π : K →ₐc[k] MonoidAlgebra k M) (α : M) :
    (adjointWeightSpace π α).map (dualCotangentMap f.hom) =
      adjointWeightSpace (π.comp f.hom) α := by
  ext x
  obtain ⟨y, rfl⟩ := (hf.dualCotangentEquivOfEtaleKernel hker).surjective x
  rw [← hf.dualCotangentEquivOfEtaleKernel_toLinearMap hker,
    Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  rw [hf.dualCotangentEquivOfEtaleKernel_apply]
  exact (hf.dualCotangentMap_mem_adjointWeightSpace_iff hker π α y).symm

/-- The differential of an isogeny with étale kernel restricts to an equivalence of each
adjoint weight space. -/
noncomputable def adjointWeightSpaceEquivOfEtaleKernel (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal))
    (π : K →ₐc[k] MonoidAlgebra k M) (α : M) :
    adjointWeightSpace π α ≃ₗ[k] adjointWeightSpace (π.comp f.hom) α :=
  ((hf.dualCotangentEquivOfEtaleKernel hker).submoduleMap (adjointWeightSpace π α)).trans
    (LinearEquiv.ofEq _ _ (by
      rw [hf.dualCotangentEquivOfEtaleKernel_toLinearMap,
        hf.map_dualCotangentMap_adjointWeightSpace hker]))

/-- On weight vectors the restricted equivalence is the differential. -/
@[simp]
theorem coe_adjointWeightSpaceEquivOfEtaleKernel_apply (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal))
    (π : K →ₐc[k] MonoidAlgebra k M) (α : M) (x : adjointWeightSpace π α) :
    (hf.adjointWeightSpaceEquivOfEtaleKernel hker π α x :
        Module.Dual k (Bialgebra.CotangentSpace k H)) = dualCotangentMap f.hom x := by
  rw [adjointWeightSpaceEquivOfEtaleKernel, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.submoduleMap_apply,
    hf.dualCotangentEquivOfEtaleKernel_apply]

/-- A smooth isogeny with étale kernel preserves the nontrivial adjoint weights after
restriction to the same diagonalizable group in its source. -/
@[simp]
theorem nontrivialAdjointWeights_comp (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal))
    (π : K →ₐc[k] MonoidAlgebra k M) :
    nontrivialAdjointWeights (π.comp f.hom) = nontrivialAdjointWeights π := by
  ext α
  rw [mem_nontrivialAdjointWeights, mem_nontrivialAdjointWeights,
    ← hf.map_dualCotangentMap_adjointWeightSpace hker,
    ← hf.dualCotangentEquivOfEtaleKernel_toLinearMap hker]
  exact and_congr_right' (not_congr Submodule.map_eq_bot_iff)

end TauCeti.CommHopfAlgCat.IsIsogeny
