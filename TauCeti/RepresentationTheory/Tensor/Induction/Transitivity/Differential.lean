/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.Transitivity.Basic
public import TauCeti.LinearAlgebra.PiTensorProduct.Regrouping

/-!
# Differential compatibility of tensor-induction transitivity

For a finite-index tower `V ≤ U ≤ G`, the transitivity regrouping of tensor induction preserves
total degree and intertwines the iterated slot differential with the direct slot differential.
Consequently the coefficient-level regrouping is also available for the sign-free tensor
complexes used to construct the Evens norm. This is the chain-level regrouping needed to
compare direct and iterated tensor-induced resolutions.

The results concern arbitrary endomorphisms and families of submodules, not only square-zero
differentials and gradings. They require no topology, equivariance, or characteristic
assumption. When the endomorphism is a differential in characteristic two, the slot sums are
the differentials of the tensor complexes. The composite transversal and representation
comparison are those of `Subgroup.tensorInducedTransitivity`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), §6, Proposition 1.
-/

public section

open scoped TensorProduct

namespace Subgroup

open TauCeti

universe u v w

variable {R : Type u} [CommSemiring R] {G : Type v} [Group G]
  {U V : Subgroup G} (hVU : V ≤ U) (s : U.LeftTransversal)
  [Fintype (G ⧸ U)] [Fintype (U ⧸ V.subgroupOf U)] [Fintype (G ⧸ V)]
  [DecidableEq (G ⧸ U)] [DecidableEq (U ⧸ V.subgroupOf U)] [DecidableEq (G ⧸ V)]
  {M : Type w} [AddCommMonoid M] [Module R M]

/-- The transitivity regrouping intertwines the iterated slot sum with the direct slot sum.
For a square-zero endomorphism in characteristic two, this is the chain-map identity for the
transitivity comparison of tensor complexes. -/
theorem tensorInducedTransitivityLinearEquiv_slotSum (d : Module.End R M)
    (z : ⨂[R] _ : G ⧸ U, ⨂[R] _ : U ⧸ V.subgroupOf U, M) :
    tensorInducedTransitivityLinearEquiv hVU s
        (PiTensorProduct.slotSum (G ⧸ U)
          (fun _ ↦ PiTensorProduct.slotSum (U ⧸ V.subgroupOf U) (fun _ ↦ d)) z) =
      PiTensorProduct.slotSum (G ⧸ V) (fun _ ↦ d)
        (tensorInducedTransitivityLinearEquiv hVU s z) := by
  rw [tensorInducedTransitivityLinearEquiv_def, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, PiTensorProduct.prodEquiv_slotSum]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using
    (LinearMap.congr_fun (PiTensorProduct.slotSum_comp_reindex
      (fun _ ↦ d) (quotientEquivProdOfLE' hVU (leftTransversalRep U s)
        (leftTransversalRep_mk U s)).symm) (PiTensorProduct.prodEquiv z)).symm

omit [DecidableEq (G ⧸ U)] [DecidableEq (U ⧸ V.subgroupOf U)] [DecidableEq (G ⧸ V)] in
/-- The transitivity regrouping detects and preserves total degree: summing the degrees first
inside each `U/V`-fibre and then over `G/U` gives the degree over `G/V`. -/
@[simp]
theorem tensorInducedTransitivityLinearEquiv_mem_totalDegreePiece_iff
    {A : Type*} [AddCommMonoid A] (ℳ : A → Submodule R M) (n : A)
    (z : ⨂[R] _ : G ⧸ U, ⨂[R] _ : U ⧸ V.subgroupOf U, M) :
    tensorInducedTransitivityLinearEquiv hVU s z ∈
        PiTensorProduct.totalDegreePiece (G ⧸ V) (fun _ ↦ ℳ) n ↔
      z ∈ PiTensorProduct.totalDegreePiece (G ⧸ U)
        (fun _ ↦ PiTensorProduct.totalDegreePiece (U ⧸ V.subgroupOf U) (fun _ ↦ ℳ)) n := by
  rw [tensorInducedTransitivityLinearEquiv_def, LinearEquiv.trans_apply]
  rw [PiTensorProduct.reindex_mem_totalDegreePiece_iff (fun _ ↦ ℳ)]
  exact PiTensorProduct.prodEquiv_mem_totalDegreePiece_iff (fun _ _ ↦ ℳ) n z

end Subgroup
