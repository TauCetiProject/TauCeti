/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.DoubleCoset.Basic
public import TauCeti.RepresentationTheory.Tensor.Induction.ChangeTransversal.Basic
public import TauCeti.LinearAlgebra.PiTensorProduct.Regrouping

/-!
# Differential compatibility of the Mackey formula for tensor induction

Let `U` and `V` be subgroups of `G` with finitely many double cosets `V \ G / U`, each meeting
finitely many cosets of `U`. The Mackey comparison for tensor induction
(`Subgroup.tensorInducedMackey`) identifies the tensor product over `V \ G / U` of the orbitwise
tensor powers, indexed by `V ⧸ (V ⊓ sUs⁻¹)`, with the tensor power over `G ⧸ U`. This file shows
that it carries the iterated slot sum of an endomorphism `d` (apply `d` in one factor of one
orbit at a time) to the slot sum over `G ⧸ U`, and that it preserves and detects total degree.

For the double-coset regrouping itself these hold for an arbitrary endomorphism and an arbitrary
family of submodules (`Subgroup.tensorInducedDoubleCosetLinearEquiv_slotSum`,
`Subgroup.tensorInducedDoubleCosetLinearEquiv_mem_totalDegreePiece_iff`). The Mackey comparison
also changes the transversal of `U`, which acts in each factor through the representation `ρ`,
so for it `d` must commute with `ρ` and `ρ` must preserve degrees. When `M` is the total module
of a complex of `U`-representations in characteristic two, `d` its differential and the
submodules its degree pieces, the slot sums are the differentials of the tensor-induced complexes
and the theorems say that the Mackey comparison is an isomorphism of graded complexes:

```text
Res_V (⨂Ind_U^G M)  ≅  ⨂_{VsU ∈ V\G/U} ⨂Ind_{V ∩ sUs⁻¹}^V (y ↦ ρ (s⁻¹ y s)).
```

This is the chain-level form of the Mackey formula in which the double-coset formula for the
multiplicative transfer compares restricted tensor-induced resolutions.

## Main results

* `Subgroup.tensorInducedDoubleCosetLinearEquiv_slotSum`,
  `Subgroup.tensorInducedDoubleCosetLinearEquiv_mem_totalDegreePiece_iff`: double-coset
  regrouping intertwines the slot sums and preserves and detects total degree.
* `Subgroup.tensorInducedMackey_slotSum`, `Subgroup.tensorInducedMackey_mem_totalDegreePiece_iff`:
  the same for the Mackey comparison, for an endomorphism commuting with the action and a grading
  preserved by it.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Trans. Amer. Math. Soc. **108** (1963), §6.2.
-/

public section

open scoped TensorProduct

namespace Subgroup

open TauCeti

universe u v w

variable {R : Type u} [CommSemiring R] {G : Type v} [Group G]
  (U V : Subgroup G)
  (r : DoubleCoset.Quotient (V : Set G) (U : Set G) → G)
  (hr : ∀ D, DoubleCoset.mk V U (r D) = D)
  [Fintype (DoubleCoset.Quotient (V : Set G) (U : Set G))]
  [∀ D, Fintype (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V)] [Fintype (G ⧸ U)]
  [DecidableEq (DoubleCoset.Quotient (V : Set G) (U : Set G))]
  [∀ D, DecidableEq (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V)] [DecidableEq (G ⧸ U)]
  {M : Type w} [AddCommMonoid M] [Module R M]

/-- Double-coset regrouping intertwines the iterated slot sum, applying `d` in one factor of one
orbit at a time, with the slot sum over `G ⧸ U`. For a square-zero endomorphism in characteristic
two, this is the chain-map identity for the regrouping of tensor complexes. -/
theorem tensorInducedDoubleCosetLinearEquiv_slotSum (d : Module.End R M)
    (z : ⨂[R] D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      ⨂[R] _ : V ⧸ (mackeySubgroup (r D) U V).subgroupOf V, M) :
    tensorInducedDoubleCosetLinearEquiv U V r hr
        (PiTensorProduct.slotSum _ (fun D ↦
          PiTensorProduct.slotSum (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V) (fun _ ↦ d)) z) =
      PiTensorProduct.slotSum (G ⧸ U) (fun _ ↦ d)
        (tensorInducedDoubleCosetLinearEquiv U V r hr z) := by
  rw [tensorInducedDoubleCosetLinearEquiv_def, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    PiTensorProduct.sigmaEquiv_slotSum]
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using
    (LinearMap.congr_fun (PiTensorProduct.slotSum_comp_reindex (fun _ ↦ d)
      (mackeyQuotientEquiv U V r hr)) (PiTensorProduct.sigmaEquiv z)).symm

omit [DecidableEq (DoubleCoset.Quotient (V : Set G) (U : Set G))]
  [∀ D, DecidableEq (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V)] [DecidableEq (G ⧸ U)] in
/-- Double-coset regrouping preserves and detects total degree: summing the degrees first inside
each orbit and then over the double cosets gives the degree over `G ⧸ U`. -/
@[simp]
theorem tensorInducedDoubleCosetLinearEquiv_mem_totalDegreePiece_iff
    {A : Type*} [AddCommMonoid A] (ℳ : A → Submodule R M) (n : A)
    (z : ⨂[R] D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      ⨂[R] _ : V ⧸ (mackeySubgroup (r D) U V).subgroupOf V, M) :
    tensorInducedDoubleCosetLinearEquiv U V r hr z ∈
        PiTensorProduct.totalDegreePiece (G ⧸ U) (fun _ ↦ ℳ) n ↔
      z ∈ PiTensorProduct.totalDegreePiece _ (fun D ↦
        PiTensorProduct.totalDegreePiece (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V)
          (fun _ ↦ ℳ)) n := by
  rw [tensorInducedDoubleCosetLinearEquiv_def, LinearEquiv.trans_apply,
    PiTensorProduct.reindex_mem_totalDegreePiece_iff (fun _ ↦ ℳ)]
  exact PiTensorProduct.sigmaEquiv_mem_totalDegreePiece_iff (fun _ _ ↦ ℳ) n z

/-! ### The Mackey comparison -/

variable (t : ∀ D, ((mackeySubgroup (r D) U V).subgroupOf V).LeftTransversal)
  (ρ : Representation R U M) (s : U.LeftTransversal)

/-- The Mackey comparison intertwines the iterated slot sum of an endomorphism commuting with the
action of `U` with the slot sum over `G ⧸ U`. For the differential of a complex of
`U`-representations in characteristic two, this says that the Mackey comparison is a chain map
between the tensor-induced complexes. -/
theorem tensorInducedMackey_slotSum {d : Module.End R M} (hd : ∀ u, d ∘ₗ ρ u = ρ u ∘ₗ d)
    (z : ⨂[R] D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      ⨂[R] _ : V ⧸ (mackeySubgroup (r D) U V).subgroupOf V, M) :
    tensorInducedMackey U V r hr t ρ s
        (PiTensorProduct.slotSum _ (fun D ↦
          PiTensorProduct.slotSum (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V) (fun _ ↦ d)) z) =
      PiTensorProduct.slotSum (G ⧸ U) (fun _ ↦ d) (tensorInducedMackey U V r hr t ρ s z) := by
  rw [tensorInducedMackey_apply, tensorInducedMackey_apply,
    tensorInducedDoubleCosetLinearEquiv_slotSum, tensorInducedChangeTransversalLinearEquiv_apply,
    tensorInducedChangeTransversalLinearEquiv_apply]
  exact (LinearMap.congr_fun (ρ.slotSum_comp_wreathTensor hd _) _).symm

omit [DecidableEq (DoubleCoset.Quotient (V : Set G) (U : Set G))]
  [∀ D, DecidableEq (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V)] [DecidableEq (G ⧸ U)] in
/-- If the action of `U` preserves the degrees of a grading of `M`, then the Mackey comparison
preserves and detects total degree. -/
theorem tensorInducedMackey_mem_totalDegreePiece_iff {A : Type*} [AddCommMonoid A]
    {ℳ : A → Submodule R M} (hρ : ∀ u, LinearMap.IsHomogeneous (ρ u) ℳ ℳ 0) (n : A)
    (z : ⨂[R] D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      ⨂[R] _ : V ⧸ (mackeySubgroup (r D) U V).subgroupOf V, M) :
    tensorInducedMackey U V r hr t ρ s z ∈
        PiTensorProduct.totalDegreePiece (G ⧸ U) (fun _ ↦ ℳ) n ↔
      z ∈ PiTensorProduct.totalDegreePiece _ (fun D ↦
        PiTensorProduct.totalDegreePiece (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V)
          (fun _ ↦ ℳ)) n := by
  rw [tensorInducedMackey_apply,
    tensorInducedChangeTransversalLinearEquiv_mem_totalDegreePiece_iff U _ _ ρ hρ,
    tensorInducedDoubleCosetLinearEquiv_mem_totalDegreePiece_iff]

end Subgroup
