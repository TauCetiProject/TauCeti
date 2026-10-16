/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.Sigma
public import TauCeti.RepresentationTheory.Induction.Mackey.Basic

/-!
# Double-coset regrouping for tensor induction

Let `U` and `V` be subgroups of `G`.  The `U`-cosets indexing tensor induction split into
`V`-orbits indexed by `V \ G / U`.  For a representative `s`, its orbit is
`V ⧸ (V ⊓ sUs⁻¹)`.  Regrouping the tensor factors along these orbits gives

```text
⨂[R] (G/U), M  ≃  ⨂[R] (VsU ∈ V\G/U), (⨂[R] V/(V ∩ sUs⁻¹), M).
```

The equivalence here is oriented from the iterated tensor product to the original tensor power,
in parallel with `Subgroup.tensorInducedTransitivityLinearEquiv`.  Its inverse is the actual
double-coset decomposition.  The construction is independent of any representation or chosen
transversal; those enter later when each orbit factor is identified with tensor induction of the
conjugated coefficient representation.

## Main definitions

* `Subgroup.tensorInducedDoubleCosetLinearEquiv`: flatten and relabel the orbitwise tensor
  products by the Mackey decomposition of the coset space.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), §6.2.
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
  [Finite (DoubleCoset.Quotient (V : Set G) (U : Set G))]
  {M : Type w} [AddCommMonoid M] [Module R M]

/-- Regroup the tensor factors over `G ⧸ U` by their `V`-orbits.  The orbit attached to a double
coset representative `s` is indexed by `V ⧸ (V ⊓ sUs⁻¹)`. -/
noncomputable def tensorInducedDoubleCosetLinearEquiv :
    (⨂[R] D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      ⨂[R] _ : V ⧸ (TauCeti.mackeySubgroup (r D) U V).subgroupOf V, M) ≃ₗ[R]
        (⨂[R] _ : G ⧸ U, M) :=
  PiTensorProduct.sigmaEquiv.trans
    (PiTensorProduct.reindex R (fun _ ↦ M) (TauCeti.mackeyQuotientEquiv U V r hr))

/-- On orbitwise pure tensors, double-coset regrouping simply reads the Mackey coordinates of
each `U`-coset. -/
@[simp]
theorem tensorInducedDoubleCosetLinearEquiv_tprod
    (m : ∀ D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      V ⧸ (TauCeti.mackeySubgroup (r D) U V).subgroupOf V → M) :
    tensorInducedDoubleCosetLinearEquiv (R := R) U V r hr
        (PiTensorProduct.tprod R fun D ↦ PiTensorProduct.tprod R (m D)) =
      PiTensorProduct.tprod R (fun q : G ⧸ U ↦
        m ((TauCeti.mackeyQuotientEquiv U V r hr).symm q).1
          ((TauCeti.mackeyQuotientEquiv U V r hr).symm q).2) := by
  simp [tensorInducedDoubleCosetLinearEquiv]

/-- The inverse comparison gathers the factors of a pure tensor into their double-coset
orbits. -/
@[simp]
theorem tensorInducedDoubleCosetLinearEquiv_symm_tprod (m : G ⧸ U → M) :
    (tensorInducedDoubleCosetLinearEquiv (R := R) U V r hr).symm
        (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun D ↦ PiTensorProduct.tprod R fun q ↦
        m (TauCeti.mackeyQuotientEquiv U V r hr ⟨D, q⟩) := by
  apply (tensorInducedDoubleCosetLinearEquiv (R := R) U V r hr).injective
  simp only [LinearEquiv.apply_symm_apply, tensorInducedDoubleCosetLinearEquiv_tprod,
    Equiv.apply_symm_apply, Sigma.eta]

/-- Double-coset regrouping is natural in a linear map on the tensor factors. -/
theorem tensorInducedDoubleCosetLinearEquiv_map
    {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N)
    (z : ⨂[R] D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      ⨂[R] _ : V ⧸ (TauCeti.mackeySubgroup (r D) U V).subgroupOf V, M) :
    tensorInducedDoubleCosetLinearEquiv (R := R) (M := N) U V r hr
        (PiTensorProduct.map (fun _ ↦ PiTensorProduct.map (fun _ ↦ f)) z) =
      PiTensorProduct.map (fun _ ↦ f)
        (tensorInducedDoubleCosetLinearEquiv (R := R) U V r hr z) := by
  simp only [tensorInducedDoubleCosetLinearEquiv, LinearEquiv.trans_apply,
    PiTensorProduct.sigmaEquiv_map]
  exact (PiTensorProduct.map_reindex
    (fun _ : Σ D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      V ⧸ (TauCeti.mackeySubgroup (r D) U V).subgroupOf V ↦ f)
    (TauCeti.mackeyQuotientEquiv U V r hr) (PiTensorProduct.sigmaEquiv z)).symm

end Subgroup
