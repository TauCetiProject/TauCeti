/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.Sigma
public import TauCeti.RepresentationTheory.Induction.Mackey.Basic
public import TauCeti.RepresentationTheory.Tensor.Induction.Diagonal
public import TauCeti.RepresentationTheory.Tensor.Pi.Basic

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
double-coset decomposition.  The regrouping depends on the chosen double-coset representatives
`r`, which index the orbit factors, but needs no further coset transversal and no representation.

With a representation `ρ` of `U`, the regrouping becomes the **Mackey formula for tensor
induction**: as representations of `V`,

```text
Res_V (⨂Ind_U^G ρ)  ≅  ⨂_{VsU ∈ V\G/U} ⨂Ind_{V ∩ sUs⁻¹}^V (y ↦ ρ (s⁻¹ y s)).
```

Each orbit factor is tensor induced along a chosen left transversal `t D` of its Mackey subgroup
in `V`.  For the transversal of `U` whose representatives are `t_D(u) * r D`
(`Subgroup.mackeyLeftTransversal`) the regrouping is itself equivariant; for any other left
transversal of `U`, the comparison is followed by the change of transversal.  The comparison
carries the tensor product of the orbitwise invariant diagonals to the invariant diagonal, which
is the form in which the double-coset formula for the multiplicative transfer consumes it.

## Main definitions

* `Subgroup.tensorInducedDoubleCosetLinearEquiv`: flatten and relabel the orbitwise tensor
  products by the Mackey decomposition of the coset space.
* `Subgroup.tensorInducedMackey`: the Mackey formula, as an equivalence of representations of
  `V`.

## Main statements

* `Subgroup.tensorInducedMackey_tprod`: the Mackey comparison on orbitwise pure tensors.
* `Subgroup.tensorInducedMackey_naturality`: naturality in the coefficient representation.
* `Subgroup.tensorInducedMackey_tensorInducedDiagonal`: the Mackey comparison of invariant
  diagonals.

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
  (PiTensorProduct.sigmaEquiv (M := fun _ _ ↦ M)).trans
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

/-! ### The Mackey formula for tensor induction -/

section Mackey

variable (t : ∀ D, ((TauCeti.mackeySubgroup (r D) U V).subgroupOf V).LeftTransversal)
  (ρ : Representation R U M)

/-- Along the Mackey-adapted transversal, double-coset regrouping intertwines the action of `V`
on the tensor product of the orbitwise tensor inductions with the restriction of tensor induction
from `U` to `G`: both act on the factor at `u (r D) U` by `(r D)⁻¹ t_D(u)⁻¹ v t_D(v⁻¹ u) (r D)`. -/
private theorem tensorInducedDoubleCosetLinearEquiv_comp_piTensorProduct (v : V) :
    (tensorInducedDoubleCosetLinearEquiv U V r hr).toLinearMap ∘ₗ
        Representation.piTensorProduct (fun D ↦
          ((TauCeti.mackeySubgroup (r D) U V).subgroupOf V).tensorInducedRepresentation (t D)
            (ρ.comp (TauCeti.mackeyToH (r D) U V))) v =
      U.tensorInducedRepresentation (U.mackeyLeftTransversal V r hr t) ρ v ∘ₗ
        (tensorInducedDoubleCosetLinearEquiv U V r hr).toLinearMap := by
  apply PiTensorProduct.ext_sigma_tprod
  intro m
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    Representation.piTensorProduct_apply_tprod, tensorInducedRepresentation_apply_tprod,
    tensorInducedDoubleCosetLinearEquiv_tprod, MonoidHom.comp_apply]
  congr 1
  funext q
  -- Name the Mackey coordinates `(D, w)` of `q`, keeping `q = e ⟨D, w⟩` non-dependent.
  set e := TauCeti.mackeyQuotientEquiv U V r hr with he
  generalize hp : e.symm q = p
  obtain rfl : q = e p := by rw [← hp, Equiv.apply_symm_apply]
  obtain ⟨D, w⟩ := p
  have hv : (v : G)⁻¹ • e ⟨D, w⟩ = e ⟨D, v⁻¹ • w⟩ := by
    rw [he, ← TauCeti.smul_mackeyQuotientEquiv, Subgroup.coe_inv]
  rw [hv, Equiv.symm_apply_apply]
  congr 2
  apply Subtype.ext
  rw [TauCeti.coe_mackeyToH_apply, monomialHom_left, monomialHom_left]
  dsimp only
  rw [TauCeti.lWord_def, TauCeti.lWord_def, hv, he, TauCeti.mackeyQuotientEquiv_apply,
    TauCeti.mackeyQuotientEquiv_apply, leftTransversalRep_mackeyLeftTransversal,
    leftTransversalRep_mackeyLeftTransversal]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

/-- **The Mackey formula for tensor induction.**  Restricted to `V`, tensor induction from `U` to
`G` along a left transversal `s` is the tensor product, over the double cosets `V \ G / U`, of the
tensor inductions from the Mackey subgroups `V ⊓ (r D) U (r D)⁻¹` to `V` of the conjugated
representations `y ↦ ρ ((r D)⁻¹ y (r D))`.

The comparison regroups the tensor factors by double cosets
(`Subgroup.tensorInducedDoubleCosetLinearEquiv`), which is already equivariant for the
Mackey-adapted transversal `Subgroup.mackeyLeftTransversal`, and then changes that transversal
to `s` (`Subgroup.tensorInducedChangeTransversal`). -/
noncomputable def tensorInducedMackey (s : U.LeftTransversal) :
    (Representation.piTensorProduct fun D ↦
      ((TauCeti.mackeySubgroup (r D) U V).subgroupOf V).tensorInducedRepresentation (t D)
        (ρ.comp (TauCeti.mackeyToH (r D) U V))).Equiv
      ((U.tensorInducedRepresentation s ρ).comp V.subtype) :=
  Representation.Equiv.mk ((tensorInducedDoubleCosetLinearEquiv U V r hr).trans
      (tensorInducedChangeTransversalLinearEquiv U s (U.mackeyLeftTransversal V r hr t) ρ))
    fun v ↦ by
      refine LinearMap.ext fun z ↦ ?_
      have h := LinearMap.congr_fun
        (tensorInducedDoubleCosetLinearEquiv_comp_piTensorProduct U V r hr t ρ v) z
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
        MonoidHom.comp_apply, Subgroup.coe_subtype, h]
      simpa only [Representation.Equiv.coe_toIntertwiningMap,
        tensorInducedChangeTransversal_apply] using
        Representation.IntertwiningMap.isIntertwining _ _
          (tensorInducedChangeTransversal U s (U.mackeyLeftTransversal V r hr t)
            ρ).toIntertwiningMap (v : G) (tensorInducedDoubleCosetLinearEquiv U V r hr z)

/-- The Mackey comparison regroups by double cosets and then changes the transversal. -/
theorem tensorInducedMackey_apply (s : U.LeftTransversal)
    (z : ⨂[R] D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      ⨂[R] _ : V ⧸ (TauCeti.mackeySubgroup (r D) U V).subgroupOf V, M) :
    tensorInducedMackey U V r hr t ρ s z =
      tensorInducedChangeTransversalLinearEquiv U s (U.mackeyLeftTransversal V r hr t) ρ
        (tensorInducedDoubleCosetLinearEquiv U V r hr z) := (rfl)

/-- Along the Mackey-adapted transversal, the Mackey comparison is double-coset regrouping. -/
@[simp]
theorem tensorInducedMackey_mackeyLeftTransversal_apply
    (z : ⨂[R] D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      ⨂[R] _ : V ⧸ (TauCeti.mackeySubgroup (r D) U V).subgroupOf V, M) :
    tensorInducedMackey U V r hr t ρ (U.mackeyLeftTransversal V r hr t) z =
      tensorInducedDoubleCosetLinearEquiv U V r hr z := by
  rw [tensorInducedMackey_apply, tensorInducedChangeTransversalLinearEquiv_self,
    LinearEquiv.refl_apply]

/-- On orbitwise pure tensors, the Mackey comparison reads the Mackey coordinates of each coset
and corrects the factor by the difference between `s` and the Mackey-adapted transversal. -/
@[simp]
theorem tensorInducedMackey_tprod (s : U.LeftTransversal)
    (m : ∀ D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      V ⧸ (TauCeti.mackeySubgroup (r D) U V).subgroupOf V → M) :
    tensorInducedMackey U V r hr t ρ s
        (PiTensorProduct.tprod R fun D ↦ PiTensorProduct.tprod R (m D)) =
      PiTensorProduct.tprod R fun q : G ⧸ U ↦
        ρ ((U.monomialChangeTransversal s (U.mackeyLeftTransversal V r hr t)).left q)
          (m ((TauCeti.mackeyQuotientEquiv U V r hr).symm q).1
            ((TauCeti.mackeyQuotientEquiv U V r hr).symm q).2) := by
  rw [tensorInducedMackey_apply, tensorInducedDoubleCosetLinearEquiv_tprod,
    tensorInducedChangeTransversalLinearEquiv_apply_tprod]

/-- The Mackey comparison is natural in an intertwining map of representations of `U`, applied
in every inner tensor factor on the source and in every factor of tensor induction on the
target. -/
theorem tensorInducedMackey_naturality {N : Type*} [AddCommMonoid N] [Module R N]
    {τ : Representation R U N} (f : ρ.IntertwiningMap τ) (s : U.LeftTransversal)
    (z : ⨂[R] D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      ⨂[R] _ : V ⧸ (TauCeti.mackeySubgroup (r D) U V).subgroupOf V, M) :
    tensorInducedMackey U V r hr t τ s
        (PiTensorProduct.map (fun _ ↦ PiTensorProduct.map fun _ ↦ f.toLinearMap) z) =
      f.tensorInduced s (tensorInducedMackey U V r hr t ρ s z) := by
  have h := congrArg (fun g ↦ g (tensorInducedDoubleCosetLinearEquiv U V r hr z))
    (tensorInducedChangeTransversal_naturality U s (U.mackeyLeftTransversal V r hr t) ρ f)
  simp only [Representation.IntertwiningMap.comp_apply, Representation.Equiv.coe_toIntertwiningMap,
    tensorInducedChangeTransversal_apply] at h
  rw [tensorInducedMackey_apply, tensorInducedMackey_apply, tensorInducedDoubleCosetLinearEquiv_map,
    h, ← Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.tensorInduced_toLinearMap]

end Mackey

end Subgroup

namespace Subgroup

universe u v w

variable {R : Type u} [CommRing R] {G : Type v} [Group G]
  (U V : Subgroup G)
  (r : DoubleCoset.Quotient (V : Set G) (U : Set G) → G)
  (hr : ∀ D, DoubleCoset.mk V U (r D) = D)
  [Finite (DoubleCoset.Quotient (V : Set G) (U : Set G))]
  (t : ∀ D, ((TauCeti.mackeySubgroup (r D) U V).subgroupOf V).LeftTransversal)
  {M : Type w} [AddCommGroup M] [Module R M]

/-- The Mackey comparison carries the tensor product of the orbitwise invariant diagonals of an
invariant vector to its invariant diagonal in tensor induction from `U` to `G`. -/
theorem tensorInducedMackey_tensorInducedDiagonal (ρ : Representation R U M)
    (s : U.LeftTransversal) (x : ρ.invariants) :
    tensorInducedMackey U V r hr t ρ s (PiTensorProduct.tprod R fun D ↦
        ((Representation.tensorInducedDiagonal (ρ.comp (TauCeti.mackeyToH (r D) U V)) (t D)
          ⟨x, fun _ ↦ x.property _⟩ : ⨂[R] _ : V ⧸ (TauCeti.mackeySubgroup (r D) U V).subgroupOf V,
            M))) =
      (ρ.tensorInducedDiagonal s x : ⨂[R] _ : G ⧸ U, M) := by
  simp only [Representation.coe_tensorInducedDiagonal, tensorInducedMackey_tprod]
  congr 1
  funext q
  exact x.property _

end Subgroup
