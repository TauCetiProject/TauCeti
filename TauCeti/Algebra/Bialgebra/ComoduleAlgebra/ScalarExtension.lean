/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra
public import TauCeti.Algebra.Coalgebra.Comodule.BaseChange
public import TauCeti.Algebra.TensorProduct.BaseChange
public import Mathlib.RingTheory.Bialgebra.TensorProduct

import Mathlib.RingTheory.Flat.Equalizer

/-!
# Scalar extension of comodule algebras and coinvariants

Extending both a bialgebra `H` and a comodule algebra `A` from `R` to `S` gives an
`S ⊗[R] H`-comodule algebra `S ⊗[R] A`. The underlying comodule is
`TauCeti.Comodule.baseChange`, equipped with its algebra structure by
`TauCeti.ComoduleAlgebra.scalarExtension`.

For flat `S`, the canonical map on coinvariants is an algebra equivalence
`S ⊗[R] coinvariants R H A ≃ₐ[S] coinvariants S (S ⊗[R] H) (S ⊗[R] A)`.
This follows by expressing coinvariants as an equalizer and applying Mathlib's
`AlgHom.tensorEqualizerEquiv`. The equivalence identifies functions invariant under an
affine monoid action after flat base change with the scalar extension of the original
invariant algebra.

## References

* C. S. Seshadri, *Geometric reductivity over arbitrary base* (1977), Lemma 2,
  as cited by Böckle–Harris–Khare–Thorne for flat base change of invariants.
-/

public section

open scoped TensorProduct

namespace TauCeti.ComoduleAlgebra

open TauCeti.Algebra.TensorProduct (baseChangeTensorAlgEquiv baseChangeTensorAlgEquiv_toLinearEquiv)

universe u v w x

section Semiring

variable {R : Type u} {H : Type v} {A : Type w} (S : Type x)
  [CommSemiring R] [CommSemiring S] [Algebra R S]
  [Semiring H] [Bialgebra R H] [Semiring A] [Algebra R A] [ComoduleAlgebra R H A]

private theorem baseChangeCoact_eq (z : S ⊗[R] A) :
    Comodule.baseChangeCoact (R := R) (H := H) S z =
      baseChangeTensorAlgEquiv R S A H
        (Algebra.TensorProduct.map (AlgHom.id S S) (coactAlgHom R H A) z) := by
  induction z with
  | tmul s a =>
    simpa only [← baseChangeTensorAlgEquiv_toLinearEquiv, AlgEquiv.coe_toLinearEquiv,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, coactAlgHom_apply] using
      Comodule.baseChangeCoact_tmul (R := R) (H := H) S s a
  | add z z' hz hz' => simp only [map_add, hz, hz']

/-- Extend the scalars of both the coefficient bialgebra and its comodule algebra.
The underlying comodule is `Comodule.baseChange`. Select the structure as a local
instance, since an algebra may carry several coactions. -/
@[instance_reducible]
noncomputable def scalarExtension : ComoduleAlgebra S (S ⊗[R] H) (S ⊗[R] A) where
  toComodule := Comodule.baseChange (R := R) (H := H) (M := A) S
  coact_one := by
    rw [Comodule.baseChange_coact, baseChangeCoact_eq]
    simp
  coact_mul z z' := by
    simp only [Comodule.baseChange_coact, baseChangeCoact_eq, map_mul]

/-- The scalar-extended coaction is the original coaction tensored with `S`, followed by
distribution of scalar extension over the tensor product. -/
theorem coact_scalarExtension (z : S ⊗[R] A) :
    letI := scalarExtension (R := R) (H := H) (A := A) S
    Comodule.coact (R := S) (C := S ⊗[R] H) z =
      baseChangeTensorAlgEquiv R S A H
        (Algebra.TensorProduct.map (AlgHom.id S S) (coactAlgHom R H A) z) := by
  let := scalarExtension (R := R) (H := H) (A := A) S
  rw [Comodule.baseChange_coact]
  exact baseChangeCoact_eq (H := H) S z

end Semiring

section Ring

variable {R : Type u} {H : Type v} {A : Type w} (S : Type x)
  [CommRing R] [CommRing S] [Algebra R S]
  [CommRing H] [Bialgebra R H] [CommRing A] [Algebra R A] [ComoduleAlgebra R H A]

private theorem scalarExtension_coinvariants_eq_equalizer :
    letI := scalarExtension (R := R) (H := H) (A := A) S
    coinvariants S (S ⊗[R] H) (S ⊗[R] A) =
      AlgHom.equalizer
        (Algebra.TensorProduct.map (AlgHom.id S S) (coactAlgHom R H A))
        (Algebra.TensorProduct.map (AlgHom.id S S)
          (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] H)) := by
  let := scalarExtension (R := R) (H := H) (A := A) S
  ext z
  rw [mem_coinvariants, AlgHom.mem_equalizer, coact_scalarExtension]
  have h (z : S ⊗[R] A) :
      baseChangeTensorAlgEquiv R S A H
        (Algebra.TensorProduct.map (AlgHom.id S S)
          (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] H) z) = z ⊗ₜ[S] 1 := by
    induction z with
    | tmul s a => simp [Algebra.TensorProduct.one_def]
    | add z z' hz hz' => simp only [map_add, hz, hz', TensorProduct.add_tmul]
  rw [← h]
  exact (baseChangeTensorAlgEquiv R S A H).injective.eq_iff

variable (R H A) in
/-- Coinvariants of an arbitrary commutative comodule algebra commute with flat scalar
extension. The equivalence sends a scalar tensored with an invariant to the same tensor in
the extended algebra. -/
noncomputable def coinvariantsScalarExtensionEquiv [Module.Flat R S] :
    letI := scalarExtension (R := R) (H := H) (A := A) S
    S ⊗[R] coinvariants R H A ≃ₐ[S]
      coinvariants S (S ⊗[R] H) (S ⊗[R] A) := by
  letI := scalarExtension (R := R) (H := H) (A := A) S
  exact ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
      (Subalgebra.equivOfEq (coinvariants R H A) _ (by
        ext a
        simp only [mem_coinvariants, AlgHom.mem_equalizer, coactAlgHom_apply,
          Algebra.TensorProduct.includeLeft_apply]))).trans
    (AlgHom.tensorEqualizerEquiv S S (coactAlgHom R H A)
      Algebra.TensorProduct.includeLeft)).trans
    (Subalgebra.equivOfEq _ _ (scalarExtension_coinvariants_eq_equalizer S).symm)

/-- Under the ambient inclusion, the flat scalar-extension equivalence is tensoring the
inclusion of the original coinvariants with `S`. -/
@[simp]
theorem coe_coinvariantsScalarExtensionEquiv [Module.Flat R S]
    (z : S ⊗[R] coinvariants R H A) :
    letI := scalarExtension (R := R) (H := H) (A := A) S
    (coinvariantsScalarExtensionEquiv R H A S z : S ⊗[R] A) =
      Algebra.TensorProduct.map (AlgHom.id S S) (coinvariants R H A).val z := by
  let := scalarExtension (R := R) (H := H) (A := A) S
  simp only [coinvariantsScalarExtensionEquiv, AlgEquiv.trans_apply,
    Subalgebra.equivOfEq_apply, AlgHom.tensorEqualizerEquiv_apply,
    AlgHom.coe_tensorEqualizer]
  induction z with
  | tmul s a => rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

end Ring

end TauCeti.ComoduleAlgebra
