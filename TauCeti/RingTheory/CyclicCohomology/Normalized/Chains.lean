/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Normalized.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Normalized Hochschild chains and their mixed operators

Normalized chains are the quotient of the tensor power of `A` by the span of tensors
having a unit in a noninitial slot. Their universal property identifies linear maps out
of them with normalized multilinear cochains, with arbitrary module coefficients.
In particular normalization does not kill degree-zero scalar chains.

The Hochschild boundary `b` and Connes' boundary `B` descend to this quotient. Their
transposes are exactly the existing normalized cochain operators, so the cochain identities
give `b² = B² = bB + Bb = 0` on chains. On a tensor, `B` is the signed sum of cyclic
rotations with an initial unit. These are the operators used for periodic Chern chains.

This file uses the quotient-by-degeneracies model; it does not yet identify it with the
tensor product having factors `A / R1` or compare its homology with the full complex.

## References

* J.-L. Loday, *Cyclic Homology*, §§1.1 and 2.1.
* A. Connes, *Noncommutative Geometry*, Chapter III, §1.

The construction uses `PiTensorProduct.lift` and `Submodule.liftQ`; the mixed identities
are transposed from `TauCeti.RingTheory.CyclicCohomology.Normalized.Basic`.
-/

public section

noncomputable section

namespace TauCeti

open PiTensorProduct
open scoped TensorProduct

section Quotient

variable (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A] [One A]

/-- The span of tensors with a unit in a noninitial slot. -/
def degenerateHochschildChains (n : ℕ) :
    Submodule R (⨂[R] (_ : Fin (n + 1)), A) :=
  Submodule.span R {t | ∃ (a : Fin (n + 1) → A) (i : Fin (n + 1)),
    i ≠ 0 ∧ a i = 1 ∧ tprod R a = t}

/-- A linear map kills all degenerate tensors exactly when its multilinear cochain is
normalized. -/
theorem degenerateHochschildChains_le_ker_iff {M : Type*} [AddCommGroup M] [Module R M]
    {n : ℕ} (f : (⨂[R] (_ : Fin (n + 1)), A) →ₗ[R] M) :
    degenerateHochschildChains R A n ≤ f.ker ↔
      f.compMultilinearMap (tprod R) ∈ normalizedHochschildCochains R A M n := by
  rw [degenerateHochschildChains, Submodule.span_le, mem_normalizedHochschildCochains_iff]
  exact ⟨fun h a i hi ha ↦ h ⟨a, i, hi, ha, rfl⟩,
    fun h _ ⟨a, i, hi, ha, ht⟩ ↦ ht ▸ h a i hi ha⟩

/-- Normalized Hochschild chains, as tensors modulo degenerate tensors. -/
abbrev normalizedHochschildChains (n : ℕ) :=
  (⨂[R] (_ : Fin (n + 1)), A) ⧸ degenerateHochschildChains R A n

namespace normalizedHochschildChains

/-- The universal normalized multilinear tensor. -/
def tensor (n : ℕ) :
    MultilinearMap R (fun _ : Fin (n + 1) ↦ A) (normalizedHochschildChains R A n) :=
  (degenerateHochschildChains R A n).mkQ.compMultilinearMap (tprod R)

/-- A tensor with a noninitial unit is zero in normalized chains. -/
theorem tensor_eq_zero {n : ℕ} (a : Fin (n + 1) → A) (i : Fin (n + 1))
    (hi : i ≠ 0) (ha : a i = 1) : tensor R A n a = 0 :=
  Submodule.Quotient.mk_eq_zero _ |>.2 (Submodule.subset_span ⟨a, i, hi, ha, rfl⟩)

/-- Inserting a unit in a noninitial slot makes a normalized tensor zero. -/
@[simp]
theorem tensor_update_one {n : ℕ} (a : Fin (n + 1) → A) (i : Fin (n + 1)) (hi : i ≠ 0) :
    tensor R A n (Function.update a i 1) = 0 :=
  tensor_eq_zero R A _ i hi (Function.update_self _ _ _)

/-- The universal tensor is a normalized cochain with values in normalized chains. -/
theorem tensor_mem_normalizedHochschildCochains (n : ℕ) :
    tensor R A n ∈ normalizedHochschildCochains R A (normalizedHochschildChains R A n) n :=
  (mem_normalizedHochschildCochains_iff).2 (tensor_eq_zero R A)

variable {R A} {M : Type*} [AddCommGroup M] [Module R M]

/-- Linear maps on normalized chains are determined by their values on tensors. -/
@[ext]
theorem hom_ext {n : ℕ} {f g : normalizedHochschildChains R A n →ₗ[R] M}
    (h : ∀ a, f (tensor R A n a) = g (tensor R A n a)) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨t, rfl⟩ := (degenerateHochschildChains R A n).mkQ_surjective x
  exact LinearMap.congr_fun (PiTensorProduct.ext (MultilinearMap.ext h) :
    f ∘ₗ (degenerateHochschildChains R A n).mkQ =
      g ∘ₗ (degenerateHochschildChains R A n).mkQ) t

/-- Extend a normalized cochain uniquely to a linear map on normalized chains. -/
def lift {n : ℕ} (φ : normalizedHochschildCochains R A M n) :
    normalizedHochschildChains R A n →ₗ[R] M :=
  (degenerateHochschildChains R A n).liftQ (PiTensorProduct.lift φ.val)
    ((degenerateHochschildChains_le_ker_iff R A _).2 (by
      simpa only [← PiTensorProduct.lift_symm, LinearEquiv.symm_apply_apply] using φ.property))

/-- The extension evaluates on tensors as the original cochain. -/
@[simp]
theorem lift_tensor {n : ℕ} (φ : normalizedHochschildCochains R A M n)
    (a : Fin (n + 1) → A) : lift φ (tensor R A n a) = φ.val a :=
  PiTensorProduct.lift.tprod _

variable (R A M) in
/-- The universal property of normalized chains, with arbitrary module coefficients. -/
def cochainEquiv (n : ℕ) : (normalizedHochschildChains R A n →ₗ[R] M) ≃ₗ[R]
    normalizedHochschildCochains R A M n where
  toFun f := ⟨f.compMultilinearMap (tensor R A n),
    f.compMultilinearMap_mem_normalizedHochschildCochains
      (tensor_mem_normalizedHochschildCochains R A n)⟩
  invFun := lift
  left_inv _ := hom_ext fun a ↦ lift_tensor _ a
  right_inv φ := Subtype.ext (MultilinearMap.ext (lift_tensor φ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The universal-property equivalence is evaluation on normalized tensors. -/
@[simp]
theorem cochainEquiv_apply {n : ℕ} (f : normalizedHochschildChains R A n →ₗ[R] M) :
    (cochainEquiv R A M n f).val = f.compMultilinearMap (tensor R A n) := (rfl)

/-- The inverse universal-property equivalence is the extension of a normalized cochain. -/
@[simp]
theorem cochainEquiv_symm_apply {n : ℕ} (φ : normalizedHochschildCochains R A M n) :
    (cochainEquiv R A M n).symm φ = lift φ := (rfl)

end normalizedHochschildChains

/-- There are no degenerate tensors in degree zero. -/
@[simp]
theorem degenerateHochschildChains_zero : degenerateHochschildChains R A 0 = ⊥ := by
  simp [degenerateHochschildChains]

namespace normalizedHochschildChains

/-- Normalization preserves the full algebra in degree zero. -/
def zeroEquiv : normalizedHochschildChains R A 0 ≃ₗ[R] A :=
  ((degenerateHochschildChains R A 0).quotEquivOfEqBot
    (degenerateHochschildChains_zero R A)).trans (PiTensorProduct.subsingletonEquiv (0 : Fin 1))

/-- The degree-zero identification sends a one-factor tensor to its entry. -/
@[simp]
theorem zeroEquiv_tensor (a : Fin 1 → A) : zeroEquiv R A (tensor R A 0 a) = a 0 := by
  simp [zeroEquiv, tensor, Submodule.quotEquivOfEqBot_apply_mk]

/-- The inverse degree-zero identification is the one-factor tensor. -/
@[simp]
theorem zeroEquiv_symm_apply (a : A) :
    (zeroEquiv R A).symm a = tensor R A 0 (fun _ ↦ a) := by
  apply (zeroEquiv R A).injective
  simp

/-- Connes' boundary on normalized chains, raising degree by one. -/
def B (n : ℕ) : normalizedHochschildChains R A n →ₗ[R]
    normalizedHochschildChains R A (n + 1) :=
  lift ⟨connesB R A _ n (tensor R A (n + 1)),
    connesB_mem_normalizedHochschildCochains
      (tensor_mem_normalizedHochschildCochains R A (n + 1))⟩

/-- Connes' boundary is the signed cyclic sum with an inserted initial unit. -/
theorem B_tensor (n : ℕ) (a : Fin (n + 1) → A) :
    B R A n (tensor R A n a) =
      ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n * k) •
        tensor R A (n + 1) (Fin.cons 1 (a ∘ (finRotate (n + 1) ^ k).symm)) := by
  rw [B, lift_tensor]
  exact connesB_apply_of_mem_normalizedHochschildCochains
    (tensor_mem_normalizedHochschildCochains R A (n + 1)) a

variable {R A} {M : Type*} [AddCommGroup M] [Module R M]

/-- The transpose of the normalized Connes boundary is Connes' cochain operator. -/
theorem _root_.LinearMap.comp_normalizedHochschild_B_tensor {n : ℕ}
    (f : normalizedHochschildChains R A (n + 1) →ₗ[R] M) :
    (f ∘ₗ B R A n).compMultilinearMap (tensor R A n) =
      connesB R A M n (f.compMultilinearMap (tensor R A (n + 1))) := by
  ext a
  rw [connesB_apply_of_mem_normalizedHochschildCochains
    (f.compMultilinearMap_mem_normalizedHochschildCochains
      (tensor_mem_normalizedHochschildCochains R A (n + 1)))]
  simp [B_tensor]

variable (R A)

/-- Connes' normalized boundary squares to zero. -/
@[simp]
theorem B_B (n : ℕ) : B R A (n + 1) ∘ₗ B R A n = 0 := by
  apply hom_ext
  intro a
  have hB : (B R A (n + 1)).compMultilinearMap (tensor R A (n + 1)) =
      connesB R A _ (n + 1) (tensor R A (n + 2)) := by
    simpa using (LinearMap.id : normalizedHochschildChains R A (n + 2) →ₗ[R] _)
      |>.comp_normalizedHochschild_B_tensor
  have h := MultilinearMap.congr_fun
    ((B R A (n + 1)).comp_normalizedHochschild_B_tensor) a
  simpa only [hB, connesB_connesB, zero_apply,
    LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.zero_apply] using h

end normalizedHochschildChains

end Quotient

namespace normalizedHochschildChains

section Operators

variable (R A : Type*) [CommRing R] [NonAssocRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- The Hochschild boundary on normalized chains, lowering degree by one. -/
def b (n : ℕ) : normalizedHochschildChains R A (n + 1) →ₗ[R]
    normalizedHochschildChains R A n :=
  lift ⟨hochschildCoboundary R A _ n (tensor R A n),
    hochschildCoboundary_mem_normalizedHochschildCochains
      (tensor_mem_normalizedHochschildCochains R A n)⟩

/-- On tensors the normalized Hochschild boundary is the alternating sum of multiplication
faces, with the last face multiplying the last and first arguments in that order. -/
theorem b_tensor (n : ℕ) (a : Fin (n + 2) → A) :
    b R A n (tensor R A (n + 1) a) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • tensor R A n (hochschildFace i a) := by
  rw [b, lift_tensor, hochschildCoboundary_apply]

variable {R A} {M : Type*} [AddCommGroup M] [Module R M]

/-- The transpose of the normalized boundary is the Hochschild coboundary. -/
theorem _root_.LinearMap.comp_normalizedHochschild_b_tensor {n : ℕ}
    (f : normalizedHochschildChains R A n →ₗ[R] M) :
    (f ∘ₗ b R A n).compMultilinearMap (tensor R A (n + 1)) =
      hochschildCoboundary R A M n (f.compMultilinearMap (tensor R A n)) := by
  ext a
  simp [b_tensor, hochschildCoboundary_apply]

variable (R A)

/-- The two normalized boundaries anticommute in positive degree. -/
theorem b_B_add_B_b (n : ℕ) :
    b R A (n + 1) ∘ₗ B R A (n + 1) + B R A n ∘ₗ b R A n = 0 := by
  apply hom_ext
  intro a
  have hb : (b R A (n + 1)).compMultilinearMap (tensor R A (n + 2)) =
      hochschildCoboundary R A _ (n + 1) (tensor R A (n + 1)) := by
    simpa using (LinearMap.id : normalizedHochschildChains R A (n + 1) →ₗ[R] _)
      |>.comp_normalizedHochschild_b_tensor
  have hB : (B R A n).compMultilinearMap (tensor R A n) =
      connesB R A _ n (tensor R A (n + 1)) := by
    simpa using (LinearMap.id : normalizedHochschildChains R A (n + 1) →ₗ[R] _)
      |>.comp_normalizedHochschild_B_tensor
  have h₁ := MultilinearMap.congr_fun ((b R A (n + 1)).comp_normalizedHochschild_B_tensor) a
  have h₂ := MultilinearMap.congr_fun ((B R A n).comp_normalizedHochschild_b_tensor) a
  have h := MultilinearMap.congr_fun
    (hochschildCoboundary_connesB_add_connesB_hochschildCoboundary (tensor R A (n + 1))) a
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply] at h₁ h₂
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply]
  rw [h₁, h₂, hb, hB]
  exact (add_comm _ _).trans (by simpa only [add_apply, zero_apply] using h)

/-- The mixed identity at degree zero, where the outgoing Hochschild boundary is zero. -/
@[simp]
theorem b_B_zero : b R A 0 ∘ₗ B R A 0 = 0 := by
  apply hom_ext
  intro a
  have hb : (b R A 0).compMultilinearMap (tensor R A 1) =
      hochschildCoboundary R A _ 0 (tensor R A 0) := by
    simpa using (LinearMap.id : normalizedHochschildChains R A 0 →ₗ[R] _)
      |>.comp_normalizedHochschild_b_tensor
  have h := MultilinearMap.congr_fun ((b R A 0).comp_normalizedHochschild_B_tensor) a
  simpa only [hb, connesB_hochschildCoboundary_zero, zero_apply,
    LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.zero_apply] using h

end Operators

section Associative

variable (R A : Type*) [CommRing R] [Ring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- The normalized Hochschild boundary squares to zero. -/
@[simp]
theorem b_b (n : ℕ) : b R A n ∘ₗ b R A (n + 1) = 0 := by
  apply hom_ext
  intro a
  have hb : (b R A n).compMultilinearMap (tensor R A (n + 1)) =
      hochschildCoboundary R A _ n (tensor R A n) := by
    simpa using (LinearMap.id : normalizedHochschildChains R A n →ₗ[R] _)
      |>.comp_normalizedHochschild_b_tensor
  have h := MultilinearMap.congr_fun ((b R A n).comp_normalizedHochschild_b_tensor) a
  simpa only [hb, hochschildCoboundary_hochschildCoboundary, zero_apply,
    LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearMap.zero_apply] using h

open CategoryTheory in
/-- The native chain complex of normalized Hochschild chains with boundary `b`. -/
def chainComplex : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (normalizedHochschildChains R A n))
    (fun n ↦ ModuleCat.ofHom (b R A n)) fun n ↦ by
      apply ModuleCat.hom_ext
      exact b_b R A n

open CategoryTheory in
/-- Identify the degree-`n` term of the native complex with normalized chains. -/
def chainComplexXIso (n : ℕ) :
    (chainComplex R A).X n ≅ ModuleCat.of R (normalizedHochschildChains R A n) := Iso.refl _

open CategoryTheory in
/-- Under the term identifications, the differential of the native complex is `b`. -/
@[reassoc, elementwise]
theorem chainComplex_d (n : ℕ) :
    (chainComplex R A).d (n + 1) n ≫ (chainComplexXIso R A n).hom =
      (chainComplexXIso R A (n + 1)).hom ≫ ModuleCat.ofHom (b R A n) := by
  simp [chainComplex, chainComplexXIso]

end Associative

end normalizedHochschildChains

end TauCeti
