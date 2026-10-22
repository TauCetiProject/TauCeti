/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Injective
public import TauCeti.LinearAlgebra.SymmetricPower.Algebra

/-!
# Degreewise PBW symmetrization

When `n!` is a unit in the commutative base ring, averaging the ordered products of Lie
generators defines a canonical linear map from the `n`th symmetric power to the enveloping
algebra. Its leading PBW symbol is the product of the symmetric generators. When `L` is free
as an `R`-module, this gives an injective map on every homogeneous symmetric-algebra component,
splitting its PBW symbol.

This is the degreewise filtered comparison used to lift invariant symmetric polynomials to
the enveloping algebra without changing their leading terms.

The scalar ring lies in `Type`, as required by Mathlib's `Fin n`-indexed symmetric power
`Sym[R]^n L`. The Lie algebra module has an independent universe.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §23.3.
* J. Dixmier, *Enveloping Algebras*, §2.4.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

open TauCeti.SymmetricAlgebra

universe v

variable (R : Type) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι R (L := L)

private noncomputable def wordMultilinear (n : ℕ) :
    MultilinearMap R (fun _ : Fin n ↦ L) U :=
  (MultilinearMap.mkPiAlgebraFin R n U).compLinearMap (fun _ ↦ (ι).toLinearMap)

private theorem unit_inv_smul_sum_perm_const {M : Type*} [AddCommMonoid M] [Module R M]
    (n : ℕ) (hn : IsUnit (n.factorial : R)) (y : M) :
    (↑hn.unit⁻¹ : R) • ∑ _σ : Equiv.Perm (Fin n), y = y := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul R, smul_smul, hn.val_inv_mul, one_smul]

/-- The average of all ordered products of a symmetric tensor's Lie generators. -/
noncomputable def pbwSymmetrization (n : ℕ) (hn : IsUnit (n.factorial : R)) : Sym[R]^n L →ₗ[R] U :=
  (↑hn.unit⁻¹ : R) •
    ((PiTensorProduct.lift (wordMultilinear R L n)).comp
      (SymmetricPower.toTensorPower R (Fin n) L))

/-- On pure symmetric tensors, symmetrization averages the products over all permutations. -/
@[simp]
theorem pbwSymmetrization_tprod (n : ℕ) (hn : IsUnit (n.factorial : R)) (m : Fin n → L) :
    pbwSymmetrization R L n hn (⨂ₛ[R] i, m i) =
      (↑hn.unit⁻¹ : R) •
        ∑ σ : Equiv.Perm (Fin n), (List.ofFn fun i ↦ ι (m (σ i))).prod := by
  simp [pbwSymmetrization, wordMultilinear]

/-- Over a rational algebra, the unit-normalized average is the usual rational average. -/
theorem pbwSymmetrization_tprod_rat [Algebra ℚ R] (n : ℕ)
    (hn : IsUnit (n.factorial : R)) (m : Fin n → L) :
    pbwSymmetrization R L n hn (⨂ₛ[R] i, m i) =
      algebraMap ℚ R ((n.factorial : ℚ)⁻¹) •
        ∑ σ : Equiv.Perm (Fin n), (List.ofFn fun i ↦ ι (m (σ i))).prod := by
  rw [pbwSymmetrization_tprod]
  have hinv : (↑hn.unit⁻¹ : R) = algebraMap ℚ R ((n.factorial : ℚ)⁻¹) := by
    apply hn.unit.inv_eq_of_mul_eq_one_left
    rw [IsUnit.unit_spec, ← map_natCast (algebraMap ℚ R) n.factorial]
    simp only [← map_mul]
    simp [Nat.factorial_ne_zero]
  rw [hinv]

/-- Symmetrization sends a pure power to the corresponding power of a Lie generator. -/
@[simp high] -- Normalize pure powers before expanding the permutation sum.
theorem pbwSymmetrization_tprod_const (n : ℕ) (hn : IsUnit (n.factorial : R)) (x : L) :
    pbwSymmetrization R L n hn (⨂ₛ[R] _ : Fin n, x) = (ι x) ^ n := by
  rw [pbwSymmetrization_tprod]
  simp only [List.ofFn_const, List.prod_replicate, unit_inv_smul_sum_perm_const]

/-- Symmetrization has PBW filtration degree at most its symmetric degree. -/
theorem pbwSymmetrization_mem_pbwFiltration (n : ℕ) (hn : IsUnit (n.factorial : R))
    (x : Sym[R]^n L) :
    pbwSymmetrization R L n hn x ∈ pbwFiltration R L n := by
  apply SymmetricPower.map_mem_of_forall_tprod
  intro m
  rw [pbwSymmetrization_tprod]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro σ _
  simpa only [List.map_ofFn, Function.comp_def] using
    prod_map_ι_mem_pbwFiltration R L (l := List.ofFn fun i ↦ m (σ i)) (by simp)

/-- Symmetrizing a word changes it only in strictly smaller PBW filtration degree. -/
theorem pbwSymmetrization_tprod_sub_mem_pbwFiltrationPrevious (n : ℕ)
    (hn : IsUnit (n.factorial : R)) (m : Fin n → L) :
    pbwSymmetrization R L n hn (⨂ₛ[R] i, m i) - (List.ofFn fun i ↦ ι (m i)).prod ∈
      pbwFiltrationPrevious R L n := by
  classical
  have h (σ : Equiv.Perm (Fin n)) :
      (List.ofFn fun i ↦ ι (m (σ i))).prod - (List.ofFn fun i ↦ ι (m i)).prod ∈
        pbwFiltrationPrevious R L n := by
    simpa only [List.map_ofFn, Function.comp_def, List.length_ofFn] using
      prod_map_ι_sub_prod_map_ι_mem_pbwFiltrationPrevious_of_perm R L
        (σ.ofFn_comp_perm m)
  have hsum := (pbwFiltrationPrevious R L n).smul_mem
    (↑hn.unit⁻¹ : R)
    ((pbwFiltrationPrevious R L n).sum_mem (t := Finset.univ) fun σ _ ↦ h σ)
  simpa only [Finset.sum_sub_distrib, smul_sub, unit_inv_smul_sum_perm_const,
    pbwSymmetrization_tprod] using hsum

/-- The leading symbol of tensor symmetrization is its canonical PBW image, without any
freeness assumption on the Lie algebra module. -/
@[simp↓] -- Take the symbol before expanding tensor symmetrization.
theorem mk_pbwSymmetrization (n : ℕ) (hn : IsUnit (n.factorial : R))
    (x : Sym[R]^n L) :
    Submodule.Quotient.mk
      (⟨pbwSymmetrization R L n hn x,
        by simpa only [pbwFiltration_def] using
          pbwSymmetrization_mem_pbwFiltration R L n hn x⟩ :
        TauCeti.Algebra.wordFiltration (ι).toLinearMap n) =
      pbwHomogeneousComponentMap R L n (SymmetricPower.toHomogeneous R L n x) := by
  let lhs : Sym[R]^n L →ₗ[R] PBWGradedPiece R L n :=
    (Submodule.mkQ (TauCeti.Algebra.wordFiltration.previousRestricted (ι).toLinearMap n)).comp
      ((pbwSymmetrization R L n hn).codRestrict _ fun x ↦
        by simpa only [pbwFiltration_def] using
          pbwSymmetrization_mem_pbwFiltration R L n hn x)
  suffices hl : lhs = (pbwHomogeneousComponentMap R L n).comp
      (SymmetricPower.toHomogeneous R L n) from LinearMap.congr_fun hl x
  apply SymmetricPower.ext
  intro m
  have hprod : SymmetricPower.toHomogeneous R L n (⨂ₛ[R] i, m i) =
      ⟨((List.ofFn m).map (SymmetricAlgebra.ι R L)).prod,
        by simpa only [List.length_ofFn] using
          prod_map_ι_mem_homogeneousSubmodule R L (List.ofFn m)⟩ := by
    apply Subtype.ext
    simp [List.prod_ofFn]
  simp only [LinearMap.comp_apply, hprod,
    pbwHomogeneousComponentMap_prod_map_ι_of_length_eq R L (List.ofFn m) List.length_ofFn]
  apply (Submodule.Quotient.eq _).mpr
  rw [TauCeti.Algebra.wordFiltration.mem_previousRestricted_iff]
  simp only [LinearMap.codRestrict_apply, Submodule.coe_sub]
  simpa only [pbwFiltrationPrevious_def, List.map_ofFn, Function.comp_def] using
    pbwSymmetrization_tprod_sub_mem_pbwFiltrationPrevious R L n hn m

variable [Module.Free R L]

/-- Degreewise symmetrization, expressed on homogeneous symmetric polynomials. -/
noncomputable def pbwHomogeneousSymmetrization (n : ℕ) (hn : IsUnit (n.factorial : R)) :
    homogeneousSubmodule R L n →ₗ[R] U :=
  (pbwSymmetrization R L n hn).comp
    (SymmetricPower.equivHomogeneous (R := R) (M := L) n).symm.toLinearMap

/-- Homogeneous symmetrization is tensor symmetrization after the inverse comparison. -/
@[simp low] -- Prefer cancelling the homogeneous comparison before expanding.
theorem pbwHomogeneousSymmetrization_apply (n : ℕ) (hn : IsUnit (n.factorial : R))
    (p : homogeneousSubmodule R L n) :
    pbwHomogeneousSymmetrization R L n hn p =
      pbwSymmetrization R L n hn ((SymmetricPower.equivHomogeneous n).symm p) := by
  rfl

/-- The homogeneous map agrees with tensor symmetrization under the canonical comparison. -/
@[simp]
theorem pbwHomogeneousSymmetrization_equivHomogeneous (n : ℕ) (hn : IsUnit (n.factorial : R))
    (x : Sym[R]^n L) :
    pbwHomogeneousSymmetrization R L n hn (SymmetricPower.equivHomogeneous n x) =
      pbwSymmetrization R L n hn x := by
  simp [pbwHomogeneousSymmetrization]

/-- Homogeneous symmetrization lands in the corresponding PBW filtration step. -/
theorem pbwHomogeneousSymmetrization_mem_pbwFiltration (n : ℕ) (hn : IsUnit (n.factorial : R))
    (p : homogeneousSubmodule R L n) :
    pbwHomogeneousSymmetrization R L n hn p ∈ pbwFiltration R L n := by
  rw [pbwHomogeneousSymmetrization_apply]
  exact pbwSymmetrization_mem_pbwFiltration R L n hn _

/-- Homogeneous symmetrization lands in the word filtration used for the PBW graded piece. -/
theorem pbwHomogeneousSymmetrization_mem_wordFiltration (n : ℕ) (hn : IsUnit (n.factorial : R))
    (p : homogeneousSubmodule R L n) :
    pbwHomogeneousSymmetrization R L n hn p ∈ TauCeti.Algebra.wordFiltration (ι).toLinearMap n := by
  simpa only [pbwFiltration_def] using
    pbwHomogeneousSymmetrization_mem_pbwFiltration R L n hn p

/-- Taking the leading PBW symbol of symmetrization recovers the canonical PBW image. -/
@[simp↓] -- Take the symbol before expanding homogeneous symmetrization.
theorem mk_pbwHomogeneousSymmetrization (n : ℕ) (hn : IsUnit (n.factorial : R))
    (p : homogeneousSubmodule R L n) :
    Submodule.Quotient.mk
      (⟨pbwHomogeneousSymmetrization R L n hn p,
        pbwHomogeneousSymmetrization_mem_wordFiltration R L n hn p⟩ :
        TauCeti.Algebra.wordFiltration (ι).toLinearMap n) =
      pbwHomogeneousComponentMap R L n p := by
  simpa only [← SymmetricPower.toLinearMap_equivHomogeneous, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, pbwHomogeneousSymmetrization_apply] using
    mk_pbwSymmetrization R L n hn ((SymmetricPower.equivHomogeneous n).symm p)

/-- Symmetrization of homogeneous symmetric polynomials is injective. -/
theorem pbwHomogeneousSymmetrization_injective (n : ℕ) (hn : IsUnit (n.factorial : R)) :
    Function.Injective (pbwHomogeneousSymmetrization R L n hn) := by
  intro p q hpq
  apply pbwHomogeneousComponentMap_injective R L n
  rw [← mk_pbwHomogeneousSymmetrization R L n hn,
    ← mk_pbwHomogeneousSymmetrization R L n hn]
  exact congrArg Submodule.Quotient.mk (Subtype.ext hpq)

/-- Degreewise tensor symmetrization is injective when the Lie algebra module is free. -/
theorem pbwSymmetrization_injective (n : ℕ) (hn : IsUnit (n.factorial : R)) :
    Function.Injective (pbwSymmetrization R L n hn) := by
  intro x y h
  apply (SymmetricPower.equivHomogeneous (R := R) (M := L) n).injective
  apply pbwHomogeneousSymmetrization_injective R L n hn
  simpa only [pbwHomogeneousSymmetrization_equivHomogeneous] using h

end TauCeti.UniversalEnvelopingAlgebra
