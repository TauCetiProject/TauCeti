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

Over a commutative `ℚ`-algebra, averaging the ordered products of Lie generators defines a
canonical linear map from each symmetric power to the enveloping algebra. Its leading PBW
symbol is the product of the symmetric generators. For a free Lie algebra module this gives
an injective map on every homogeneous symmetric-algebra component, splitting its PBW symbol.

This is the degreewise filtered comparison used to lift invariant symmetric polynomials to
the enveloping algebra. Equivariance and assembly across all degrees are separate statements.

The averaging map reuses `SymmetricPower.toTensorPower`; the leading-symbol computation uses
`prod_map_ι_sub_prod_map_ι_mem_pbwFiltrationPrevious_of_perm`.

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
  [Algebra ℚ R]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι R (L := L)

private noncomputable def wordMultilinear (n : ℕ) :
    MultilinearMap R (fun _ : Fin n ↦ L) U :=
  (MultilinearMap.mkPiAlgebraFin R n U).compLinearMap (fun _ ↦ (ι).toLinearMap)

/-- The average of all ordered products of a symmetric tensor's Lie generators. -/
noncomputable def pbwSymmetrization (n : ℕ) : Sym[R]^n L →ₗ[R] U :=
  algebraMap ℚ R ((n.factorial : ℚ)⁻¹) •
    ((PiTensorProduct.lift (wordMultilinear R L n)).comp
      (SymmetricPower.toTensorPower R (Fin n) L))

/-- On pure symmetric tensors, symmetrization averages the products over all permutations. -/
@[simp]
theorem pbwSymmetrization_tprod (n : ℕ) (m : Fin n → L) :
    pbwSymmetrization R L n (⨂ₛ[R] i, m i) =
      algebraMap ℚ R ((n.factorial : ℚ)⁻¹) •
        ∑ σ : Equiv.Perm (Fin n), (List.ofFn fun i ↦ ι (m (σ i))).prod := by
  simp [pbwSymmetrization, wordMultilinear]

private theorem normalization (n : ℕ) :
    algebraMap ℚ R ((n.factorial : ℚ)⁻¹) * (n.factorial : R) = 1 := by
  rw [← map_natCast (algebraMap ℚ R) n.factorial, ← map_mul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), map_one]

/-- Symmetrization sends a pure power to the corresponding power of a Lie generator. -/
@[simp high] -- Normalize pure powers before expanding the permutation sum.
theorem pbwSymmetrization_tprod_const (n : ℕ) (x : L) :
    pbwSymmetrization R L n (⨂ₛ[R] _ : Fin n, x) = (ι x) ^ n := by
  rw [pbwSymmetrization_tprod]
  simp only [List.ofFn_const, List.prod_replicate, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul R, smul_smul,
    normalization, one_smul]

/-- Symmetrization has PBW filtration degree at most its symmetric degree. -/
theorem pbwSymmetrization_mem (n : ℕ) (x : Sym[R]^n L) :
    pbwSymmetrization R L n x ∈ pbwFiltration R L n := by
  have hle : (⊤ : Submodule R (Sym[R]^n L)) ≤
      (pbwFiltration R L n).comap (pbwSymmetrization R L n) := by
    rw [← SymmetricPower.span_tprod_eq_top R (Fin n) L, Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    apply (Submodule.mem_comap).mpr
    rw [pbwSymmetrization_tprod]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro σ _
    simpa only [List.map_ofFn, Function.comp_def] using
      prod_map_ι_mem_pbwFiltration R L (l := List.ofFn fun i ↦ m (σ i)) (by simp)
  exact hle Submodule.mem_top

/-- Symmetrizing a word changes it only in strictly smaller PBW filtration degree. -/
theorem pbwSymmetrization_tprod_sub_mem (n : ℕ) (m : Fin n → L) :
    pbwSymmetrization R L n (⨂ₛ[R] i, m i) - (List.ofFn fun i ↦ ι (m i)).prod ∈
      pbwFiltrationPrevious R L n := by
  classical
  have h (σ : Equiv.Perm (Fin n)) :
      (List.ofFn fun i ↦ ι (m (σ i))).prod - (List.ofFn fun i ↦ ι (m i)).prod ∈
        pbwFiltrationPrevious R L n := by
    simpa only [List.map_ofFn, Function.comp_def, List.length_ofFn] using
      prod_map_ι_sub_prod_map_ι_mem_pbwFiltrationPrevious_of_perm R L
        (σ.ofFn_comp_perm m)
  have hsum := (pbwFiltrationPrevious R L n).smul_mem
    (algebraMap ℚ R ((n.factorial : ℚ)⁻¹))
    ((pbwFiltrationPrevious R L n).sum_mem (t := Finset.univ) fun σ _ ↦ h σ)
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, smul_sub, ← Nat.cast_smul_eq_nsmul R,
    smul_smul, normalization, one_smul, pbwSymmetrization_tprod] using hsum

variable [Module.Free R L]

/-- Degreewise symmetrization, expressed on homogeneous symmetric polynomials. -/
noncomputable def pbwHomogeneousSymmetrization (n : ℕ) :
    homogeneousSubmodule R L n →ₗ[R] U :=
  (pbwSymmetrization R L n).comp
    (SymmetricPower.equivHomogeneous (R := R) (M := L) n).symm.toLinearMap

/-- The homogeneous map agrees with tensor symmetrization under the canonical comparison. -/
@[simp]
theorem pbwHomogeneousSymmetrization_equivHomogeneous (n : ℕ) (x : Sym[R]^n L) :
    pbwHomogeneousSymmetrization R L n (SymmetricPower.equivHomogeneous n x) =
      pbwSymmetrization R L n x := by
  simp [pbwHomogeneousSymmetrization]

/-- Homogeneous symmetrization lands in the corresponding PBW filtration step. -/
theorem pbwHomogeneousSymmetrization_mem (n : ℕ) (p : homogeneousSubmodule R L n) :
    pbwHomogeneousSymmetrization R L n p ∈ pbwFiltration R L n := by
  rw [pbwHomogeneousSymmetrization, LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact pbwSymmetrization_mem R L n _

/-- Taking the leading PBW symbol of symmetrization recovers the canonical PBW image. -/
theorem mk_pbwHomogeneousSymmetrization (n : ℕ) (p : homogeneousSubmodule R L n) :
    Submodule.Quotient.mk
      (⟨pbwHomogeneousSymmetrization R L n p,
        by simpa only [pbwFiltration_def] using pbwHomogeneousSymmetrization_mem R L n p⟩ :
        TauCeti.Algebra.wordFiltration (ι).toLinearMap n) =
      pbwHomogeneousComponentMap R L n p := by
  let lhs : homogeneousSubmodule R L n →ₗ[R] PBWGradedPiece R L n :=
    (Submodule.mkQ (TauCeti.Algebra.wordFiltration.previousRestricted (ι).toLinearMap n)).comp
      ((pbwHomogeneousSymmetrization R L n).codRestrict _
        (fun p ↦ by simpa only [pbwFiltration_def] using
          pbwHomogeneousSymmetrization_mem R L n p))
  suffices hl : lhs = pbwHomogeneousComponentMap R L n from LinearMap.congr_fun hl p
  apply (LinearMap.cancel_right
    (SymmetricPower.equivHomogeneous (R := R) (M := L) n).surjective).mp
  apply SymmetricPower.ext
  intro m
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have hprod : (∏ i, SymmetricAlgebra.ι R L (m i)) =
      ((List.ofFn m).map (SymmetricAlgebra.ι R L)).prod := by
    simp [List.prod_ofFn]
  have hp : SymmetricPower.equivHomogeneous n (⨂ₛ[R] i, m i) =
      (⟨((List.ofFn m).map (SymmetricAlgebra.ι R L)).prod,
        by simpa using prod_map_ι_mem_homogeneousSubmodule R L (List.ofFn m)⟩ :
          homogeneousSubmodule R L n) := by
    apply Subtype.ext
    rw [SymmetricPower.coe_equivHomogeneous_apply, SymmetricPower.toSymmetricAlgebra_tprod,
      hprod]
  rw [hp]
  have hsymbol (l : List L) (hl : l.length = n) :
      pbwHomogeneousComponentMap R L n
          ⟨(l.map (SymmetricAlgebra.ι R L)).prod,
            by simpa only [hl] using prod_map_ι_mem_homogeneousSubmodule R L l⟩ =
        (Submodule.Quotient.mk
          ⟨(l.map (ι)).prod, TauCeti.Algebra.prod_map_mem_wordFiltration
            (ι).toLinearMap hl.le⟩ : PBWGradedPiece R L n) := by
    subst n
    exact pbwHomogeneousComponentMap_prod_map_ι R L l
  rw [hsymbol (List.ofFn m) List.length_ofFn]
  apply (Submodule.Quotient.eq _).mpr
  rw [TauCeti.Algebra.wordFiltration.mem_previousRestricted_iff]
  simp only [LinearMap.codRestrict_apply, Submodule.coe_sub]
  rw [← hp, pbwHomogeneousSymmetrization_equivHomogeneous]
  simpa only [pbwFiltrationPrevious_def, List.map_ofFn, Function.comp_def] using
    pbwSymmetrization_tprod_sub_mem R L n m

/-- Symmetrization of homogeneous symmetric polynomials is injective. -/
theorem pbwHomogeneousSymmetrization_injective (n : ℕ) :
    Function.Injective (pbwHomogeneousSymmetrization R L n) := by
  intro p q hpq
  apply pbwHomogeneousComponentMap_injective R L n
  rw [← mk_pbwHomogeneousSymmetrization, ← mk_pbwHomogeneousSymmetrization]
  exact congrArg Submodule.Quotient.mk (Subtype.ext hpq)

/-- Degreewise tensor symmetrization is injective when the Lie algebra module is free. -/
theorem pbwSymmetrization_injective (n : ℕ) :
    Function.Injective (pbwSymmetrization R L n) := by
  intro x y h
  apply (SymmetricPower.equivHomogeneous (R := R) (M := L) n).injective
  apply pbwHomogeneousSymmetrization_injective R L n
  simpa only [pbwHomogeneousSymmetrization_equivHomogeneous] using h

end TauCeti.UniversalEnvelopingAlgebra
