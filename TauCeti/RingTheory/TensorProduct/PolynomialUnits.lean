/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.RingTheory.Polynomial.DivisorsOfSplit
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Units after localizing a split polynomial and extending a domain

If `h : k[X]` splits over the field `k` and `A` is a domain over `k`, every unit of
`A ⊗[k] k[X]ₕ` is a pure tensor of units. This includes `h = 0`, when the localization
is the trivial ring. For algebraically closed `k`, every `h` satisfies the splitting hypothesis.

This controls transition units when comparing line bundles along points of an open affine line.

## References

* The Stacks Project, Tag 0BEH.
-/

public noncomputable section

open Polynomial TensorProduct

variable {k : Type*} [Field k]

/-- A unit after base change of a polynomial localization at a split polynomial is
one unit from the coefficient domain tensored with one from the polynomial localization. -/
theorem TauCeti.Algebra.TensorProduct.exists_units_eq_tmul_of_splits
    (A : Type*) [CommRing A] [IsDomain A] [Algebra k A]
    {h : k[X]} (hsplit : h.Splits) (u : (A ⊗[k] Localization.Away h)ˣ) :
    ∃ (a : Aˣ) (v : (Localization.Away h)ˣ),
      (u : A ⊗[k] Localization.Away h) = (a : A) ⊗ₜ (v : Localization.Away h) := by
  by_cases hh : h = 0
  · subst h
    have : Subsingleton (Localization.Away (0 : k[X])) := by
      have hz : IsUnit (0 : Localization.Away (0 : k[X])) := by
        simpa only [map_zero] using
          IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (0 : k[X])) (0 : k[X])
      exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hz)
    exact ⟨1, 1, Subsingleton.elim _ _⟩
  let : IsDomain (A ⊗[k] k[X]) :=
    (polyEquivTensor k A).toMulEquiv.symm.isDomain _
  let : Algebra (A ⊗[k] k[X]) (A ⊗[k] Localization.Away h) :=
    (Algebra.TensorProduct.map (AlgHom.id k A)
      (IsScalarTower.toAlgHom k k[X] (Localization.Away h))).toAlgebra
  have : IsScalarTower A (A ⊗[k] k[X]) (A ⊗[k] Localization.Away h) := by
    refine IsScalarTower.of_algebraMap_eq (R := A)
      (S := A ⊗[k] k[X])
      (A := A ⊗[k] Localization.Away h) ?_
    intro scalar
    change scalar ⊗ₜ[k] (1 : Localization.Away h) =
      scalar ⊗ₜ[k] (algebraMap k[X] (Localization.Away h) 1)
    rw [map_one]
  have hloc := IsLocalization.tensorProduct_tensorProduct_right k A (Submonoid.powers h)
    (Localization.Away h) (by ext <;> simp [RingHom.algebraMap_toAlgebra])
  rw [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply] at hloc
  have halg (x : A) (y : k[X]) : algebraMap (A ⊗[k] k[X]) (A ⊗[k] Localization.Away h)
      (x ⊗ₜ y) = x ⊗ₜ algebraMap k[X] _ y := rfl
  have hM : Submonoid.powers ((1 : A) ⊗ₜ[k] h) ≤ nonZeroDivisors (A ⊗[k] k[X]) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (by
      intro hz
      have := congrArg (polyEquivTensor k A).symm hz
      rw [polyEquivTensor_symm_apply_tmul_eq_smul, one_smul, map_zero,
        Polynomial.map_eq_zero_iff (algebraMap k A).injective] at this
      exact hh this)
  obtain ⟨⟨p, roots, n, rfl⟩, hP⟩ := IsLocalization.surj (Submonoid.powers ((1 : A) ⊗ₜ[k] h))
    (u : A ⊗[k] Localization.Away h)
  obtain ⟨⟨q, s', m, rfl⟩, hQ⟩ := IsLocalization.surj (Submonoid.powers ((1 : A) ⊗ₜ[k] h))
    (↑u⁻¹ : A ⊗[k] Localization.Away h)
  have hPQ : p * q = (1 ⊗ₜ h) ^ (n + m) := by
    apply IsLocalization.injective (A ⊗[k] Localization.Away h) hM
    rw [map_mul, ← hP, ← hQ, mul_mul_mul_comm, Units.mul_inv, one_mul, ← map_mul, pow_add]
  have hdvd : (polyEquivTensor k A).symm p ∣ (h ^ (n + m)).map (algebraMap k A) := by
    refine ⟨(polyEquivTensor k A).symm q, ?_⟩
    rw [← map_mul, hPQ, Algebra.TensorProduct.tmul_pow, one_pow,
      polyEquivTensor_symm_apply_tmul_eq_smul, one_smul]
  obtain ⟨a, g, hg, hPg⟩ := (hsplit.pow _).exists_eq_C_mul_map_of_dvd_map (pow_ne_zero _ hh) hdvd
  have hgu : IsUnit (algebraMap k[X] (Localization.Away h) g) := by
    obtain ⟨c, hc⟩ := hg
    refine isUnit_of_mul_isUnit_left (y := algebraMap k[X] (Localization.Away h) c) ?_
    rw [← map_mul, ← hc, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit h).pow _
  have hhu : IsUnit (algebraMap k[X] (Localization.Away h) h ^ n) :=
    (IsLocalization.Away.algebraMap_isUnit h).pow _
  refine ⟨a, hgu.unit * hhu.unit⁻¹, ?_⟩
  have hP' : p = (a : A) ⊗ₜ g := by
    rw [← (polyEquivTensor k A).apply_symm_apply p, hPg, ← smul_eq_C_mul,
      ← polyEquivTensor_symm_apply_tmul_eq_smul, AlgEquiv.apply_symm_apply]
  have hunit : IsUnit (algebraMap (A ⊗[k] k[X]) (A ⊗[k] Localization.Away h)
      ((1 ⊗ₜ h) ^ n)) := IsLocalization.map_units _ (⟨_, n, rfl⟩ : Submonoid.powers _)
  rw [← hunit.mul_left_inj, hP, hP', halg, Algebra.TensorProduct.tmul_pow, one_pow, halg,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, Units.val_mul, mul_assoc, map_pow,
    IsUnit.val_inv_mul, mul_one, IsUnit.unit_spec]
