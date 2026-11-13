/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.Algebra.Polynomial.Splits
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.PolynomialAlgebra

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

/-- Over a field `k`, a unit after base change of a localization at a split polynomial is
one unit from the coefficient domain tensored with one from the polynomial localization.
The statement applies to any model of the localization, including basic-open coordinate rings. -/
theorem TauCeti.Algebra.TensorProduct.exists_units_eq_tmul_of_splits
    {A B : Type*} [CommRing A] [IsDomain A] [Algebra k A]
    [CommRing B] [Algebra k B] [Algebra k[X] B] [IsScalarTower k k[X] B]
    {h : k[X]} [IsLocalization.Away h B] (hsplit : h.Splits) (u : (A ⊗[k] B)ˣ) :
    ∃ (a : Aˣ) (v : Bˣ), (u : A ⊗[k] B) = (a : A) ⊗ₜ (v : B) := by
  by_cases hh : h = 0
  · subst h
    have : Subsingleton B :=
      IsLocalization.subsingleton (M := Submonoid.powers (0 : k[X])) (Submonoid.mem_powers 0)
    exact ⟨1, 1, Subsingleton.elim _ _⟩
  let : IsDomain (A ⊗[k] k[X]) :=
    (polyEquivTensor k A).toMulEquiv.symm.isDomain _
  let tensorAlgebra : Algebra (A ⊗[k] k[X]) (A ⊗[k] B) :=
    (Algebra.TensorProduct.map (AlgHom.id k A)
      (IsScalarTower.toAlgHom k k[X] B)).toAlgebra
  -- Base change makes the tensor algebra a localization of the polynomial tensor algebra.
  have : IsScalarTower A (A ⊗[k] k[X]) (A ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := A ⊗[k] k[X]) (A := A ⊗[k] B) <| by
      intro scalar
      simp [tensorAlgebra, RingHom.algebraMap_toAlgebra]
  have hloc := IsLocalization.tensorProduct_tensorProduct_right k A (Submonoid.powers h)
    B (by ext <;> simp [tensorAlgebra, RingHom.algebraMap_toAlgebra])
  rw [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply] at hloc
  have halg (x : A) (y : k[X]) : algebraMap (A ⊗[k] k[X]) (A ⊗[k] B)
      (x ⊗ₜ y) = x ⊗ₜ algebraMap k[X] _ y := by
    simp [tensorAlgebra, RingHom.algebraMap_toAlgebra]
  have hM : Submonoid.powers ((1 : A) ⊗ₜ[k] h) ≤ nonZeroDivisors (A ⊗[k] k[X]) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (by
      intro hz
      have := congrArg (polyEquivTensor k A).symm hz
      rw [polyEquivTensor_symm_apply_tmul_eq_smul, one_smul, map_zero,
        Polynomial.map_eq_zero_iff (algebraMap k A).injective] at this
      exact hh this)
  -- Clear denominators for the unit and its inverse, then descend their numerator factors.
  obtain ⟨⟨p, roots, n, rfl⟩, hP⟩ := IsLocalization.surj (Submonoid.powers ((1 : A) ⊗ₜ[k] h))
    (u : A ⊗[k] B)
  obtain ⟨⟨q, s', m, rfl⟩, hQ⟩ := IsLocalization.surj (Submonoid.powers ((1 : A) ⊗ₜ[k] h))
    (↑u⁻¹ : A ⊗[k] B)
  have hPQ : p * q = (1 ⊗ₜ h) ^ (n + m) := by
    apply IsLocalization.injective (A ⊗[k] B) hM
    rw [map_mul, ← hP, ← hQ, mul_mul_mul_comm, Units.mul_inv, one_mul, ← map_mul, pow_add]
  have hdvd : (polyEquivTensor k A).symm p ∣ (h ^ (n + m)).map (algebraMap k A) := by
    refine ⟨(polyEquivTensor k A).symm q, ?_⟩
    rw [← map_mul, hPQ, Algebra.TensorProduct.tmul_pow, one_pow,
      polyEquivTensor_symm_apply_tmul_eq_smul, one_smul]
  obtain ⟨a, g, hg, hPg⟩ := (hsplit.pow _).exists_eq_C_mul_map_of_dvd_map (pow_ne_zero _ hh) hdvd
  have hgu : IsUnit (algebraMap k[X] B g) :=
    (IsLocalization.Away.algebraMap_isUnit_iff h).mpr ⟨n + m, hg⟩
  have hhu : IsUnit (algebraMap k[X] B h ^ n) :=
    (IsLocalization.Away.algebraMap_isUnit h).pow _
  refine ⟨a, hgu.unit * hhu.unit⁻¹, ?_⟩
  have hP' : p = (a : A) ⊗ₜ g := by
    rw [← (polyEquivTensor k A).apply_symm_apply p, hPg, ← smul_eq_C_mul,
      ← polyEquivTensor_symm_apply_tmul_eq_smul, AlgEquiv.apply_symm_apply]
  have hunit : IsUnit (algebraMap (A ⊗[k] k[X]) (A ⊗[k] B)
      ((1 ⊗ₜ h) ^ n)) := IsLocalization.map_units _ (⟨_, n, rfl⟩ : Submonoid.powers _)
  -- Cancel the denominator unit separately from the tensor-product normalization.
  rw [← hunit.mul_left_inj, hP, hP']
  simp [halg, mul_assoc]
