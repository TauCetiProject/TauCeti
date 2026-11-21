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
# Units after localizing split polynomials and extending a domain

For a submonoid `M` of split polynomials over a commutative ring `R`, assume their leading
coefficients map to units in a domain `A` over `R`. Every unit after localizing and extending
scalars to `A` is a pure tensor of units.

Over a field `k`, nonzero polynomials have unit leading coefficients. If `0 ∈ M`, the
localization is trivial, and the pure-tensor-of-units conclusion still holds. Thus the field
result applies to all submonoids of split polynomials, including localization at a single
split polynomial `h = 0`. If `k` is algebraically closed, every polynomial splits.

This controls transition units when comparing line bundles along points of an open affine line.

## References

* The Stacks Project, Tag 0BEH.
-/

public noncomputable section

open Polynomial TensorProduct

/-- Units after base change to a domain of a polynomial localization are pure tensors of
units when every inverted polynomial splits over the base ring and its leading coefficient
maps to a unit in the domain. -/
theorem Submonoid.exists_units_eq_tmul_of_splits_of_isUnit_algebraMap_leadingCoeff
    {R A B : Type*} [CommRing R] [CommRing A] [IsDomain A] [Algebra R A]
    [CommRing B] [Algebra R B] [Algebra R[X] B] [IsScalarTower R R[X] B]
    (M : Submonoid R[X]) [IsLocalization M B]
    (hsplit : ∀ h ∈ M, h.Splits)
    (hu : ∀ h ∈ M, IsUnit (algebraMap R A h.leadingCoeff))
    (u : (A ⊗[R] B)ˣ) :
    ∃ (a : Aˣ) (v : Bˣ), (u : A ⊗[R] B) = (a : A) ⊗ₜ (v : B) := by
  let M' := M.map (Algebra.TensorProduct.includeRight (R := R) (A := A))
  let S := Localization M'
  let e := IsLocalization.tensorProductEquivOfMapIncludeRight R A M B S
  obtain ⟨⟨p, q⟩, hP⟩ := IsLocalization.surj M' (e (u : A ⊗[R] B))
  have hqu : IsUnit (algebraMap (A ⊗[R] R[X]) S (q : A ⊗[R] R[X])) :=
    IsLocalization.map_units S q
  have hpu : IsUnit (algebraMap (A ⊗[R] R[X]) S p) :=
    hP ▸ (u.isUnit.map e).mul hqu
  obtain ⟨n, hn, hpn⟩ := (IsLocalization.algebraMap_isUnit_iff M' (S := S)).mp hpu
  obtain ⟨h, hh, rfl⟩ := hn
  have hdvd : (polyEquivTensor R A).symm p ∣ h.map (algebraMap R A) := by
    simpa using map_dvd (polyEquivTensor R A).symm.toRingHom hpn
  obtain ⟨a, g, hg, hpg⟩ := (hsplit h hh).exists_eq_C_mul_map_of_dvd_map (hu h hh) hdvd
  have hp : p = (a : A) ⊗ₜ[R] g := by
    apply (polyEquivTensor R A).symm.injective
    simpa [polyEquivTensor_symm_apply_tmul_eq_smul, smul_eq_C_mul] using hpg
  obtain ⟨den, hden, hdeneq⟩ := q.property
  have hgu : IsUnit (algebraMap R[X] B g) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap R[X] B) hg)
      (IsLocalization.map_units B ⟨h, hh⟩)
  have hdu : IsUnit (algebraMap R[X] B den) := IsLocalization.map_units B ⟨den, hden⟩
  refine ⟨a, hgu.unit * hdu.unit⁻¹, e.injective ?_⟩
  rw [← hqu.mul_left_inj, hP, hp]
  rw [← hdeneq, Algebra.TensorProduct.includeRight_apply]
  rw [← IsLocalization.tensorProductEquivOfMapIncludeRight_tmul (R := R) (S := A)
      R[X] M B S 1 den,
    ← map_mul, Algebra.TensorProduct.tmul_mul_tmul]
  have hcancel : (↑hdu.unit⁻¹ : B) * (algebraMap R[X] B den) = 1 := by
    simpa only [IsUnit.unit_spec] using Units.inv_mul hdu.unit
  simp only [Units.val_mul, IsUnit.unit_spec, mul_one, mul_assoc, hcancel]
  exact (IsLocalization.tensorProductEquivOfMapIncludeRight_tmul R[X] M B S (a : A) g).symm

/-- Over a field, localizing at any submonoid of split polynomials and extending a domain
creates only pure tensors of units. The statement includes the zero localization. -/
theorem Submonoid.exists_units_eq_tmul_of_splits
    {k A B : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [CommRing B] [Algebra k B] [Algebra k[X] B] [IsScalarTower k k[X] B]
    (M : Submonoid k[X]) [IsLocalization M B]
    (hsplit : ∀ h ∈ M, h.Splits) (u : (A ⊗[k] B)ˣ) :
    ∃ (a : Aˣ) (v : Bˣ), (u : A ⊗[k] B) = (a : A) ⊗ₜ (v : B) := by
  by_cases hzero : 0 ∈ M
  · have : Subsingleton B := IsLocalization.subsingleton hzero
    exact ⟨1, 1, Subsingleton.elim _ _⟩
  exact M.exists_units_eq_tmul_of_splits_of_isUnit_algebraMap_leadingCoeff hsplit (fun h hh ↦
    ((leadingCoeff_ne_zero.mpr (ne_of_mem_of_not_mem hh hzero)).isUnit).map
      (algebraMap k A)) u

/-- A unit after base change to a domain of a localization at a split polynomial over a field
is a pure tensor of units. This applies to any localization model, including the zero ring. -/
theorem Polynomial.Splits.exists_units_eq_tmul
    {k A B : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [CommRing B] [Algebra k B] [Algebra k[X] B] [IsScalarTower k k[X] B]
    {h : k[X]} [IsLocalization.Away h B] (hsplit : h.Splits) (u : (A ⊗[k] B)ˣ) :
    ∃ (a : Aˣ) (v : Bˣ), (u : A ⊗[k] B) = (a : A) ⊗ₜ (v : B) := by
  apply (Submonoid.powers h).exists_units_eq_tmul_of_splits _ u
  rintro _ ⟨n, rfl⟩
  exact hsplit.pow n
