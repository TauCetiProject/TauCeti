/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Localization.Module
public import TauCeti.RingTheory.Derivation.Ideal

/-!
# Derivations of a localization

Let `T` be a localization of a commutative ring `A` at a submonoid `S`, and let `N` be a
`T`-module. Every `R`-derivation `A → N` extends uniquely to an `R`-derivation `T → N`, by the
quotient rule `D (a / s) = (s • D a - a • D s) / s ^ 2`.

Uniqueness is elementary: if `t * s = a` in `T` with `s ∈ S`, the Leibniz rule gives
`s • D t = D a - t • D s`, and `s` acts invertibly on `N`. The uniqueness statement only
needs commutative semirings, left cancellative addition in `N`, and a multiplicative action of `T`.
Existence goes through Kähler differentials: `Ω[T⁄R]` is the localization of `Ω[A⁄R]` at `S`
(`KaehlerDifferential.isLocalizedModule_map`), so the `A`-linear map `Ω[A⁄R] → N` classifying a
derivation of `A` extends to a `T`-linear map `Ω[T⁄R] → N`.

These are the algebraic inputs for computing the sheaf of relative differentials of an affine
scheme on its basic open subsets.

## Main declarations

* `IsLocalization.eq_of_leibniz`: two maps `T → N` satisfying the Leibniz rule and agreeing on
  the image of `A` are equal;
* `Derivation.extendOfIsLocalization`: the extension of a derivation of `A` to `T`, with
  `Derivation.extendOfIsLocalization_algebraMap` stating that it extends.
* `Derivation.algebraMap_notMem_maximalIdeal_sq`: if `D f ∉ Q` for a prime `Q` of `A`, then the
  image of `f` in `A_Q` does not lie in the square of its maximal ideal.
-/

public section

/-- Two maps from a localization `T` of a commutative semiring `A` to a type with left
cancellative addition and a multiplicative `T`-action that satisfy the Leibniz rule are equal
once they agree on the image of `A`. In particular a derivation of `T` is determined by its
values on `A`. -/
theorem IsLocalization.eq_of_leibniz {A T N : Type*} [CommSemiring A] [CommSemiring T]
    [Algebra A T] [Add N] [IsLeftCancelAdd N] [MulAction T N]
    (S : Submonoid A) [IsLocalization S T]
    {δ₁ δ₂ : T → N} (h₁ : ∀ x y, δ₁ (x * y) = x • δ₁ y + y • δ₁ x)
    (h₂ : ∀ x y, δ₂ (x * y) = x • δ₂ y + y • δ₂ x)
    (h : ∀ a : A, δ₁ (algebraMap A T a) = δ₂ (algebraMap A T a)) : δ₁ = δ₂ := by
  funext t
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj S t
  apply (IsLocalization.map_units T s).smul_left_cancel.mp
  have hm : t • δ₁ (algebraMap A T s) + algebraMap A T s • δ₁ t =
      t • δ₂ (algebraMap A T s) + algebraMap A T s • δ₂ t := by
    rw [← h₁, ← h₂, hs, h]
  exact add_left_cancel (by simpa only [h] using hm)

namespace Derivation

variable {R A T N : Type*} [CommRing R] [CommRing A] [CommRing T] [Algebra R T] [Algebra A T]
  [AddCommGroup N] [Module T N] [Module R N] [Algebra R A] [IsScalarTower R A T] [Module A N]
  [IsScalarTower A T N] [IsScalarTower R A N]

/-- The extension of an `R`-derivation `D : A → N` to an `R`-derivation of the localization `T`
of `A` at `S`, for `N` a `T`-module. By `IsLocalization.eq_of_leibniz` it is the only derivation
of `T` agreeing with `D` on `A`. -/
noncomputable def extendOfIsLocalization (S : Submonoid A) [IsLocalization S T]
    (D : Derivation R A N) : Derivation R T N :=
  haveI : IsScalarTower R T N := .of_algebraMap_smul fun r n ↦ by
    rw [IsScalarTower.algebraMap_apply R A T, algebraMap_smul, algebraMap_smul]
  letI := isLocalizedModule_id S N T
  let f := IsLocalizedModule.lift S (KaehlerDifferential.map R R A T) D.liftKaehlerDifferential
    (IsLocalizedModule.map_units (LinearMap.id : N →ₗ[A] N))
  (f.extendScalarsOfIsLocalization S T).compDer (KaehlerDifferential.D R T)

/-- The extension of `D` to the localization `T` agrees with `D` on the image of `A`. -/
@[simp]
theorem extendOfIsLocalization_algebraMap (S : Submonoid A) [IsLocalization S T]
    (D : Derivation R A N) (a : A) :
    D.extendOfIsLocalization S (algebraMap A T a) = D a := by
  simp only [extendOfIsLocalization, coe_comp, LinearMap.comp_apply, coeFn_coe]
  rw [← KaehlerDifferential.map_D R R A T]
  -- Keep the differential in the image of `map` so the localization lift simplifies.
  simp [-KaehlerDifferential.map_D]

/-- If a derivation `D` of `A` maps `f` outside the prime ideal `Q`, then the image of `f` in the
local ring `A_Q` does not lie in the square of its maximal ideal. -/
theorem algebraMap_notMem_maximalIdeal_sq (D : Derivation R A A) {Q : Ideal A} [Q.IsPrime]
    {f : A} (hf : D f ∉ Q) :
    algebraMap A (Localization.AtPrime Q) f ∉
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) ^ 2 := by
  -- the extension of `D` to `A_Q` maps the square of the maximal ideal into the maximal ideal
  intro h
  have h' := (((Algebra.linearMap A (Localization.AtPrime Q)).compDer D).extendOfIsLocalization
    Q.primeCompl).apply_mem_smul_top_of_mem_sq h
  rw [extendOfIsLocalization_algebraMap, smul_eq_mul, Ideal.mul_top] at h'
  exact hf ((IsLocalization.AtPrime.to_map_mem_maximal_iff _ Q _).mp h')

end Derivation
