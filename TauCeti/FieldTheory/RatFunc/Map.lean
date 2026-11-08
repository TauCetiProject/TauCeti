/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Coefficient maps of rational function fields

A field isomorphism `σ : K ≃+* L` induces the isomorphism `K(X) ≃+* L(X)` applying `σ` to the
coefficients and fixing the variable `X`: the map of fraction fields induced by
`Polynomial.mapEquiv σ`. It is the field-isomorphism counterpart of Mathlib's
`RatFunc.mapRingHom`, and is how an automorphism of the constants, such as an element of an
absolute Galois group, acts on the rational function field.

## Main definitions

* `TauCeti.RatFunc.mapRingEquiv`: the coefficient map `K(X) ≃+* L(X)` of `σ : K ≃+* L`.

## Main results

* `TauCeti.RatFunc.mapRingEquiv_X` and `TauCeti.RatFunc.mapRingEquiv_C`: it fixes `X` and acts
  on the constants by `σ`.
* `TauCeti.RatFunc.coe_mapRingEquiv`: as a function it is `RatFunc.mapRingHom` of
  `Polynomial.mapRingHom σ`.
* `TauCeti.RatFunc.mapRingEquiv_refl`, `TauCeti.RatFunc.mapRingEquiv_symm` and
  `TauCeti.RatFunc.mapRingEquiv_trans`: it is functorial in `σ`.
* `TauCeti.apply_algebraMap_eq_of_mapRingEquiv` and `TauCeti.finrank_eq_of_mapRingEquiv`: an
  isomorphism `F ≃+* F'` of extensions carrying `K(X)` onto `L(X)` by the coefficient map of `σ`
  carries `K` onto `L` along `σ`, and the two extensions have the same degree.
* `TauCeti.algebraMap_ratFunc_algebraMap_polynomial`: a `K`-algebra map `K(X) → L(X)` sending `X`
  to `X` maps a polynomial over `K` to the polynomial with its coefficients mapped to `L`.
* `RatFunc.mapRingEquiv_algebraMap_ratFunc`: for such an algebra map from `K(X)` to `L(X)`, the
  coefficient map of an automorphism of `L` fixing the image of `K` fixes the image of `K(X)`.
-/

public section

namespace TauCeti.RatFunc

open _root_.RatFunc
open scoped Polynomial

variable {K L M : Type*} [Field K] [Field L] [Field M]

/-- The isomorphism `K(X) ≃+* L(X)` induced by a field isomorphism `σ : K ≃+* L`, applying `σ` to
the coefficients and fixing `X`. -/
noncomputable def mapRingEquiv (σ : K ≃+* L) : RatFunc K ≃+* RatFunc L :=
  IsFractionRing.ringEquivOfRingEquiv (Polynomial.mapEquiv σ)

variable (σ : K ≃+* L)

/-- On polynomials, the coefficient map of `σ` is `Polynomial.map σ`. -/
@[simp]
theorem mapRingEquiv_algebraMap (p : K[X]) :
    mapRingEquiv σ (algebraMap K[X] (RatFunc K) p) = algebraMap L[X] (RatFunc L) (p.map σ) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ p

/-- The coefficient map of `σ` is Mathlib's `RatFunc.mapRingHom` of `Polynomial.mapRingHom σ`. -/
theorem coe_mapRingEquiv : ⇑(mapRingEquiv σ) = mapRingHom (Polynomial.mapRingHom (σ : K →+* L))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ σ.injective)) := by
  funext f
  induction f using RatFunc.induction_on with
  | f p q _ =>
    rw [coe_mapRingHom_eq_coe_map, map_apply_div, map_div₀, mapRingEquiv_algebraMap,
      mapRingEquiv_algebraMap, Polynomial.coe_mapRingHom]

/-- The coefficient map fixes the variable. -/
@[simp]
theorem mapRingEquiv_X : mapRingEquiv σ X = X := by
  rw [← algebraMap_X, mapRingEquiv_algebraMap, Polynomial.map_X, algebraMap_X]

/-- The coefficient map acts on the constants by `σ`. -/
@[simp]
theorem mapRingEquiv_C (c : K) : mapRingEquiv σ (C c) = C (σ c) := by
  rw [← algebraMap_C, mapRingEquiv_algebraMap, Polynomial.map_C, RingHom.coe_coe, algebraMap_C]

/-- The coefficient map carries the image of `K` in `K(X)` onto the image of `L` along `σ`. -/
theorem mapRingEquiv_algebraMap_const (c : K) :
    mapRingEquiv σ (algebraMap K (RatFunc K) c) = algebraMap L (RatFunc L) (σ c) := by
  rw [algebraMap_eq_C, algebraMap_eq_C, mapRingEquiv_C]

/-- The coefficient map of the identity is the identity. -/
@[simp]
theorem mapRingEquiv_refl : mapRingEquiv (RingEquiv.refl K) = RingEquiv.refl (RatFunc K) := by
  have h : Polynomial.mapEquiv (RingEquiv.refl K) = RingEquiv.refl K[X] :=
    RingEquiv.ext fun _ ↦ Polynomial.map_id
  rw [mapRingEquiv, h, IsFractionRing.ringEquivOfRingEquiv_refl]

/-- The inverse of the coefficient map of `σ` is the coefficient map of `σ⁻¹`. -/
@[simp]
theorem mapRingEquiv_symm : (mapRingEquiv σ).symm = mapRingEquiv σ.symm := by
  have h : (Polynomial.mapEquiv σ).symm = Polynomial.mapEquiv σ.symm := RingEquiv.ext fun _ ↦ rfl
  rw [mapRingEquiv, mapRingEquiv, IsFractionRing.ringEquivOfRingEquiv_symm, h]

/-- The coefficient map of a composite is the composite of the coefficient maps. -/
theorem mapRingEquiv_trans (τ : L ≃+* M) :
    mapRingEquiv (σ.trans τ) = (mapRingEquiv σ).trans (mapRingEquiv τ) := by
  have h : Polynomial.mapEquiv (σ.trans τ) =
      (Polynomial.mapEquiv σ).trans (Polynomial.mapEquiv τ) :=
    RingEquiv.ext fun p ↦ by simp [Polynomial.map_map]
  rw [mapRingEquiv, mapRingEquiv, mapRingEquiv, h,
    IsFractionRing.ringEquivOfRingEquiv_comp (RatFunc K) (RatFunc L) (RatFunc M)]

/-- An algebra map between rational function fields that preserves the given map on constants
is compatible with the coefficient-field scalar tower. -/
theorem isScalarTower_of_algebraMap_C {F K : Type*} [Field F] [Field K] [Algebra F K]
    [Algebra (RatFunc F) (RatFunc K)]
    (hC : ∀ c : F, algebraMap (RatFunc F) (RatFunc K) (C c) = C (algebraMap F K c)) :
    IsScalarTower F (RatFunc F) (RatFunc K) := by
  -- At generic F and K, typeclass synthesis uses coefficient rather than subtype algebras.
  apply IsScalarTower.of_algebraMap_eq
  intro c
  rw [IsScalarTower.algebraMap_apply F K (RatFunc K), algebraMap_eq_C, algebraMap_eq_C, hC]

end TauCeti.RatFunc

namespace TauCeti

section Extension

variable {K L F F' : Type*} [Field K] [Field L] [Field F] [Field F']
  [Algebra (RatFunc K) F] [Algebra (RatFunc L) F']
  (σ : K ≃+* L) (τ : F ≃+* F')
  (hτ : ∀ x, τ (algebraMap (RatFunc K) F x) =
    algebraMap (RatFunc L) F' (RatFunc.mapRingEquiv σ x))

include hτ

/-- An isomorphism `τ : F ≃+* F'` carrying `K(X)` onto `L(X)` by the coefficient map of `σ`
carries the constants `K` onto `L` along `σ`. -/
theorem apply_algebraMap_eq_of_mapRingEquiv [Algebra K F] [Algebra L F']
    [IsScalarTower K (RatFunc K) F] [IsScalarTower L (RatFunc L) F'] (c : K) :
    τ (algebraMap K F c) = algebraMap L F' (σ c) := by
  rw [IsScalarTower.algebraMap_apply K (RatFunc K) F, hτ,
    RatFunc.mapRingEquiv_algebraMap_const, ← IsScalarTower.algebraMap_apply]

/-- An isomorphism `τ : F ≃+* F'` carrying `K(X)` onto `L(X)` by the coefficient map of `σ`
preserves the degree: the degrees of `F` and `F'` over the rational function fields agree. -/
theorem finrank_eq_of_mapRingEquiv :
    Module.finrank (RatFunc L) F' = Module.finrank (RatFunc K) F :=
  (Algebra.finrank_eq_of_equiv_equiv (RatFunc.mapRingEquiv σ) τ
    (RingHom.ext fun x ↦ (hτ x).symm)).symm

end Extension

section Polynomial

open scoped Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra (RatFunc K) (RatFunc L)]
  [IsScalarTower K (RatFunc K) (RatFunc L)]

/-- A `K`-algebra map `K(X) → L(X)` sending `X` to `X` maps a polynomial over `K` to the same
polynomial with its coefficients read in `L`. -/
theorem algebraMap_ratFunc_algebraMap_polynomial
    (hX : algebraMap (RatFunc K) (RatFunc L) RatFunc.X = RatFunc.X) (f : K[X]) :
    algebraMap (RatFunc K) (RatFunc L) (algebraMap K[X] (RatFunc K) f) =
      algebraMap L[X] (RatFunc L) (f.map (algebraMap K L)) := by
  rw [← RatFunc.aeval_X_left_eq_algebraMap, ← Polynomial.aeval_algebraMap_apply, hX,
    ← RatFunc.aeval_X_left_eq_algebraMap, Polynomial.aeval_map_algebraMap]

end Polynomial

end TauCeti

namespace RatFunc

open TauCeti.RatFunc
open scoped Polynomial

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Algebra (RatFunc F) (RatFunc K)]
  [IsScalarTower F (RatFunc F) (RatFunc K)]

/-- A coefficient automorphism of `K(X)` whose automorphism `σ` of `K` fixes the image of `F`
fixes the image of `F(X)`, for any `F`-algebra map `F(X) → K(X)` sending `X` to `X`. -/
theorem mapRingEquiv_algebraMap_ratFunc
    (hX : algebraMap (RatFunc F) (RatFunc K) RatFunc.X = RatFunc.X)
    {σ : K ≃+* K} (hσ : ∀ c : F, σ (algebraMap F K c) = algebraMap F K c) (w : RatFunc F) :
    mapRingEquiv σ (algebraMap (RatFunc F) (RatFunc K) w) =
      algebraMap (RatFunc F) (RatFunc K) w := by
  have h : (mapRingEquiv σ : RatFunc K →+* RatFunc K).comp
      (algebraMap (RatFunc F) (RatFunc K)) = algebraMap (RatFunc F) (RatFunc K) := by
    refine IsFractionRing.ringHom_ext (A := F[X]) fun p ↦ ?_
    have hp : (p.map (algebraMap F K)).map (σ : K →+* K) = p.map (algebraMap F K) := by
      ext n
      simp [hσ]
    rw [RingHom.comp_apply, RingHom.coe_coe, TauCeti.algebraMap_ratFunc_algebraMap_polynomial hX,
      mapRingEquiv_algebraMap, hp]
  exact congr($h w)

end RatFunc
