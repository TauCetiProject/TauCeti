/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Kaehler.MapSemilinear
public import TauCeti.RingTheory.LaurentSeries.Derivative
public import TauCeti.RingTheory.LaurentSeries.Substitution.Basic

/-!
# Kähler differentials under Laurent expansion

Let `e : F →ₐ[k] C⸨X⸩` be a `k`-algebra map from a commutative `k`-algebra `F` into Laurent series
over a commutative `k`-algebra `C`, for instance the Laurent expansion of the functions of a curve
at a place in a chosen uniformizer. The formal derivative `z ↦ (e z)'` is a `k`-derivation of `F`,
so by the universal property of Kähler differentials it factors through `d : F → Ω[F⁄k]`. In
particular every relation `dz = c dt` in `Ω[F⁄k]` becomes the identity `(e z)' = e c · (e t)'` of
Laurent series.

If `e` sends `t` to the variable `X`, then `(e t)' = 1`, so `dt ≠ 0`. This is how a Laurent
expansion certifies that `dt ≠ 0`; when `Ω[F⁄k]` is one-dimensional (for instance when a function
field `F / k` is separably generated), this makes `t` separating.

Lifting this derivation packages the factorization as the `k`-linear map
`AlgHom.differentialLaurentExpansion e : Ω[F⁄k] →ₗ[k] C⸨X⸩` sending `a df` to `(e a) * (e f)'`.
When `C` is a field and `q : C⟦X⟧` is a nonzero power series with zero constant coefficient, a
commuting square `e₁ ∘ f = substAlgHom q ∘ e₂` satisfies the Laurent chain rule
`TauCeti.differentialLaurentExpansion_mapSemilinear`.

## Main definitions

* `AlgHom.differentialLaurentExpansion`: the `k`-linear differential Laurent expansion
  `Ω[F⁄k] →ₗ[k] C⸨X⸩` induced by an algebra map `e : F →ₐ[k] C⸨X⸩`.

## Main results

* `AlgHom.differentialLaurentExpansion_D` and `AlgHom.differentialLaurentExpansion_smul`:
  compatibility of `AlgHom.differentialLaurentExpansion` with `D` and scalar multiplication.
* `TauCeti.differentialLaurentExpansion_mapSemilinear`: the Laurent chain rule for a commuting
  square of algebra maps with Laurent substitution by a nonzero power series `q` with zero constant
  coefficient.
* `TauCeti.derivative_algHom_eq_mul_of_D_eq_smul`: `dz = c dt` implies `(e z)' = e c · (e t)'`.
* `TauCeti.D_ne_zero_of_algHom_laurentSeries`: if `e t = X` and the coefficient ring `A` is
  nontrivial, then `dt ≠ 0` in `Ω[F⁄k]`.
-/

public section

open KaehlerDifferential
open scoped LaurentSeries PowerSeries

namespace AlgHom

private theorem isScalarTower_toAlgebra {k F C : Type*} [CommRing k] [CommRing F]
    [Algebra k F] [CommRing C] [Algebra k C] (e : F →ₐ[k] C⸨X⸩) :
    let _ : Algebra F C⸨X⸩ := e.toRingHom.toAlgebra
    IsScalarTower k F C⸨X⸩ :=
  -- Introduce the induced `F`-algebra structure on `C⸨X⸩` so `liftKaehlerDifferential` applies.
  let _ : Algebra F C⸨X⸩ := e.toRingHom.toAlgebra
  ⟨fun a z f ↦ by
    -- The `k`-module structure on `C⸨X⸩` found by instance search is coefficientwise.
    have hek : e (a • z) = a • e z := by
      rw [Algebra.smul_def, map_mul, AlgHom.commutes, TauCeti.laurentSeries_algebraMap_mul_eq_smul]
    -- The induced algebra acts by multiplication with the expansion of the scalar.
    rw [Algebra.smul_def (A := C⸨X⸩) (a • z), Algebra.smul_def (A := C⸨X⸩) z,
      RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hek,
      ← TauCeti.laurentSeries_algebraMap_mul_eq_smul,
      ← TauCeti.laurentSeries_algebraMap_mul_eq_smul, mul_assoc]⟩

private noncomputable def laurentDerivation {k F C : Type*} [CommRing k] [CommRing F]
    [Algebra k F] [CommRing C] [Algebra k C] (e : F →ₐ[k] C⸨X⸩) :
    let _ : Algebra F C⸨X⸩ := e.toRingHom.toAlgebra
    Derivation k F C⸨X⸩ :=
  -- Equip `C⸨X⸩` with the `F`-algebra structure induced by `e` to restrict
  -- `laurentSeriesDerivation C` along `e`.
  let _ : Algebra F C⸨X⸩ := e.toRingHom.toAlgebra
  have _ := isScalarTower_toAlgebra e
  -- `laurentSeriesDerivation C` uses `Algebra.toSMul` on `C⸨X⸩`, while `restrictScalars k`
  -- uses the coefficientwise `k`-action; both `IsScalarTower k C C⸨X⸩` instances are needed
  -- and follow because both actions factor through `C`.
  have _ : @IsScalarTower k C C⸨X⸩ Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    .of_algebraMap_eq fun a ↦ by
      simp only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
        IsScalarTower.algebraMap_apply k C C⟦X⟧]
  have _ : IsScalarTower k C C⸨X⸩ := ⟨fun a b f ↦ by
    ext n
    simp only [HahnSeries.coeff_smul, Algebra.smul_def, Algebra.algebraMap_self,
      RingHom.id_apply, mul_assoc]⟩
  ((TauCeti.laurentSeriesDerivation C).restrictScalars k).compAlgebraMap F

/-- **Laurent expansion of Kähler differentials along an algebra map `e : F →ₐ[k] C⸨X⸩`**:
lifting the `k`-derivation `f ↦ (e f)'` through `Ω[F⁄k]` sends `a db` to `e a * (e b)'` in
`C⸨X⸩`. -/
noncomputable def differentialLaurentExpansion {k F C : Type*} [CommRing k] [CommRing F]
    [Algebra k F] [CommRing C] [Algebra k C] (e : F →ₐ[k] C⸨X⸩) : Ω[F⁄k] →ₗ[k] C⸨X⸩ :=
  let _ : Algebra F C⸨X⸩ := e.toRingHom.toAlgebra
  have _ := isScalarTower_toAlgebra e
  (laurentDerivation e).liftKaehlerDifferential.restrictScalars k

/-- **The differential `d a` expands to the formal derivative of `e a`.** -/
@[simp]
theorem differentialLaurentExpansion_D {k F C : Type*} [CommRing k] [CommRing F]
    [Algebra k F] [CommRing C] [Algebra k C] (e : F →ₐ[k] C⸨X⸩) (a : F) :
    e.differentialLaurentExpansion (D k F a) = _root_.LaurentSeries.derivative C (e a) := by
  let _ : Algebra F C⸨X⸩ := e.toRingHom.toAlgebra
  have _ := isScalarTower_toAlgebra e
  rw [differentialLaurentExpansion, LinearMap.restrictScalars_apply,
    Derivation.liftKaehlerDifferential_comp_D, laurentDerivation, Derivation.compAlgebraMap_apply,
    Derivation.restrictScalars_apply, TauCeti.laurentSeriesDerivation_apply,
    RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- **Scalar multiplication by `a` becomes multiplication by `e a`.** -/
@[simp]
theorem differentialLaurentExpansion_smul {k F C : Type*} [CommRing k] [CommRing F]
    [Algebra k F] [CommRing C] [Algebra k C] (e : F →ₐ[k] C⸨X⸩) (a : F) (η : Ω[F⁄k]) :
    e.differentialLaurentExpansion (a • η) = e a * e.differentialLaurentExpansion η := by
  let _ : Algebra F C⸨X⸩ := e.toRingHom.toAlgebra
  have _ := isScalarTower_toAlgebra e
  exact LinearMap.map_smul ((laurentDerivation e).liftKaehlerDifferential) a η

end AlgHom

namespace TauCeti

/-- **Laurent chain rule for a commuting square with Laurent substitution**: if `q : C⟦X⟧` is a
nonzero power series with zero constant coefficient and `e₁ (f b) = substAlgHom q (e₂ b)` for
all `b : B`, then `e₁.differentialLaurentExpansion` on the pullback of `η : Ω[B⁄k]` substitutes `q`
into `e₂.differentialLaurentExpansion η` and multiplies by `q'`. -/
theorem differentialLaurentExpansion_mapSemilinear
    {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [Field C] [Algebra k C]
    {e₁ : A →ₐ[k] C⸨X⸩} {e₂ : B →ₐ[k] C⸨X⸩} {f : B →ₐ[k] A}
    {q : C⟦X⟧} (hq₀ : PowerSeries.constantCoeff q = 0) (hq : q ≠ 0)
    (hsq : ∀ b : B, e₁ (f b) = LaurentSeries.substAlgHom hq₀ hq (e₂ b)) (η : Ω[B⁄k]) :
    e₁.differentialLaurentExpansion (KaehlerDifferential.mapSemilinear f η) =
      LaurentSeries.substAlgHom hq₀ hq (e₂.differentialLaurentExpansion η) *
        _root_.LaurentSeries.derivative C (q : C⸨X⸩) := by
  induction (KaehlerDifferential.span_range_derivation k B ▸ Submodule.mem_top :
      η ∈ Submodule.span B (Set.range (D k B))) using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨b, rfl⟩ := h
    rw [KaehlerDifferential.mapSemilinear_D, AlgHom.differentialLaurentExpansion_D,
      AlgHom.differentialLaurentExpansion_D, hsq b, LaurentSeries.derivative_substAlgHom]
  | zero => rw [map_zero, map_zero, map_zero, map_zero, zero_mul]
  | add _ _ _ _ ih₁ ih₂ => rw [map_add, map_add, map_add, map_add, ih₁, ih₂, add_mul]
  | smul b _ _ ih =>
    rw [KaehlerDifferential.mapSemilinear_smul, AlgHom.differentialLaurentExpansion_smul,
      AlgHom.differentialLaurentExpansion_smul, map_mul, hsq b, ih, mul_assoc]

/-- **Relations between differentials survive Laurent expansion.** Let `e : F → A((X))` be a
`k`-algebra map into Laurent series over a `k`-algebra `A`. If `dz = c dt` in `Ω[F⁄k]`, then the
formal derivatives of the expansions satisfy `(e z)' = e c · (e t)'`: the derivation `z ↦ (e z)'`
factors through the universal derivation `d`. -/
theorem derivative_algHom_eq_mul_of_D_eq_smul {k F A : Type*} [CommRing k] [CommRing F]
    [Algebra k F] [CommRing A] [Algebra k A] {e : F →ₐ[k] LaurentSeries A} {z c t : F}
    (h : D k F z = c • D k F t) :
    LaurentSeries.derivative A (e z) = e c * LaurentSeries.derivative A (e t) := by
  have h' := congrArg e.differentialLaurentExpansion h
  simpa using h'

/-- **A Laurent variable has a nonzero differential.** If a `k`-algebra map `e : F → A((X))` into
Laurent series over a nontrivial `k`-algebra `A` sends `t` to the variable `X`, then `dt ≠ 0` in
`Ω[F⁄k]`: the derivation `z ↦ (e z)'` takes the value `1` at `t`. -/
theorem D_ne_zero_of_algHom_laurentSeries {k F A : Type*} [CommRing k] [CommRing F]
    [Algebra k F] [CommRing A] [Nontrivial A] [Algebra k A] {e : F →ₐ[k] LaurentSeries A} {t : F}
    (he : e t = HahnSeries.single 1 1) : D k F t ≠ 0 := fun h ↦ by
  have h' := congrArg e.differentialLaurentExpansion h
  simp [he] at h'

end TauCeti
