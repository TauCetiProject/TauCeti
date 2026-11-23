/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Basic

/-!
# Kähler differentials under Laurent expansion

Let `e : F → A((X))` be a `k`-algebra map from a commutative `k`-algebra `F` into Laurent series
over a commutative `k`-algebra `A`, for instance the Laurent expansion of the functions of a curve
at a place in a chosen uniformizer. The formal derivative `z ↦ (e z)'` is a `k`-derivation of `F`,
so by the universal property of Kähler differentials it factors through `d : F → Ω[F⁄k]`. In
particular every relation `dz = c dt` in `Ω[F⁄k]` becomes the identity `(e z)' = e c · (e t)'` of
Laurent series.

If `e` sends `t` to the variable `X`, then `(e t)' = 1`, so `dt ≠ 0`. This is how a Laurent
expansion certifies that `dt ≠ 0`; when `Ω[F⁄k]` is one-dimensional (for instance when a function
field `F / k` is separably generated), this makes `t` separating.

When `A = k`, contracting `KaehlerDifferential.mapSemilinear e` with `laurentSeriesDerivation k`
packages this factorization as the `k`-linear map
`TauCeti.differentialLaurentExpansion e : Ω[F⁄k] →ₗ[k] k⸨X⸩` sending `a df` to `(e a) * (e f)'`.
Over a field `K`, a commuting square `e₁ ∘ f = substAlgHom q ∘ e₂` satisfies the Laurent chain
rule `differentialLaurentExpansion_mapSemilinear`.

## Main definitions

* `TauCeti.differentialLaurentExpansion`: the `k`-linear differential Laurent expansion
  `Ω[A⁄k] →ₗ[k] k⸨X⸩` induced by an algebra map `e : A →ₐ[k] k⸨X⸩`.

## Main results

* `TauCeti.derivative_algHom_eq_mul_of_D_eq_smul`: `dz = c dt` implies `(e z)' = e c · (e t)'`.
* `TauCeti.D_ne_zero_of_algHom_laurentSeries`: if `e t = X` and `A` is nontrivial, then
  `dt ≠ 0` in `Ω[F⁄k]`.
* `TauCeti.differentialLaurentExpansion_D` and `TauCeti.differentialLaurentExpansion_smul`:
  compatibility of `differentialLaurentExpansion` with `D` and scalar multiplication.
* `TauCeti.differentialLaurentExpansion_mapSemilinear`: the Laurent chain rule for a commuting
  square of algebra maps with Laurent substitution.
-/

public section

open KaehlerDifferential
open scoped LaurentSeries PowerSeries

namespace TauCeti

/-- **Laurent expansion of Kähler differentials along an algebra map `e : A →ₐ[k] k⸨X⸩`**:
pushing `Ω[A⁄k]` forward along `e` and contracting with `laurentSeriesDerivation k` sends
`a db` to `e a * (e b)'` in `k⸨X⸩`. -/
noncomputable def differentialLaurentExpansion {k A : Type*} [CommRing k] [CommRing A]
    [Algebra k A] (e : A →ₐ[k] k⸨X⸩) : Ω[A⁄k] →ₗ[k] k⸨X⸩ where
  toFun η := (laurentSeriesDerivation k).liftKaehlerDifferential
    (KaehlerDifferential.mapSemilinear e η)
  map_add' η₁ η₂ := by rw [map_add, map_add]
  map_smul' c η := by
    rw [RingHom.id_apply, ← algebraMap_smul A c η,
      KaehlerDifferential.mapSemilinear_smul, AlgHom.commutes, LinearMap.map_smul,
      smul_eq_mul, laurentSeries_algebraMap_mul_eq_smul]

/-- `differentialLaurentExpansion` lifts `laurentSeriesDerivation` along `e`. -/
theorem differentialLaurentExpansion_apply {k A : Type*} [CommRing k] [CommRing A]
    [Algebra k A] (e : A →ₐ[k] k⸨X⸩) (η : Ω[A⁄k]) :
    differentialLaurentExpansion e η =
      (laurentSeriesDerivation k).liftKaehlerDifferential
        (KaehlerDifferential.mapSemilinear e η) :=
  (rfl)

/-- **The differential `d a` expands to the formal derivative of `e a`.** -/
@[simp]
theorem differentialLaurentExpansion_D {k A : Type*} [CommRing k] [CommRing A]
    [Algebra k A] (e : A →ₐ[k] k⸨X⸩) (a : A) :
    differentialLaurentExpansion e (D k A a) = _root_.LaurentSeries.derivative k (e a) := by
  rw [differentialLaurentExpansion_apply, KaehlerDifferential.mapSemilinear_D,
    Derivation.liftKaehlerDifferential_comp_D, laurentSeriesDerivation_apply]

/-- **Scalar multiplication by `a` becomes multiplication by `e a`.** -/
@[simp]
theorem differentialLaurentExpansion_smul {k A : Type*} [CommRing k] [CommRing A]
    [Algebra k A] (e : A →ₐ[k] k⸨X⸩) (a : A) (η : Ω[A⁄k]) :
    differentialLaurentExpansion e (a • η) = e a * differentialLaurentExpansion e η := by
  rw [differentialLaurentExpansion_apply, KaehlerDifferential.mapSemilinear_smul,
    LinearMap.map_smul, smul_eq_mul, ← differentialLaurentExpansion_apply]

/-- **Laurent chain rule for a commuting square with Laurent substitution**: if `e₁ (f b) =
substAlgHom q (e₂ b)` for all `b : B`, then `differentialLaurentExpansion e₁` on the pullback
of `η : Ω[B⁄K]` substitutes `q` into `differentialLaurentExpansion e₂ η` and multiplies by `q'`. -/
theorem differentialLaurentExpansion_mapSemilinear
    {K A B : Type*} [Field K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    {e₁ : A →ₐ[K] K⸨X⸩} {e₂ : B →ₐ[K] K⸨X⸩} {f : B →ₐ[K] A}
    {q : K⟦X⟧} (hq₀ : PowerSeries.constantCoeff q = 0) (hq : q ≠ 0)
    (hsq : ∀ b : B, e₁ (f b) = LaurentSeries.substAlgHom hq₀ hq (e₂ b)) (η : Ω[B⁄K]) :
    differentialLaurentExpansion e₁ (KaehlerDifferential.mapSemilinear f η) =
      LaurentSeries.substAlgHom hq₀ hq (differentialLaurentExpansion e₂ η) *
        _root_.LaurentSeries.derivative K (q : K⸨X⸩) := by
  have hcomp : e₁.comp f = (LaurentSeries.substAlgHom hq₀ hq).comp e₂ := AlgHom.ext hsq
  rw [differentialLaurentExpansion_apply, ← ContinuousKaehlerDifferential.equivLaurentSeries_mk,
    ← KaehlerDifferential.mapSemilinear_comp_apply, hcomp,
    KaehlerDifferential.mapSemilinear_comp_apply, ← ContinuousKaehlerDifferential.subst_mk hq₀ hq,
    ContinuousKaehlerDifferential.equivLaurentSeries_subst,
    ContinuousKaehlerDifferential.equivLaurentSeries_mk, ← differentialLaurentExpansion_apply]

/-- **Relations between differentials survive Laurent expansion.** Let `e : F → A((X))` be a
`k`-algebra map into Laurent series over a `k`-algebra `A`. If `dz = c dt` in `Ω[F⁄k]`, then the
formal derivatives of the expansions satisfy `(e z)' = e c · (e t)'`: the derivation `z ↦ (e z)'`
factors through the universal derivation `d`. -/
theorem derivative_algHom_eq_mul_of_D_eq_smul {k F A : Type*} [CommRing k] [CommRing F]
    [Algebra k F] [CommRing A] [Algebra k A] {e : F →ₐ[k] LaurentSeries A} {z c t : F}
    (h : D k F z = c • D k F t) :
    LaurentSeries.derivative A (e z) = e c * LaurentSeries.derivative A (e t) := by
  -- Give `A((X))` the `F`-algebra structure induced by the expansion map.
  let _ : Algebra F (LaurentSeries A) := e.toRingHom.toAlgebra
  -- The `k`-module structure on `A((X))` found by instance search is the coefficientwise one.
  have hek (a : k) (z : F) : e (a • z) = a • e z := by
    rw [Algebra.smul_def, map_mul, AlgHom.commutes, laurentSeries_algebraMap_mul_eq_smul]
  have _ : IsScalarTower k F (LaurentSeries A) := ⟨fun a z f ↦ by
    -- The induced algebra acts by multiplication with the expansion of the scalar.
    rw [Algebra.smul_def (A := LaurentSeries A) (a • z), Algebra.smul_def (A := LaurentSeries A) z,
      RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hek,
      ← laurentSeries_algebraMap_mul_eq_smul, ← laurentSeries_algebraMap_mul_eq_smul, mul_assoc]⟩
  -- The source of the Laurent derivation uses algebra scalars, while its target uses
  -- coefficientwise scalars. Both actions factor through `A`, giving scalar compatibility.
  have _ : @IsScalarTower k A (LaurentSeries A)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    .of_algebraMap_eq fun a ↦ by
      simp only [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
  have _ : IsScalarTower k A (LaurentSeries A) := ⟨fun a b f ↦ by
    ext n
    simp only [HahnSeries.coeff_smul, Algebra.smul_def, Algebra.algebraMap_self,
      RingHom.id_apply, mul_assoc]⟩
  let D' : Derivation k F (LaurentSeries A) :=
    ((laurentSeriesDerivation A).restrictScalars k).compAlgebraMap F
  -- `D'` factors through `d`, so it inherits the relation `dz = c dt`.
  have h' : D' z = c • D' t := by
    rw [← D'.liftKaehlerDifferential_comp_D, h, LinearMap.map_smul,
      D'.liftKaehlerDifferential_comp_D]
  simp only [D', Derivation.compAlgebraMap_apply, Derivation.restrictScalars_apply,
    laurentSeriesDerivation_apply, Algebra.smul_def] at h'
  -- The scalar action of the induced algebra is multiplication by the expansion.
  rwa [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h'

/-- **A Laurent variable has a nonzero differential.** If a `k`-algebra map `e : F → A((X))` into
Laurent series over a nontrivial `k`-algebra `A` sends `t` to the variable `X`, then `dt ≠ 0` in
`Ω[F⁄k]`: the derivation `z ↦ (e z)'` takes the value `1` at `t`. -/
theorem D_ne_zero_of_algHom_laurentSeries {k F A : Type*} [CommRing k] [CommRing F]
    [Algebra k F] [CommRing A] [Nontrivial A] [Algebra k A] {e : F →ₐ[k] LaurentSeries A} {t : F}
    (he : e t = HahnSeries.single 1 1) : D k F t ≠ 0 := fun h ↦ by
  simpa [he] using
    derivative_algHom_eq_mul_of_D_eq_smul (e := e) (z := t) (c := 0) (t := t) (by simp [h])

end TauCeti
