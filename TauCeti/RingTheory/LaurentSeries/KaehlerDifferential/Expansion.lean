/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import TauCeti.RingTheory.LaurentSeries.Derivative

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

## Main results

* `TauCeti.derivative_algHom_eq_mul_of_D_eq_smul`: `dz = c dt` implies `(e z)' = e c · (e t)'`.
* `TauCeti.D_ne_zero_of_algHom_laurentSeries`: if `e t = X` and `A` is nontrivial, then
  `dt ≠ 0` in `Ω[F⁄k]`.
-/

public section

open KaehlerDifferential

namespace TauCeti

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
