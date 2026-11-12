/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.Rescale
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic

/-!
# Rescaling restricted power series

Multiplying each variable by a multiplicative unit identifies restricted-series algebras at
the correspondingly rescaled polyradii. More precisely, if `u i` is a multiplicative unit and
`‖u i‖ * s i = r i`, then substitution `X i ↦ u i * X i` is an isometric algebra equivalence
from the algebra at polyradius `r` to the algebra at polyradius `s`. Its inverse substitutes
the inverse units.

The construction works at arbitrary positive real polyradii, including radii that are not norms
of scalars. It uses Mathlib's coefficientwise `MvPowerSeries.rescale`, so its coefficient formula
and compatibility with constants are inherited without introducing another series carrier.
The algebra equivalence does not require positive weights; positivity is needed only for the
Gauss-norm statements.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {σ R : Type*} [NormedCommRing R] {r s : σ → ℝ}

section Equiv

variable [IsUltrametricDist R]

/-- Rescale restricted series by multiplicative units, from radii `r` to radii `s` satisfying
`‖u i‖ * s i = r i`. -/
private noncomputable def restrictedRescaleAlgHom (u : σ → R)
    (hu : ∀ i, IsNormMulUnit (u i)) (hrs : ∀ i, ‖u i‖ * s i = r i) :
    IsRestricted.subring (R := R) r →ₐ[R] IsRestricted.subring (R := R) s where
  toFun f := ⟨MvPowerSeries.rescale u f, (isRestricted_rescale_iff u hu hrs f).mpr f.2⟩
  map_one' := Subtype.ext (map_one (MvPowerSeries.rescale u))
  map_mul' f g := Subtype.ext (map_mul (MvPowerSeries.rescale u) (f : MvPowerSeries σ R) g)
  map_zero' := Subtype.ext (map_zero (MvPowerSeries.rescale u))
  map_add' f g := Subtype.ext (map_add (MvPowerSeries.rescale u) (f : MvPowerSeries σ R) g)
  commutes' a := Subtype.ext <| by
    simpa only [MvPowerSeries.rescaleAlgHom_apply, coe_algebraMap_isRestrictedSubring,
      MvPowerSeries.c_eq_algebraMap] using (MvPowerSeries.rescaleAlgHom u).commutes a

/-- The underlying formal series of `restrictedRescaleAlgHom` is Mathlib's rescaling. -/
@[simp]
private theorem coe_restrictedRescaleAlgHom (u : σ → R) (hu : ∀ i, IsNormMulUnit (u i))
    (hrs : ∀ i, ‖u i‖ * s i = r i) (f : IsRestricted.subring (R := R) r) :
    (restrictedRescaleAlgHom u hu hrs f : MvPowerSeries σ R) = MvPowerSeries.rescale u f := by
  rfl

/-- The change of weights obtained by substituting `X i ↦ u i * X i`, where each `u i` is a
multiplicative unit and `‖u i‖ * s i = r i`. The inverse substitutes `u i⁻¹`. For positive
polyradii, this equivalence is an isometry. -/
noncomputable def restrictedRescaleEquiv (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i) :
    IsRestricted.subring (R := R) r ≃ₐ[R] IsRestricted.subring (R := R) s :=
  { restrictedRescaleAlgHom (fun i ↦ (u i : R)) hu hrs with
    invFun f := ⟨MvPowerSeries.rescale (fun i ↦ (((u i)⁻¹ : Rˣ) : R)) f,
      (isRestricted_rescale_iff (fun i ↦ (u i : R)) hu hrs _).mp <| by
        have hcancel := rescale_inv_rescale (fun i ↦ (u i)⁻¹) (f : MvPowerSeries σ R)
        simp only [inv_inv] at hcancel
        exact hcancel.symm ▸ f.2⟩
    left_inv f := Subtype.ext (rescale_inv_rescale u f)
    right_inv f := Subtype.ext <| by
      simpa using rescale_inv_rescale (fun i ↦ (u i)⁻¹) (f : MvPowerSeries σ R) }

/-- The rescaling equivalence acts by Mathlib's rescaling on the underlying formal series. -/
@[simp]
theorem coe_restrictedRescaleEquiv (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i)
    (f : IsRestricted.subring (R := R) r) :
    (restrictedRescaleEquiv u hu hrs f : MvPowerSeries σ R) =
      MvPowerSeries.rescale (fun i ↦ (u i : R)) f := by
  rfl

/-- The inverse rescaling equivalence substitutes the inverse units. -/
@[simp]
theorem coe_restrictedRescaleEquiv_symm (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i)
    (f : IsRestricted.subring (R := R) s) :
    ((restrictedRescaleEquiv u hu hrs).symm f : MvPowerSeries σ R) =
      MvPowerSeries.rescale (fun i ↦ (((u i)⁻¹ : Rˣ) : R)) f := by
  rfl

/-- The rescaling equivalence sends `X i` to `u i * X i`. -/
@[simp]
theorem restrictedRescaleEquiv_X (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i) (i : σ) :
    restrictedRescaleEquiv u hu hrs
        (⟨MvPowerSeries.X i, isRestricted_X r i⟩ : IsRestricted.subring (R := R) r) =
      algebraMap R (IsRestricted.subring (R := R) s) (u i : R) *
        (⟨MvPowerSeries.X i, isRestricted_X s i⟩ : IsRestricted.subring (R := R) s) := by
  classical
  apply Subtype.ext
  ext n
  rw [coe_restrictedRescaleEquiv, Subring.coe_mul, coe_algebraMap_isRestrictedSubring,
    coeff_rescale, coeff_C_mul, coeff_X]
  split_ifs with hn
  · simp [hn]
  · simp

variable [∀ i, Fact (0 < r i)] [∀ i, Fact (0 < s i)]

/-- The rescaling equivalence preserves the Gauss norm. -/
@[simp]
theorem norm_restrictedRescaleEquiv (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i)
    (f : IsRestricted.subring (R := R) r) :
    ‖restrictedRescaleEquiv u hu hrs f‖ = ‖f‖ := by
  rw [norm_eq_gaussNorm, norm_eq_gaussNorm, gaussNorm]
  congr 1
  funext n
  rw [coe_restrictedRescaleEquiv]
  exact norm_coeff_rescale_mul_prod (fun i ↦ (u i : R)) hu hrs f n

/-- The rescaling equivalence is an isometry for the two Gauss norms. -/
theorem isometry_restrictedRescaleEquiv (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i) :
    Isometry (restrictedRescaleEquiv u hu hrs) :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr (norm_restrictedRescaleEquiv u hu hrs)

end Equiv

end TauCeti.MvPowerSeries
