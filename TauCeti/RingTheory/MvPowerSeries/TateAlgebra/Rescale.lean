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

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {σ R : Type*} [NormedCommRing R] {r s : σ → ℝ}

section Equiv

variable [IsUltrametricDist R] [∀ i, Fact (0 < r i)] [∀ i, Fact (0 < s i)]

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

omit [∀ i, Fact (0 < r i)] [∀ i, Fact (0 < s i)] in
/-- The underlying formal series of `restrictedRescaleAlgHom` is Mathlib's rescaling. -/
@[simp]
private theorem coe_restrictedRescaleAlgHom (u : σ → R) (hu : ∀ i, IsNormMulUnit (u i))
    (hrs : ∀ i, ‖u i‖ * s i = r i) (f : IsRestricted.subring (R := R) r) :
    (restrictedRescaleAlgHom u hu hrs f : MvPowerSeries σ R) = MvPowerSeries.rescale u f := by
  rfl

/-- Rescaling between corresponding radii preserves the Gauss norm. -/
private theorem norm_restrictedRescaleAlgHom (u : σ → R) (hu : ∀ i, IsNormMulUnit (u i))
    (hrs : ∀ i, ‖u i‖ * s i = r i) (f : IsRestricted.subring (R := R) r) :
    ‖restrictedRescaleAlgHom u hu hrs f‖ = ‖f‖ := by
  rw [norm_eq_gaussNorm, norm_eq_gaussNorm, gaussNorm]
  congr 1
  funext n
  rw [coe_restrictedRescaleAlgHom]
  exact norm_coeff_rescale_mul_prod u hu hrs f n

omit [IsUltrametricDist R] in
private theorem norm_ne_zero_of_radius_eq (u : σ → Rˣ)
    (hrs : ∀ i, ‖(u i : R)‖ * s i = r i) (i : σ) : ‖(u i : R)‖ ≠ 0 := by
  have hr : 0 < r i := Fact.out
  have hs : 0 < s i := Fact.out
  nlinarith [norm_nonneg (u i : R), hrs i]

omit [IsUltrametricDist R] in
private theorem inverse_radius_eq (u : σ → Rˣ) (hu : ∀ i, IsNormMulUnit (u i : R))
    (hrs : ∀ i, ‖(u i : R)‖ * s i = r i) (i : σ) :
    ‖(((u i)⁻¹ : Rˣ) : R)‖ * r i = s i := by
  have hne := norm_ne_zero_of_radius_eq u hrs i
  have hnorm : ‖(((u i)⁻¹ : Rˣ) : R)‖ = ‖(u i : R)‖⁻¹ :=
    TauCeti.NormedRing.norm_units_inv_of_norm_mul hne
      (hu i).norm_mul
  rw [hnorm]
  calc
    ‖(u i : R)‖⁻¹ * r i = ‖(u i : R)‖⁻¹ * (‖(u i : R)‖ * s i) := by
      rw [hrs i]
    _ = s i := inv_mul_cancel_left₀ hne _

/-- The isometric change of polyradii obtained by substituting `X i ↦ u i * X i`, where each
`u i` is a multiplicative unit and `‖u i‖ * s i = r i`. The inverse substitutes `u i⁻¹`. -/
noncomputable def restrictedRescaleEquiv (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i) :
    IsRestricted.subring (R := R) r ≃ₐ[R] IsRestricted.subring (R := R) s :=
  AlgEquiv.ofAlgHom (restrictedRescaleAlgHom (fun i ↦ (u i : R)) hu hrs)
    (restrictedRescaleAlgHom (fun i ↦ (((u i)⁻¹ : Rˣ) : R)) (fun i ↦ (hu i).units_inv)
      (inverse_radius_eq u hu hrs))
    (AlgHom.ext fun f ↦ Subtype.ext <| by
      simpa using rescale_inv_rescale (fun i ↦ (u i)⁻¹) (f : MvPowerSeries σ R))
    (AlgHom.ext fun f ↦ Subtype.ext <| rescale_inv_rescale u f)

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

/-- The rescaling equivalence preserves the Gauss norm. -/
@[simp]
theorem norm_restrictedRescaleEquiv (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i)
    (f : IsRestricted.subring (R := R) r) :
    ‖restrictedRescaleEquiv u hu hrs f‖ = ‖f‖ :=
  norm_restrictedRescaleAlgHom (fun i ↦ (u i : R)) hu hrs f

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

/-- The rescaling equivalence is an isometry for the two Gauss norms. -/
theorem isometry_restrictedRescaleEquiv (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i) :
    Isometry (restrictedRescaleEquiv u hu hrs) :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr (norm_restrictedRescaleEquiv u hu hrs)

end Equiv

end TauCeti.MvPowerSeries
