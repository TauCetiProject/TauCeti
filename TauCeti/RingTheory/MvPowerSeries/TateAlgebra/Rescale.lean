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

Multiplying each variable by a scalar maps restricted-series algebras at the correspondingly
rescaled polyradii to each other. If left multiplication by each `u i` scales every norm by `‖u i‖`
and `‖u i‖ * s i = r i`, then substitution `X i ↦ u i * X i` is an algebra homomorphism from the
algebra at polyradius `r` to the algebra at polyradius `s`, isometric for positive polyradii
(`TauCeti.MvPowerSeries.restrictedRescaleAlgHom`); the `u i` need not be invertible. If each `u i`
is a multiplicative unit, this substitution is an isometric algebra equivalence
(`TauCeti.MvPowerSeries.restrictedRescaleEquiv`) whose inverse substitutes the inverse units, and
whose underlying homomorphism is the rescaling homomorphism
(`TauCeti.MvPowerSeries.restrictedRescaleEquiv_toAlgHom`). Rescaling by `1` is the identity
(`TauCeti.MvPowerSeries.restrictedRescaleAlgHom_one`), and successive rescalings compose to the
rescaling by the pointwise product
(`TauCeti.MvPowerSeries.restrictedRescaleAlgHom_comp_restrictedRescaleAlgHom`).

The construction works at arbitrary positive real polyradii, including radii that are not norms
of scalars. It uses Mathlib's coefficientwise `MvPowerSeries.rescale`, so its coefficient formula
and compatibility with constants are inherited without introducing another series carrier.
The algebra homomorphism and equivalence do not require positive weights; positivity is needed
only for the Gauss-norm statements.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {σ R : Type*} [NormedCommRing R] {r s : σ → ℝ}

section Equiv

variable [IsUltrametricDist R]

/-- Rescale restricted series by elements `u i` by which left multiplication scales every norm by
`‖u i‖`, from radii `r` to radii `s` satisfying `‖u i‖ * s i = r i`. -/
noncomputable def restrictedRescaleAlgHom (u : σ → R)
    (hu : ∀ i (x : R), ‖u i * x‖ = ‖u i‖ * ‖x‖) (hrs : ∀ i, ‖u i‖ * s i = r i) :
    IsRestricted.subring (R := R) r →ₐ[R] IsRestricted.subring (R := R) s where
  toFun f := ⟨MvPowerSeries.rescale u f, (isRestricted_rescale_iff u hu hrs f).mpr f.property⟩
  map_one' := Subtype.ext (map_one (MvPowerSeries.rescale u))
  map_mul' f g := Subtype.ext (map_mul (MvPowerSeries.rescale u) (f : MvPowerSeries σ R) g)
  map_zero' := Subtype.ext (map_zero (MvPowerSeries.rescale u))
  map_add' f g := Subtype.ext (map_add (MvPowerSeries.rescale u) (f : MvPowerSeries σ R) g)
  commutes' a := Subtype.ext <| by
    simpa only [MvPowerSeries.rescaleAlgHom_apply, coe_algebraMap_isRestrictedSubring,
      MvPowerSeries.c_eq_algebraMap] using (MvPowerSeries.rescaleAlgHom u).commutes a

/-- The underlying formal series of `restrictedRescaleAlgHom` is Mathlib's rescaling. -/
@[simp]
theorem coe_restrictedRescaleAlgHom (u : σ → R)
    (hu : ∀ i (x : R), ‖u i * x‖ = ‖u i‖ * ‖x‖) (hrs : ∀ i, ‖u i‖ * s i = r i)
    (f : IsRestricted.subring (R := R) r) :
    (restrictedRescaleAlgHom u hu hrs f : MvPowerSeries σ R) = MvPowerSeries.rescale u f := by
  rfl

/-- The rescaling homomorphism sends `X i` to `u i * X i`. -/
@[simp]
theorem restrictedRescaleAlgHom_X (u : σ → R) (hu : ∀ i (x : R), ‖u i * x‖ = ‖u i‖ * ‖x‖)
    (hrs : ∀ i, ‖u i‖ * s i = r i) (i : σ) :
    restrictedRescaleAlgHom u hu hrs
        (⟨MvPowerSeries.X i, isRestricted_X r i⟩ : IsRestricted.subring (R := R) r) =
      algebraMap R (IsRestricted.subring (R := R) s) (u i) *
        (⟨MvPowerSeries.X i, isRestricted_X s i⟩ : IsRestricted.subring (R := R) s) := by
  apply Subtype.ext
  rw [coe_restrictedRescaleAlgHom, Subring.coe_mul, coe_algebraMap_isRestrictedSubring,
    MvPowerSeries.rescale_X]

/-- Rescaling by `1` at the same polyradius is the identity. -/
@[simp]
theorem restrictedRescaleAlgHom_one
    (hu : ∀ i (x : R), ‖(1 : σ → R) i * x‖ = ‖(1 : σ → R) i‖ * ‖x‖)
    (hrr : ∀ i, ‖(1 : σ → R) i‖ * r i = r i) :
    restrictedRescaleAlgHom 1 hu hrr = AlgHom.id R (IsRestricted.subring (R := R) r) :=
  AlgHom.ext fun _ ↦ Subtype.ext (by simp)

/-- Rescaling homomorphisms compose by multiplying their scaling families. -/
theorem restrictedRescaleAlgHom_comp_restrictedRescaleAlgHom {t : σ → ℝ} (u v : σ → R)
    (hu : ∀ i (x : R), ‖u i * x‖ = ‖u i‖ * ‖x‖) (hrs : ∀ i, ‖u i‖ * s i = r i)
    (hv : ∀ i (x : R), ‖v i * x‖ = ‖v i‖ * ‖x‖) (hst : ∀ i, ‖v i‖ * t i = s i)
    (huv : ∀ i (x : R), ‖(u * v) i * x‖ = ‖(u * v) i‖ * ‖x‖)
    (hrt : ∀ i, ‖(u * v) i‖ * t i = r i) :
    (restrictedRescaleAlgHom v hv hst).comp (restrictedRescaleAlgHom u hu hrs) =
      restrictedRescaleAlgHom (u * v) huv hrt :=
  AlgHom.ext fun _ ↦ Subtype.ext (by simp [rescale_rescale])

/-- Applying two rescaling homomorphisms in turn rescales by the pointwise product of their
scaling families. -/
@[simp]
theorem restrictedRescaleAlgHom_restrictedRescaleAlgHom {t : σ → ℝ} (u v : σ → R)
    (hu : ∀ i (x : R), ‖u i * x‖ = ‖u i‖ * ‖x‖) (hrs : ∀ i, ‖u i‖ * s i = r i)
    (hv : ∀ i (x : R), ‖v i * x‖ = ‖v i‖ * ‖x‖) (hst : ∀ i, ‖v i‖ * t i = s i)
    (f : IsRestricted.subring (R := R) r) :
    restrictedRescaleAlgHom v hv hst (restrictedRescaleAlgHom u hu hrs f) =
      restrictedRescaleAlgHom (u * v)
        (fun i x ↦ by rw [Pi.mul_apply, mul_assoc, hu, hv, hu, mul_assoc])
        (fun i ↦ by rw [Pi.mul_apply, hu, mul_assoc, hst, hrs]) f :=
  Subtype.ext (by simp [rescale_rescale])

/-- The change of weights obtained by substituting `X i ↦ u i * X i`, where each `u i` is a
multiplicative unit and `‖u i‖ * s i = r i`. The inverse substitutes `u i⁻¹`. For positive
polyradii, this equivalence is an isometry. -/
noncomputable def restrictedRescaleEquiv (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i) :
    IsRestricted.subring (R := R) r ≃ₐ[R] IsRestricted.subring (R := R) s :=
  { restrictedRescaleAlgHom (fun i ↦ (u i : R)) (fun i ↦ (hu i).norm_mul) hrs with
    invFun f := ⟨MvPowerSeries.rescale (fun i ↦ (((u i)⁻¹ : Rˣ) : R)) f,
      (isRestricted_rescale_iff (fun i ↦ (u i : R)) (fun i ↦ (hu i).norm_mul) hrs _).mp <| by
        have hcancel := rescale_inv_rescale (fun i ↦ (u i)⁻¹) (f : MvPowerSeries σ R)
        simp only [inv_inv] at hcancel
        exact hcancel.symm ▸ f.property⟩
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

/-- As an algebra homomorphism, the rescaling equivalence is the rescaling homomorphism by the
underlying elements of the units. -/
@[simp]
theorem restrictedRescaleEquiv_toAlgHom (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i) :
    (restrictedRescaleEquiv u hu hrs :
        IsRestricted.subring (R := R) r →ₐ[R] IsRestricted.subring (R := R) s) =
      restrictedRescaleAlgHom (fun i ↦ (u i : R)) (fun i ↦ (hu i).norm_mul) hrs :=
  AlgHom.ext fun _ ↦ Subtype.ext (by simp)

/-- The rescaling equivalence sends `X i` to `u i * X i`. -/
@[simp]
theorem restrictedRescaleEquiv_X (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i) (i : σ) :
    restrictedRescaleEquiv u hu hrs
        (⟨MvPowerSeries.X i, isRestricted_X r i⟩ : IsRestricted.subring (R := R) r) =
      algebraMap R (IsRestricted.subring (R := R) s) (u i : R) *
        (⟨MvPowerSeries.X i, isRestricted_X s i⟩ : IsRestricted.subring (R := R) s) :=
  restrictedRescaleAlgHom_X (fun i ↦ (u i : R)) (fun i ↦ (hu i).norm_mul) hrs i

variable [∀ i, Fact (0 < r i)] [∀ i, Fact (0 < s i)]

/-- The rescaling homomorphism preserves the Gauss norm. -/
@[simp]
theorem norm_restrictedRescaleAlgHom (u : σ → R) (hu : ∀ i (x : R), ‖u i * x‖ = ‖u i‖ * ‖x‖)
    (hrs : ∀ i, ‖u i‖ * s i = r i) (f : IsRestricted.subring (R := R) r) :
    ‖restrictedRescaleAlgHom u hu hrs f‖ = ‖f‖ := by
  rw [norm_eq_gaussNorm, norm_eq_gaussNorm, gaussNorm]
  congr 1
  funext n
  rw [coe_restrictedRescaleAlgHom]
  exact norm_coeff_rescale_mul_prod u hu hrs f n

/-- The rescaling homomorphism is an isometry for the two Gauss norms. -/
theorem isometry_restrictedRescaleAlgHom (u : σ → R)
    (hu : ∀ i (x : R), ‖u i * x‖ = ‖u i‖ * ‖x‖) (hrs : ∀ i, ‖u i‖ * s i = r i) :
    Isometry (restrictedRescaleAlgHom u hu hrs) :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr (norm_restrictedRescaleAlgHom u hu hrs)

/-- The rescaling equivalence preserves the Gauss norm. -/
@[simp]
theorem norm_restrictedRescaleEquiv (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i)
    (f : IsRestricted.subring (R := R) r) :
    ‖restrictedRescaleEquiv u hu hrs f‖ = ‖f‖ :=
  norm_restrictedRescaleAlgHom (fun i ↦ (u i : R)) (fun i ↦ (hu i).norm_mul) hrs f

/-- The rescaling equivalence is an isometry for the two Gauss norms. -/
theorem isometry_restrictedRescaleEquiv (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i) :
    Isometry (restrictedRescaleEquiv u hu hrs) :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr (norm_restrictedRescaleEquiv u hu hrs)

end Equiv

end TauCeti.MvPowerSeries
