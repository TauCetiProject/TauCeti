/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import TauCeti.Analysis.Normed.Ring.MulUnit
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Radius

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

namespace MvPowerSeries

open Filter TauCeti

variable {σ R : Type*} [NormedCommRing R] [NormOneClass R] {r s : σ → ℝ}

private theorem isNormMulUnit_prod_pow (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (n : σ →₀ ℕ) :
    IsNormMulUnit (n.prod fun i m ↦ (u i : R) ^ m) := by
  classical
  rw [Finsupp.prod]
  exact Finset.prod_induction _ IsNormMulUnit (fun _ _ ↦ IsNormMulUnit.mul)
    isNormMulUnit_one fun i _ ↦ (hu i).pow _

private theorem norm_prod_pow (u : σ → Rˣ) (hu : ∀ i, IsNormMulUnit (u i : R))
    (n : σ →₀ ℕ) :
    ‖n.prod fun i m ↦ (u i : R) ^ m‖ = n.prod fun i m ↦ ‖(u i : R)‖ ^ m := by
  classical
  have norm_pow (i : σ) (m : ℕ) : ‖(u i : R) ^ m‖ = ‖(u i : R)‖ ^ m := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', (hu i).norm_mul, ih, pow_succ']
  simp only [Finsupp.prod]
  induction n.support using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, ((hu i).pow (n i)).norm_mul, ih,
        norm_pow]

private theorem weighted_norm_coeff_rescale (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i)
    (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    ‖coeff n (MvPowerSeries.rescale (fun i ↦ (u i : R)) f)‖ * n.prod (s · ^ ·) =
      ‖coeff n f‖ * n.prod (r · ^ ·) := by
  rw [coeff_rescale, (isNormMulUnit_prod_pow u hu n).norm_mul, norm_prod_pow u hu n]
  calc
    (n.prod fun i m ↦ ‖(u i : R)‖ ^ m) * ‖coeff n f‖ * n.prod (s · ^ ·) =
        ‖coeff n f‖ *
          ((n.prod fun i m ↦ ‖(u i : R)‖ ^ m) * n.prod (s · ^ ·)) := by
      ac_rfl
    _ = ‖coeff n f‖ * n.prod (r · ^ ·) := by
      congr 1
      simp only [Finsupp.prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ ↦ by rw [← mul_pow, hrs i]

/-- Rescaling by multiplicative units converts restrictedness at `r` into restrictedness at `s`
when `‖u i‖ * s i = r i`. -/
theorem isRestricted_rescale_iff (u : σ → Rˣ) (hu : ∀ i, IsNormMulUnit (u i : R))
    (hrs : ∀ i, ‖(u i : R)‖ * s i = r i) (f : MvPowerSeries σ R) :
    IsRestricted s (MvPowerSeries.rescale (fun i ↦ (u i : R)) f) ↔ IsRestricted r f := by
  unfold IsRestricted
  apply tendsto_congr'
  exact .of_forall (weighted_norm_coeff_rescale u hu hrs f)

end MvPowerSeries

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {σ R : Type*} [NormedCommRing R] [NormOneClass R] {r s : σ → ℝ}

section Equiv

variable [IsUltrametricDist R] [∀ i, Fact (0 < r i)] [∀ i, Fact (0 < s i)]

/-- Rescale restricted series by multiplicative units, from radii `r` to radii `s` satisfying
`‖u i‖ * s i = r i`. -/
private noncomputable def restrictedRescaleAlgHom (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i) :
    IsRestricted.subring (R := R) r →ₐ[R] IsRestricted.subring (R := R) s where
  toFun f := ⟨MvPowerSeries.rescale (fun i ↦ (u i : R)) f,
    (isRestricted_rescale_iff u hu hrs f).mpr f.2⟩
  map_one' := Subtype.ext (map_one (MvPowerSeries.rescale fun i ↦ (u i : R)))
  map_mul' f g := Subtype.ext
    (map_mul (MvPowerSeries.rescale fun i ↦ (u i : R)) (f : MvPowerSeries σ R) g)
  map_zero' := Subtype.ext (map_zero (MvPowerSeries.rescale fun i ↦ (u i : R)))
  map_add' f g := Subtype.ext
    (map_add (MvPowerSeries.rescale fun i ↦ (u i : R)) (f : MvPowerSeries σ R) g)
  commutes' a := Subtype.ext <| by
    simpa only [MvPowerSeries.rescaleAlgHom_apply, coe_algebraMap_isRestrictedSubring,
      MvPowerSeries.c_eq_algebraMap] using
      (MvPowerSeries.rescaleAlgHom (fun i ↦ (u i : R))).commutes a

omit [∀ i, Fact (0 < r i)] [∀ i, Fact (0 < s i)] in
/-- The underlying formal series of `restrictedRescaleAlgHom` is Mathlib's rescaling. -/
@[simp]
private theorem coe_restrictedRescaleAlgHom (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R))
    (hrs : ∀ i, ‖(u i : R)‖ * s i = r i) (f : IsRestricted.subring (R := R) r) :
    (restrictedRescaleAlgHom u hu hrs f : MvPowerSeries σ R) =
      MvPowerSeries.rescale (fun i ↦ (u i : R)) f := by
  rfl

/-- Rescaling between corresponding radii preserves the Gauss norm. -/
private theorem norm_restrictedRescaleAlgHom (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i)
    (f : IsRestricted.subring (R := R) r) :
    ‖restrictedRescaleAlgHom u hu hrs f‖ = ‖f‖ := by
  rw [norm_eq_gaussNorm, norm_eq_gaussNorm, gaussNorm]
  congr 1
  funext n
  rw [coe_restrictedRescaleAlgHom]
  exact weighted_norm_coeff_rescale u hu hrs f n

omit [IsUltrametricDist R] in
private theorem inverse_radius_eq (u : σ → Rˣ) (hu : ∀ i, IsNormMulUnit (u i : R))
    (hrs : ∀ i, ‖(u i : R)‖ * s i = r i) (i : σ) :
    ‖(((u i)⁻¹ : Rˣ) : R)‖ * r i = s i := by
  have hnorm : ‖(((u i)⁻¹ : Rˣ) : R)‖ = ‖(u i : R)‖⁻¹ :=
    (Units.isNormMulUnit_iff_norm_inv (u i)).mp (hu i)
  have hne : ‖(u i : R)‖ ≠ 0 := by
    have hr : 0 < r i := Fact.out
    have hs : 0 < s i := Fact.out
    nlinarith [norm_nonneg (u i : R), hrs i]
  rw [hnorm]
  calc
    ‖(u i : R)‖⁻¹ * r i = ‖(u i : R)‖⁻¹ * (‖(u i : R)‖ * s i) := by
      rw [hrs i]
    _ = s i := inv_mul_cancel_left₀ hne _

private theorem restrictedRescaleAlgHom_comp_inverse (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i) :
    (restrictedRescaleAlgHom u hu hrs).comp
        (restrictedRescaleAlgHom (fun i ↦ (u i)⁻¹) (fun i ↦ (hu i).units_inv)
          (inverse_radius_eq u hu hrs)) =
      AlgHom.id R (IsRestricted.subring (R := R) s) := by
  apply AlgHom.ext fun f ↦ Subtype.ext <| by
    simp only [AlgHom.coe_comp, Function.comp_apply, coe_restrictedRescaleAlgHom,
      AlgHom.coe_id, id_eq, MvPowerSeries.rescale_rescale]
    have h : ((fun i ↦ (((u i)⁻¹ : Rˣ) : R)) * fun i ↦ (u i : R)) = 1 := by
      funext i
      simp
    rw [h, MvPowerSeries.rescale_one]
    rfl

private theorem restrictedRescaleAlgHom_inverse_comp (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i) :
    (restrictedRescaleAlgHom (fun i ↦ (u i)⁻¹) (fun i ↦ (hu i).units_inv)
        (inverse_radius_eq u hu hrs)).comp
        (restrictedRescaleAlgHom u hu hrs) =
      AlgHom.id R (IsRestricted.subring (R := R) r) := by
  apply AlgHom.ext fun f ↦ Subtype.ext <| by
    simp only [AlgHom.coe_comp, Function.comp_apply, coe_restrictedRescaleAlgHom,
      AlgHom.coe_id, id_eq, MvPowerSeries.rescale_rescale]
    have h : ((fun i ↦ (u i : R)) * fun i ↦ (((u i)⁻¹ : Rˣ) : R)) = 1 := by
      funext i
      simp
    rw [h, MvPowerSeries.rescale_one]
    rfl

/-- The isometric change of polyradii obtained by substituting `X i ↦ u i * X i`, where each
`u i` is a multiplicative unit and `‖u i‖ * s i = r i`. The inverse substitutes `u i⁻¹`. -/
noncomputable def restrictedRescaleEquiv (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i) :
    IsRestricted.subring (R := R) r ≃ₐ[R] IsRestricted.subring (R := R) s :=
  AlgEquiv.ofAlgHom (restrictedRescaleAlgHom u hu hrs)
    (restrictedRescaleAlgHom (fun i ↦ (u i)⁻¹) (fun i ↦ (hu i).units_inv)
      (inverse_radius_eq u hu hrs))
    (restrictedRescaleAlgHom_comp_inverse u hu hrs)
    (restrictedRescaleAlgHom_inverse_comp u hu hrs)

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
theorem norm_restrictedRescaleEquiv (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i)
    (f : IsRestricted.subring (R := R) r) :
    ‖restrictedRescaleEquiv u hu hrs f‖ = ‖f‖ :=
  norm_restrictedRescaleAlgHom u hu hrs f

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
    coeff_rescale, coeff_C_mul]
  by_cases hn : n = Finsupp.single i 1
  · subst n
    simp [MvPowerSeries.X]
  · rw [coeff_X]
    simp [hn]

/-- The rescaling equivalence is an isometry for the two Gauss norms. -/
theorem isometry_restrictedRescaleEquiv (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R)) (hrs : ∀ i, ‖(u i : R)‖ * s i = r i) :
    Isometry (restrictedRescaleEquiv u hu hrs) :=
  AddMonoidHomClass.isometry_iff_norm _ |>.mpr (norm_restrictedRescaleEquiv u hu hrs)

end Equiv

end TauCeti.MvPowerSeries
