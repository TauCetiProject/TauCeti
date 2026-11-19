/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.HahnSeries.Map
public import TauCeti.RingTheory.LaurentSeries.Lattice
public import TauCeti.RingTheory.LaurentSeries.Rescale
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic

/-!
# Coordinate automorphisms of formal Laurent series over a commutative ring

Let `R` be a commutative ring and `φ = u X + ⋯` a formal coordinate over `R`
(`TauCeti.FormalCoordinate R`), so that `u` is a unit. Substitution `f ↦ f (φ)` is an
automorphism `σ_φ` of the `R`-algebra `R⟦X⟧` (`TauCeti.FormalCoordinate.substAlgEquiv`). This
file extends it to an automorphism of the `R`-algebra `R⸨X⸩` of formal Laurent series, with no
hypothesis on `R`: nilpotents and zero divisors are allowed.

Laurent series are the localization of power series at the powers of `X`
(`LaurentSeries.of_powerSeries_localization`). Since `φ = X * (u + ⋯)` and `u + ⋯` is a unit
power series, `σ_φ X = φ` is a unit of `R⸨X⸩`, so `σ_φ` extends uniquely to `R⸨X⸩`; the
extension of the substitution of the compositional inverse `φ⁻¹` is its inverse. For an integer
`N`, the extension sends `X ^ N` to `φ ^ N = X ^ N (u + ⋯) ^ N`, so it maps each lattice
`X ^ N R⟦X⟧` (`TauCeti.LaurentSeries.lattice`) onto itself.

As for power series, the automorphisms reverse composition: `σ_φ ∘ σ_ψ = σ_(ψ ∘ φ)`, where
`(ψ ∘ φ) (X) = ψ (φ (X))` is the product `ψ * φ` of formal coordinates. So coordinate changes act
on `R⸨X⸩` on the right, and `φ ↦ σ_φ` is an injective group homomorphism to the opposite of the
automorphism group. The construction is natural in `R`: applying a ring homomorphism to the
coefficients intertwines `σ_φ` with the automorphism of the base-changed coordinate. The
homothety `X ↦ a X` by a unit `a` gives the rescaling `TauCeti.LaurentSeries.rescale a`. Over a
field, `σ_φ` is the substitution `TauCeti.LaurentSeries.substAlgHom` into the fraction field of
`K⟦X⟧` (`TauCeti.LaurentSeries.coe_substAlgEquiv`, in
`TauCeti.RingTheory.LaurentSeries.Substitution.Basic`).

The final examples check the composition order for `φ = 2 X` and `ψ = X + X²` over `ℚ`:
`σ_φ (σ_ψ X) = 2 X + 4 X²` while `σ_ψ (σ_φ X) = 2 X + 2 X²`.

## Main definitions

* `TauCeti.LaurentSeries.substAlgEquiv φ`: the automorphism `f ↦ f (φ)` of the `R`-algebra
  `R⸨X⸩`.
* `TauCeti.LaurentSeries.substAlgEquivHom`: the antihomomorphism `φ ↦ σ_φ`.

## Main results

* `TauCeti.FormalCoordinate.isUnit_coe_toPowerSeries`: a formal coordinate is a unit of `R⸨X⸩`.
* `TauCeti.LaurentSeries.substAlgEquiv_coe`: `σ_φ` extends the substitution automorphism of
  `R⟦X⟧`.
* `TauCeti.LaurentSeries.substAlgEquiv_single`: `σ_φ (a X ^ n) = a φ ^ n` for every integer `n`.
* `TauCeti.LaurentSeries.substAlgEquiv_mul`: `σ_(φ ∘ ψ) = σ_ψ ∘ σ_φ`.
* `TauCeti.LaurentSeries.substAlgEquiv_mem_lattice_iff`,
  `TauCeti.LaurentSeries.image_substAlgEquiv_lattice`: `σ_φ` maps `X ^ N R⟦X⟧` onto itself.
* `TauCeti.LaurentSeries.mapRingHom_substAlgEquiv`: naturality in the coefficient ring.
* `TauCeti.LaurentSeries.substAlgEquiv_homothety`: the homothety by `a` gives rescaling by `a`.

## References

* E. Frenkel, *Langlands correspondence for loop groups*, Cambridge Studies in Advanced
  Mathematics 103, 2007, §§3.5.3–3.5.4.
-/

public section

open scoped LaurentSeries PowerSeries
open HahnSeries PowerSeries

namespace TauCeti

namespace LaurentSeries

variable {R : Type*} [CommRing R]

/-- A formal coordinate `φ = X (u + ⋯)` as a unit of `R⸨X⸩`: the product of the units `X` and
`u + ⋯`. -/
private noncomputable def unitCoord (φ : FormalCoordinate R) : R⸨X⸩ˣ :=
  unitX * Units.map (ofPowerSeries ℤ R : R⟦X⟧ →* R⸨X⸩) φ.isUnit_mk_coeff_succ.unit

private theorem val_unitCoord (φ : FormalCoordinate R) :
    (unitCoord φ : R⸨X⸩) = (φ.toPowerSeries : R⸨X⸩) := by
  rw [unitCoord, Units.val_mul, Units.coe_map, IsUnit.unit_spec, val_unitX]
  conv_rhs => rw [φ.toPowerSeries_eq_X_mul, map_mul, ofPowerSeries_X]
  rw [MonoidHom.coe_ofClass]

end LaurentSeries

namespace FormalCoordinate

variable {R : Type*} [CommRing R]

/-- A formal coordinate `φ = X (u + ⋯)` is a unit of `R⸨X⸩`, since `X` and `u + ⋯` are. -/
theorem isUnit_coe_toPowerSeries (φ : FormalCoordinate R) : IsUnit (φ.toPowerSeries : R⸨X⸩) :=
  ⟨LaurentSeries.unitCoord φ, LaurentSeries.val_unitCoord φ⟩

end FormalCoordinate

namespace LaurentSeries

variable {R : Type*} [CommRing R]

private theorem unit_eq_unitCoord (φ : FormalCoordinate R) :
    φ.isUnit_coe_toPowerSeries.unit = unitCoord φ :=
  Units.ext (val_unitCoord φ).symm

/-- Substitution of a formal coordinate, as an `R`-algebra map `R⟦X⟧ → R⸨X⸩` sending the powers
of `X` to units. -/
private noncomputable def substCoeAlgHom (φ : FormalCoordinate R) : R⟦X⟧ →ₐ[R] R⸨X⸩ :=
  (IsScalarTower.toAlgHom R R⟦X⟧ R⸨X⸩).comp φ.substAlgEquiv.toAlgHom

private theorem substCoeAlgHom_apply (φ : FormalCoordinate R) (f : R⟦X⟧) :
    substCoeAlgHom φ f = ((φ.substAlgEquiv f : R⟦X⟧) : R⸨X⸩) :=
  (rfl)

private theorem isUnit_substCoeAlgHom (φ : FormalCoordinate R) (y : Submonoid.powers (X : R⟦X⟧)) :
    IsUnit (substCoeAlgHom φ y) := by
  obtain ⟨_, n, rfl⟩ := y
  rw [map_pow, substCoeAlgHom_apply, FormalCoordinate.substAlgEquiv_X]
  exact φ.isUnit_coe_toPowerSeries.pow n

/-- The extension `R⸨X⸩ → R⸨X⸩` of the substitution of a formal coordinate, by localization at
`X`. -/
private noncomputable def substAlgHom' (φ : FormalCoordinate R) : R⸨X⸩ →ₐ[R] R⸨X⸩ :=
  IsLocalization.liftAlgHom (M := Submonoid.powers X) (isUnit_substCoeAlgHom φ)

private theorem substAlgHom'_coe (φ : FormalCoordinate R) (f : R⟦X⟧) :
    substAlgHom' φ (f : R⸨X⸩) = ((φ.substAlgEquiv f : R⟦X⟧) : R⸨X⸩) :=
  IsLocalization.lift_eq (M := Submonoid.powers X) _ f

/-- The extension `substAlgHom' φ` is the only `R`-algebra map `R⸨X⸩ → R⸨X⸩` extending the
substitution of `φ`, as `R⸨X⸩` is the localization of `R⟦X⟧` at the powers of `X`. -/
private theorem eq_substAlgHom' {φ : FormalCoordinate R} {g : R⸨X⸩ →ₐ[R] R⸨X⸩}
    (h : ∀ f : R⟦X⟧, g f = ((φ.substAlgEquiv f : R⟦X⟧) : R⸨X⸩)) : g = substAlgHom' φ :=
  AlgHom.toRingHom_injective <| IsLocalization.ringHom_ext (Submonoid.powers (X : R⟦X⟧)) <|
    RingHom.ext fun f ↦ by
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_coe, RingHom.coe_coe,
        _root_.LaurentSeries.coe_algebraMap, h, substAlgHom'_coe]

private theorem substAlgHom'_comp (φ ψ : FormalCoordinate R) :
    (substAlgHom' ψ).comp (substAlgHom' φ) = substAlgHom' (φ * ψ) :=
  eq_substAlgHom' fun p ↦ by
    rw [AlgHom.comp_apply, substAlgHom'_coe, substAlgHom'_coe,
      FormalCoordinate.substAlgEquiv_mul, AlgEquiv.mul_apply]

private theorem substAlgHom'_one : substAlgHom' (1 : FormalCoordinate R) = AlgHom.id R R⸨X⸩ :=
  (eq_substAlgHom' fun p ↦ by
    rw [FormalCoordinate.substAlgEquiv_one, AlgEquiv.one_apply, AlgHom.id_apply]).symm

/-- The automorphism `σ_φ : f ↦ f (φ)` of the `R`-algebra `R⸨X⸩` attached to a formal coordinate
`φ`. It is the unique extension of the substitution automorphism
`TauCeti.FormalCoordinate.substAlgEquiv` of `R⟦X⟧`, through the localization of `R⟦X⟧` at the
powers of `X`, and its inverse is the automorphism of the compositional inverse `φ⁻¹`. -/
noncomputable def substAlgEquiv (φ : FormalCoordinate R) : R⸨X⸩ ≃ₐ[R] R⸨X⸩ :=
  .ofAlgHom (substAlgHom' φ) (substAlgHom' φ⁻¹)
    (by rw [substAlgHom'_comp, inv_mul_cancel, substAlgHom'_one])
    (by rw [substAlgHom'_comp, mul_inv_cancel, substAlgHom'_one])

/-- On power series, the automorphism `σ_φ` of `R⸨X⸩` is that of `R⟦X⟧`. -/
@[simp]
theorem substAlgEquiv_coe (φ : FormalCoordinate R) (f : R⟦X⟧) :
    substAlgEquiv φ (f : R⸨X⸩) = ((φ.substAlgEquiv f : R⟦X⟧) : R⸨X⸩) :=
  substAlgHom'_coe φ f

/-- `σ_φ` is the only `R`-algebra map `R⸨X⸩ → R⸨X⸩` extending the substitution automorphism of
`R⟦X⟧`. -/
theorem eq_substAlgEquiv_of_coe {φ : FormalCoordinate R} {g : R⸨X⸩ →ₐ[R] R⸨X⸩}
    (h : ∀ f : R⟦X⟧, g f = ((φ.substAlgEquiv f : R⟦X⟧) : R⸨X⸩)) :
    g = (substAlgEquiv φ : R⸨X⸩ →ₐ[R] R⸨X⸩) :=
  (eq_substAlgHom' h).trans (AlgEquiv.toAlgHom_ofAlgHom _ _ _ _).symm

/-- `σ_φ` sends the variable `X = single 1 1` to `φ`. -/
@[simp]
theorem substAlgEquiv_single_one (φ : FormalCoordinate R) :
    substAlgEquiv φ (single 1 1) = (φ.toPowerSeries : R⸨X⸩) := by
  rw [← ofPowerSeries_X, substAlgEquiv_coe,
    FormalCoordinate.substAlgEquiv_X]

/-- `σ_φ` sends the power `Xⁿ` of the unit `X`, for every integer `n`, to `φⁿ`. -/
private theorem substAlgEquiv_single_one_zpow (φ : FormalCoordinate R) (n : ℤ) :
    substAlgEquiv φ (single n 1) = ↑(unitCoord φ ^ n) := by
  have hx : Units.map (substAlgEquiv φ : R⸨X⸩ →* R⸨X⸩) unitX = unitCoord φ :=
    Units.ext <| by
      rw [Units.coe_map, MonoidHom.coe_ofClass, val_unitX, substAlgEquiv_single_one,
        val_unitCoord]
  rw [← val_unitX_zpow, ← hx, ← map_zpow, Units.coe_map, MonoidHom.coe_ofClass]

/-- `σ_φ` sends the monomial `a X ^ n`, for every integer `n`, to `a φ ^ n`, a power of the unit
`φ` of `R⸨X⸩`. -/
theorem substAlgEquiv_single (φ : FormalCoordinate R) (n : ℤ) (a : R) :
    substAlgEquiv φ (single n a) =
      (HahnSeries.C a : R⸨X⸩) * ((φ.isUnit_coe_toPowerSeries.unit ^ n : R⸨X⸩ˣ) : R⸨X⸩) := by
  have hC : substAlgEquiv φ (HahnSeries.C a) = HahnSeries.C a := by
    rw [← ofPowerSeries_C, substAlgEquiv_coe, FormalCoordinate.substAlgEquiv_apply,
      ← PowerSeries.algebraMap_eq, ← coe_substAlgHom φ.hasSubst, AlgHom.commutes]
  rw [unit_eq_unitCoord, ← substAlgEquiv_single_one_zpow, ← hC, ← map_mul, HahnSeries.C_apply,
    single_mul_single, zero_add, mul_one]

@[simp]
theorem substAlgEquiv_symm (φ : FormalCoordinate R) :
    (substAlgEquiv φ).symm = substAlgEquiv φ⁻¹ :=
  AlgEquiv.ext fun _ ↦ (rfl)

/-- The automorphisms of formal coordinates reverse composition: `σ_(φ ∘ ψ) = σ_ψ ∘ σ_φ`, so
`σ_φ ∘ σ_ψ = σ_(ψ ∘ φ)`. -/
@[simp]
theorem substAlgEquiv_mul (φ ψ : FormalCoordinate R) :
    substAlgEquiv (φ * ψ) = substAlgEquiv ψ * substAlgEquiv φ :=
  AlgEquiv.ext fun f ↦ congr($((substAlgHom'_comp φ ψ).symm) f)

@[simp]
theorem substAlgEquiv_one : substAlgEquiv (1 : FormalCoordinate R) = 1 :=
  AlgEquiv.ext fun f ↦ congr($substAlgHom'_one f)

/-- A formal coordinate is determined by its automorphism of `R⸨X⸩`. -/
theorem substAlgEquiv_injective :
    Function.Injective (substAlgEquiv : FormalCoordinate R → R⸨X⸩ ≃ₐ[R] R⸨X⸩) := fun φ ψ h ↦
  FormalCoordinate.ext <| ofPowerSeries_injective <| by
    rw [← substAlgEquiv_single_one, h, substAlgEquiv_single_one]

/-- The map `φ ↦ σ_φ` from formal coordinates to the opposite of the automorphism group of
`R⸨X⸩`. It is a homomorphism because `σ_(φ ∘ ψ) = σ_ψ ∘ σ_φ`: coordinate changes act on the
right. -/
noncomputable def substAlgEquivHom : FormalCoordinate R →* (R⸨X⸩ ≃ₐ[R] R⸨X⸩)ᵐᵒᵖ where
  toFun φ := .op (substAlgEquiv φ)
  map_one' := by simp
  map_mul' φ ψ := by simp

@[simp]
theorem substAlgEquivHom_apply (φ : FormalCoordinate R) :
    substAlgEquivHom φ = .op (substAlgEquiv φ) :=
  (rfl)

theorem substAlgEquivHom_injective :
    Function.Injective (substAlgEquivHom : FormalCoordinate R →* (R⸨X⸩ ≃ₐ[R] R⸨X⸩)ᵐᵒᵖ) :=
  MulOpposite.op_injective.comp substAlgEquiv_injective

/-- The ring homomorphisms underlying `σ_φ` and its inverse are inverse to each other, so that
`σ_φ`-semilinear equivalences can be formed. -/
instance (φ : FormalCoordinate R) :
    RingHomInvPair ((substAlgEquiv φ).toRingEquiv : R⸨X⸩ →+* R⸨X⸩)
      ((substAlgEquiv φ).toRingEquiv.symm : R⸨X⸩ →+* R⸨X⸩) :=
  .of_ringEquiv _

/-- The ring homomorphisms underlying the inverse of `σ_φ` and `σ_φ` are inverse to each other. -/
instance (φ : FormalCoordinate R) :
    RingHomInvPair ((substAlgEquiv φ).toRingEquiv.symm : R⸨X⸩ →+* R⸨X⸩)
      ((substAlgEquiv φ).toRingEquiv : R⸨X⸩ →+* R⸨X⸩) :=
  .of_ringEquiv_symm _

/-! ### The lattices `X ^ N R⟦X⟧` -/

/-- `σ_φ` maps the lattice `X ^ N R⟦X⟧` into itself, for every integer `N`. -/
theorem substAlgEquiv_mem_lattice {φ : FormalCoordinate R} {N : ℤ} {f : R⸨X⸩}
    (hf : f ∈ lattice R R N) : substAlgEquiv φ f ∈ lattice R R N := by
  obtain ⟨p, rfl⟩ := mem_lattice_iff_exists.mp hf
  -- `σ_φ (Xᴺ p) = φᴺ p (φ) = Xᴺ ((u + ⋯)ᴺ p (φ))`
  refine mem_lattice_iff_exists.mpr
    ⟨↑(φ.isUnit_mk_coeff_succ.unit ^ N) * φ.substAlgEquiv p, ?_⟩
  rw [map_mul, map_mul, substAlgEquiv_single_one_zpow, substAlgEquiv_coe, ← mul_assoc,
    unitCoord, mul_zpow, Units.val_mul, val_unitX_zpow, ← map_zpow, Units.coe_map,
    MonoidHom.coe_ofClass]

/-- `σ_φ (f)` lies in the lattice `X ^ N R⟦X⟧` exactly when `f` does, for every integer `N`. -/
@[simp]
theorem substAlgEquiv_mem_lattice_iff {φ : FormalCoordinate R} {N : ℤ} {f : R⸨X⸩} :
    substAlgEquiv φ f ∈ lattice R R N ↔ f ∈ lattice R R N := by
  refine ⟨fun h ↦ ?_, substAlgEquiv_mem_lattice⟩
  have h' := substAlgEquiv_mem_lattice (φ := φ⁻¹) h
  rwa [← substAlgEquiv_symm, AlgEquiv.symm_apply_apply] at h'

/-- `σ_φ` maps the lattice `X ^ N R⟦X⟧` onto itself, for every integer `N`. -/
theorem image_substAlgEquiv_lattice (φ : FormalCoordinate R) (N : ℤ) :
    substAlgEquiv φ '' (lattice R R N : Set R⸨X⸩) = lattice R R N := by
  ext f
  rw [← AlgEquiv.coe_toEquiv, Equiv.image_eq_preimage_symm]
  simp

/-! ### Naturality and rescaling -/

/-- The automorphisms `σ_φ` are natural in the coefficient ring: applying a ring homomorphism
`g : R →+* S` to the coefficients intertwines `σ_φ` with the automorphism of the base-changed
coordinate. -/
theorem mapRingHom_substAlgEquiv {S : Type*} [CommRing S] (g : R →+* S)
    (φ : FormalCoordinate R) (f : R⸨X⸩) :
    mapRingHom g (substAlgEquiv φ f) =
      substAlgEquiv (FormalCoordinate.map g φ) (mapRingHom g f) := by
  refine congr($(IsLocalization.ringHom_ext (Submonoid.powers (X : R⟦X⟧))
    (j := (mapRingHom g).comp (substAlgEquiv φ : R⸨X⸩ →+* R⸨X⸩))
    (k := (substAlgEquiv (FormalCoordinate.map g φ) : S⸨X⸩ →+* S⸨X⸩).comp (mapRingHom g))
    (RingHom.ext fun p ↦ ?_)) f)
  simp only [RingHom.comp_apply, RingHom.coe_coe, _root_.LaurentSeries.coe_algebraMap,
    substAlgEquiv_coe, mapRingHom_apply, map_ofPowerSeries, FormalCoordinate.map_substAlgEquiv]

/-- The automorphism of the homothety `X ↦ a X` by a unit `a` is the rescaling by `a`. -/
@[simp]
theorem substAlgEquiv_homothety (a : Rˣ) :
    substAlgEquiv (FormalCoordinate.homothety a) = rescale a :=
  AlgEquiv.coe_toAlgHom_injective <| (eq_substAlgEquiv_of_coe fun p ↦ by
    rw [AlgEquiv.coe_toAlgHom, rescale_coe, FormalCoordinate.substAlgEquiv_apply,
      FormalCoordinate.toPowerSeries_homothety, rescale_eq_subst]).symm

/-! ### The composition order for `φ = 2 X` and `ψ = X + X²` -/

section Check

/-- `ψ = X + X²` over `ℚ` is the Laurent series `X + X²`. -/
private theorem coe_toPowerSeries_X_add_X_sq :
    ((FormalCoordinate.ofStrictCoeffs (Pi.single 1 1) : FormalCoordinate ℚ).toPowerSeries :
      ℚ⸨X⸩) = single 1 1 + single 2 1 := by
  rw [FormalCoordinate.toPowerSeries_ofStrictCoeffs_single, map_add, map_mul, map_pow,
    ofPowerSeries_X, ofPowerSeries_C, HahnSeries.C_apply, single_pow, single_mul_single]
  simp

/-- For `φ = 2 X` and `ψ = X + X²`: `σ_φ (σ_ψ X) = (ψ ∘ φ) (X) = 2 X + 4 X²`. -/
private theorem substAlgEquiv_two_X_mul_X_add_X_sq :
    (substAlgEquiv (FormalCoordinate.homothety (Units.mk0 (2 : ℚ) two_ne_zero)) *
      substAlgEquiv (FormalCoordinate.ofStrictCoeffs (Pi.single 1 1)) : ℚ⸨X⸩ ≃ₐ[ℚ] ℚ⸨X⸩)
      (single 1 1) = single 1 2 + single 2 4 := by
  rw [AlgEquiv.mul_apply, substAlgEquiv_single_one, coe_toPowerSeries_X_add_X_sq,
    substAlgEquiv_homothety, map_add, rescale_single, rescale_single]
  norm_num

/-- For `φ = 2 X` and `ψ = X + X²`: `σ_ψ (σ_φ X) = (φ ∘ ψ) (X) = 2 X + 2 X²`. -/
private theorem substAlgEquiv_X_add_X_sq_mul_two_X :
    (substAlgEquiv (FormalCoordinate.ofStrictCoeffs (Pi.single 1 1)) *
      substAlgEquiv (FormalCoordinate.homothety (Units.mk0 (2 : ℚ) two_ne_zero)) :
      ℚ⸨X⸩ ≃ₐ[ℚ] ℚ⸨X⸩) (single 1 1) = single 1 2 + single 2 2 := by
  rw [AlgEquiv.mul_apply, substAlgEquiv_homothety, rescale_single, substAlgEquiv_single,
    zpow_one, zpow_one, IsUnit.unit_spec, coe_toPowerSeries_X_add_X_sq, mul_add,
    HahnSeries.C_apply, single_mul_single, single_mul_single]
  norm_num

/-- `σ_φ ∘ σ_ψ` is the automorphism of `ψ ∘ φ = ψ * φ`: for `φ = 2 X` and `ψ = X + X²`,
`ψ (φ (X)) = 2 X + 4 X²`. -/
example : substAlgEquiv (FormalCoordinate.ofStrictCoeffs (Pi.single 1 1) *
      FormalCoordinate.homothety (Units.mk0 (2 : ℚ) two_ne_zero)) (single 1 1) =
    single 1 2 + single 2 4 := by
  rw [substAlgEquiv_mul, substAlgEquiv_two_X_mul_X_add_X_sq]

/-- The two orders differ, in the coefficient of `X²`: `σ_φ ∘ σ_ψ ≠ σ_ψ ∘ σ_φ` for `φ = 2 X` and
`ψ = X + X²`. -/
example : (substAlgEquiv (FormalCoordinate.homothety (Units.mk0 (2 : ℚ) two_ne_zero)) *
      substAlgEquiv (FormalCoordinate.ofStrictCoeffs (Pi.single 1 1)) : ℚ⸨X⸩ ≃ₐ[ℚ] ℚ⸨X⸩) ≠
    substAlgEquiv (FormalCoordinate.ofStrictCoeffs (Pi.single 1 1)) *
      substAlgEquiv (FormalCoordinate.homothety (Units.mk0 (2 : ℚ) two_ne_zero)) := by
  intro h
  have h₂ := congr(($h (single 1 1)).coeff 2)
  rw [substAlgEquiv_two_X_mul_X_add_X_sq, substAlgEquiv_X_add_X_sq_mul_two_X] at h₂
  norm_num [coeff_single] at h₂

end Check

end LaurentSeries

end TauCeti
