/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Derivative
public import TauCeti.RingTheory.LaurentSeries.Rescale
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic

/-!
# Substituting formal coordinates into Laurent series over a commutative ring

Let `R` be a commutative ring and `φ = u X + ⋯` a formal coordinate over `R`, so that `u` is a
unit (`TauCeti.FormalCoordinate R`). Then `φ = X v` for a unit power series `v`, so `φ` is a unit
of `R⸨X⸩`. Since `R⸨X⸩` is the localization of `R⟦X⟧` at the powers of `X`, the substitution
automorphism `f ↦ f (φ)` of `R⟦X⟧` extends uniquely to an `R`-algebra automorphism
`TauCeti.LaurentSeries.substAlgEquiv φ` of `R⸨X⸩`. No hypothesis on `R` is needed: it may have
zero divisors, nilpotents or positive characteristic.

Substitution is contravariant, `σ_(φ ∘ ψ) = σ_ψ ∘ σ_φ`, where `φ * ψ = φ ∘ ψ` in
`FormalCoordinate R`; so pulling back Laurent series is a right action of the coordinate group,
and `φ ↦ σ_φ` is an injective homomorphism to the opposite of the automorphism group. It is
natural in the coefficients: a ring homomorphism `R →+* S` applied to every coefficient
intertwines `σ_φ` with the substitution of the base-changed coordinate. The homothety `X ↦ a X`
by a unit `a` gives the rescaling `TauCeti.LaurentSeries.rescale a`.

Each `σ_φ` preserves the power series and, by
`TauCeti.RingTheory.LaurentSeries.Substitution.Lattice`, every lattice `Xᵃ R⟦X⟧`, so it is a
homeomorphism for the `X`-adic topology. Formal differentiation obeys the chain rule
`D(f (φ)) = (Df)(φ) Dφ`, so that `f dX ↦ f (φ) dφ` is the pullback of differential forms. Residues
are invariant: `Res(f (φ) dφ) = Res(f dX)`. Over a field of characteristic zero this follows from
`Res(dg) = 0`, since `φ⁻ⁿ dφ` is exact for `n ≠ 1`. Over an arbitrary ring, writing `φ = X v`, it
rests on the identity `coeff n (v⁻¹ ^ n) + coeff (n - 1) (v⁻¹ ^ (n + 1) v') = 0` for `n ≥ 1`,
which holds over every commutative ring (`TauCeti.RingTheory.PowerSeries.Derivative`).

Over a field these automorphisms agree with the substitution `TauCeti.LaurentSeries.substAlgHom`
of nonzero series of positive order (`TauCeti.LaurentSeries.coe_substAlgEquiv`).

The final examples check the composition order for `φ = 2 X` and `ψ = X + X²` over `ℚ`:
`σ_φ (σ_ψ X) = 2 X + 4 X²` while `σ_ψ (σ_φ X) = 2 X + 2 X²`.

## Main definitions

* `TauCeti.LaurentSeries.substAlgEquiv φ`: the substitution automorphism `f ↦ f (φ)` of `R⸨X⸩`.
* `TauCeti.LaurentSeries.substAlgEquivHom`: `φ ↦ σ_φ` as a homomorphism to the opposite of the
  automorphism group.

## Main results

* `TauCeti.LaurentSeries.substAlgEquiv_coe`: on power series it is
  `TauCeti.FormalCoordinate.substAlgEquiv`.
* `TauCeti.LaurentSeries.algHom_eq_substAlgEquiv`: it is the only `R`-algebra endomorphism of
  `R⸨X⸩` extending substitution of power series.
* `TauCeti.LaurentSeries.substAlgEquiv_single`: `σ_φ (a X ^ n) = a φ ^ n` for every integer `n`.
* `TauCeti.LaurentSeries.substAlgEquiv_mul`: `σ_(φ ∘ ψ) = σ_ψ ∘ σ_φ`.
* `TauCeti.LaurentSeries.mapRingHom_substAlgEquiv`: naturality in the coefficient ring.
* `TauCeti.LaurentSeries.substAlgEquiv_homothety`: the homothety by `a` gives rescaling by `a`.
* `TauCeti.LaurentSeries.derivative_substAlgEquiv`: the chain rule.
* `TauCeti.LaurentSeries.coeff_neg_one_substAlgEquiv_mul_derivative`: invariance of the residue.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §3.5, for the group of coordinate
  changes of the formal disc and its action on Laurent series and differential forms.
-/

public section

open scoped LaurentSeries PowerSeries
open HahnSeries PowerSeries

namespace TauCeti.LaurentSeries

variable {R : Type*} [CommRing R]

/-- A formal coordinate is a unit of the ring of Laurent series. -/
theorem isUnit_coe_toPowerSeries (φ : FormalCoordinate R) : IsUnit (φ.toPowerSeries : R⸨X⸩) := by
  obtain ⟨v, hv⟩ := φ.exists_unit_toPowerSeries_eq_X_mul
  rw [hv, PowerSeries.coe_mul]
  refine IsUnit.mul ?_ (v.isUnit.map _)
  simpa using IsLocalization.map_units R⸨X⸩ (⟨X, Submonoid.mem_powers X⟩ :
    Submonoid.powers (X : R⟦X⟧))

/-- Substituting a formal coordinate into `X ^ n` gives a unit of `R⸨X⸩`. -/
private theorem isUnit_coe_substAlgEquiv_X_pow (φ : FormalCoordinate R) (n : ℕ) :
    IsUnit ((φ.substAlgEquiv (X ^ n) : R⟦X⟧) : R⸨X⸩) := by
  rw [map_pow, FormalCoordinate.substAlgEquiv_X, PowerSeries.coe_pow]
  exact (isUnit_coe_toPowerSeries φ).pow n

/-- Substitution of a formal coordinate into power series, followed by the inclusion into Laurent
series, extended to the localization `R⸨X⸩` of `R⟦X⟧` at the powers of `X`. -/
private noncomputable def substAlgHomAux (φ : FormalCoordinate R) : R⸨X⸩ →ₐ[R] R⸨X⸩ :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (X : R⟦X⟧))
    (f := (IsScalarTower.toAlgHom R R⟦X⟧ R⸨X⸩).comp φ.substAlgEquiv.toAlgHom) (by
      rintro ⟨_, n, rfl⟩
      rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', _root_.LaurentSeries.coe_algebraMap,
        AlgEquiv.toAlgHom_apply]
      exact isUnit_coe_substAlgEquiv_X_pow φ n)

private theorem substAlgHomAux_coe (φ : FormalCoordinate R) (f : R⟦X⟧) :
    substAlgHomAux φ (f : R⸨X⸩) = ((φ.substAlgEquiv f : R⟦X⟧) : R⸨X⸩) := by
  rw [substAlgHomAux, IsLocalization.liftAlgHom_apply, ← _root_.LaurentSeries.coe_algebraMap,
    IsLocalization.lift_eq]
  simp

private theorem substAlgHomAux_comp (φ ψ : FormalCoordinate R) :
    (substAlgHomAux ψ).comp (substAlgHomAux φ) = substAlgHomAux (φ * ψ) :=
  algHom_ext fun p ↦ by
    simp [substAlgHomAux_coe, FormalCoordinate.substAlgEquiv_mul, AlgEquiv.mul_apply]

private theorem substAlgHomAux_one : substAlgHomAux (1 : FormalCoordinate R) = AlgHom.id R R⸨X⸩ :=
  algHom_ext fun p ↦ by simp [substAlgHomAux_coe]

/-- The substitution automorphism `σ_φ : f ↦ f (φ)` of `R⸨X⸩` attached to a formal coordinate `φ`
over a commutative ring, with inverse the substitution of the compositional inverse `φ⁻¹`. It
extends the substitution automorphism `TauCeti.FormalCoordinate.substAlgEquiv` of `R⟦X⟧`. -/
noncomputable def substAlgEquiv (φ : FormalCoordinate R) : R⸨X⸩ ≃ₐ[R] R⸨X⸩ :=
  .ofAlgHom (substAlgHomAux φ) (substAlgHomAux φ⁻¹)
    (by rw [substAlgHomAux_comp, inv_mul_cancel, substAlgHomAux_one])
    (by rw [substAlgHomAux_comp, mul_inv_cancel, substAlgHomAux_one])

/-- On power series, the substitution automorphism of `R⸨X⸩` is that of `R⟦X⟧`. -/
@[simp]
theorem substAlgEquiv_coe (φ : FormalCoordinate R) (f : R⟦X⟧) :
    substAlgEquiv φ (f : R⸨X⸩) = ((φ.substAlgEquiv f : R⟦X⟧) : R⸨X⸩) :=
  substAlgHomAux_coe φ f

/-- Substitution sends the variable `X = single 1 1` to `φ`. -/
@[simp]
theorem substAlgEquiv_single_one (φ : FormalCoordinate R) :
    substAlgEquiv φ (single 1 1) = (φ.toPowerSeries : R⸨X⸩) := by
  rw [← PowerSeries.coe_X, substAlgEquiv_coe, FormalCoordinate.substAlgEquiv_X]

/-- **Uniqueness of the extension.** An `R`-algebra endomorphism of `R⸨X⸩` that substitutes `φ`
into power series is the substitution automorphism `σ_φ`. -/
theorem algHom_eq_substAlgEquiv (φ : FormalCoordinate R) (σ : R⸨X⸩ →ₐ[R] R⸨X⸩)
    (h : ∀ f : R⟦X⟧, σ f = ((φ.substAlgEquiv f : R⟦X⟧) : R⸨X⸩)) :
    σ = (substAlgEquiv φ).toAlgHom :=
  algHom_ext fun f ↦ by simp [h]

/-- Substitution fixes the constants, in the simp-normal form `single 0 a` of `C a`. -/
@[simp]
theorem substAlgEquiv_single_zero (φ : FormalCoordinate R) (a : R) :
    substAlgEquiv φ (single 0 a) = single 0 a := by
  rw [← HahnSeries.C_apply, ← ofPowerSeries_C, substAlgEquiv_coe, ← PowerSeries.algebraMap_eq,
    AlgEquiv.commutes]

/-- Write `φ = X v` with `v` a unit power series. Substitution sends the monomial `a X ^ n`, for
every integer `n`, to `a φ ^ n = a X ^ n v ^ n`. -/
theorem substAlgEquiv_single_of_eq_X_mul (φ : FormalCoordinate R) {v : R⟦X⟧ˣ}
    (hv : φ.toPowerSeries = X * (v : R⟦X⟧)) (n : ℤ) (a : R) :
    substAlgEquiv φ (single n a) = single n a * ((↑(v ^ n) : R⟦X⟧) : R⸨X⸩) := by
  have hnat (m : ℕ) :
      substAlgEquiv φ (single (m : ℤ) 1) = single (m : ℤ) 1 * ((↑(v ^ m) : R⟦X⟧) : R⸨X⸩) := by
    have hX (m : ℕ) : (single (m : ℤ) 1 : R⸨X⸩) = single 1 1 ^ m := by simp [single_pow]
    rw [hX, map_pow, substAlgEquiv_single_one, hv]
    simp [mul_pow]
  have hone : substAlgEquiv φ (single n 1) = single n 1 * ((↑(v ^ n) : R⟦X⟧) : R⸨X⸩) := by
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · simpa using hnat m
    -- `σ_φ (X ^ (-m))` and `X ^ (-m) v ^ (-m)` are both inverse to `σ_φ (X ^ m)`
    have h₁ : substAlgEquiv φ (single (-(m : ℤ)) 1) * substAlgEquiv φ (single (m : ℤ) 1) = 1 := by
      rw [← map_mul, single_mul_single, neg_add_cancel, one_mul, single_zero_one, map_one]
    have h₂ : single (-(m : ℤ)) 1 * ((↑(v ^ (-(m : ℤ))) : R⟦X⟧) : R⸨X⸩) *
        substAlgEquiv φ (single (m : ℤ) 1) = 1 := by
      have hv : v ^ (-(m : ℤ)) * v ^ m = 1 := by group
      rw [hnat, mul_mul_mul_comm, single_mul_single, ← PowerSeries.coe_mul, ← Units.val_mul, hv]
      simp
    exact (IsUnit.of_mul_eq_one_right _ h₁).mul_left_injective (h₁.trans h₂.symm)
  have hC : (single n a : R⸨X⸩) = single 0 a * single n 1 := by
    rw [single_mul_single, zero_add, mul_one]
  rw [hC, map_mul, substAlgEquiv_single_zero, hone, mul_assoc]

/-- Substitution sends the monomial `a X ^ n`, for every integer `n`, to `a φ ^ n`, a power of the
unit `φ` of `R⸨X⸩`. -/
theorem substAlgEquiv_single (φ : FormalCoordinate R) (n : ℤ) (a : R) :
    substAlgEquiv φ (single n a) =
      (HahnSeries.C a : R⸨X⸩) * (((isUnit_coe_toPowerSeries φ).unit ^ n : R⸨X⸩ˣ) : R⸨X⸩) := by
  have hx : Units.map (substAlgEquiv φ : R⸨X⸩ →* R⸨X⸩) unitX = (isUnit_coe_toPowerSeries φ).unit :=
    Units.ext <| by
      rw [Units.coe_map, MonoidHom.coe_ofClass, val_unitX, substAlgEquiv_single_one,
        IsUnit.unit_spec]
  have hC : (single n a : R⸨X⸩) = single 0 a * single n 1 := by
    rw [single_mul_single, zero_add, mul_one]
  rw [hC, map_mul, substAlgEquiv_single_zero, ← val_unitX_zpow, ← hx, ← map_zpow, Units.coe_map,
    MonoidHom.coe_ofClass, HahnSeries.C_apply]

/-- Substitution automorphisms reverse composition: `σ_(φ ∘ ψ) = σ_ψ ∘ σ_φ`. -/
@[simp]
theorem substAlgEquiv_mul (φ ψ : FormalCoordinate R) :
    substAlgEquiv (φ * ψ) = substAlgEquiv ψ * substAlgEquiv φ :=
  AlgEquiv.ext fun f ↦ by
    rw [AlgEquiv.mul_apply]
    exact (congr($(substAlgHomAux_comp φ ψ) f)).symm

/-- Substituting the identity coordinate `X` is the identity. -/
@[simp]
theorem substAlgEquiv_one : substAlgEquiv (1 : FormalCoordinate R) = 1 :=
  AlgEquiv.ext fun f ↦ congr($(substAlgHomAux_one) f)

/-- The inverse of `σ_φ` is the substitution of the compositional inverse `φ⁻¹`. -/
@[simp]
theorem substAlgEquiv_symm (φ : FormalCoordinate R) :
    (substAlgEquiv φ).symm = substAlgEquiv φ⁻¹ :=
  AlgEquiv.ext fun _ ↦ rfl

/-- The map `φ ↦ σ_φ` from formal coordinates to the opposite of the automorphism group of
`R⸨X⸩`. It is a homomorphism because `σ_(φ ∘ ψ) = σ_ψ ∘ σ_φ`. -/
noncomputable def substAlgEquivHom : FormalCoordinate R →* (R⸨X⸩ ≃ₐ[R] R⸨X⸩)ᵐᵒᵖ where
  toFun φ := .op (substAlgEquiv φ)
  map_one' := by simp
  map_mul' φ ψ := by simp

@[simp]
theorem substAlgEquivHom_apply (φ : FormalCoordinate R) :
    substAlgEquivHom φ = .op (substAlgEquiv φ) := (rfl)

/-- A formal coordinate is determined by its substitution automorphism of `R⸨X⸩`. -/
theorem substAlgEquiv_injective :
    Function.Injective (substAlgEquiv : FormalCoordinate R → R⸨X⸩ ≃ₐ[R] R⸨X⸩) := fun φ ψ h ↦
  FormalCoordinate.ext <| HahnSeries.ofPowerSeries_injective <| by
    rw [← substAlgEquiv_single_one, h, substAlgEquiv_single_one]

/-- The homomorphism `φ ↦ σ_φ` is injective. -/
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

/-- Substitution automorphisms are natural in the coefficient ring: applying a ring homomorphism
`σ : R →+* S` to the coefficients intertwines `σ_φ` with the substitution automorphism of the
base-changed coordinate. -/
theorem mapRingHom_substAlgEquiv {S : Type*} [CommRing S] (σ : R →+* S) (φ : FormalCoordinate R)
    (f : R⸨X⸩) :
    mapRingHom σ (substAlgEquiv φ f) =
      substAlgEquiv (FormalCoordinate.map σ φ) (mapRingHom σ f) := by
  have h : (mapRingHom σ).comp (substAlgEquiv φ : R⸨X⸩ →+* R⸨X⸩) =
      (substAlgEquiv (FormalCoordinate.map σ φ) : S⸨X⸩ →+* S⸨X⸩).comp (mapRingHom σ) :=
    ringHom_ext fun p ↦ by
      simp only [RingHom.comp_apply, RingHom.coe_coe, substAlgEquiv_coe, mapRingHom_apply,
        map_ofPowerSeries, FormalCoordinate.map_substAlgEquiv]
  exact congr($h f)

/-- The substitution automorphism of the homothety `X ↦ a X` by a unit `a` is the rescaling by
`a`. -/
@[simp]
theorem substAlgEquiv_homothety (a : Rˣ) :
    substAlgEquiv (FormalCoordinate.homothety a) = rescale a :=
  AlgEquiv.coe_toAlgHom_injective (algHom_eq_substAlgEquiv _ _ fun p ↦ by
    rw [AlgEquiv.coe_toAlgHom, rescale_coe, FormalCoordinate.substAlgEquiv_apply,
      FormalCoordinate.toPowerSeries_homothety, rescale_eq_subst]).symm

/-! ### Differentiation and residues -/

/-- **Chain rule for substitution of a formal coordinate.** The derivative of `f (φ)` is
`(Df)(φ) * Dφ`, over every commutative ring. -/
theorem derivative_substAlgEquiv (φ : FormalCoordinate R) (f : R⸨X⸩) :
    _root_.LaurentSeries.derivative R (substAlgEquiv φ f) =
      substAlgEquiv φ (_root_.LaurentSeries.derivative R f) *
        _root_.LaurentSeries.derivative R (φ.toPowerSeries : R⸨X⸩) := by
  simp only [← laurentSeriesDerivation_apply]
  set D := laurentSeriesDerivation R
  set σ := substAlgEquiv φ
  -- the chain rule for power series
  have hcoe (p : R⟦X⟧) : D (σ p) = σ (D p) * D φ.toPowerSeries := by
    simp only [D, σ, laurentSeriesDerivation_apply, substAlgEquiv_coe,
      ← PowerSeries.coe_derivative, FormalCoordinate.substAlgEquiv_apply,
      derivative_subst φ.hasSubst, PowerSeries.coe_mul]
  -- write `f * x = p` with `x = X ^ n` and `p` a power series, and cancel the unit `σ x`
  obtain ⟨⟨p, _, n, rfl⟩, hp⟩ := IsLocalization.surj (Submonoid.powers (X : R⟦X⟧)) f
  simp only [_root_.LaurentSeries.coe_algebraMap] at hp
  set x : R⸨X⸩ := ((X ^ n : R⟦X⟧) : R⸨X⸩)
  have hx : IsUnit (σ x) := by
    rw [substAlgEquiv_coe]
    exact isUnit_coe_substAlgEquiv_X_pow φ n
  have h₁ : D (σ (f * x)) = D (σ p) := by rw [hp]
  have h₂ : σ (D (f * x)) = σ (D p) := by rw [hp]
  rw [map_mul, D.leibniz, hcoe, hcoe, smul_eq_mul, smul_eq_mul] at h₁
  rw [D.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul] at h₂
  refine hx.mul_left_cancel ?_
  linear_combination h₁ - D φ.toPowerSeries * h₂

/-- The residue of `φ ^ (-(k + 1)) dφ` is `1` for `k = 0` and `0` otherwise, over every
commutative ring. -/
private theorem coeff_neg_one_substAlgEquiv_single_mul_derivative (φ : FormalCoordinate R)
    (k : ℕ) (c : R) :
    (substAlgEquiv φ (single (-((k + 1 : ℕ) : ℤ)) c) *
        _root_.LaurentSeries.derivative R (φ.toPowerSeries : R⸨X⸩)).coeff (-1) =
      if k = 0 then c else 0 := by
  obtain ⟨v, hv⟩ := φ.exists_unit_toPowerSeries_eq_X_mul
  have hpow : (↑(v ^ (-((k + 1 : ℕ) : ℤ))) : R⟦X⟧) = (↑v⁻¹ : R⟦X⟧) ^ (k + 1) := by
    rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
  -- `φ ^ (-(k + 1)) φ' = X ^ (-(k + 1)) (v ^ (-k) + X v ^ (-(k + 1)) v')`
  have hφ' : (↑v⁻¹ : R⟦X⟧) ^ (k + 1) * d⁄dX (X * (v : R⟦X⟧)) =
      (↑v⁻¹ : R⟦X⟧) ^ k + X * ((↑v⁻¹ : R⟦X⟧) ^ (k + 1) * d⁄dX (v : R⟦X⟧)) := by
    have hv₁ : (↑v⁻¹ : R⟦X⟧) * v = 1 := Units.inv_mul v
    rw [Derivation.leibniz, derivative_X, smul_eq_mul, smul_eq_mul, mul_one, pow_succ]
    linear_combination (↑v⁻¹ : R⟦X⟧) ^ k * hv₁
  have hprod : substAlgEquiv φ (single (-((k + 1 : ℕ) : ℤ)) c) *
      _root_.LaurentSeries.derivative R (φ.toPowerSeries : R⸨X⸩) =
      single (-((k + 1 : ℕ) : ℤ)) c * (((↑v⁻¹ : R⟦X⟧) ^ k +
        X * ((↑v⁻¹ : R⟦X⟧) ^ (k + 1) * d⁄dX (v : R⟦X⟧)) : R⟦X⟧) : R⸨X⸩) := by
    rw [substAlgEquiv_single_of_eq_X_mul φ hv, hv, ← hφ', ← hpow]
    simp only [mul_assoc, PowerSeries.coe_mul, PowerSeries.coe_derivative]
  rw [hprod, show (-1 : ℤ) = (k : ℤ) + -((k + 1 : ℕ) : ℤ) by push_cast; ring,
    coeff_single_mul_add, _root_.LaurentSeries.coeff_coe_powerSeries, map_add]
  rcases k with _ | n
  · simp
  · -- the universal coefficient identity for negative powers of a unit power series
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    have h :=
      nsmul_coeff_val_inv_pow_succ_add_coeff_X_mul_val_inv_pow_add_two_mul_derivative_eq_zero v 1 n
    rw [one_smul, one_mul] at h
    exact (congrArg (c * ·) h).trans (mul_zero c)

/-- **Invariance of the residue under a formal coordinate change.** Over every commutative ring,
the residue of `f (φ) dφ` is that of `f dX`: the coefficient of `X⁻¹` in `f (φ) * Dφ` is the
coefficient of `X⁻¹` in `f`. -/
theorem coeff_neg_one_substAlgEquiv_mul_derivative (φ : FormalCoordinate R) (f : R⸨X⸩) :
    (substAlgEquiv φ f * _root_.LaurentSeries.derivative R (φ.toPowerSeries : R⸨X⸩)).coeff (-1) =
      f.coeff (-1) := by
  -- Induction on the pole order `d` of `f`, removing the leading monomial at each step.
  suffices key : ∀ d : ℕ, ∀ f : R⸨X⸩, (∀ n < -(d : ℤ), f.coeff n = 0) →
      (substAlgEquiv φ f * _root_.LaurentSeries.derivative R (φ.toPowerSeries : R⸨X⸩)).coeff
        (-1) = f.coeff (-1) from
    key (-f.order).toNat f fun n hn ↦ coeff_eq_zero_of_lt_order (by omega)
  intro d
  induction d with
  | zero =>
    -- both sides vanish on power series
    intro f hf
    obtain ⟨p, rfl⟩ := mem_range_ofPowerSeries_iff.mpr fun n hn ↦ hf n (by omega)
    rw [substAlgEquiv_coe, ← PowerSeries.coe_derivative, ← PowerSeries.coe_mul,
      PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    simp
  | succ d ih =>
    intro f hf
    set s : R⸨X⸩ := single (-((d + 1 : ℕ) : ℤ)) (f.coeff (-((d + 1 : ℕ) : ℤ)))
    have hs : ∀ n < -(d : ℤ), (f - s).coeff n = 0 := fun n hn ↦ by
      rw [coeff_sub, coeff_single]
      split_ifs with h
      · rw [h, sub_self]
      · rw [hf n (by omega), sub_zero]
    calc (substAlgEquiv φ f *
          _root_.LaurentSeries.derivative R (φ.toPowerSeries : R⸨X⸩)).coeff (-1)
        = (substAlgEquiv φ (f - s) *
              _root_.LaurentSeries.derivative R (φ.toPowerSeries : R⸨X⸩)).coeff (-1) +
            (substAlgEquiv φ s *
              _root_.LaurentSeries.derivative R (φ.toPowerSeries : R⸨X⸩)).coeff (-1) := by
          rw [map_sub, sub_mul, coeff_sub, sub_add_cancel]
      _ = (f - s).coeff (-1) + s.coeff (-1) := by
          rw [ih _ hs, coeff_neg_one_substAlgEquiv_single_mul_derivative, coeff_single]
          split_ifs <;> first | rfl | omega
      _ = f.coeff (-1) := by rw [coeff_sub, sub_add_cancel]

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

end TauCeti.LaurentSeries
