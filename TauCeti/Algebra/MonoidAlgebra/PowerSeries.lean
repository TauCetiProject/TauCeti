/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Power series over a monoid algebra

For a commutative semiring `R`, an `R`-algebra `A` and a monoid `M`, the monoid algebra of `M`
over the power-series ring `A⟦X⟧` maps to the power-series ring over the monoid algebra `A[M]` by
collecting, for each `n`, the coefficients of `Xⁿ` of the monomial coefficients:

```text
∑ₘ φₘ · m  ↦  ∑ₙ (∑ₘ (coeff n φₘ) · m) Xⁿ.
```

This is an `R`-algebra homomorphism `MonoidAlgebra.toPowerSeries`, characterised by
`coeff_coeff_toPowerSeries`: the coefficient at `m` of the coefficient of `Xⁿ` of the image is
the coefficient of `Xⁿ` of the coefficient at `m` of the argument. It is always injective, and
for a finite monoid `M` it is an isomorphism `MonoidAlgebra.powerSeriesAlgEquiv`. For an
infinite `M` and a nontrivial `A` it is not surjective: a power series whose coefficients are
supported on infinitely many elements of `M` altogether is not in the image, since an element of
`A⟦X⟧[M]` involves only finitely many elements of `M`.

The finite case writes the ring `ℤ_p⟦X⟧[C]` attached to a finite group `C` as the power-series
ring `ℤ_p[C]⟦X⟧` over the group ring `ℤ_p[C]`; this is how the completed group algebra of a
product `C × ℤ_p` becomes a power-series ring over `ℤ_p[C]`.

## Main declarations

* `MonoidAlgebra.toPowerSeries R A M`: the `R`-algebra homomorphism
  `A⟦X⟧[M] →ₐ[R] A[M]⟦X⟧`, with `coeff_coeff_toPowerSeries` and `toPowerSeries_injective`.
* `MonoidAlgebra.powerSeriesAlgEquiv R A M`: the isomorphism `A⟦X⟧[M] ≃ₐ[R] A[M]⟦X⟧`
  for finite `M`.
-/

public section

namespace MonoidAlgebra

open PowerSeries

variable (R : Type*) [CommSemiring R] (A : Type*) [Semiring A] [Algebra R A]
  (M : Type*) [Monoid M]

/-- The coefficient of `Xⁿ` in `A⟦X⟧` placed at `1 ∈ M`, so `single 1 (coeff n φ)`, commutes with
every monomial `single m 1` read as a constant power series. -/
private theorem commute_mapAlgHom_singleOneAlgHom_C_single (φ : PowerSeries A) (m : M) :
    Commute (PowerSeries.mapAlgHom (singleOneAlgHom : A →ₐ[R] MonoidAlgebra A M) φ)
      (PowerSeries.C (single m (1 : A))) := by
  refine PowerSeries.ext fun n ↦ ?_
  simp only [PowerSeries.mapAlgHom_apply, PowerSeries.coeff_mul_C, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_map, AlgHom.coe_toRingHom, singleOneAlgHom_apply, single_mul_single, one_mul,
    mul_one]

/-- The `R`-algebra homomorphism `A⟦X⟧[M] →ₐ[R] A[M]⟦X⟧` collecting the coefficients of `Xⁿ`:
the coefficient at `m` of the coefficient of `Xⁿ` of the image of `x` is the coefficient of `Xⁿ`
of the coefficient at `m` of `x` (`coeff_coeff_toPowerSeries`). It is injective, and bijective
for finite `M` (`powerSeriesAlgEquiv`). -/
noncomputable def toPowerSeries :
    MonoidAlgebra (PowerSeries A) M →ₐ[R] PowerSeries (MonoidAlgebra A M) :=
  liftNCAlgHom (PowerSeries.mapAlgHom (singleOneAlgHom : A →ₐ[R] MonoidAlgebra A M))
    ((PowerSeries.C : MonoidAlgebra A M →+* PowerSeries (MonoidAlgebra A M)).toMonoidHom.comp
      (of A M))
    (commute_mapAlgHom_singleOneAlgHom_C_single R A M)

/-- On the monomial `φ · m`, the map to power series over `A[M]` is the power series `φ` with
coefficients placed at `1`, times the constant `m`. -/
theorem toPowerSeries_single (m : M) (φ : PowerSeries A) :
    toPowerSeries R A M (single m φ) =
      PowerSeries.mapAlgHom (singleOneAlgHom : A →ₐ[R] MonoidAlgebra A M) φ *
        PowerSeries.C (single m (1 : A)) := by
  simp only [toPowerSeries, coe_liftNCAlgHom, liftNC_single, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, of_apply, AddMonoidHom.coe_coe]

/-- The characteristic property of `toPowerSeries`: the coefficient at `m` of the coefficient of
`Xⁿ` of the image is the coefficient of `Xⁿ` of the coefficient at `m`. -/
@[simp]
theorem coeff_coeff_toPowerSeries (x : MonoidAlgebra (PowerSeries A) M) (n : ℕ) (m : M) :
    (PowerSeries.coeff n (toPowerSeries R A M x)).coeff m = PowerSeries.coeff n (x.coeff m) := by
  classical
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single m' φ =>
    rw [toPowerSeries_single, PowerSeries.coeff_mul_C, PowerSeries.mapAlgHom_apply,
      PowerSeries.coeff_map, AlgHom.coe_toRingHom, singleOneAlgHom_apply, single_mul_single,
      one_mul]
    simp only [coeff_single, Finsupp.single_apply]
    split_ifs <;> simp

/-- The map to power series over `A[M]` sends the constant monomial `a · m` to the constant power
series `a · m`. -/
@[simp]
theorem toPowerSeries_single_C (m : M) (a : A) :
    toPowerSeries R A M (single m (PowerSeries.C a)) = PowerSeries.C (single m a) := by
  rw [toPowerSeries_single, PowerSeries.mapAlgHom_apply, PowerSeries.map_C, AlgHom.coe_toRingHom,
    singleOneAlgHom_apply, ← map_mul, single_mul_single, one_mul, mul_one]

/-- The map to power series over `A[M]` sends `X`, placed at `1 ∈ M`, to `X`. -/
@[simp]
theorem toPowerSeries_single_one_X :
    toPowerSeries R A M (single 1 PowerSeries.X) = PowerSeries.X := by
  rw [toPowerSeries_single, PowerSeries.mapAlgHom_apply, PowerSeries.map_X, ← MonoidAlgebra.one_def,
    map_one, mul_one]

/-- The map `A⟦X⟧[M] → A[M]⟦X⟧` is injective, for every monoid `M`: it determines all the
coefficients of its argument (`coeff_coeff_toPowerSeries`). -/
theorem toPowerSeries_injective : Function.Injective (toPowerSeries R A M) := fun x y h ↦ by
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun m ↦ PowerSeries.ext fun n ↦ ?_)
  rw [← coeff_coeff_toPowerSeries R A M x, ← coeff_coeff_toPowerSeries R A M y, h]

/-- The map `A⟦X⟧[M] → A[M]⟦X⟧` is surjective when `M` is finite: a power series over `A[M]` is
the image of the monoid algebra element whose coefficient at `m` is the power series of the
coefficients at `m`, which is finitely supported in `m` because `M` is finite. -/
theorem toPowerSeries_surjective [Finite M] : Function.Surjective (toPowerSeries R A M) :=
  fun ψ ↦ ⟨ofCoeff (Finsupp.equivFunOnFinite.symm fun m ↦
    PowerSeries.mk fun n ↦ (PowerSeries.coeff n ψ).coeff m), PowerSeries.ext fun n ↦
      MonoidAlgebra.coeff_injective (Finsupp.ext fun m ↦ by simp)⟩

/-- **Power series over the monoid algebra of a finite monoid.** For a finite monoid `M`, the
monoid algebra of `M` over `A⟦X⟧` is the power-series ring over the monoid algebra `A[M]`, by
collecting the coefficients of `Xⁿ` (`toPowerSeries`). -/
noncomputable def powerSeriesAlgEquiv [Finite M] :
    MonoidAlgebra (PowerSeries A) M ≃ₐ[R] PowerSeries (MonoidAlgebra A M) :=
  AlgEquiv.ofBijective (toPowerSeries R A M)
    ⟨toPowerSeries_injective R A M, toPowerSeries_surjective R A M⟩

variable [Finite M]

@[simp]
theorem coe_powerSeriesAlgEquiv : ⇑(powerSeriesAlgEquiv R A M) = toPowerSeries R A M := (rfl)

/-- The inverse of `powerSeriesAlgEquiv` reads the coefficients back: the coefficient of `Xⁿ` of
the coefficient at `m` of the inverse image of `ψ` is the coefficient at `m` of the coefficient of
`Xⁿ` of `ψ`. -/
@[simp]
theorem coeff_coeff_powerSeriesAlgEquiv_symm (ψ : PowerSeries (MonoidAlgebra A M)) (m : M)
    (n : ℕ) :
    PowerSeries.coeff n (((powerSeriesAlgEquiv R A M).symm ψ).coeff m) =
      (PowerSeries.coeff n ψ).coeff m := by
  rw [← coeff_coeff_toPowerSeries R A M, ← coe_powerSeriesAlgEquiv, AlgEquiv.apply_symm_apply]

/-- The inverse of `powerSeriesAlgEquiv` sends the constant power series `a · m` to the constant
monomial `a · m`. -/
@[simp]
theorem powerSeriesAlgEquiv_symm_C_single (m : M) (a : A) :
    (powerSeriesAlgEquiv R A M).symm (PowerSeries.C (single m a)) = single m (PowerSeries.C a) :=
  (powerSeriesAlgEquiv R A M).symm_apply_eq.mpr (toPowerSeries_single_C R A M m a).symm

/-- The inverse of `powerSeriesAlgEquiv` sends `X` to `X`, placed at `1 ∈ M`. -/
@[simp]
theorem powerSeriesAlgEquiv_symm_X :
    (powerSeriesAlgEquiv R A M).symm PowerSeries.X = single 1 PowerSeries.X :=
  (powerSeriesAlgEquiv R A M).symm_apply_eq.mpr (toPowerSeries_single_one_X R A M).symm

end MonoidAlgebra
