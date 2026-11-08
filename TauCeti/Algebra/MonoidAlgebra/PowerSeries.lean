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
* `MonoidAlgebra.map_singleOneRingHom_dvd_toPowerSeries_iff`: a power series with coefficients in
  `A` divides the image of `x ∈ A⟦X⟧[M]` exactly when it divides, in `A⟦X⟧`, the coefficient of
  `x` at every `m ∈ M`; `MonoidAlgebra.map_singleOneRingHom_dvd_iff` is the finite-`M` form for an
  arbitrary `ψ ∈ A[M]⟦X⟧`.
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
  ext n : 1
  simp [PowerSeries.mapAlgHom_apply, PowerSeries.coeff_mul_C, PowerSeries.coeff_C_mul]

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
coefficients placed at `1` (along `singleOneRingHom`), times the constant `m`. -/
theorem toPowerSeries_single (m : M) (φ : PowerSeries A) :
    toPowerSeries R A M (single m φ) =
      PowerSeries.map (singleOneRingHom : A →+* MonoidAlgebra A M) φ *
        PowerSeries.C (single m (1 : A)) := by
  ext n m'
  simp [toPowerSeries, PowerSeries.mapAlgHom_apply, PowerSeries.coeff_mul_C]

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
    by_cases h : m' = m <;>
      simp [h, toPowerSeries_single, PowerSeries.coeff_mul_C, single_mul_single, coeff_single]

/-- The map to power series over `A[M]` sends the constant monomial `a · m` to the constant power
series `a · m`. -/
@[simp]
theorem toPowerSeries_single_C (m : M) (a : A) :
    toPowerSeries R A M (single m (PowerSeries.C a)) = PowerSeries.C (single m a) := by
  simp [toPowerSeries_single, ← map_mul, single_mul_single]

/-- The map to power series over `A[M]` sends `X`, placed at `1 ∈ M`, to `X`. -/
@[simp]
theorem toPowerSeries_single_one_X :
    toPowerSeries R A M (single 1 PowerSeries.X) = PowerSeries.X := by
  simp [toPowerSeries_single, ← one_def]

/-- The map to power series over `A[M]` sends the power series `φ`, placed at `1 ∈ M`, to `φ` with
its coefficients read in `A[M]` along `singleOneRingHom`. -/
theorem toPowerSeries_single_one (φ : PowerSeries A) :
    toPowerSeries R A M (single 1 φ) =
      PowerSeries.map (singleOneRingHom : A →+* MonoidAlgebra A M) φ := by
  rw [toPowerSeries_single, ← one_def, map_one, mul_one]

/-- The map `A⟦X⟧[M] → A[M]⟦X⟧` is injective, for every monoid `M`: it determines all the
coefficients of its argument (`coeff_coeff_toPowerSeries`). -/
theorem toPowerSeries_injective : Function.Injective (toPowerSeries R A M) := fun x y h ↦ by
  ext m n
  rw [← coeff_coeff_toPowerSeries R A M x, ← coeff_coeff_toPowerSeries R A M y, h]

/-- **Divisibility by a power series with coefficients in `A`.** For `φ ∈ A⟦X⟧` and
`x ∈ A⟦X⟧[M]`, with `M` any monoid, `φ` read in `A[M]⟦X⟧` divides the image of `x` exactly when
`φ` divides, in `A⟦X⟧`, the coefficient of `x` at every `m ∈ M`. -/
theorem map_singleOneRingHom_dvd_toPowerSeries_iff (φ : PowerSeries A)
    (x : MonoidAlgebra (PowerSeries A) M) :
    PowerSeries.map (singleOneRingHom : A →+* MonoidAlgebra A M) φ ∣ toPowerSeries R A M x ↔
      ∀ m, φ ∣ x.coeff m := by
  constructor
  · -- The coefficient at `m` of `φ * ψ` is `φ` times the series of the coefficients of `ψ` at `m`.
    rintro ⟨ψ, hψ⟩ m
    refine ⟨PowerSeries.mk fun j ↦ (PowerSeries.coeff j ψ).coeff m, PowerSeries.ext fun n ↦ ?_⟩
    rw [← coeff_coeff_toPowerSeries R A M, hψ]
    simp [PowerSeries.coeff_mul, coeff_single_one_mul]
  · -- `x` is the sum of its monomials `single m (x.coeff m)`, each a multiple of `single 1 φ`.
    intro h
    rw [← toPowerSeries_single_one R A M]
    refine map_dvd _ ?_
    rw [← sum_coeff_single x]
    refine Finset.dvd_sum fun m _ ↦ ?_
    obtain ⟨q, hq⟩ := h m
    exact ⟨single m q, by rw [hq, single_mul_single, one_mul]⟩

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

/-- For `φ ∈ A⟦X⟧` and `ψ ∈ A[M]⟦X⟧`, with `M` finite, `φ` read in `A[M]⟦X⟧` divides `ψ` exactly
when it divides, in `A⟦X⟧`, the coefficient at every `m ∈ M` of the element of `A⟦X⟧[M]`
corresponding to `ψ`: the multiples of `φ` are the elements all of whose `M`-coefficients are
multiples of `φ`. This is `map_singleOneRingHom_dvd_toPowerSeries_iff` read through
`powerSeriesAlgEquiv`. -/
theorem map_singleOneRingHom_dvd_iff (φ : PowerSeries A) (ψ : PowerSeries (MonoidAlgebra A M)) :
    PowerSeries.map (singleOneRingHom : A →+* MonoidAlgebra A M) φ ∣ ψ ↔
      ∀ m, φ ∣ ((powerSeriesAlgEquiv R A M).symm ψ).coeff m := by
  rw [← map_singleOneRingHom_dvd_toPowerSeries_iff R, ← coe_powerSeriesAlgEquiv,
    AlgEquiv.apply_symm_apply]

end MonoidAlgebra
