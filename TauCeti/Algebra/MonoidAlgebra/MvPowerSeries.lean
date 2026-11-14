/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Multivariate power series over a monoid algebra

For a commutative semiring `R`, an index type `σ`, an `R`-algebra `A` and a monoid `M`, the monoid
algebra of `M` over the multivariate power-series ring `MvPowerSeries σ A` maps to the
multivariate power-series ring over the monoid algebra `A[M]` by collecting, for each multi-index
`d : σ →₀ ℕ`, the `d`-th coefficients of the monomial coefficients:

```text
∑ₘ φₘ · m  ↦  ∑_d (∑ₘ (coeff d φₘ) · m) X^d.
```

This is an `R`-algebra homomorphism `MonoidAlgebra.toMvPowerSeries`, characterised by
`coeff_coeff_toMvPowerSeries`: the coefficient at `m` of the `d`-th coefficient of the image is
the `d`-th coefficient of the coefficient at `m` of the argument. It is always injective, and for
a finite monoid `M` it is an isomorphism `MonoidAlgebra.mvPowerSeriesAlgEquiv`.

## Main declarations

* `MonoidAlgebra.toMvPowerSeries R σ A M`: the `R`-algebra homomorphism
  `(MvPowerSeries σ A)[M] →ₐ[R] MvPowerSeries σ (A[M])`, with `coeff_coeff_toMvPowerSeries` and
  `toMvPowerSeries_injective`.
* `MonoidAlgebra.mvPowerSeriesAlgEquiv R σ A M`: the isomorphism
  `(MvPowerSeries σ A)[M] ≃ₐ[R] MvPowerSeries σ (A[M])` for finite `M`.
* `MonoidAlgebra.map_singleOneRingHom_dvd_toMvPowerSeries_iff`: a multivariate power series with
  coefficients in `A` divides the image of `x ∈ (MvPowerSeries σ A)[M]` exactly when it divides, in
  `MvPowerSeries σ A`, the coefficient of `x` at every `m ∈ M`;
  `MonoidAlgebra.map_singleOneRingHom_dvd_mvPowerSeries_iff` is the finite-`M` form for an arbitrary
  `ψ ∈ MvPowerSeries σ (A[M])`.
-/

public section

namespace MonoidAlgebra

variable (R : Type*) [CommSemiring R] (σ : Type*) (A : Type*) [Semiring A] [Algebra R A]
  (M : Type*) [Monoid M]

/-- A multivariate power series with coefficients in `A` placed at `1 ∈ M` commutes with every
monomial `single m 1` read as a constant multivariate power series. -/
private theorem commute_mapAlgHom_singleOneAlgHom_mvPowerSeries_C_single
    (φ : MvPowerSeries σ A) (m : M) :
    Commute (MvPowerSeries.mapAlgHom (σ := σ) (singleOneAlgHom : A →ₐ[R] MonoidAlgebra A M) φ)
      (MvPowerSeries.C (single m (1 : A))) := by
  ext d : 1
  simp [MvPowerSeries.mapAlgHom_apply, MvPowerSeries.coeff_mul_C, MvPowerSeries.coeff_C_mul]

/-- The `R`-algebra homomorphism `(MvPowerSeries σ A)[M] →ₐ[R] MvPowerSeries σ (A[M])` collecting
the `d`-th coefficients for each `d : σ →₀ ℕ`: the coefficient at `m` of the `d`-th coefficient of
the image of `x` is the `d`-th coefficient of the coefficient at `m` of `x`
(`coeff_coeff_toMvPowerSeries`). It is injective, and bijective for finite `M`
(`mvPowerSeriesAlgEquiv`). -/
noncomputable def toMvPowerSeries :
    MonoidAlgebra (MvPowerSeries σ A) M →ₐ[R] MvPowerSeries σ (MonoidAlgebra A M) :=
  liftNCAlgHom (MvPowerSeries.mapAlgHom (σ := σ) (singleOneAlgHom : A →ₐ[R] MonoidAlgebra A M))
    ((MvPowerSeries.C : MonoidAlgebra A M →+* MvPowerSeries σ (MonoidAlgebra A M)).toMonoidHom.comp
      (of A M))
    (commute_mapAlgHom_singleOneAlgHom_mvPowerSeries_C_single R σ A M)

/-- On the monomial `φ · m`, the map to multivariate power series over `A[M]` is the power series
`φ` with coefficients placed at `1` (along `singleOneRingHom`), times the constant `m`. -/
theorem toMvPowerSeries_single (m : M) (φ : MvPowerSeries σ A) :
    toMvPowerSeries R σ A M (single m φ) =
      MvPowerSeries.map (singleOneRingHom : A →+* MonoidAlgebra A M) φ *
        MvPowerSeries.C (single m (1 : A)) := by
  ext d m'
  simp [toMvPowerSeries, MvPowerSeries.mapAlgHom_apply, MvPowerSeries.coeff_mul_C]

/-- The characteristic property of `toMvPowerSeries`: the coefficient at `m` of the `d`-th
coefficient of the image is the `d`-th coefficient of the coefficient at `m`. -/
@[simp]
theorem coeff_coeff_toMvPowerSeries (x : MonoidAlgebra (MvPowerSeries σ A) M) (d : σ →₀ ℕ)
    (m : M) :
    (MvPowerSeries.coeff d (toMvPowerSeries R σ A M x)).coeff m =
      MvPowerSeries.coeff d (x.coeff m) := by
  classical
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single m' φ =>
    by_cases h : m' = m <;>
      simp [h, toMvPowerSeries_single, MvPowerSeries.coeff_mul_C, single_mul_single, coeff_single]

/-- The map to multivariate power series over `A[M]` sends the constant monomial `a · m` to the
constant power series `a · m`. -/
@[simp]
theorem toMvPowerSeries_single_C (m : M) (a : A) :
    toMvPowerSeries R σ A M (single m (MvPowerSeries.C a)) = MvPowerSeries.C (single m a) := by
  simp [toMvPowerSeries_single, ← map_mul, single_mul_single]

/-- The map to multivariate power series over `A[M]` sends `X s`, placed at `1 ∈ M`, to `X s`. -/
@[simp]
theorem toMvPowerSeries_single_one_X (s : σ) :
    toMvPowerSeries R σ A M (single 1 (MvPowerSeries.X s)) = MvPowerSeries.X s := by
  simp [toMvPowerSeries_single, ← one_def]

/-- The map to multivariate power series over `A[M]` sends the power series `φ`, placed at `1 ∈ M`,
to `φ` with its coefficients read in `A[M]` along `singleOneRingHom`. -/
theorem toMvPowerSeries_single_one (φ : MvPowerSeries σ A) :
    toMvPowerSeries R σ A M (single 1 φ) =
      MvPowerSeries.map (singleOneRingHom : A →+* MonoidAlgebra A M) φ := by
  rw [toMvPowerSeries_single, ← one_def, map_one, mul_one]

/-- The map `(MvPowerSeries σ A)[M] → MvPowerSeries σ (A[M])` is injective for every monoid `M`: it
determines all the coefficients of its argument (`coeff_coeff_toMvPowerSeries`). -/
theorem toMvPowerSeries_injective : Function.Injective (toMvPowerSeries R σ A M) := fun x y h ↦ by
  ext m d
  rw [← coeff_coeff_toMvPowerSeries R σ A M x, ← coeff_coeff_toMvPowerSeries R σ A M y, h]

/-- **Divisibility by a multivariate power series with coefficients in `A`.** For
`φ ∈ MvPowerSeries σ A` and `x ∈ (MvPowerSeries σ A)[M]`, with `M` any monoid, `φ` read in
`MvPowerSeries σ (A[M])` divides the image of `x` exactly when `φ` divides, in `MvPowerSeries σ A`,
the coefficient of `x` at every `m ∈ M`. -/
theorem map_singleOneRingHom_dvd_toMvPowerSeries_iff (φ : MvPowerSeries σ A)
    (x : MonoidAlgebra (MvPowerSeries σ A) M) :
    MvPowerSeries.map (singleOneRingHom : A →+* MonoidAlgebra A M) φ ∣
        toMvPowerSeries R σ A M x ↔
      ∀ m, φ ∣ x.coeff m := by
  constructor
  · classical
    rintro ⟨ψ, hψ⟩ m
    let χ : MvPowerSeries σ A := fun d ↦ (MvPowerSeries.coeff d ψ).coeff m
    refine ⟨χ, MvPowerSeries.ext fun d ↦ ?_⟩
    rw [← coeff_coeff_toMvPowerSeries R σ A M, hψ]
    simp [MvPowerSeries.coeff_mul, coeff_single_one_mul]
    rfl
  · intro h
    rw [← toMvPowerSeries_single_one R σ A M]
    refine map_dvd _ ?_
    rw [← sum_coeff_single x]
    refine Finset.dvd_sum fun m _ ↦ ?_
    obtain ⟨q, hq⟩ := h m
    exact ⟨single m q, by rw [hq, single_mul_single, one_mul]⟩

/-- The map `(MvPowerSeries σ A)[M] → MvPowerSeries σ (A[M])` is surjective when `M` is finite: a
multivariate power series over `A[M]` is the image of the monoid algebra element whose coefficient
at `m` is the power series of the coefficients at `m`, which is finitely supported in `m` because
`M` is finite. -/
theorem toMvPowerSeries_surjective [Finite M] : Function.Surjective (toMvPowerSeries R σ A M) :=
  fun ψ ↦
    let f : M → MvPowerSeries σ A := fun m d ↦ (MvPowerSeries.coeff d ψ).coeff m
    ⟨ofCoeff (Finsupp.equivFunOnFinite.symm f),
      MvPowerSeries.ext fun d ↦ MonoidAlgebra.coeff_injective (Finsupp.ext fun m ↦ by
        rw [coeff_coeff_toMvPowerSeries, coeff_ofCoeff]
        exact congr_arg (MvPowerSeries.coeff d)
          (congr_fun (Finsupp.equivFunOnFinite.apply_symm_apply f) m))⟩

/-- **Multivariate power series over the monoid algebra of a finite monoid.** For a finite monoid
`M`, the monoid algebra of `M` over `MvPowerSeries σ A` is the multivariate power-series ring over
the monoid algebra `A[M]`, by collecting the `d`-th coefficients (`toMvPowerSeries`). -/
noncomputable def mvPowerSeriesAlgEquiv [Finite M] :
    MonoidAlgebra (MvPowerSeries σ A) M ≃ₐ[R] MvPowerSeries σ (MonoidAlgebra A M) :=
  AlgEquiv.ofBijective (toMvPowerSeries R σ A M)
    ⟨toMvPowerSeries_injective R σ A M, toMvPowerSeries_surjective R σ A M⟩

variable [Finite M]

@[simp]
theorem coe_mvPowerSeriesAlgEquiv :
    ⇑(mvPowerSeriesAlgEquiv R σ A M) = toMvPowerSeries R σ A M := (rfl)

/-- The inverse of `mvPowerSeriesAlgEquiv` reads the coefficients back: the `d`-th coefficient of
the coefficient at `m` of the inverse image of `ψ` is the coefficient at `m` of the `d`-th
coefficient of `ψ`. -/
@[simp]
theorem coeff_coeff_mvPowerSeriesAlgEquiv_symm (ψ : MvPowerSeries σ (MonoidAlgebra A M)) (m : M)
    (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (((mvPowerSeriesAlgEquiv R σ A M).symm ψ).coeff m) =
      (MvPowerSeries.coeff d ψ).coeff m := by
  rw [← coeff_coeff_toMvPowerSeries R σ A M, ← coe_mvPowerSeriesAlgEquiv,
    AlgEquiv.apply_symm_apply]

/-- The inverse of `mvPowerSeriesAlgEquiv` sends the constant power series `a · m` to the constant
monomial `a · m`. -/
@[simp]
theorem mvPowerSeriesAlgEquiv_symm_C_single (m : M) (a : A) :
    (mvPowerSeriesAlgEquiv R σ A M).symm (MvPowerSeries.C (single m a)) =
      single m (MvPowerSeries.C a) :=
  (mvPowerSeriesAlgEquiv R σ A M).symm_apply_eq.mpr (toMvPowerSeries_single_C R σ A M m a).symm

/-- The inverse of `mvPowerSeriesAlgEquiv` sends `X s` to `X s`, placed at `1 ∈ M`. -/
@[simp]
theorem mvPowerSeriesAlgEquiv_symm_X (s : σ) :
    (mvPowerSeriesAlgEquiv R σ A M).symm (MvPowerSeries.X s) = single 1 (MvPowerSeries.X s) :=
  (mvPowerSeriesAlgEquiv R σ A M).symm_apply_eq.mpr (toMvPowerSeries_single_one_X R σ A M s).symm

/-- For `φ ∈ MvPowerSeries σ A` and `ψ ∈ MvPowerSeries σ (A[M])`, with `M` finite, `φ` read in
`MvPowerSeries σ (A[M])` divides `ψ` exactly when it divides, in `MvPowerSeries σ A`, the
coefficient at every `m ∈ M` of the element of `(MvPowerSeries σ A)[M]` corresponding to `ψ`. -/
theorem map_singleOneRingHom_dvd_mvPowerSeries_iff (φ : MvPowerSeries σ A)
    (ψ : MvPowerSeries σ (MonoidAlgebra A M)) :
    MvPowerSeries.map (singleOneRingHom : A →+* MonoidAlgebra A M) φ ∣ ψ ↔
      ∀ m, φ ∣ ((mvPowerSeriesAlgEquiv R σ A M).symm ψ).coeff m := by
  rw [← map_singleOneRingHom_dvd_toMvPowerSeries_iff R σ A M, ← coe_mvPowerSeriesAlgEquiv,
    AlgEquiv.apply_symm_apply]

end MonoidAlgebra
