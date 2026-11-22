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

For a commutative semiring `R`, an index type `σ`, an `R`-algebra `A`, and a monoid `M`, collecting
coefficients for each `d : σ →₀ ℕ` defines an injective `R`-algebra homomorphism
`MonoidAlgebra.toMvPowerSeries : (MvPowerSeries σ A)[M] →ₐ[R] MvPowerSeries σ (A[M])`, which is an
isomorphism `MonoidAlgebra.mvPowerSeriesAlgEquiv` when `M` is finite. Taking `σ = Unit` recovers
the one-variable power-series isomorphism `A⟦X⟧[M] ≃ₐ[R] A[M]⟦X⟧` (`PowerSeries A =
MvPowerSeries Unit A`).

## Main declarations

* `MonoidAlgebra.toMvPowerSeries`: injective homomorphism
  `(MvPowerSeries σ A)[M] →ₐ[R] MvPowerSeries σ (A[M])`.
* `MonoidAlgebra.mvPowerSeriesAlgEquiv`: isomorphism
  `(MvPowerSeries σ A)[M] ≃ₐ[R] MvPowerSeries σ (A[M])` for finite `M`.
* `MonoidAlgebra.map_singleOneRingHom_dvd_mvPowerSeries_iff`: coefficientwise divisibility by
  scalar multivariate power series.
-/

public section

namespace MonoidAlgebra

variable (R : Type*) [CommSemiring R] (σ : Type*) (A : Type*) [Semiring A] [Algebra R A]
  (M : Type*) [Monoid M]

/-- The `R`-algebra homomorphism `(MvPowerSeries σ A)[M] →ₐ[R] MvPowerSeries σ (A[M])` collecting
the `d`-th coefficients for each `d : σ →₀ ℕ` (`coeff_coeff_toMvPowerSeries`). -/
noncomputable def toMvPowerSeries :
    MonoidAlgebra (MvPowerSeries σ A) M →ₐ[R] MvPowerSeries σ (MonoidAlgebra A M) :=
  liftNCAlgHom (MvPowerSeries.mapAlgHom (σ := σ) (singleOneAlgHom : A →ₐ[R] MonoidAlgebra A M))
    ((MvPowerSeries.C : MonoidAlgebra A M →+* MvPowerSeries σ (MonoidAlgebra A M)).toMonoidHom.comp
      (of A M)) fun _ _ ↦ by
    ext : 1; simp [MvPowerSeries.mapAlgHom_apply, MvPowerSeries.coeff_mul_C,
      MvPowerSeries.coeff_C_mul]

/-- On a monomial `single m φ`, `toMvPowerSeries` maps `φ` into `A[M]` via `singleOneRingHom` and
multiplies by the constant series `C (single m 1)`. -/
theorem toMvPowerSeries_single (m : M) (φ : MvPowerSeries σ A) :
    toMvPowerSeries R σ A M (single m φ) =
      MvPowerSeries.map (singleOneRingHom : A →+* MonoidAlgebra A M) φ *
        MvPowerSeries.C (single m (1 : A)) := by
  ext d m'; simp [toMvPowerSeries, MvPowerSeries.mapAlgHom_apply, MvPowerSeries.coeff_mul_C]
@[simp] theorem coeff_coeff_toMvPowerSeries (x : MonoidAlgebra (MvPowerSeries σ A) M) (d : σ →₀ ℕ)
    (m : M) : (MvPowerSeries.coeff d (toMvPowerSeries R σ A M x)).coeff m =
      MvPowerSeries.coeff d (x.coeff m) := by
  classical
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single m' φ =>
    by_cases h : m' = m <;>
      simp [h, toMvPowerSeries_single, MvPowerSeries.coeff_mul_C, single_mul_single, coeff_single]
@[simp] theorem toMvPowerSeries_single_C (m : M) (a : A) :
    toMvPowerSeries R σ A M (single m (MvPowerSeries.C a)) = MvPowerSeries.C (single m a) := by
  simp [toMvPowerSeries_single, ← map_mul, single_mul_single]
@[simp] theorem toMvPowerSeries_single_one_X (s : σ) :
    toMvPowerSeries R σ A M (single 1 (MvPowerSeries.X s)) = MvPowerSeries.X s := by
  simp [toMvPowerSeries_single, ← one_def]

/-- On `single 1 φ`, `toMvPowerSeries` agrees with `MvPowerSeries.map singleOneRingHom`. -/
theorem toMvPowerSeries_single_one (φ : MvPowerSeries σ A) : toMvPowerSeries R σ A M (single 1 φ) =
    MvPowerSeries.map (singleOneRingHom : A →+* MonoidAlgebra A M) φ := by
  rw [toMvPowerSeries_single, ← one_def, map_one, mul_one]

/-- `toMvPowerSeries` is injective for any monoid `M`: elements are determined by coefficients. -/
theorem toMvPowerSeries_injective : Function.Injective (toMvPowerSeries R σ A M) := fun x y h ↦ by
  ext m d; rw [← coeff_coeff_toMvPowerSeries R σ A M x, ← coeff_coeff_toMvPowerSeries R σ A M y, h]

/-- A scalar series `φ` divides `toMvPowerSeries x` iff `φ` divides every `x.coeff m`. -/
theorem map_singleOneRingHom_dvd_toMvPowerSeries_iff (φ : MvPowerSeries σ A)
    (x : MonoidAlgebra (MvPowerSeries σ A) M) :
    MvPowerSeries.map (singleOneRingHom : A →+* MonoidAlgebra A M) φ ∣
        toMvPowerSeries R σ A M x ↔ ∀ m, φ ∣ x.coeff m := by
  refine ⟨?_, fun h ↦ ?_⟩
  · classical
    rintro ⟨ψ, hψ⟩ m
    let q : MvPowerSeries σ A := fun d ↦ (MvPowerSeries.coeff d ψ).coeff m
    refine ⟨q, MvPowerSeries.ext fun d ↦ ?_⟩
    rw [← coeff_coeff_toMvPowerSeries R σ A M, hψ, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MvPowerSeries.coeff_map]
    exact Finset.sum_congr rfl fun c _ ↦ by
      rw [MvPowerSeries.coeff_apply q c.2]; simp [coeff_single_one_mul, q]
  · rw [← toMvPowerSeries_single_one R σ A M, ← sum_coeff_single x]
    exact map_dvd _ (Finset.dvd_sum fun m _ ↦
      let ⟨q, hq⟩ := h m; ⟨single m q, by rw [hq, single_mul_single, one_mul]⟩)

/-- When `M` is finite, `toMvPowerSeries` is surjective, since every series in `A[M]` has finitely
many `M`-coordinates and reassembles into an element of `(MvPowerSeries σ A)[M]`. -/
theorem toMvPowerSeries_surjective [Finite M] : Function.Surjective (toMvPowerSeries R σ A M) :=
  fun ψ ↦ let f : M → MvPowerSeries σ A := fun m d ↦ (MvPowerSeries.coeff d ψ).coeff m
    ⟨ofCoeff (Finsupp.equivFunOnFinite.symm f), MvPowerSeries.ext fun d ↦
      MonoidAlgebra.coeff_injective (Finsupp.ext fun m ↦ by
        rw [coeff_coeff_toMvPowerSeries, coeff_ofCoeff]
        simpa [f, MvPowerSeries.coeff_apply] using (congr_arg (MvPowerSeries.coeff d)
          (congr_fun (Finsupp.equivFunOnFinite.apply_symm_apply f) m)).trans
          (MvPowerSeries.coeff_apply (f m) d))⟩

/-- For a finite monoid `M`, `(MvPowerSeries σ A)[M] ≃ₐ[R] MvPowerSeries σ (A[M])`. -/
noncomputable def mvPowerSeriesAlgEquiv [Finite M] :
    MonoidAlgebra (MvPowerSeries σ A) M ≃ₐ[R] MvPowerSeries σ (MonoidAlgebra A M) :=
  AlgEquiv.ofBijective (toMvPowerSeries R σ A M)
    ⟨toMvPowerSeries_injective R σ A M, toMvPowerSeries_surjective R σ A M⟩

variable [Finite M]
@[simp] theorem coe_mvPowerSeriesAlgEquiv :
    ⇑(mvPowerSeriesAlgEquiv R σ A M) = toMvPowerSeries R σ A M := (rfl)
@[simp] theorem coeff_coeff_mvPowerSeriesAlgEquiv_symm (ψ : MvPowerSeries σ (MonoidAlgebra A M))
    (m : M) (d : σ →₀ ℕ) : MvPowerSeries.coeff d (((mvPowerSeriesAlgEquiv R σ A M).symm ψ).coeff m)
      = (MvPowerSeries.coeff d ψ).coeff m := by
  rw [← coeff_coeff_toMvPowerSeries R σ A M, ← coe_mvPowerSeriesAlgEquiv, AlgEquiv.apply_symm_apply]
@[simp] theorem mvPowerSeriesAlgEquiv_symm_C_single (m : M) (a : A) :
    (mvPowerSeriesAlgEquiv R σ A M).symm (MvPowerSeries.C (single m a)) =
      single m (MvPowerSeries.C a) :=
  (mvPowerSeriesAlgEquiv R σ A M).symm_apply_eq.mpr (toMvPowerSeries_single_C R σ A M m a).symm
@[simp] theorem mvPowerSeriesAlgEquiv_symm_X (s : σ) :
    (mvPowerSeriesAlgEquiv R σ A M).symm (MvPowerSeries.X s) = single 1 (MvPowerSeries.X s) :=
  (mvPowerSeriesAlgEquiv R σ A M).symm_apply_eq.mpr (toMvPowerSeries_single_one_X R σ A M s).symm

/-- **Coefficientwise divisibility in `MvPowerSeries σ (A[M])`**: for finite `M`, the scalar image
of `φ ∈ MvPowerSeries σ A` divides `ψ` iff `φ` divides every `M`-coordinate of `ψ`. -/
theorem map_singleOneRingHom_dvd_mvPowerSeries_iff (φ : MvPowerSeries σ A)
    (ψ : MvPowerSeries σ (MonoidAlgebra A M)) :
    MvPowerSeries.map (singleOneRingHom : A →+* MonoidAlgebra A M) φ ∣ ψ ↔
      ∀ m, φ ∣ ((mvPowerSeriesAlgEquiv R σ A M).symm ψ).coeff m := by
  rw [← map_singleOneRingHom_dvd_toMvPowerSeries_iff R σ A M, ← coe_mvPowerSeriesAlgEquiv,
    AlgEquiv.apply_symm_apply]

end MonoidAlgebra
