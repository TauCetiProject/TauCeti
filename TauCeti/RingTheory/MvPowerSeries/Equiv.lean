/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Equivalences and coefficient formulas for power series

## Viewing a one-variable power series in one variable of a family

`PowerSeries.toMvPowerSeries i` views a one-variable power series as a multivariate one in the
single variable `i`. Mathlib records that it is an algebra map, how it acts on `C` and `X`, that
it is injective, and that its coefficients vanish off the powers of `i`
(`PowerSeries.toMvPowerSeries_coeff_eq_zero`); this file adds the remaining half, the value of
the coefficients that do not vanish.

## Separating two families of variables

Power series in the variables `σ ⊕ τ` are power series in `σ` whose coefficients are power series
in `τ` (`MvPowerSeries.sumAlgEquiv`). This is the power-series analogue of Mathlib's
`MvPolynomial.sumAlgEquiv`, and generalizes Mathlib's `MvPowerSeries.optionEquivLeft`, which
separates a single variable. It underlies the identification of restricted series in two
families of variables with iterated restricted series
(`TauCeti.MvPowerSeries.restrictedSumEquiv`).

## Main results

* `PowerSeries.coeff_toMvPowerSeries`: the coefficients of `w.toMvPowerSeries i`.
* `MvPowerSeries.sumAlgEquiv`: the algebra isomorphism
  `MvPowerSeries (σ ⊕ τ) R ≃ₐ[R] MvPowerSeries σ (MvPowerSeries τ R)`.
* `MvPowerSeries.coeff_coeff_sumAlgEquiv` and
  `MvPowerSeries.coeff_sumAlgEquiv_symm`: its coefficients.
* `MvPowerSeries.sumAlgEquiv_X_inl` and `MvPowerSeries.sumAlgEquiv_X_inr`: its action on the
  variables, with inverses `MvPowerSeries.sumAlgEquiv_symm_X` and
  `MvPowerSeries.sumAlgEquiv_symm_C_X`.

## Provenance

`PowerSeries.coeff_toMvPowerSeries` is adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, revision `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/Chord.lean`, the private lemma `coeff_rename_single`.
There it is stated for `MvPowerSeries.rename (fun _ => s)` and only where it is used; here it is
stated for the `PowerSeries.toMvPowerSeries` spelling of that map, which is Mathlib's, and it
carries no elliptic content so it is recorded on its own.
-/

public section

namespace PowerSeries

variable {σ R : Type*} [CommSemiring R] [DecidableEq σ]

/-- The coefficients of a one-variable power series viewed in the single variable `i`: the
coefficient of a monomial `d` is the `d i`-th coefficient of the original series if `d` is a
power of `i`, and `0` otherwise. -/
@[simp]
theorem coeff_toMvPowerSeries (i : σ) (w : PowerSeries R) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (w.toMvPowerSeries i) =
      if d = Finsupp.single i (d i) then coeff (d i) w else 0 := by
  rw [toMvPowerSeries_apply]
  split_ifs with h
  · have hd : d = Finsupp.embDomain (⟨fun _ => i, fun _ _ _ => rfl⟩ : Unit ↪ σ)
        (Finsupp.single () (d i)) := by
      rw [Finsupp.embDomain_single]
      exact h
    have h1 := MvPowerSeries.coeff_embDomain_rename
      (⟨fun _ => i, fun _ _ _ => rfl⟩ : Unit ↪ σ) w (Finsupp.single () (d i))
    rw [← hd] at h1
    exact h1
  · refine MvPowerSeries.coeff_rename_eq_zero _ _ fun ⟨y, hy⟩ => h ?_
    rw [← hy, Finsupp.unique_single y, Finsupp.mapDomain_single]
    simp

omit [DecidableEq σ] in
/-- Base change commutes with viewing a one-variable series in a single variable `i`. -/
@[simp]
theorem map_toMvPowerSeries {S : Type*} [CommSemiring S] (φ : R →+* S) (i : σ) (w : PowerSeries R) :
    MvPowerSeries.map φ (w.toMvPowerSeries i) = (PowerSeries.map φ w).toMvPowerSeries i := by
  simp only [toMvPowerSeries_apply, PowerSeries.map, ← MvPowerSeries.rename_map]


end PowerSeries

namespace MvPowerSeries

open Finset

section Semiring

variable (R σ τ : Type*) [Semiring R]

/-- Reindexing coefficients by the two parts of a monomial and currying the resulting family.
Implementation detail of `sumAlgEquiv`. -/
private noncomputable def sumEquiv :
    MvPowerSeries (σ ⊕ τ) R ≃ MvPowerSeries σ (MvPowerSeries τ R) :=
  (Equiv.arrowCongr Finsupp.sumFinsuppEquivProdFinsupp (Equiv.refl R)).trans
    (Equiv.curry (σ →₀ ℕ) (τ →₀ ℕ) R)

variable {R σ τ}

private theorem coeff_coeff_sumEquiv (f : MvPowerSeries (σ ⊕ τ) R) (a : σ →₀ ℕ)
    (b : τ →₀ ℕ) : coeff b (coeff a (sumEquiv R σ τ f)) = coeff (a.sumElim b) f := (rfl)

private theorem sumEquiv_mul (f g : MvPowerSeries (σ ⊕ τ) R) :
    sumEquiv R σ τ (f * g) = sumEquiv R σ τ f * sumEquiv R σ τ g := by
  classical
  ext a b
  simp only [coeff_coeff_sumEquiv, coeff_mul, map_sum]
  rw [← Finsupp.image_sumElim_product_antidiagonal, sum_image, sum_product]
  rintro ⟨⟨a₁, a₂⟩, b₁, b₂⟩ - ⟨⟨a₁', a₂'⟩, b₁', b₂'⟩ - h
  simp only [Prod.mk.injEq, Finsupp.ext_iff, Sum.forall, Finsupp.sumElim_inl,
    Finsupp.sumElim_inr] at h ⊢
  tauto

end Semiring

variable {R σ τ : Type*} [CommSemiring R]

variable (R σ τ) in
/-- **Power series in `σ ⊕ τ` are power series in `σ` over power series in `τ`.** The
coefficient of `xᵃ` of the image of `f` is the power series in `τ` whose coefficient of `yᵇ` is
the coefficient of `xᵃ yᵇ` in `f`. This is the power-series analogue of Mathlib's
`MvPolynomial.sumAlgEquiv`. -/
noncomputable def sumAlgEquiv :
    MvPowerSeries (σ ⊕ τ) R ≃ₐ[R] MvPowerSeries σ (MvPowerSeries τ R) where
  toEquiv := sumEquiv R σ τ
  map_mul' := sumEquiv_mul
  map_add' f g := by
    ext a b
    simp [coeff_coeff_sumEquiv]
  commutes' r := by
    classical
    ext a b
    have h : a.sumElim b = 0 ↔ a = 0 ∧ b = 0 := by
      simp [Finsupp.ext_iff, Sum.forall]
    simp only [Equiv.toFun_as_coe, algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [coeff_coeff_sumEquiv]
    simp only [coeff_C, h]
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [ha, hb, coeff_C]

/-- The coefficients of `sumAlgEquiv`: the coefficient of `yᵇ` in the coefficient of `xᵃ` of the
image of `f` is the coefficient of `xᵃ yᵇ` in `f`. -/
@[simp]
theorem coeff_coeff_sumAlgEquiv (f : MvPowerSeries (σ ⊕ τ) R) (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    coeff b (coeff a (sumAlgEquiv R σ τ f)) = coeff (a.sumElim b) f := (rfl)

/-- The coefficients of the inverse of `sumAlgEquiv`: the coefficient of a monomial in `σ ⊕ τ` is
read off from its `σ` and `τ` parts. -/
@[simp]
theorem coeff_sumAlgEquiv_symm (g : MvPowerSeries σ (MvPowerSeries τ R)) (a : σ →₀ ℕ)
    (b : τ →₀ ℕ) : coeff (a.sumElim b) ((sumAlgEquiv R σ τ).symm g) = coeff b (coeff a g) := by
  rw [← coeff_coeff_sumAlgEquiv, AlgEquiv.apply_symm_apply]

/-- `sumAlgEquiv` sends a variable of the first family to the corresponding variable. -/
@[simp]
theorem sumAlgEquiv_X_inl (i : σ) : sumAlgEquiv R σ τ (X (.inl i)) = X i := by
  classical
  ext a b
  rw [coeff_coeff_sumAlgEquiv, coeff_X, coeff_X, ← Finsupp.sumElim_single_zero]
  split_ifs <;> simp_all [coeff_one, Finsupp.ext_iff, Sum.forall, Finsupp.single_apply]

/-- `sumAlgEquiv` sends a variable of the second family to the corresponding variable, viewed as
a constant coefficient. -/
@[simp]
theorem sumAlgEquiv_X_inr (j : τ) : sumAlgEquiv R σ τ (X (.inr j)) = C (X j) := by
  classical
  ext a b
  rw [coeff_coeff_sumAlgEquiv, coeff_X, coeff_C, ← Finsupp.sumElim_zero_single]
  split_ifs <;> simp_all [coeff_X, Finsupp.ext_iff, Sum.forall, Finsupp.single_apply]

/-- The inverse of `sumAlgEquiv` sends a variable to the corresponding variable of the first
family. -/
@[simp]
theorem sumAlgEquiv_symm_X (i : σ) : (sumAlgEquiv R σ τ).symm (X i) = X (.inl i) := by
  rw [AlgEquiv.symm_apply_eq, sumAlgEquiv_X_inl]

/-- The inverse of `sumAlgEquiv` sends a constant variable to the corresponding variable of the
second family. -/
@[simp]
theorem sumAlgEquiv_symm_C_X (j : τ) : (sumAlgEquiv R σ τ).symm (C (X j)) = X (.inr j) := by
  rw [AlgEquiv.symm_apply_eq, sumAlgEquiv_X_inr]

end MvPowerSeries
