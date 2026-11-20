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
in `τ` (`MvPowerSeries.sumAlgEquiv`), over any `R`-algebra `A` of coefficients, commutative or
not. This is the power-series analogue of Mathlib's `MvPolynomial.sumAlgEquiv`, and generalizes
Mathlib's `MvPowerSeries.optionEquivLeft`, which separates a single variable. It underlies the
identification of restricted series in two families of variables with iterated restricted series
(`TauCeti.MvPowerSeries.restrictedSumEquiv`).

## Main results

* `PowerSeries.coeff_toMvPowerSeries`: the coefficients of `w.toMvPowerSeries i`.
* `MvPowerSeries.sumAlgEquiv`: the algebra isomorphism
  `MvPowerSeries (σ ⊕ τ) A ≃ₐ[R] MvPowerSeries σ (MvPowerSeries τ A)`.
* `MvPowerSeries.coeff_coeff_sumAlgEquiv` and
  `MvPowerSeries.coeff_sumAlgEquiv_symm`: its coefficients.
* `MvPowerSeries.sumAlgEquiv_C`: its action on constants, with inverse
  `MvPowerSeries.sumAlgEquiv_symm_C`.
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

variable (A σ τ : Type*)

/-- Reindexing coefficients by the two parts of a monomial and currying the resulting family.
Implementation detail of `sumAlgEquiv`. -/
private noncomputable def sumEquiv :
    MvPowerSeries (σ ⊕ τ) A ≃ MvPowerSeries σ (MvPowerSeries τ A) :=
  (Equiv.arrowCongr Finsupp.sumFinsuppEquivProdFinsupp (Equiv.refl A)).trans
    (Equiv.curry (σ →₀ ℕ) (τ →₀ ℕ) A)

variable {A σ τ} [Semiring A]

private theorem coeff_coeff_sumEquiv (f : MvPowerSeries (σ ⊕ τ) A) (a : σ →₀ ℕ)
    (b : τ →₀ ℕ) : coeff b (coeff a (sumEquiv A σ τ f)) = coeff (a.sumElim b) f := (rfl)

private theorem sumEquiv_mul (f g : MvPowerSeries (σ ⊕ τ) A) :
    sumEquiv A σ τ (f * g) = sumEquiv A σ τ f * sumEquiv A σ τ g := by
  classical
  ext a b
  simp only [coeff_coeff_sumEquiv, coeff_mul, map_sum]
  rw [← Finsupp.image_sumElim_product_antidiagonal, sum_image, sum_product]
  rintro ⟨⟨a₁, a₂⟩, b₁, b₂⟩ - ⟨⟨a₁', a₂'⟩, b₁', b₂'⟩ - h
  simp only [Prod.mk.injEq, Finsupp.ext_iff, Sum.forall, Finsupp.sumElim_inl,
    Finsupp.sumElim_inr] at h ⊢
  tauto

end Semiring

variable {R A σ τ : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

variable (R A σ τ) in
/-- **Power series in `σ ⊕ τ` are power series in `σ` over power series in `τ`.** The
coefficient of `xᵃ` of the image of `f` is the power series in `τ` whose coefficient of `yᵇ` is
the coefficient of `xᵃ yᵇ` in `f`. The coefficients `A` form an arbitrary, not necessarily
commutative, `R`-algebra. This is the power-series analogue of Mathlib's
`MvPolynomial.sumAlgEquiv`. -/
noncomputable def sumAlgEquiv :
    MvPowerSeries (σ ⊕ τ) A ≃ₐ[R] MvPowerSeries σ (MvPowerSeries τ A) where
  toEquiv := sumEquiv A σ τ
  map_mul' := sumEquiv_mul
  map_add' f g := by
    ext a b
    simp [coeff_coeff_sumEquiv]
  commutes' r := by
    classical
    ext a b
    simp [coeff_coeff_sumEquiv, algebraMap_apply, coeff_C, apply_ite (coeff b), Finsupp.ext_iff,
      Sum.forall, ite_and]

/-- The coefficients of `sumAlgEquiv`: the coefficient of `yᵇ` in the coefficient of `xᵃ` of the
image of `f` is the coefficient of `xᵃ yᵇ` in `f`. -/
@[simp]
theorem coeff_coeff_sumAlgEquiv (f : MvPowerSeries (σ ⊕ τ) A) (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    coeff b (coeff a (sumAlgEquiv R A σ τ f)) = coeff (a.sumElim b) f := (rfl)

/-- The coefficients of the inverse of `sumAlgEquiv`: the coefficient of a monomial in `σ ⊕ τ` is
read off from its `σ` and `τ` parts. -/
@[simp]
theorem coeff_sumAlgEquiv_symm (g : MvPowerSeries σ (MvPowerSeries τ A)) (a : σ →₀ ℕ)
    (b : τ →₀ ℕ) : coeff (a.sumElim b) ((sumAlgEquiv R A σ τ).symm g) = coeff b (coeff a g) := by
  rw [← coeff_coeff_sumAlgEquiv (R := R), AlgEquiv.apply_symm_apply]

/-- `sumAlgEquiv` sends a constant to the corresponding constant with constant coefficient. -/
@[simp]
theorem sumAlgEquiv_C (c : A) : sumAlgEquiv R A σ τ (C c) = C (C c) := by
  classical
  ext a b
  simp [coeff_C, apply_ite (coeff b), Finsupp.ext_iff, Sum.forall, ite_and]

/-- `sumAlgEquiv` sends a variable of the first family to the corresponding variable. -/
@[simp]
theorem sumAlgEquiv_X_inl (i : σ) : sumAlgEquiv R A σ τ (X (.inl i)) = X i := by
  classical
  ext a b
  rw [coeff_coeff_sumAlgEquiv, coeff_X, coeff_X, ← Finsupp.sumElim_single_zero]
  split_ifs <;> simp_all [coeff_one, Finsupp.ext_iff, Sum.forall, Finsupp.single_apply]

/-- `sumAlgEquiv` sends a variable of the second family to the corresponding variable, viewed as
a constant coefficient. -/
@[simp]
theorem sumAlgEquiv_X_inr (j : τ) : sumAlgEquiv R A σ τ (X (.inr j)) = C (X j) := by
  classical
  ext a b
  rw [coeff_coeff_sumAlgEquiv, coeff_X, coeff_C, ← Finsupp.sumElim_zero_single]
  split_ifs <;> simp_all [coeff_X, Finsupp.ext_iff, Sum.forall, Finsupp.single_apply]

/-- The inverse of `sumAlgEquiv` sends a constant with constant coefficient to the corresponding
constant. -/
@[simp]
theorem sumAlgEquiv_symm_C (c : A) : (sumAlgEquiv R A σ τ).symm (C (C c)) = C c := by
  rw [AlgEquiv.symm_apply_eq, sumAlgEquiv_C]

/-- The inverse of `sumAlgEquiv` sends a variable to the corresponding variable of the first
family. -/
@[simp]
theorem sumAlgEquiv_symm_X (i : σ) : (sumAlgEquiv R A σ τ).symm (X i) = X (.inl i) := by
  rw [AlgEquiv.symm_apply_eq, sumAlgEquiv_X_inl]

/-- The inverse of `sumAlgEquiv` sends a constant variable to the corresponding variable of the
second family. -/
@[simp]
theorem sumAlgEquiv_symm_C_X (j : τ) : (sumAlgEquiv R A σ τ).symm (C (X j)) = X (.inr j) := by
  rw [AlgEquiv.symm_apply_eq, sumAlgEquiv_X_inr]

end MvPowerSeries
