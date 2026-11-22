/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Primality of linear differences and injective renamings in `MvPolynomial`

This file complements `MvPolynomial.prime_X` and `MvPolynomial.prime_rename_iff` with basic
primality facts and a shear automorphism for multivariate polynomials:

* `MvPolynomial.prime_rename_iff_of_injective`: renaming variables along any injective map
  preserves and reflects primality.
* `MvPolynomial.shearXEquiv`: the `R`-algebra automorphism shearing `X j` to `X j + X i`.
* `MvPolynomial.prime_X_sub_X`: for distinct variables `i ≠ j` over a cancellative nontrivial
  commutative ring, the linear difference `X j - X i` is prime (carried to `X j` by
  `shearXEquiv`).
* `MvPolynomial.not_associated_X_sub_X`: over any nontrivial commutative ring, linear differences
  `X j - X i` and `X j' - X i'` on distinct unordered pairs `{i, j} ≠ {i', j'}` are not associated.
-/

public section

namespace MvPolynomial

section CommRing

variable {σ τ R : Type*} [CommRing R]

/-- Renaming variables along any injective map preserves and reflects primality. -/
theorem prime_rename_iff_of_injective {f : τ → σ} (hf : Function.Injective f)
    {p : MvPolynomial τ R} : Prime (rename f p) ↔ Prime p := by
  let e : τ ≃ Set.range f := Equiv.ofInjective f hf
  have hcomp : rename f p = rename ((↑) : Set.range f → σ) (renameEquiv R e p) := by
    rw [renameEquiv_apply, rename_rename]
    rfl
  rw [hcomp, prime_rename_iff (Set.range f)]
  exact MulEquiv.prime_iff (renameEquiv R e).toMulEquiv

/-- The `R`-algebra automorphism of `MvPolynomial σ R` shearing `X j` by `X i` (`X j ↦ X j + X i`
and fixing `X k` for `k ≠ j`). -/
noncomputable def shearXEquiv (R : Type*) [CommRing R] [DecidableEq σ] {i j : σ} (hij : i ≠ j) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  let f : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
    aeval (Function.update (X : σ → MvPolynomial σ R) j (X j + X i))
  let g : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
    aeval (Function.update (X : σ → MvPolynomial σ R) j (X j - X i))
  have hfg : f.comp g = AlgHom.id R _ := by
    ext k
    rcases eq_or_ne k j with rfl | hkj
    · simp [f, g, Function.update_of_ne hij]
    · simp [f, g, Function.update_of_ne hkj]
  have hgf : g.comp f = AlgHom.id R _ := by
    ext k
    rcases eq_or_ne k j with rfl | hkj
    · simp [f, g, Function.update_of_ne hij]
    · simp [f, g, Function.update_of_ne hkj]
  AlgEquiv.ofAlgHom f g hfg hgf

/-- `shearXEquiv R hij` maps the sheared variable `X j` to `X j + X i`. -/
@[simp]
theorem shearXEquiv_X_self (R : Type*) [CommRing R] [DecidableEq σ] {i j : σ} (hij : i ≠ j) :
    shearXEquiv R hij (X j) = X j + X i := by
  simp [shearXEquiv]

/-- `shearXEquiv R hij` fixes every variable `X k` with `k ≠ j`. -/
@[simp]
theorem shearXEquiv_X_of_ne (R : Type*) [CommRing R] [DecidableEq σ] {i j k : σ} (hij : i ≠ j)
    (hkj : k ≠ j) : shearXEquiv R hij (X k) = X k := by
  simp [shearXEquiv, Function.update_of_ne hkj]

/-- The inverse of `shearXEquiv R hij` maps `X j` to `X j - X i`. -/
@[simp]
theorem shearXEquiv_symm_X_self (R : Type*) [CommRing R] [DecidableEq σ] {i j : σ} (hij : i ≠ j) :
    (shearXEquiv R hij).symm (X j) = X j - X i := by
  simp [shearXEquiv]

/-- The inverse of `shearXEquiv R hij` fixes every variable `X k` with `k ≠ j`. -/
@[simp]
theorem shearXEquiv_symm_X_of_ne (R : Type*) [CommRing R] [DecidableEq σ] {i j k : σ} (hij : i ≠ j)
    (hkj : k ≠ j) : (shearXEquiv R hij).symm (X k) = X k := by
  simp [shearXEquiv, Function.update_of_ne hkj]

/-- Over a nontrivial cancellative commutative ring, the difference `X j - X i` of two distinct
variables is prime in `MvPolynomial σ R`. -/
theorem prime_X_sub_X [IsCancelMulZero R] [Nontrivial R] {i j : σ} (hij : i ≠ j) :
    Prime (X j - X i : MvPolynomial σ R) := by
  classical
  let e := shearXEquiv R hij
  rw [← MulEquiv.prime_iff e.toMulEquiv]
  have he : e.toMulEquiv (X j - X i) = X j := by
    simp [e, hij]
  rw [he]
  exact prime_X

/-- Over any nontrivial commutative ring, linear differences `X j - X i` and `X j' - X i'` with
`i' ≠ j'` are not associated unless `{i', j'} = {i, j}`. -/
theorem not_associated_X_sub_X [Nontrivial R] {i j i' j' : σ}
    (h1 : i' ≠ i ∨ j' ≠ j) (h2 : i' ≠ j ∨ j' ≠ i) (hij' : i' ≠ j') :
    ¬ Associated (X j - X i : MvPolynomial σ R) (X j' - X i') := by
  classical
  rintro ⟨u, hu⟩
  by_cases hi' : i' ≠ i ∧ i' ≠ j
  · have heval := congrArg (eval (Pi.single i' (1 : R))) hu
    simp [Pi.single_eq_of_ne hi'.1.symm, Pi.single_eq_of_ne hi'.2.symm,
      Pi.single_eq_of_ne hij'.symm] at heval
  · have hj' : j' ≠ i ∧ j' ≠ j := by
      rcases not_and_or.mp hi' with h | h
      · have h' : i' = i := not_not.mp h
        subst h'
        exact ⟨hij'.symm, h1.resolve_left (not_not.mpr rfl)⟩
      · have h' : i' = j := not_not.mp h
        subst h'
        exact ⟨h2.resolve_left (not_not.mpr rfl), hij'.symm⟩
    have heval := congrArg (eval (Pi.single j' (1 : R))) hu
    simp [Pi.single_eq_of_ne hj'.1.symm, Pi.single_eq_of_ne hj'.2.symm,
      Pi.single_eq_of_ne hij'] at heval

end CommRing

end MvPolynomial
