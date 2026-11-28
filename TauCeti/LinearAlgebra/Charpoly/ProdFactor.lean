/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
public import Mathlib.RingTheory.Finiteness.Prod

import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Characteristic polynomial of a product endomorphism with a scalar factor

Let `R` be a commutative ring and `M` a finite free `R`-module. An endomorphism
`Y : Module.End R (R × M)` that preserves both factors and acts by multiplication by `ν : R` on the
first factor splits as `LinearMap.prodMap (ν • 1) g` for a unique endomorphism `g : Module.End R M`,
so its characteristic polynomial factors as `(X - C ν) * g.charpoly`. Over a domain, the
characteristic roots of `g` are those of `Y` with one copy of `ν` removed.

## Main results

* `LinearMap.exists_charpoly_eq_X_sub_C_mul_of_prod`: block-diagonal splitting and characteristic
  polynomial factorization `Y.charpoly = (X - C ν) * g.charpoly`.
* `LinearMap.exists_charpoly_roots_eq_erase_of_prod`: over a domain, `g.charpoly.roots` equals
  `Y.charpoly.roots.erase ν`.
* `LinearMap.exists_matrix_charpoly_roots_eq_erase_of_prod`: specialization to `R × (n → R)`
  producing a square matrix `N : Matrix n n R`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Shimura/Uniformisation/BallModel.lean` (`exists_charpoly_roots_eq_erase`).
-/

@[expose] public section

open LinearMap Matrix Polynomial

/-- An endomorphism `Y` of `R × M` (with `M` finite free over a commutative ring `R`) that maps
`(1, 0)` to `(ν, 0)` and sends `{0} × M` into `{0} × M` decomposes as `(a, w) ↦ (ν * a, g w)` for
an endomorphism `g` of `M` whose characteristic polynomial satisfies
`Y.charpoly = (X - C ν) * g.charpoly`. -/
theorem LinearMap.exists_charpoly_eq_X_sub_C_mul_of_prod {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (ν : R)
    (Y : Module.End R (R × M)) (hY_fst : Y (1, 0) = (ν, 0))
    (hY_snd : ∀ w : M, (Y (0, w)).fst = 0) :
    ∃ g : Module.End R M, (∀ x : R × M, Y x = (ν * x.fst, g x.snd)) ∧
      Y.charpoly = (X - C ν) * g.charpoly := by
  let g : Module.End R M := (snd R R M).comp (Y.comp (inr R R M))
  have hY_eq : Y = prodMap (0 - -ν • 1) g := by
    ext <;> simp [g, hY_fst, hY_snd, Prod.mk_zero_zero]
  refine ⟨g, fun x ↦ by simp [hY_eq], ?_⟩
  rcases subsingleton_or_nontrivial R with _ | _
  · exact Subsingleton.elim _ _
  · rw [hY_eq, charpoly_prodMap, charpoly_sub_smul]
    simp [sub_eq_add_neg]

/-- Over a commutative domain `R`, an endomorphism `Y` of `R × M` (with `M` finite free) that maps
`(1, 0)` to `(ν, 0)` and sends `{0} × M` into `{0} × M` decomposes as `(a, w) ↦ (ν * a, g w)` for
an endomorphism `g` of `M` whose characteristic roots are those of `Y` with one copy of `ν`
removed. -/
theorem LinearMap.exists_charpoly_roots_eq_erase_of_prod {R M : Type*} [CommRing R] [IsDomain R]
    [DecidableEq R] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (ν : R)
    (Y : Module.End R (R × M)) (hY_fst : Y (1, 0) = (ν, 0))
    (hY_snd : ∀ w : M, (Y (0, w)).fst = 0) :
    ∃ g : Module.End R M, (∀ x : R × M, Y x = (ν * x.fst, g x.snd)) ∧
      g.charpoly.roots = Y.charpoly.roots.erase ν := by
  obtain ⟨g, hY_eq, hcp⟩ := exists_charpoly_eq_X_sub_C_mul_of_prod ν Y hY_fst hY_snd
  refine ⟨g, hY_eq, ?_⟩
  simp [hcp, roots_mul (mul_ne_zero (X_sub_C_ne_zero ν) g.charpoly_monic.ne_zero)]

/-- Matrix form of `LinearMap.exists_charpoly_roots_eq_erase_of_prod`: an endomorphism `Y` of
`R × (n → R)` (over a commutative domain `R`) that maps `(1, 0)` to `(ν, 0)` and sends
`{0} × (n → R)` into `{0} × (n → R)` decomposes as `(a, w) ↦ (ν * a, N *ᵥ w)` for a square matrix
`N : Matrix n n R` whose characteristic roots are those of `Y` with one copy of `ν` removed. -/
theorem LinearMap.exists_matrix_charpoly_roots_eq_erase_of_prod {R n : Type*} [CommRing R]
    [IsDomain R] [DecidableEq R] [Fintype n] [DecidableEq n] (ν : R)
    (Y : Module.End R (R × (n → R))) (hY_fst : Y (1, 0) = (ν, 0))
    (hY_snd : ∀ w : n → R, (Y (0, w)).fst = 0) :
    ∃ N : Matrix n n R, (∀ x : R × (n → R), Y x = (ν * x.fst, N *ᵥ x.snd)) ∧
      N.charpoly.roots = Y.charpoly.roots.erase ν := by
  obtain ⟨g, hY_eq, hroots⟩ := exists_charpoly_roots_eq_erase_of_prod ν Y hY_fst hY_snd
  refine ⟨g.toMatrix', fun x ↦ by simpa [toMatrix'_mulVec] using hY_eq x, ?_⟩
  simpa [← Matrix.charpoly_toLin'] using hroots
