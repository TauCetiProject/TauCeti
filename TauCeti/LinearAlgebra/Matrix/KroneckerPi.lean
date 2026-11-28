/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite indexed Kronecker products of matrices

This file defines the Kronecker product `TauCeti.Matrix.kroneckerPi` of a finite family of matrices
`A : ∀ s : S, Matrix (a s) (b s) R`, with entry `(β, α) ↦ ∏ s, A s (β s) (α s)`, and proves its
compatibility with matrix multiplication, the identity matrix, monoid homomorphisms, and transpose.

## Main definitions and results

* `TauCeti.Matrix.kroneckerPi`: the Kronecker product of a finite family of matrices.
* `TauCeti.Matrix.kroneckerPi_mul`:
  `kroneckerPi (fun s ↦ A s * B s) = kroneckerPi A * kroneckerPi B`.
* `TauCeti.Matrix.kroneckerPi_one`: `kroneckerPi (fun s ↦ 1) = 1`.
* `TauCeti.Matrix.kroneckerPi_map`: `kroneckerPi (fun s ↦ (A s).map φ) = (kroneckerPi A).map φ`.
* `TauCeti.Matrix.kroneckerPi_transpose`:
  `kroneckerPi (fun s ↦ (A s)ᵀ) = (kroneckerPi A)ᵀ`.

## Provenance

Generalized from `New.kroneckerPi`, `New.kroneckerPi_mul`, `New.kroneckerPi_one`, and
`New.kroneckerPi_map` in `src/Lib/General/Groups/BesselGroups.lean` of
[grh-lean](https://github.com/lsernau/grh-lean) at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Finset
open scoped Matrix

namespace TauCeti.Matrix

variable {R : Type*} {S : Type*} [Fintype S] {a b c : S → Type*}

/-- The Kronecker product of a finite family of matrices `A s`: its entry at `(β, α)` is
`∏ s, A s (β s) (α s)`. -/
def kroneckerPi [CommMonoid R] (A : ∀ s : S, _root_.Matrix (a s) (b s) R) :
    _root_.Matrix (∀ s : S, a s) (∀ s : S, b s) R :=
  _root_.Matrix.of fun β α ↦ ∏ s : S, A s (β s) (α s)

/-- The Kronecker product of a family of matrix products equals the product of the Kronecker
products. -/
theorem kroneckerPi_mul [CommSemiring R] [DecidableEq S] [∀ s : S, Fintype (b s)]
    (A : ∀ s : S, _root_.Matrix (a s) (b s) R) (B : ∀ s : S, _root_.Matrix (b s) (c s) R) :
    kroneckerPi (fun s ↦ A s * B s) = kroneckerPi A * kroneckerPi B := by
  simp [kroneckerPi, ← _root_.Matrix.ext_iff, _root_.Matrix.mul_apply, prod_univ_sum,
    prod_mul_distrib]

/-- The Kronecker product of identity matrices is the identity matrix. -/
@[simp]
theorem kroneckerPi_one [CommSemiring R] [∀ s : S, DecidableEq (a s)] [DecidableEq (∀ s : S, a s)] :
    kroneckerPi (fun s : S ↦ (1 : _root_.Matrix (a s) (a s) R)) = 1 := by
  simp [kroneckerPi, ← _root_.Matrix.ext_iff, prod_boole, funext_iff, _root_.Matrix.one_apply]

/-- Mapping entries by a monoid homomorphism commutes with `kroneckerPi`. -/
theorem kroneckerPi_map [CommMonoid R] {R' : Type*} [CommMonoid R']
    (A : ∀ s : S, _root_.Matrix (a s) (b s) R) (φ : R →* R') :
    kroneckerPi (fun s ↦ (A s).map φ) = (kroneckerPi A).map φ := by
  simp [kroneckerPi, ← _root_.Matrix.ext_iff, map_prod]

/-- Taking the transpose commutes with `kroneckerPi`. -/
theorem kroneckerPi_transpose [CommMonoid R]
    (A : ∀ s : S, _root_.Matrix (a s) (b s) R) :
    kroneckerPi (fun s ↦ (A s)ᵀ) = (kroneckerPi A)ᵀ := by
  simp [kroneckerPi]

end TauCeti.Matrix
