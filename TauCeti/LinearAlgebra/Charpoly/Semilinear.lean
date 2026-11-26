/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import TauCeti.LinearAlgebra.Basis.Semilinear

/-!
# Characteristic polynomials under semilinear conjugation

Let `σ : R →+* S` be a ring isomorphism and `e : M ≃ₛₗ[σ] M'` a `σ`-semilinear equivalence of
finite free modules. If an `R`-linear endomorphism `f` of `M` and an `S`-linear endomorphism `g`
of `M'` satisfy `e ∘ f = g ∘ e`, then the characteristic polynomial of `g` is obtained from that
of `f` by applying `σ` to the coefficients. In the basis `e ∘ b` the matrix of `g` is the image
under `σ` of the matrix of `f` in `b`. For `σ = id` this is Mathlib's `LinearEquiv.charpoly_conj`.

The typical use is a module with a bijective `σ`-semilinear Frobenius `φ`: conjugation by `φ`
turns a linear endomorphism `f` into the linear endomorphism `φ ∘ f ∘ φ⁻¹`, whose characteristic
polynomial is that of `f` with `σ` applied to the coefficients.

## Main results

* `LinearEquiv.charpoly_eq_map_charpoly_of_semiconj`: if `e ∘ f = g ∘ e` for a `σ`-semilinear
  equivalence `e`, then `g.charpoly = f.charpoly.map σ`.
-/

public section

open Polynomial

namespace LinearEquiv

variable {R S M M' : Type*} [CommRing R] [CommRing S] {σ : R →+* S} {σ' : S →+* R}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
  [AddCommGroup M'] [Module S M'] [Module.Free S M'] [Module.Finite S M']

/-- If a `σ`-semilinear equivalence `e` intertwines the endomorphisms `f` and `g`, that is
`e ∘ f = g ∘ e`, then the characteristic polynomial of `g` is that of `f` with `σ` applied to the
coefficients. -/
theorem charpoly_eq_map_charpoly_of_semiconj (e : M ≃ₛₗ[σ] M') {f : Module.End R M}
    {g : Module.End S M'} (h : Function.Semiconj e f g) : g.charpoly = f.charpoly.map σ := by
  classical
  let b := Module.Free.chooseBasis R M
  have hmat : LinearMap.toMatrix (b.mapₛₗ e) (b.mapₛₗ e) g = (LinearMap.toMatrix b b f).map σ := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
      Module.Basis.mapₛₗ_apply, ← h, Module.Basis.repr_mapₛₗ_apply]
  rw [← LinearMap.charpoly_toMatrix g (b.mapₛₗ e), hmat, Matrix.charpoly_map,
    LinearMap.charpoly_toMatrix]

end LinearEquiv
