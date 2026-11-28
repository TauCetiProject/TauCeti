/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import TauCeti.FieldTheory.Finite.MinpolyOrbit
import TauCeti.LinearAlgebra.Charpoly.Aeval.Comp

/-!
# Roots of the characteristic polynomial of left multiplication over a finite field

Let `L` be a finite extension of a finite field `k` with `q = |k|` elements, and let `φ : L →ₐ[k] K`
be a `k`-algebra homomorphism into a commutative domain `K`. For any `u : L`, the characteristic
polynomial of left multiplication by `u` on `L` is a power of the minimal polynomial of `u` over
`k`, and its multiset of roots in `K` consists of the Frobenius conjugates `φ u ^ q ^ i` for
`i < [L : k]`.

## Main results

* `AlgHom.aroots_charpoly_mulLeft`: the roots in `K` of
  `(LinearMap.mulLeft k u).charpoly` are
  `(Multiset.range (Module.finrank k L)).map (fun i ↦ φ u ^ Nat.card k ^ i)`.

## Provenance

Adapted from grh-lean
(https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207,
Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/LocalGL/Green/TauFunctions.lean` (`New.aroots_charpoly_mulLeft`).
-/

public section

open Polynomial TauCeti.FiniteField

/-- Let `L` be a finite extension of a finite field `k` and `φ : L →ₐ[k] K` a `k`-algebra
homomorphism into a commutative domain `K`. The roots in `K` of the characteristic polynomial of
left multiplication by `u : L` on `L`, counted with multiplicity, are the Frobenius conjugates
`φ u ^ |k| ^ i` for `i < [L : k]`. -/
theorem AlgHom.aroots_charpoly_mulLeft {k L K : Type*} [Field k] [_root_.Finite k] [Field L]
    [Algebra k L]
    [FiniteDimensional k L] [CommRing K] [IsDomain K] [Algebra k K] (φ : L →ₐ[k] K) (u : L) :
    (LinearMap.mulLeft k u).charpoly.aroots K =
      (Multiset.range (Module.finrank k L)).map fun i : ℕ ↦ φ u ^ Nat.card k ^ i := by
  let _ : Fintype k := Fintype.ofFinite k
  have hint : IsIntegral k u := Algebra.IsIntegral.isIntegral u
  have haeval : aeval (LinearMap.mulLeft k u) (minpoly k u) = 0 := by
    have hlmul : LinearMap.mulLeft k u = Algebra.lmul k L u :=
      LinearMap.ext fun v ↦ by simp [LinearMap.mulLeft_apply]
    rw [hlmul, aeval_algHom_apply, minpoly.aeval, map_zero]
  obtain ⟨j, hpow⟩ := (LinearMap.mulLeft k u).exists_charpoly_eq_pow_of_isNilpotent_aeval
    (minpoly.irreducible hint) (minpoly.monic hint) (by simp [haeval])
  have hroot : aeval (φ u) (minpoly k u) = 0 := by
    simp [aeval_algHom_apply]
  have hdeg : (minpoly k u ^ j).natDegree = Module.finrank k L := by
    rw [← hpow, LinearMap.charpoly_natDegree]
  rw [hpow, aroots_pow_eq_map_pow_card_pow (minpoly.irreducible hint) hroot, hdeg]
  simp only [Nat.card_eq_fintype_card]

