/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Basic

/-!
# Witt vectors of a ring isomorphism

A ring isomorphism `e : R ≃+* S` induces a ring isomorphism `WittVector p R ≃+* WittVector p S`,
acting on Witt coordinates by `e`, with inverse induced by `e.symm`. It upgrades Mathlib's
`WittVector.map` to ring isomorphisms.

## Main definitions

* `WittVector.mapEquiv`: the ring isomorphism of Witt vectors induced by a ring isomorphism.
-/

public section

namespace WittVector

variable {p : ℕ} [Fact p.Prime] {R S : Type*} [CommRing R] [CommRing S]

/-- The ring isomorphism `WittVector p R ≃+* WittVector p S` induced by a ring isomorphism
`e : R ≃+* S`, acting on Witt coordinates by `e`. -/
noncomputable def mapEquiv (e : R ≃+* S) : WittVector p R ≃+* WittVector p S where
  __ := map (e : R →+* S)
  invFun := map (e.symm : S →+* R)
  left_inv x := ext fun n ↦ by simp [map_coeff]
  right_inv y := ext fun n ↦ by simp [map_coeff]

@[simp]
theorem mapEquiv_apply (e : R ≃+* S) (x : WittVector p R) :
    mapEquiv e x = map (e : R →+* S) x :=
  (rfl)

@[simp]
theorem mapEquiv_symm (e : R ≃+* S) : (mapEquiv e).symm = mapEquiv (p := p) e.symm :=
  (rfl)

theorem coeff_mapEquiv (e : R ≃+* S) (x : WittVector p R) (n : ℕ) :
    (mapEquiv e x).coeff n = e (x.coeff n) :=
  map_coeff _ x n

end WittVector
