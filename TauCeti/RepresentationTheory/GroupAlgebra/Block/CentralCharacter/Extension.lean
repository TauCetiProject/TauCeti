/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Basis.AlgHom
public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.CenterMap

/-!
# Central characters under scalar extension

Let `f : k →+* k'` be a ring homomorphism of commutative semirings and `G` a finite group. Every
`k`-algebra homomorphism `λ : Z(k[G]) → k`, for instance the central character `λ_B` of a block,
extends to a `k'`-algebra homomorphism `λ' : Z(k'[G]) → k'` with `λ'(x) = f(λ(x))` on the image
of `Z(k[G])`: `λ'` takes the value `f(λ(K_C))` at the class sum `K_C`. It is multiplicative
because the products of class sums of `k'[G]` are the images of those of `k[G]`. In particular the
central character of a block over `k'` extends the central character over `k`.

The construction is an instance of `TauCeti.exists_algHom_comp_eq_of_basis`, applied to the map
of centres `Z(k[G]) → Z(k'[G])` and the class-sum bases.

## Main results

* `TauCeti.exists_algHom_centerMapRingHom`: for `f : k →+* k'` and `λ : Z(k[G]) →ₐ[k] k`, there
  is `λ' : Z(k'[G]) →ₐ[k'] k'` with `λ'(f_* x) = f(λ(x))`.
-/

public section

namespace TauCeti

open _root_.MonoidAlgebra

variable {k k' G : Type*} [CommSemiring k] [CommSemiring k'] [Group G] [Finite G]

/-- **Central characters extend along scalar extension.** For a ring homomorphism
`f : k →+* k'`, every `k`-algebra homomorphism `λ : Z(k[G]) → k`, for instance the central
character of a block, extends to a `k'`-algebra homomorphism `λ' : Z(k'[G]) → k'` with
`λ'(f_* x) = f(λ(x))` for the induced map `f_* : Z(k[G]) → Z(k'[G])`. -/
theorem exists_algHom_centerMapRingHom (f : k →+* k')
    (φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k) :
    ∃ φ' : Subalgebra.center k' (MonoidAlgebra k' G) →ₐ[k'] k',
      ∀ x, φ' (centerMapRingHom G f x) = f (φ x) := by
  classical
  have := Fintype.ofFinite G
  exact exists_algHom_comp_eq_of_basis f (centerMapRingHom G f) (centerMapRingHom_algebraMap G f)
    classSumBasis classSumBasis (fun C => by
      rw [classSumBasis_apply, classSumBasis_apply, centerMapRingHom_classSumCenter]) φ

end TauCeti
