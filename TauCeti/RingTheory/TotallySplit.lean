/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TotallySplit
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import TauCeti.Algebra.Algebra.Pi

/-!
# Finite algebras over a field with many characters are totally split

A finite-dimensional commutative algebra `A` over a field `K` has at most `finrank K A` characters
`A →ₐ[K] K` (Mathlib's `card_algHom_le_finrank`). When it has that many, evaluation at the
characters identifies `A` with the algebra of `K`-valued functions on them
(`TauCeti.AlgHom.pi_id_bijective_of_finrank_le_card`), so `A` is totally split
(`Algebra.IsFiniteSplit`), and in particular étale over `K`. Conversely, a totally split algebra
is the algebra of functions on its characters (`Algebra.IsFiniteSplit.pi_id_bijective`).

Geometrically: a finite scheme over a field with as many rational points as its degree is a
disjoint union of copies of the base. This is the criterion used to show that the `n`-torsion of an
elliptic curve over a separably closed field in which `n` is invertible is étale.

## Main results

* `Algebra.IsFiniteSplit.of_finrank_le_card_algHom`: a finite-dimensional commutative algebra over
  a field with at least `finrank K A` characters is totally split.
* `Algebra.IsFiniteSplit.pi_id_bijective`: evaluation at all characters identifies a totally split
  algebra over a field with the algebra of functions on its characters.
-/

public section

/-- **A finite algebra over a field with as many characters as its dimension is totally split.**
If a finite-dimensional commutative algebra `A` over a field `K` has at least `finrank K A`
characters `A →ₐ[K] K`, then `A` is isomorphic to a finite product of copies of `K`; in
particular it is étale over `K`. -/
theorem Algebra.IsFiniteSplit.of_finrank_le_card_algHom {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] [Module.Finite K A] (h : Module.finrank K A ≤ Nat.card (A →ₐ[K] K)) :
    Algebra.IsFiniteSplit K A := by
  have := Finite.algHom K A K
  exact .of_algEquiv
    (AlgEquiv.ofBijective _ (TauCeti.AlgHom.pi_id_bijective_of_finrank_le_card h)).symm

/-- **A totally split algebra is the algebra of functions on its characters.** If `A` is
isomorphic to a finite product of copies of the field `K`, then evaluation at all characters
`A →ₐ[K] K` is an isomorphism from `A` onto the algebra of `K`-valued functions on them. -/
theorem Algebra.IsFiniteSplit.pi_id_bijective {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] [Algebra.IsFiniteSplit K A] :
    Function.Bijective (AlgHom.pi fun χ : A →ₐ[K] K ↦ χ) := by
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun K A
  have hA : Module.finrank K A = n := by simp [e.toLinearEquiv.finrank_eq]
  have hχ : Nat.card (A →ₐ[K] K) = n := by
    rw [Nat.card_congr (e.arrowCongr AlgEquiv.refl), ← Nat.card_congr (Pi.evalAlgHomEquiv K _)]
    simp
  exact TauCeti.AlgHom.pi_id_bijective_of_finrank_le_card (hA.trans hχ.symm).le
