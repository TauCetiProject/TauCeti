/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.CharTwoLinearAlgebra
public import TauCeti.Algebra.Lie.F4.ShortRoot.DerivationConstraint

/-!
# Certified homogeneous blocks of type-F4 derivations

A block lists one degree, its matrix positions, selected derivation or coordinate constraints, and
a binary left inverse. The generic theorem replays that finite certificate over every commutative
ring of characteristic two.
-/

public section

open Matrix
namespace TauCeti.F4ShortRoot
universe u

/-- A binary matrix stored as one natural-number bitmask per row. -/
@[expose] def binaryMatrix {n : ℕ} (rows : Fin n → ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if (rows i).testBit j then 1 else 0

/-- Finite data for one homogeneous block of the derivation equations. -/
structure HomogeneousBlock (n : ℕ) where
  degree : Fin 4 → ℤ
  positions : Fin n → Fin 26 × Fin 26
  constraints : Fin n → DerivationConstraint
  B : Matrix (Fin n) (Fin n) (ZMod 2)

namespace HomogeneousBlock

/-- The binary constraint matrix computed from the selected equations and positions. -/
@[expose] def A {n : ℕ} (C : HomogeneousBlock n) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun r q => (C.constraints r).coeff (C.positions q)

/-- A complete supported block with a certified binary left inverse has trivial kernel. -/
theorem eq_zero {n : ℕ} (C : HomogeneousBlock n)
    (hBA : C.B * C.A = 1) (hpos : Function.Injective C.positions)
    (hsupport : ∀ i j, (∀ k, entryDegree i j k = C.degree k) ↔ ∃ q, C.positions q = (i, j))
    {R : Type u} [CommRing R] [CharP R 2] {X : Matrix (Fin 26) (Fin 26) R}
    (hX : IsDerivation X) (hhom : IsHomogeneous C.degree X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  let x : Fin n → R := fun q => X (C.positions q).1 (C.positions q).2
  have hsum (c : DerivationConstraint) : c.evaluate X =
      ∑ q : Fin n, ZMod.castHom dvd_rfl R (c.coeff (C.positions q)) * x q := by
    rw [c.evaluate_eq_sum_coeff]
    let s := Finset.univ.filter fun p : Fin 26 × Fin 26 =>
      ∀ k, entryDegree p.1 p.2 k = C.degree k
    let f := fun p : Fin 26 × Fin 26 => ZMod.castHom dvd_rfl R (c.coeff p) * X p.1 p.2
    have hsubset : ∑ p ∈ s, f p = ∑ p, f p := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro p _ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      change ZMod.castHom dvd_rfl R (c.coeff p) * X p.1 p.2 = 0
      have hout : entryDegree p.1 p.2 ≠ C.degree := fun heq =>
        hp fun k => congrFun heq k
      rw [hhom.eq_zero _ _ hout, mul_zero]
    rw [← hsubset]
    symm
    refine Finset.sum_bij (fun q _ => C.positions q) ?_ ?_ ?_ ?_
    · intro q _
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hsupport _ _).mpr ⟨q, rfl⟩
    · intro q₁ _ q₂ _ heq
      exact hpos heq
    · intro p hp
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨q, hq'⟩ := (hsupport p.1 p.2).mp hp
      exact ⟨q, Finset.mem_univ _, hq'⟩
    · intro q _
      rfl
  have hx : C.A.map (ZMod.castHom dvd_rfl R) *ᵥ x = 0 := by
    funext r
    change ∑ q, ZMod.castHom dvd_rfl R ((C.constraints r).coeff (C.positions q)) * x q = 0
    rw [← hsum]
    exact DerivationConstraint.evaluate_eq_zero hX hq hi _
  have hx0 := eq_zero_of_modTwo_leftInverse C.A C.B hBA x hx
  ext i j
  rw [Matrix.zero_apply]
  by_cases hd : entryDegree i j = C.degree
  · obtain ⟨q, hq'⟩ := (hsupport i j).mp fun k => congrFun hd k
    have := congrFun hx0 q
    simpa [x, hq'] using this
  · exact hhom.eq_zero i j hd
end HomogeneousBlock
end TauCeti.F4ShortRoot
