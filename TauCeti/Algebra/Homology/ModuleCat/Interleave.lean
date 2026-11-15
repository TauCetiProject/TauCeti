/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import TauCeti.Algebra.Homology.Interleave

/-!
# Bases of interleaved complexes of modules

Let `X₁`, `X₂`, `X₃` be three `ℤ`-indexed families of free modules over a ring `R`, with ordered
bases of ranks `m₁ q`, `m₂ q` and `m₃ q`, and maps making up an interleaved chain complex
`ChainComplex.interleave`. This file assembles bases of the terms of that complex. The rank in
degree `n` is `ChainComplex.interleave.rank`, which is `m₁ q`, `m₂ q` or `m₃ q` according as
`n = 3q + 2`, `3q + 1` or `3q`, and it has finite support when the three rank functions do
(`ChainComplex.interleave.finite_setOf_rank_ne_zero`).

The main application is the based long exact homology sequence, whose Reidemeister torsion is
the correction term in Milnor's multiplicativity formula
(`TauCeti.Algebra.Homology.ReidemeisterTorsion.HomologySequence`).

## Main declarations

* `ChainComplex.interleave.rank`: the rank function of the interleaved complex.
* `ChainComplex.interleave.basis`: the basis of the interleaved complex in each degree.
* `ChainComplex.interleave.XIso₁_hom_basis` and its two companions: the basis vectors are the given
  ones under the identifications of the terms.
-/

public section

noncomputable section

open CategoryTheory Module

namespace ChainComplex.interleave

section Rank

variable (m₁ m₂ m₃ : ℤ → ℕ)

/-- The rank in degree `n` of an interleaved complex whose three families have ranks
`m₁`, `m₂` and `m₃`: it is `m₃ q`, `m₂ q` or `m₁ q` according as `n = 3q`, `3q + 1` or
`3q + 2`. -/
def rank (n : ℤ) : ℕ :=
  if n % 3 = 0 then m₃ (n / 3) else if n % 3 = 1 then m₂ (n / 3) else m₁ (n / 3)

variable {m₁ m₂ m₃}

theorem rank_of_eq_three_mul_add_two {n q : ℤ} (h : n = 3 * q + 2) : rank m₁ m₂ m₃ n = m₁ q := by
  have h₁ : n % 3 = 2 := by omega
  have h₂ : n / 3 = q := by omega
  simp [rank, h₁, h₂]

theorem rank_of_eq_three_mul_add_one {n q : ℤ} (h : n = 3 * q + 1) : rank m₁ m₂ m₃ n = m₂ q := by
  have h₁ : n % 3 = 1 := by omega
  have h₂ : n / 3 = q := by omega
  simp [rank, h₁, h₂]

theorem rank_of_eq_three_mul {n q : ℤ} (h : n = 3 * q) : rank m₁ m₂ m₃ n = m₃ q := by
  have h₁ : n % 3 = 0 := by omega
  have h₂ : n / 3 = q := by omega
  simp [rank, h₁, h₂]

/-- If each of the three rank functions has finite support, so does `rank`. -/
theorem finite_setOf_rank_ne_zero (h₁ : {q | m₁ q ≠ 0}.Finite) (h₂ : {q | m₂ q ≠ 0}.Finite)
    (h₃ : {q | m₃ q ≠ 0}.Finite) : {n | rank m₁ m₂ m₃ n ≠ 0}.Finite := by
  refine (((h₁.image fun q ↦ 3 * q + 2).union (h₂.image fun q ↦ 3 * q + 1)).union
    (h₃.image fun q ↦ 3 * q)).subset fun n hn ↦ ?_
  obtain ⟨q, hq | hq | hq⟩ : ∃ q, n = 3 * q + 2 ∨ n = 3 * q + 1 ∨ n = 3 * q :=
    ⟨n / 3, by omega⟩
  · exact .inl <| .inl ⟨q, (rank_of_eq_three_mul_add_two hq).symm.trans_ne hn, hq.symm⟩
  · exact .inl <| .inr ⟨q, (rank_of_eq_three_mul_add_one hq).symm.trans_ne hn, hq.symm⟩
  · exact .inr ⟨q, (rank_of_eq_three_mul hq).symm.trans_ne hn, hq.symm⟩

end Rank

variable {R : Type*} [Ring R] {X₁ X₂ X₃ : ℤ → ModuleCat R} {f : ∀ q, X₁ q ⟶ X₂ q}
  {g : ∀ q, X₂ q ⟶ X₃ q} {δ : ∀ q, X₃ (q + 1) ⟶ X₁ q} (hfg : ∀ q, f q ≫ g q = 0)
  (hgδ : ∀ q, g (q + 1) ≫ δ q = 0) (hδf : ∀ q, δ q ≫ f q = 0)
  {m₁ m₂ m₃ : ℤ → ℕ} (b₁ : ∀ q, Basis (Fin (m₁ q)) R (X₁ q)) (b₂ : ∀ q, Basis (Fin (m₂ q)) R (X₂ q))
  (b₃ : ∀ q, Basis (Fin (m₃ q)) R (X₃ q))

/-- The basis of the interleaved complex in degree `n`: the basis `b₃ q`, `b₂ q` or `b₁ q`
according as `n = 3q`, `3q + 1` or `3q + 2`, transported along the identification of the term. -/
def basis (n : ℤ) :
    Basis (Fin (rank m₁ m₂ m₃ n)) R ((interleave X₁ X₂ X₃ f g δ hfg hgδ hδf).X n) :=
  if h₀ : n % 3 = 0 then
    ((b₃ (n / 3)).reindex (finCongr (rank_of_eq_three_mul (by omega)).symm)).map
      (XIso₃ hfg hgδ hδf n (n / 3) (by omega)).symm.toLinearEquiv
  else if h₁ : n % 3 = 1 then
    ((b₂ (n / 3)).reindex (finCongr (rank_of_eq_three_mul_add_one (by omega)).symm)).map
      (XIso₂ hfg hgδ hδf n (n / 3) (by omega)).symm.toLinearEquiv
  else
    ((b₁ (n / 3)).reindex (finCongr (rank_of_eq_three_mul_add_two (by omega)).symm)).map
      (XIso₁ hfg hgδ hδf n (n / 3) (by omega)).symm.toLinearEquiv

/-- In degree `n = 3q + 2` the basis of the interleaved complex is `b₁ q`. -/
@[simp]
theorem XIso₁_hom_basis {n q : ℤ} (h : n = 3 * q + 2) (i : Fin (rank m₁ m₂ m₃ n)) :
    (XIso₁ hfg hgδ hδf n q h).hom (basis hfg hgδ hδf b₁ b₂ b₃ n i) =
      b₁ q (Fin.cast (rank_of_eq_three_mul_add_two h) i) := by
  obtain rfl : n / 3 = q := by omega
  rw [basis, dite_eq_right (by omega), dite_eq_right (by omega)]
  simp

/-- In degree `n = 3q + 1` the basis of the interleaved complex is `b₂ q`. -/
@[simp]
theorem XIso₂_hom_basis {n q : ℤ} (h : n = 3 * q + 1) (i : Fin (rank m₁ m₂ m₃ n)) :
    (XIso₂ hfg hgδ hδf n q h).hom (basis hfg hgδ hδf b₁ b₂ b₃ n i) =
      b₂ q (Fin.cast (rank_of_eq_three_mul_add_one h) i) := by
  obtain rfl : n / 3 = q := by omega
  rw [basis, dite_eq_right (by omega), dite_eq_left (by omega)]
  simp

/-- In degree `n = 3q` the basis of the interleaved complex is `b₃ q`. -/
@[simp]
theorem XIso₃_hom_basis {n q : ℤ} (h : n = 3 * q) (i : Fin (rank m₁ m₂ m₃ n)) :
    (XIso₃ hfg hgδ hδf n q h).hom (basis hfg hgδ hδf b₁ b₂ b₃ n i) =
      b₃ q (Fin.cast (rank_of_eq_three_mul h) i) := by
  obtain rfl : n / 3 = q := by omega
  rw [basis, dite_eq_left (by omega)]
  simp

end ChainComplex.interleave
