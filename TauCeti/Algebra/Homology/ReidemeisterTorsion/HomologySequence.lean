/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Interleave
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Basic

/-!
# The based long exact homology sequence

Let `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` be a short exact sequence of `ℤ`-graded chain complexes of
vector spaces over a field `F`. Its long exact homology sequence is the acyclic chain complex
`CategoryTheory.ShortComplex.ShortExact.homologySequenceComplex`, with `Hᵢ(S.X₁)`, `Hᵢ(S.X₂)` and
`Hᵢ(S.X₃)` in degrees `3i + 2`, `3i + 1` and `3i`. This file makes it a based complex: ordered
bases of the homology groups give ordered bases of its terms
(`ChainComplex.interleave.basis`), and the resulting Reidemeister torsion is a nonzero scalar
once only finitely many homology groups are nonzero
(`CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsion_homologySequenceComplex_ne_zero`).

This scalar is the correction term in Milnor's formula for the torsion with homology bases of a
short exact sequence of complexes that need not be acyclic: with compatible chain bases,
`τ(S.X₂) = ± τ(S.X₁) · τ(S.X₃) · τ(H)`, where `H` is the based long exact homology sequence
(Milnor, *Whitehead torsion*, Theorem 3.2).

The bases are assembled for any interleaved complex `ChainComplex.interleave` of three families of
free modules over a ring. The rank in degree `n` is `ChainComplex.interleave.rank`, which is
`m₁ q`, `m₂ q` or `m₃ q` according as `n = 3q + 2`, `3q + 1` or `3q`.

## Main declarations

* `ChainComplex.interleave.rank`: the rank function of the interleaved complex.
* `ChainComplex.interleave.basis`: the basis of the interleaved complex in each degree.
* `ChainComplex.interleave.XIso₁_hom_basis` and its two companions: the basis vectors are the given
  ones under the identifications of the terms.
* `CategoryTheory.ShortComplex.ShortExact.reidemeisterTorsion_homologySequenceComplex_ne_zero`: the
  based long exact homology sequence has nonzero torsion.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3, Theorem 3.2.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, Theorem 1.14.
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
theorem XIso₁_hom_basis {n q : ℤ} (h : n = 3 * q + 2) (i : Fin (rank m₁ m₂ m₃ n)) :
    (XIso₁ hfg hgδ hδf n q h).hom (basis hfg hgδ hδf b₁ b₂ b₃ n i) =
      b₁ q (Fin.cast (rank_of_eq_three_mul_add_two h) i) := by
  obtain rfl : n / 3 = q := by omega
  rw [basis, dite_eq_right (by omega), dite_eq_right (by omega)]
  simp

/-- In degree `n = 3q + 1` the basis of the interleaved complex is `b₂ q`. -/
theorem XIso₂_hom_basis {n q : ℤ} (h : n = 3 * q + 1) (i : Fin (rank m₁ m₂ m₃ n)) :
    (XIso₂ hfg hgδ hδf n q h).hom (basis hfg hgδ hδf b₁ b₂ b₃ n i) =
      b₂ q (Fin.cast (rank_of_eq_three_mul_add_one h) i) := by
  obtain rfl : n / 3 = q := by omega
  rw [basis, dite_eq_right (by omega), dite_eq_left (by omega)]
  simp

/-- In degree `n = 3q` the basis of the interleaved complex is `b₃ q`. -/
theorem XIso₃_hom_basis {n q : ℤ} (h : n = 3 * q) (i : Fin (rank m₁ m₂ m₃ n)) :
    (XIso₃ hfg hgδ hδf n q h).hom (basis hfg hgδ hδf b₁ b₂ b₃ n i) =
      b₃ q (Fin.cast (rank_of_eq_three_mul h) i) := by
  obtain rfl : n / 3 = q := by omega
  rw [basis, dite_eq_left (by omega)]
  simp

end ChainComplex.interleave

namespace CategoryTheory.ShortComplex.ShortExact

variable {F : Type*} [Field F] {S : ShortComplex (ChainComplex (ModuleCat F) ℤ)}
  (hS : S.ShortExact) {m₁ m₂ m₃ : ℤ → ℕ} (b₁ : ∀ i, Basis (Fin (m₁ i)) F (S.X₁.homology i))
  (b₂ : ∀ i, Basis (Fin (m₂ i)) F (S.X₂.homology i))
  (b₃ : ∀ i, Basis (Fin (m₃ i)) F (S.X₃.homology i))

/-- The long exact homology sequence, based by ordered bases of the homology groups of which only
finitely many are nonempty, has nonzero Reidemeister torsion. -/
theorem reidemeisterTorsion_homologySequenceComplex_ne_zero (h₁ : {i | m₁ i ≠ 0}.Finite)
    (h₂ : {i | m₂ i ≠ 0}.Finite) (h₃ : {i | m₃ i ≠ 0}.Finite) :
    hS.homologySequenceComplex.reidemeisterTorsion
      (ChainComplex.interleave.basis _ _ _ b₁ b₂ b₃) ≠ 0 :=
  HomologicalComplex.reidemeisterTorsion_ne_zero _ _
    (ChainComplex.interleave.finite_setOf_rank_ne_zero h₁ h₂ h₃)
    hS.acyclic_homologySequenceComplex

end CategoryTheory.ShortComplex.ShortExact
