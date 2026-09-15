/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.DerivationGrading
public import TauCeti.Algebra.Lie.F4.ShortRoot.IdealCoordinate

/-!
# Degree-zero derivations of the short-root algebra

The degree-zero part of a derivation is supported on the diagonal and the two entries between the
zero-weight coordinate vectors. The private lemmas below solve the resulting 28-variable linear
system from a small set of derivation equations and the four relevant coordinate functionals.
-/

public section

open Matrix
namespace TauCeti.F4ShortRoot
open TauCeti.DynkinType
universe u
variable {R : Type u} [CommRing R] [CharP R 2]


attribute [local simp] multTargetOne multCoeffOne multTargetTwo multCoeffTwo
  multRowTargetOne multRowCoeffOne multRowTargetTwo multRowCoeffTwo multIndexOne
  multIndexCoeffOne multIndexTwo multIndexCoeffTwo coordinateCoeff coordinateRow coordinateCol
  idealRow idealCol

private theorem zeroDiagonal0 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 0 0 = 0 := by
  have h0 := hi 13
  simp at h0
  clear hX hq hi
  grind
private theorem zeroDiagonal1 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 1 1 = 0 := by
  have h0 := hX.entry 1 0 10
  have h1 := hi 12
  have h2 := hi 13
  simp at h0 h1 h2
  clear hX hq hi
  grind
private theorem zeroDiagonal2 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 2 2 = 0 := by
  have h0 := hX.entry 0 8 23
  have h1 := hX.entry 1 0 10
  have h2 := hX.entry 1 11 23
  have h3 := hX.entry 2 0 8
  have h4 := quotientCoordinate_entries hq 12
  have h5 := hi 12
  simp at h0 h1 h2 h3 h4 h5
  clear hX hq hi
  grind
private theorem zeroDiagonal3 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 3 3 = 0 := by
  have h0 := hX.entry 0 5 21
  have h1 := hX.entry 0 8 23
  have h2 := hX.entry 1 0 10
  have h3 := hX.entry 1 3 16
  have h4 := hX.entry 1 7 21
  have h5 := hX.entry 1 11 23
  have h6 := hX.entry 2 0 8
  have h7 := hX.entry 2 5 16
  have h8 := quotientCoordinate_entries hq 12
  have h9 := quotientCoordinate_entries hq 13
  have h10 := hi 12
  simp at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  clear hX hq hi
  grind
private theorem zeroDiagonal4 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 4 4 = 0 := by
  have h0 := hX.entry 0 5 21
  have h1 := hX.entry 1 0 10
  have h2 := hX.entry 1 3 16
  have h3 := hX.entry 1 4 18
  have h4 := hX.entry 1 7 21
  have h5 := hX.entry 2 5 16
  have h6 := hX.entry 2 6 18
  have h7 := hX.entry 3 0 6
  have h8 := quotientCoordinate_entries hq 13
  have h9 := hi 12
  simp at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  clear hX hq hi
  grind
private theorem zeroDiagonal5 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 5 5 = 0 := by
  have h0 := hX.entry 0 5 21
  have h1 := hX.entry 1 0 10
  have h2 := hX.entry 1 7 21
  have h3 := quotientCoordinate_entries hq 13
  have h4 := hi 12
  have h5 := hi 13
  simp at h0 h1 h2 h3 h4 h5
  clear hX hq hi
  grind
private theorem zeroDiagonal6 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 6 6 = 0 := by
  have h0 := hX.entry 0 5 21
  have h1 := hX.entry 0 8 23
  have h2 := hX.entry 1 0 10
  have h3 := hX.entry 1 3 16
  have h4 := hX.entry 1 7 21
  have h5 := hX.entry 1 11 23
  have h6 := hX.entry 2 0 8
  have h7 := hX.entry 2 5 16
  have h8 := hX.entry 3 0 6
  have h9 := quotientCoordinate_entries hq 12
  have h10 := quotientCoordinate_entries hq 13
  have h11 := hi 12
  have h12 := hi 13
  simp at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  clear hX hq hi
  grind
private theorem zeroDiagonal7 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 7 7 = 0 := by
  have h0 := quotientCoordinate_entries hq 13
  have h1 := hi 13
  simp at h0 h1
  clear hX hq hi
  grind
private theorem zeroDiagonal8 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 8 8 = 0 := by
  have h0 := hX.entry 0 8 23
  have h1 := hX.entry 1 0 10
  have h2 := hX.entry 1 11 23
  have h3 := quotientCoordinate_entries hq 12
  have h4 := hi 12
  have h5 := hi 13
  simp at h0 h1 h2 h3 h4 h5
  clear hX hq hi
  grind
private theorem zeroDiagonal9 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 9 9 = 0 := by
  have h0 := hX.entry 0 5 21
  have h1 := hX.entry 0 6 22
  have h2 := hX.entry 0 8 23
  have h3 := hX.entry 1 3 16
  have h4 := hX.entry 1 7 21
  have h5 := hX.entry 1 9 22
  have h6 := hX.entry 1 11 23
  have h7 := hX.entry 2 0 8
  have h8 := hX.entry 2 5 16
  have h9 := hX.entry 3 0 6
  have h10 := quotientCoordinate_entries hq 12
  have h11 := quotientCoordinate_entries hq 13
  have h12 := hi 13
  simp at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  clear hX hq hi
  grind
private theorem zeroDiagonal10 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 10 10 = 0 := by
  have h0 := hi 12
  simp at h0
  clear hX hq hi
  grind
private theorem zeroDiagonal11 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 11 11 = 0 := by
  have h0 := quotientCoordinate_entries hq 12
  have h1 := hi 13
  simp at h0 h1
  clear hX hq hi
  grind
private theorem zeroDiagonal12 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 12 12 = 0 := by
  have h0 := hX.entry 0 0 12
  have h1 := hX.entry 1 1 12
  simp at h0 h1
  clear hX hq hi
  grind
private theorem zeroDiagonal13 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 13 13 = 0 := by
  have h0 := hX.entry 0 0 13
  simp at h0
  clear hX hq hi
  grind
private theorem zeroDiagonal14 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 14 14 = 0 := by
  have h0 := hX.entry 0 8 23
  have h1 := hX.entry 1 2 14
  have h2 := hX.entry 1 11 23
  have h3 := hX.entry 2 0 8
  have h4 := quotientCoordinate_entries hq 12
  have h5 := hi 13
  simp at h0 h1 h2 h3 h4 h5
  clear hX hq hi
  grind
private theorem zeroDiagonal15 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 15 15 = 0 := by
  have h0 := hX.entry 0 1 15
  have h1 := hX.entry 1 0 10
  have h2 := hi 12
  simp at h0 h1 h2
  clear hX hq hi
  grind
private theorem zeroDiagonal16 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 16 16 = 0 := by
  have h0 := hX.entry 0 5 21
  have h1 := hX.entry 0 8 23
  have h2 := hX.entry 1 7 21
  have h3 := hX.entry 1 11 23
  have h4 := hX.entry 2 0 8
  have h5 := hX.entry 2 5 16
  have h6 := quotientCoordinate_entries hq 12
  have h7 := quotientCoordinate_entries hq 13
  have h8 := hi 13
  simp at h0 h1 h2 h3 h4 h5 h6 h7 h8
  clear hX hq hi
  grind
private theorem zeroDiagonal17 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 17 17 = 0 := by
  have h0 := hX.entry 0 2 17
  have h1 := hX.entry 0 8 23
  have h2 := hX.entry 1 0 10
  have h3 := hX.entry 1 11 23
  have h4 := hX.entry 2 0 8
  have h5 := quotientCoordinate_entries hq 12
  have h6 := hi 12
  have h7 := hi 13
  simp at h0 h1 h2 h3 h4 h5 h6 h7
  clear hX hq hi
  grind
private theorem zeroDiagonal18 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 18 18 = 0 := by
  have h0 := hX.entry 0 5 21
  have h1 := hX.entry 1 3 16
  have h2 := hX.entry 1 7 21
  have h3 := hX.entry 2 5 16
  have h4 := hX.entry 2 6 18
  have h5 := hX.entry 3 0 6
  have h6 := quotientCoordinate_entries hq 13
  have h7 := hi 13
  simp at h0 h1 h2 h3 h4 h5 h6 h7
  clear hX hq hi
  grind
private theorem zeroDiagonal19 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 19 19 = 0 := by
  have h0 := hX.entry 0 3 19
  have h1 := hX.entry 0 5 21
  have h2 := hX.entry 0 8 23
  have h3 := hX.entry 1 0 10
  have h4 := hX.entry 1 3 16
  have h5 := hX.entry 1 7 21
  have h6 := hX.entry 1 11 23
  have h7 := hX.entry 2 0 8
  have h8 := hX.entry 2 5 16
  have h9 := quotientCoordinate_entries hq 12
  have h10 := quotientCoordinate_entries hq 13
  have h11 := hi 12
  have h12 := hi 13
  simp at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  clear hX hq hi
  grind
private theorem zeroDiagonal20 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 20 20 = 0 := by
  have h0 := hX.entry 0 4 20
  have h1 := hX.entry 0 5 21
  have h2 := hX.entry 1 0 10
  have h3 := hX.entry 1 3 16
  have h4 := hX.entry 1 4 18
  have h5 := hX.entry 1 7 21
  have h6 := hX.entry 2 5 16
  have h7 := hX.entry 2 6 18
  have h8 := hX.entry 3 0 6
  have h9 := quotientCoordinate_entries hq 13
  have h10 := hi 12
  have h11 := hi 13
  simp at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  clear hX hq hi
  grind
private theorem zeroDiagonal21 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 21 21 = 0 := by
  have h0 := hX.entry 1 0 10
  have h1 := hX.entry 1 7 21
  have h2 := quotientCoordinate_entries hq 13
  have h3 := hi 12
  simp at h0 h1 h2 h3
  clear hX hq hi
  grind
private theorem zeroDiagonal22 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 22 22 = 0 := by
  have h0 := hX.entry 0 5 21
  have h1 := hX.entry 0 6 22
  have h2 := hX.entry 0 8 23
  have h3 := hX.entry 1 0 10
  have h4 := hX.entry 1 3 16
  have h5 := hX.entry 1 7 21
  have h6 := hX.entry 1 11 23
  have h7 := hX.entry 2 0 8
  have h8 := hX.entry 2 5 16
  have h9 := hX.entry 3 0 6
  have h10 := quotientCoordinate_entries hq 12
  have h11 := quotientCoordinate_entries hq 13
  have h12 := hi 12
  simp at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  clear hX hq hi
  grind
private theorem zeroDiagonal23 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 23 23 = 0 := by
  have h0 := hX.entry 1 0 10
  have h1 := hX.entry 1 11 23
  have h2 := quotientCoordinate_entries hq 12
  have h3 := hi 12
  simp at h0 h1 h2 h3
  clear hX hq hi
  grind
private theorem zeroDiagonal24 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 24 24 = 0 := by
  have h0 := hX.entry 0 10 24
  have h1 := hi 12
  have h2 := hi 13
  simp at h0 h1 h2
  clear hX hq hi
  grind
private theorem zeroDiagonal25 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X 25 25 = 0 := by
  have h0 := hX.entry 0 0 12
  have h1 := hX.entry 0 12 25
  have h2 := hX.entry 1 1 12
  have h3 := hi 13
  simp at h0 h1 h2 h3
  clear hX hq hi
  grind
private theorem zeroCross1213 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X) :
    X 12 13 = 0 := by
  have h0 := hX.entry 0 0 13
  have h1 := hX.entry 1 1 13
  simp at h0 h1
  grind

private theorem zeroCross1312 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X) :
    X 13 12 = 0 := by
  have h0 := hX.entry 0 0 12
  simp at h0
  grind

/-- A homogeneous derivation of degree zero is determined by its quotient and ideal coordinates. -/
theorem eq_zero_of_isHomogeneous_zero {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous 0 X) (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 := by
  ext i j
  rw [Matrix.zero_apply]
  by_cases hij : f4ShortRootWeight i = f4ShortRootWeight j
  · rcases (weight_eq_iff i j).mp hij with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · fin_cases i <;> first
        | apply zeroDiagonal0 hX hq hi | apply zeroDiagonal1 hX hq hi
        | apply zeroDiagonal2 hX hq hi | apply zeroDiagonal3 hX hq hi
        | apply zeroDiagonal4 hX hq hi | apply zeroDiagonal5 hX hq hi
        | apply zeroDiagonal6 hX hq hi | apply zeroDiagonal7 hX hq hi
        | apply zeroDiagonal8 hX hq hi | apply zeroDiagonal9 hX hq hi
        | apply zeroDiagonal10 hX hq hi | apply zeroDiagonal11 hX hq hi
        | apply zeroDiagonal12 hX hq hi | apply zeroDiagonal13 hX hq hi
        | apply zeroDiagonal14 hX hq hi | apply zeroDiagonal15 hX hq hi
        | apply zeroDiagonal16 hX hq hi | apply zeroDiagonal17 hX hq hi
        | apply zeroDiagonal18 hX hq hi | apply zeroDiagonal19 hX hq hi
        | apply zeroDiagonal20 hX hq hi | apply zeroDiagonal21 hX hq hi
        | apply zeroDiagonal22 hX hq hi | apply zeroDiagonal23 hX hq hi
        | apply zeroDiagonal24 hX hq hi | apply zeroDiagonal25 hX hq hi
    · exact zeroCross1213 hX
    · exact zeroCross1312 hX
  · exact hhom.eq_zero i j (by simpa [entryDegree_eq_zero_iff] using hij)

end TauCeti.F4ShortRoot
