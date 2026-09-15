/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.DerivationHomogeneousBlock

/-! # Certified nonzero homogeneous blocks for type-F4 derivations -/

public section

namespace TauCeti.F4ShortRoot

universe u
variable {R : Type u} [CommRing R] [CharP R 2]

private def block112 : HomogeneousBlock 2 where
  degree := ![1, -2, 1, 2]
  positions :=
    ![(8, 9), (16, 17)]
  constraints :=
    ![.entry 1 3 17, .entry 1 8 22]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse112 : block112.B * block112.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective112 : Function.Injective block112.positions := by
  decide +kernel

private theorem blockSupport112 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block112.degree k) ↔
      ∃ q, block112.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 112, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock112 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -2, 1, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block112.eq_zero blockLeftInverse112 blockPositionsInjective112
    blockSupport112 hX (by simpa [block112] using hhom) hq hi

private def block113 : HomogeneousBlock 2 where
  degree := ![1, -2, 2, -1]
  positions :=
    ![(19, 2), (23, 6)]
  constraints :=
    ![.entry 0 3 2, .entry 0 8 6]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse113 : block113.B * block113.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective113 : Function.Injective block113.positions := by
  decide +kernel

private theorem blockSupport113 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block113.degree k) ↔
      ∃ q, block113.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 113, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock113 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -2, 2, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block113.eq_zero blockLeftInverse113 blockPositionsInjective113
    blockSupport113 hX (by simpa [block113] using hhom) hq hi

private def block114 : HomogeneousBlock 6 where
  degree := ![1, -2, 2, 0]
  positions :=
    ![(3, 2), (8, 6), (11, 9), (16, 14), (19, 17), (23, 22)]
  constraints :=
    ![.entry 0 3 17, .entry 0 8 22, .entry 1 3 14, .entry 1 11 22, .entry 2 0 6, .quotient 14]
  B := binaryMatrix ![32, 48, 58, 36, 33, 50]

private theorem blockLeftInverse114 : block114.B * block114.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective114 : Function.Injective block114.positions := by
  decide +kernel

private theorem blockSupport114 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block114.degree k) ↔
      ∃ q, block114.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 114, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock114 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -2, 2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block114.eq_zero blockLeftInverse114 blockPositionsInjective114
    blockSupport114 hX (by simpa [block114] using hhom) hq hi

private def block115 : HomogeneousBlock 2 where
  degree := ![1, -2, 2, 1]
  positions :=
    ![(3, 17), (8, 22)]
  constraints :=
    ![.entry 2 0 22, .entry 2 3 25]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse115 : block115.B * block115.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective115 : Function.Injective block115.positions := by
  decide +kernel

private theorem blockSupport115 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block115.degree k) ↔
      ∃ q, block115.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 115, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock115 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -2, 2, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block115.eq_zero blockLeftInverse115 blockPositionsInjective115
    blockSupport115 hX (by simpa [block115] using hhom) hq hi

private def block116 : HomogeneousBlock 2 where
  degree := ![1, -2, 3, -2]
  positions :=
    ![(11, 6), (19, 14)]
  constraints :=
    ![.entry 0 3 14, .entry 0 11 22]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse116 : block116.B * block116.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective116 : Function.Injective block116.positions := by
  decide +kernel

private theorem blockSupport116 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block116.degree k) ↔
      ∃ q, block116.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 116, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock116 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -2, 3, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block116.eq_zero blockLeftInverse116 blockPositionsInjective116
    blockSupport116 hX (by simpa [block116] using hhom) hq hi

private def block117 : HomogeneousBlock 2 where
  degree := ![1, -2, 3, -1]
  positions :=
    ![(3, 14), (11, 22)]
  constraints :=
    ![.entry 2 1 22, .entry 2 3 24]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse117 : block117.B * block117.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective117 : Function.Injective block117.positions := by
  decide +kernel

private theorem blockSupport117 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block117.degree k) ↔
      ∃ q, block117.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 117, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock117 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -2, 3, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block117.eq_zero blockLeftInverse117 blockPositionsInjective117
    blockSupport117 hX (by simpa [block117] using hhom) hq hi

private def block118 : HomogeneousBlock 2 where
  degree := ![1, -1, -1, 2]
  positions :=
    ![(16, 1), (24, 9)]
  constraints :=
    ![.entry 0 10 9, .entry 0 16 15]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse118 : block118.B * block118.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective118 : Function.Injective block118.positions := by
  decide +kernel

private theorem blockSupport118 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block118.degree k) ↔
      ∃ q, block118.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 118, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock118 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, -1, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block118.eq_zero blockLeftInverse118 blockPositionsInjective118
    blockSupport118 hX (by simpa [block118] using hhom) hq hi

private def block119 : HomogeneousBlock 2 where
  degree := ![1, -1, -1, 3]
  positions :=
    ![(10, 9), (16, 15)]
  constraints :=
    ![.entry 1 0 9, .entry 1 3 15]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse119 : block119.B * block119.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective119 : Function.Injective block119.positions := by
  decide +kernel

private theorem blockSupport119 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block119.degree k) ↔
      ∃ q, block119.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 119, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock119 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, -1, 3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block119.eq_zero blockLeftInverse119 blockPositionsInjective119
    blockSupport119 hX (by simpa [block119] using hhom) hq hi

private def block120 : HomogeneousBlock 6 where
  degree := ![1, -1, 0, 0]
  positions :=
    ![(16, 0), (19, 1), (21, 2), (23, 4), (24, 6), (25, 9)]
  constraints :=
    ![.entry 0 3 1, .entry 0 5 2, .entry 0 8 4, .entry 0 10 6, .entry 0 12 9, .quotient 24]
  B := binaryMatrix ![32, 33, 34, 36, 40, 48]

private theorem blockLeftInverse120 : block120.B * block120.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective120 : Function.Injective block120.positions := by
  decide +kernel

private theorem blockSupport120 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block120.degree k) ↔
      ∃ q, block120.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 120, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock120 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, 0, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block120.eq_zero blockLeftInverse120 blockPositionsInjective120
    blockSupport120 hX (by simpa [block120] using hhom) hq hi

private def block121 : HomogeneousBlock 12 where
  degree := ![1, -1, 0, 1]
  positions :=
    ![(3, 1), (5, 2), (8, 4), (10, 6), (12, 9), (13, 9), (16, 12), (16, 13), (19, 15),
      (21, 17), (23, 20), (24, 22)]
  constraints :=
    ![.entry 0 0 9, .entry 0 3 15, .entry 0 5 17, .entry 0 8 20, .entry 0 10 22,
      .entry 0 16 25, .entry 1 0 6, .entry 1 1 9, .entry 1 3 13, .entry 1 5 14,
      .entry 1 8 18, .ideal 16]
  B := binaryMatrix ![2048, 2560, 3072, 2112, 2177, 1, 32, 2304, 2050, 2564, 3080, 2128]

private theorem blockLeftInverse121 : block121.B * block121.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective121 : Function.Injective block121.positions := by
  decide +kernel

private theorem blockSupport121 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block121.degree k) ↔
      ∃ q, block121.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 121, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock121 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, 0, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block121.eq_zero blockLeftInverse121 blockPositionsInjective121
    blockSupport121 hX (by simpa [block121] using hhom) hq hi

private def block122 : HomogeneousBlock 6 where
  degree := ![1, -1, 0, 2]
  positions :=
    ![(0, 9), (3, 15), (5, 17), (8, 20), (10, 22), (16, 25)]
  constraints :=
    ![.entry 1 0 22, .entry 1 3 25, .entry 2 0 20, .entry 2 5 25, .entry 4 0 17, .quotient 5]
  B := binaryMatrix ![32, 58, 48, 36, 33, 56]

private theorem blockLeftInverse122 : block122.B * block122.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective122 : Function.Injective block122.positions := by
  decide +kernel

private theorem blockSupport122 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block122.degree k) ↔
      ∃ q, block122.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 122, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock122 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, 0, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block122.eq_zero blockLeftInverse122 blockPositionsInjective122
    blockSupport122 hX (by simpa [block122] using hhom) hq hi

private def block123 : HomogeneousBlock 2 where
  degree := ![1, -1, 1, -2]
  positions :=
    ![(19, 0), (25, 6)]
  constraints :=
    ![.entry 0 7 2, .entry 0 12 6]
  B := binaryMatrix ![1, 3]

private theorem blockLeftInverse123 : block123.B * block123.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective123 : Function.Injective block123.positions := by
  decide +kernel

private theorem blockSupport123 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block123.degree k) ↔
      ∃ q, block123.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 123, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock123 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, 1, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block123.eq_zero blockLeftInverse123 blockPositionsInjective123
    blockSupport123 hX (by simpa [block123] using hhom) hq hi

private def block124 : HomogeneousBlock 12 where
  degree := ![1, -1, 1, -1]
  positions :=
    ![(3, 0), (7, 2), (11, 4), (12, 6), (13, 6), (15, 9), (16, 10), (19, 12), (19, 13),
      (21, 14), (23, 18), (25, 22)]
  constraints :=
    ![.entry 0 0 6, .entry 0 1 9, .entry 0 3 12, .entry 0 3 13, .entry 0 5 14, .entry 0 7 17,
      .entry 0 8 18, .entry 0 11 20, .entry 0 12 22, .entry 0 16 24, .entry 1 1 6, .ideal 19]
  B := binaryMatrix ![2048, 2080, 2176, 3073, 2049, 2050, 2560, 2052, 2056, 2064, 2112, 3329]

private theorem blockLeftInverse124 : block124.B * block124.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective124 : Function.Injective block124.positions := by
  decide +kernel

private theorem blockSupport124 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block124.degree k) ↔
      ∃ q, block124.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 124, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock124 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, 1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block124.eq_zero blockLeftInverse124 blockPositionsInjective124
    blockSupport124 hX (by simpa [block124] using hhom) hq hi

private def block125 : HomogeneousBlock 12 where
  degree := ![1, -1, 1, 0]
  positions :=
    ![(0, 6), (1, 9), (3, 12), (3, 13), (5, 14), (7, 17), (8, 18), (11, 20), (12, 22),
      (13, 22), (16, 24), (19, 25)]
  constraints :=
    ![.entry 0 0 22, .entry 0 3 25, .entry 1 1 22, .entry 1 3 24, .entry 2 0 18, .entry 2 1 20,
      .entry 2 2 22, .entry 2 3 23, .entry 2 5 24, .entry 2 7 25, .entry 4 0 14, .ideal 3]
  B := binaryMatrix ![2048, 2117, 3464, 128, 3072, 3978, 2064, 2149, 64, 2049, 3328, 3466]

private theorem blockLeftInverse125 : block125.B * block125.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective125 : Function.Injective block125.positions := by
  decide +kernel

private theorem blockSupport125 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block125.degree k) ↔
      ∃ q, block125.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 125, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock125 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, 1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block125.eq_zero blockLeftInverse125 blockPositionsInjective125
    blockSupport125 hX (by simpa [block125] using hhom) hq hi

end TauCeti.F4ShortRoot
