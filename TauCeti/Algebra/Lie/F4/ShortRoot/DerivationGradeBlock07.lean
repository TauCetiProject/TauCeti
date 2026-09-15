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

private def block098 : HomogeneousBlock 2 where
  degree := ![0, 1, -1, -2]
  positions :=
    ![(17, 0), (25, 8)]
  constraints :=
    ![.entry 0 7 3, .entry 0 12 8]
  B := binaryMatrix ![1, 3]

private theorem blockLeftInverse098 : block098.B * block098.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective098 : Function.Injective block098.positions := by
  decide +kernel

private theorem blockSupport098 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block098.degree k) ↔
      ∃ q, block098.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 98, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock098 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, -1, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block098.eq_zero blockLeftInverse098 blockPositionsInjective098
    blockSupport098 hX (by simpa [block098] using hhom) hq hi

private def block099 : HomogeneousBlock 12 where
  degree := ![0, 1, -1, -1]
  positions :=
    ![(2, 0), (7, 3), (9, 4), (12, 8), (13, 8), (14, 10), (15, 11), (17, 12), (17, 13),
      (21, 16), (22, 18), (25, 23)]
  constraints :=
    ![.entry 0 0 8, .entry 0 1 11, .entry 0 2 12, .entry 0 2 13, .entry 0 5 16, .entry 0 6 18,
      .entry 0 7 19, .entry 0 9 20, .entry 0 12 23, .entry 0 14 24, .entry 1 1 8, .ideal 17]
  B := binaryMatrix ![2048, 2112, 2176, 3073, 2049, 2560, 2050, 2052, 2056, 2064, 2080, 3329]

private theorem blockLeftInverse099 : block099.B * block099.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective099 : Function.Injective block099.positions := by
  decide +kernel

private theorem blockSupport099 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block099.degree k) ↔
      ∃ q, block099.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 99, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock099 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, -1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block099.eq_zero blockLeftInverse099 blockPositionsInjective099
    blockSupport099 hX (by simpa [block099] using hhom) hq hi

private def block100 : HomogeneousBlock 12 where
  degree := ![0, 1, -1, 0]
  positions :=
    ![(0, 8), (1, 11), (2, 12), (2, 13), (5, 16), (6, 18), (7, 19), (9, 20), (12, 23),
      (13, 23), (14, 24), (17, 25)]
  constraints :=
    ![.entry 0 0 23, .entry 0 2 25, .entry 1 1 23, .entry 1 2 24, .entry 2 2 23, .entry 3 0 18,
      .entry 3 1 20, .entry 3 2 22, .entry 3 5 24, .entry 3 7 25, .entry 4 0 16, .ideal 2]
  B := binaryMatrix ![2048, 2197, 3464, 128, 3072, 2080, 3978, 2261, 144, 2049, 3328, 3466]

private theorem blockLeftInverse100 : block100.B * block100.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective100 : Function.Injective block100.positions := by
  decide +kernel

private theorem blockSupport100 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block100.degree k) ↔
      ∃ q, block100.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 100, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock100 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, -1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block100.eq_zero blockLeftInverse100 blockPositionsInjective100
    blockSupport100 hX (by simpa [block100] using hhom) hq hi

private def block101 : HomogeneousBlock 2 where
  degree := ![0, 1, -1, 1]
  positions :=
    ![(0, 23), (2, 25)]
  constraints :=
    ![.entry 8 0 25, .entry 11 0 24]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse101 : block101.B * block101.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective101 : Function.Injective block101.positions := by
  decide +kernel

private theorem blockSupport101 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block101.degree k) ↔
      ∃ q, block101.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 101, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock101 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, -1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block101.eq_zero blockLeftInverse101 blockPositionsInjective101
    blockSupport101 hX (by simpa [block101] using hhom) hq hi

private def block102 : HomogeneousBlock 2 where
  degree := ![0, 1, 0, -3]
  positions :=
    ![(15, 8), (17, 10)]
  constraints :=
    ![.entry 0 1 8, .entry 0 2 10]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse102 : block102.B * block102.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective102 : Function.Injective block102.positions := by
  decide +kernel

private theorem blockSupport102 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block102.degree k) ↔
      ∃ q, block102.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 102, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock102 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, 0, -3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block102.eq_zero blockLeftInverse102 blockPositionsInjective102
    blockSupport102 hX (by simpa [block102] using hhom) hq hi

private def block103 : HomogeneousBlock 6 where
  degree := ![0, 1, 0, -2]
  positions :=
    ![(1, 8), (2, 10), (7, 16), (9, 18), (15, 23), (17, 24)]
  constraints :=
    ![.entry 0 1 23, .entry 0 2 24, .entry 3 1 18, .entry 3 7 24, .entry 4 1 16, .quotient 4]
  B := binaryMatrix ![32, 58, 48, 36, 33, 56]

private theorem blockLeftInverse103 : block103.B * block103.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective103 : Function.Injective block103.positions := by
  decide +kernel

private theorem blockSupport103 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block103.degree k) ↔
      ∃ q, block103.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 103, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock103 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, 0, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block103.eq_zero blockLeftInverse103 blockPositionsInjective103
    blockSupport103 hX (by simpa [block103] using hhom) hq hi

private def block104 : HomogeneousBlock 2 where
  degree := ![0, 1, 0, -1]
  positions :=
    ![(1, 23), (2, 24)]
  constraints :=
    ![.entry 8 0 24, .entry 8 1 25]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse104 : block104.B * block104.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective104 : Function.Injective block104.positions := by
  decide +kernel

private theorem blockSupport104 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block104.degree k) ↔
      ∃ q, block104.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 104, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock104 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, 0, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block104.eq_zero blockLeftInverse104 blockPositionsInjective104
    blockSupport104 hX (by simpa [block104] using hhom) hq hi

private def block105 : HomogeneousBlock 1 where
  degree := ![0, 2, -4, 2]
  positions :=
    ![(14, 11)]
  constraints :=
    ![.entry 1 2 11]
  B := binaryMatrix ![1]

private theorem blockLeftInverse105 : block105.B * block105.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective105 : Function.Injective block105.positions := by
  decide +kernel

private theorem blockSupport105 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block105.degree k) ↔
      ∃ q, block105.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 105, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock105 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 2, -4, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block105.eq_zero blockLeftInverse105 blockPositionsInjective105
    blockSupport105 hX (by simpa [block105] using hhom) hq hi

private def block106 : HomogeneousBlock 2 where
  degree := ![0, 2, -3, 0]
  positions :=
    ![(14, 8), (17, 11)]
  constraints :=
    ![.entry 0 2 11, .entry 0 14 23]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse106 : block106.B * block106.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective106 : Function.Injective block106.positions := by
  decide +kernel

private theorem blockSupport106 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block106.degree k) ↔
      ∃ q, block106.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 106, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock106 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 2, -3, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block106.eq_zero blockLeftInverse106 blockPositionsInjective106
    blockSupport106 hX (by simpa [block106] using hhom) hq hi

private def block107 : HomogeneousBlock 2 where
  degree := ![0, 2, -3, 1]
  positions :=
    ![(2, 11), (14, 23)]
  constraints :=
    ![.entry 1 2 23, .entry 3 2 20]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse107 : block107.B * block107.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective107 : Function.Injective block107.positions := by
  decide +kernel

private theorem blockSupport107 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block107.degree k) ↔
      ∃ q, block107.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 107, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock107 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 2, -3, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block107.eq_zero blockLeftInverse107 blockPositionsInjective107
    blockSupport107 hX (by simpa [block107] using hhom) hq hi

private def block108 : HomogeneousBlock 1 where
  degree := ![0, 2, -2, -2]
  positions :=
    ![(17, 8)]
  constraints :=
    ![.entry 0 2 8]
  B := binaryMatrix ![1]

private theorem blockLeftInverse108 : block108.B * block108.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective108 : Function.Injective block108.positions := by
  decide +kernel

private theorem blockSupport108 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block108.degree k) ↔
      ∃ q, block108.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 108, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock108 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 2, -2, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block108.eq_zero blockLeftInverse108 blockPositionsInjective108
    blockSupport108 hX (by simpa [block108] using hhom) hq hi

private def block109 : HomogeneousBlock 2 where
  degree := ![0, 2, -2, -1]
  positions :=
    ![(2, 8), (17, 23)]
  constraints :=
    ![.entry 0 2 23, .entry 3 2 18]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse109 : block109.B * block109.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective109 : Function.Injective block109.positions := by
  decide +kernel

private theorem blockSupport109 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block109.degree k) ↔
      ∃ q, block109.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 109, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock109 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 2, -2, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block109.eq_zero blockLeftInverse109 blockPositionsInjective109
    blockSupport109 hX (by simpa [block109] using hhom) hq hi

private def block110 : HomogeneousBlock 1 where
  degree := ![0, 2, -2, 0]
  positions :=
    ![(2, 23)]
  constraints :=
    ![.entry 8 0 23]
  B := binaryMatrix ![1]

private theorem blockLeftInverse110 : block110.B * block110.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective110 : Function.Injective block110.positions := by
  decide +kernel

private theorem blockSupport110 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block110.degree k) ↔
      ∃ q, block110.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 110, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock110 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 2, -2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block110.eq_zero blockLeftInverse110 blockPositionsInjective110
    blockSupport110 hX (by simpa [block110] using hhom) hq hi

private def block111 : HomogeneousBlock 2 where
  degree := ![1, -2, 1, 1]
  positions :=
    ![(16, 2), (23, 9)]
  constraints :=
    ![.entry 0 8 9, .entry 0 16 17]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse111 : block111.B * block111.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective111 : Function.Injective block111.positions := by
  decide +kernel

private theorem blockSupport111 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block111.degree k) ↔
      ∃ q, block111.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 111, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock111 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -2, 1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block111.eq_zero blockLeftInverse111 blockPositionsInjective111
    blockSupport111 hX (by simpa [block111] using hhom) hq hi

end TauCeti.F4ShortRoot
