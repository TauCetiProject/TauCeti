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

private def block126 : HomogeneousBlock 2 where
  degree := ![1, -1, 1, 1]
  positions :=
    ![(0, 22), (3, 25)]
  constraints :=
    ![.entry 6 0 25, .entry 9 0 24]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse126 : block126.B * block126.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective126 : Function.Injective block126.positions := by
  decide +kernel

private theorem blockSupport126 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block126.degree k) ↔
      ∃ q, block126.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 126, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock126 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, 1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block126.eq_zero blockLeftInverse126 blockPositionsInjective126
    blockSupport126 hX (by simpa [block126] using hhom) hq hi

private def block127 : HomogeneousBlock 2 where
  degree := ![1, -1, 2, -3]
  positions :=
    ![(15, 6), (19, 10)]
  constraints :=
    ![.entry 0 1 6, .entry 0 3 10]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse127 : block127.B * block127.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective127 : Function.Injective block127.positions := by
  decide +kernel

private theorem blockSupport127 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block127.degree k) ↔
      ∃ q, block127.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 127, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock127 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, 2, -3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block127.eq_zero blockLeftInverse127 blockPositionsInjective127
    blockSupport127 hX (by simpa [block127] using hhom) hq hi

private def block128 : HomogeneousBlock 6 where
  degree := ![1, -1, 2, -2]
  positions :=
    ![(1, 6), (3, 10), (7, 14), (11, 18), (15, 22), (19, 24)]
  constraints :=
    ![.entry 0 1 22, .entry 0 3 24, .entry 2 1 18, .entry 2 7 24, .entry 4 1 14, .quotient 6]
  B := binaryMatrix ![32, 58, 48, 36, 33, 56]

private theorem blockLeftInverse128 : block128.B * block128.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective128 : Function.Injective block128.positions := by
  decide +kernel

private theorem blockSupport128 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block128.degree k) ↔
      ∃ q, block128.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 128, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock128 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, 2, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block128.eq_zero blockLeftInverse128 blockPositionsInjective128
    blockSupport128 hX (by simpa [block128] using hhom) hq hi

private def block129 : HomogeneousBlock 2 where
  degree := ![1, -1, 2, -1]
  positions :=
    ![(1, 22), (3, 24)]
  constraints :=
    ![.entry 6 0 24, .entry 6 1 25]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse129 : block129.B * block129.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective129 : Function.Injective block129.positions := by
  decide +kernel

private theorem blockSupport129 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block129.degree k) ↔
      ∃ q, block129.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 129, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock129 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, -1, 2, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block129.eq_zero blockLeftInverse129 blockPositionsInjective129
    blockSupport129 hX (by simpa [block129] using hhom) hq hi

private def block130 : HomogeneousBlock 2 where
  degree := ![1, 0, -2, 1]
  positions :=
    ![(21, 1), (24, 4)]
  constraints :=
    ![.entry 0 5 1, .entry 0 10 4]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse130 : block130.B * block130.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective130 : Function.Injective block130.positions := by
  decide +kernel

private theorem blockSupport130 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block130.degree k) ↔
      ∃ q, block130.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 130, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock130 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, -2, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block130.eq_zero blockLeftInverse130 blockPositionsInjective130
    blockSupport130 hX (by simpa [block130] using hhom) hq hi

private def block131 : HomogeneousBlock 6 where
  degree := ![1, 0, -2, 2]
  positions :=
    ![(5, 1), (10, 4), (14, 9), (16, 11), (21, 15), (24, 20)]
  constraints :=
    ![.entry 0 5 15, .entry 0 10 20, .entry 1 0 4, .entry 1 2 9, .entry 1 3 11, .quotient 16]
  B := binaryMatrix ![32, 36, 40, 48, 33, 38]

private theorem blockLeftInverse131 : block131.B * block131.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective131 : Function.Injective block131.positions := by
  decide +kernel

private theorem blockSupport131 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block131.degree k) ↔
      ∃ q, block131.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 131, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock131 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, -2, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block131.eq_zero blockLeftInverse131 blockPositionsInjective131
    blockSupport131 hX (by simpa [block131] using hhom) hq hi

private def block132 : HomogeneousBlock 2 where
  degree := ![1, 0, -2, 3]
  positions :=
    ![(5, 15), (10, 20)]
  constraints :=
    ![.entry 1 0 20, .entry 1 5 25]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse132 : block132.B * block132.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective132 : Function.Injective block132.positions := by
  decide +kernel

private theorem blockSupport132 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block132.degree k) ↔
      ∃ q, block132.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 132, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock132 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, -2, 3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block132.eq_zero blockLeftInverse132 blockPositionsInjective132
    blockSupport132 hX (by simpa [block132] using hhom) hq hi

private def block133 : HomogeneousBlock 2 where
  degree := ![1, 0, -1, -1]
  positions :=
    ![(21, 0), (25, 4)]
  constraints :=
    ![.entry 0 7 1, .entry 0 12 4]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse133 : block133.B * block133.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective133 : Function.Injective block133.positions := by
  decide +kernel

private theorem blockSupport133 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block133.degree k) ↔
      ∃ q, block133.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 133, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock133 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, -1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block133.eq_zero blockLeftInverse133 blockPositionsInjective133
    blockSupport133 hX (by simpa [block133] using hhom) hq hi

private def block134 : HomogeneousBlock 12 where
  degree := ![1, 0, -1, 0]
  positions :=
    ![(5, 0), (7, 1), (12, 4), (13, 4), (14, 6), (16, 8), (17, 9), (19, 11), (21, 12),
      (21, 13), (24, 18), (25, 20)]
  constraints :=
    ![.entry 0 0 4, .entry 0 2 9, .entry 0 3 11, .entry 0 5 12, .entry 0 5 13, .entry 0 7 15,
      .entry 0 10 18, .entry 0 12 20, .entry 0 14 22, .entry 0 16 23, .entry 1 1 4, .ideal 21]
  B := binaryMatrix ![2048, 2080, 1057, 2049, 2304, 2560, 2050, 2052, 2056, 16, 2112, 3233]

private theorem blockLeftInverse134 : block134.B * block134.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective134 : Function.Injective block134.positions := by
  decide +kernel

private theorem blockSupport134 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block134.degree k) ↔
      ∃ q, block134.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 134, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock134 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, -1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block134.eq_zero blockLeftInverse134 blockPositionsInjective134
    blockSupport134 hX (by simpa [block134] using hhom) hq hi

private def block135 : HomogeneousBlock 12 where
  degree := ![1, 0, -1, 1]
  positions :=
    ![(0, 4), (2, 9), (3, 11), (5, 12), (5, 13), (7, 15), (10, 18), (12, 20), (13, 20),
      (14, 22), (16, 23), (21, 25)]
  constraints :=
    ![.entry 0 0 20, .entry 0 5 25, .entry 1 0 18, .entry 1 1 20, .entry 1 2 22, .entry 1 3 23,
      .entry 1 5 24, .entry 1 7 25, .entry 2 2 20, .entry 2 5 23, .entry 3 3 20, .ideal 5]
  B := binaryMatrix ![2048, 2313, 3081, 3689, 3625, 3819, 2052, 2057, 2049, 2329, 3113, 3691]

private theorem blockLeftInverse135 : block135.B * block135.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective135 : Function.Injective block135.positions := by
  decide +kernel

private theorem blockSupport135 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block135.degree k) ↔
      ∃ q, block135.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 135, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock135 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, -1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block135.eq_zero blockLeftInverse135 blockPositionsInjective135
    blockSupport135 hX (by simpa [block135] using hhom) hq hi

private def block136 : HomogeneousBlock 2 where
  degree := ![1, 0, -1, 2]
  positions :=
    ![(0, 20), (5, 25)]
  constraints :=
    ![.entry 4 0 25, .entry 9 0 23]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse136 : block136.B * block136.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective136 : Function.Injective block136.positions := by
  decide +kernel

private theorem blockSupport136 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block136.degree k) ↔
      ∃ q, block136.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 136, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock136 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, -1, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block136.eq_zero blockLeftInverse136 blockPositionsInjective136
    blockSupport136 hX (by simpa [block136] using hhom) hq hi

private def block137 : HomogeneousBlock 6 where
  degree := ![1, 0, 0, -2]
  positions :=
    ![(7, 0), (15, 4), (17, 6), (19, 8), (21, 10), (25, 18)]
  constraints :=
    ![.entry 0 1 4, .entry 0 2 6, .entry 0 3 8, .entry 0 5 10, .entry 0 12 18, .quotient 18]
  B := binaryMatrix ![32, 33, 34, 36, 40, 48]

private theorem blockLeftInverse137 : block137.B * block137.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective137 : Function.Injective block137.positions := by
  decide +kernel

private theorem blockSupport137 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block137.degree k) ↔
      ∃ q, block137.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 137, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock137 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, 0, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block137.eq_zero blockLeftInverse137 blockPositionsInjective137
    blockSupport137 hX (by simpa [block137] using hhom) hq hi

private def block138 : HomogeneousBlock 12 where
  degree := ![1, 0, 0, -1]
  positions :=
    ![(1, 4), (2, 6), (3, 8), (5, 10), (7, 12), (7, 13), (12, 18), (13, 18), (15, 20),
      (17, 22), (19, 23), (21, 24)]
  constraints :=
    ![.entry 0 0 18, .entry 0 1 20, .entry 0 2 22, .entry 0 3 23, .entry 0 5 24, .entry 0 7 25,
      .entry 1 1 18, .entry 1 7 24, .entry 2 2 18, .entry 2 7 23, .entry 3 3 18, .ideal 7]
  B := binaryMatrix ![2048, 2369, 3137, 3833, 32, 3657, 2113, 1, 2050, 2373, 3145, 3817]

private theorem blockLeftInverse138 : block138.B * block138.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective138 : Function.Injective block138.positions := by
  decide +kernel

private theorem blockSupport138 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block138.degree k) ↔
      ∃ q, block138.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 138, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock138 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, 0, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block138.eq_zero blockLeftInverse138 blockPositionsInjective138
    blockSupport138 hX (by simpa [block138] using hhom) hq hi

private def block139 : HomogeneousBlock 6 where
  degree := ![1, 0, 0, 0]
  positions :=
    ![(0, 18), (1, 20), (2, 22), (3, 23), (5, 24), (7, 25)]
  constraints :=
    ![.entry 4 0 24, .entry 4 1 25, .entry 6 0 23, .entry 6 2 25, .entry 8 0 22, .quotient 0]
  B := binaryMatrix ![32, 58, 48, 36, 33, 56]

private theorem blockLeftInverse139 : block139.B * block139.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective139 : Function.Injective block139.positions := by
  decide +kernel

private theorem blockSupport139 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block139.degree k) ↔
      ∃ q, block139.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 139, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock139 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, 0, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block139.eq_zero blockLeftInverse139 blockPositionsInjective139
    blockSupport139 hX (by simpa [block139] using hhom) hq hi

end TauCeti.F4ShortRoot
