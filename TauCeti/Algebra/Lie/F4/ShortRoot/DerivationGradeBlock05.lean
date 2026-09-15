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

private def block070 : HomogeneousBlock 6 where
  degree := ![0, -1, 2, -2]
  positions :=
    ![(11, 0), (15, 2), (19, 5), (20, 6), (23, 10), (25, 14)]
  constraints :=
    ![.entry 0 1 2, .entry 0 3 5, .entry 0 4 6, .entry 0 8 10, .entry 0 12 14, .quotient 22]
  B := binaryMatrix ![32, 33, 34, 36, 40, 48]

private theorem blockLeftInverse070 : block070.B * block070.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective070 : Function.Injective block070.positions := by
  decide +kernel

private theorem blockSupport070 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block070.degree k) ↔
      ∃ q, block070.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 70, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock070 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 2, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block070.eq_zero blockLeftInverse070 blockPositionsInjective070
    blockSupport070 hX (by simpa [block070] using hhom) hq hi

private def block071 : HomogeneousBlock 12 where
  degree := ![0, -1, 2, -1]
  positions :=
    ![(1, 2), (3, 5), (4, 6), (8, 10), (11, 12), (11, 13), (12, 14), (13, 14), (15, 17),
      (19, 21), (20, 22), (23, 24)]
  constraints :=
    ![.entry 0 0 14, .entry 0 1 17, .entry 0 3 21, .entry 0 4 22, .entry 0 8 24,
      .entry 0 11 25, .entry 1 1 14, .entry 1 11 24, .entry 2 0 10, .entry 2 3 16,
      .entry 2 4 18, .ideal 11]
  B := binaryMatrix ![2048, 2560, 3072, 2304, 32, 2480, 2113, 1, 2050, 2564, 3080, 2320]

private theorem blockLeftInverse071 : block071.B * block071.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective071 : Function.Injective block071.positions := by
  decide +kernel

private theorem blockSupport071 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block071.degree k) ↔
      ∃ q, block071.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 71, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock071 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 2, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block071.eq_zero blockLeftInverse071 blockPositionsInjective071
    blockSupport071 hX (by simpa [block071] using hhom) hq hi

private def block072 : HomogeneousBlock 6 where
  degree := ![0, -1, 2, 0]
  positions :=
    ![(0, 14), (1, 17), (3, 21), (4, 22), (8, 24), (11, 25)]
  constraints :=
    ![.entry 2 0 24, .entry 2 1 25, .entry 5 0 22, .entry 5 3 25, .entry 6 0 21, .quotient 2]
  B := binaryMatrix ![32, 58, 48, 36, 33, 56]

private theorem blockLeftInverse072 : block072.B * block072.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective072 : Function.Injective block072.positions := by
  decide +kernel

private theorem blockSupport072 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block072.degree k) ↔
      ∃ q, block072.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 72, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock072 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block072.eq_zero blockLeftInverse072 blockPositionsInjective072
    blockSupport072 hX (by simpa [block072] using hhom) hq hi

private def block073 : HomogeneousBlock 2 where
  degree := ![0, -1, 3, -3]
  positions :=
    ![(11, 10), (15, 14)]
  constraints :=
    ![.entry 0 1 14, .entry 0 11 24]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse073 : block073.B * block073.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective073 : Function.Injective block073.positions := by
  decide +kernel

private theorem blockSupport073 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block073.degree k) ↔
      ∃ q, block073.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 73, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock073 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 3, -3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block073.eq_zero blockLeftInverse073 blockPositionsInjective073
    blockSupport073 hX (by simpa [block073] using hhom) hq hi

private def block074 : HomogeneousBlock 2 where
  degree := ![0, -1, 3, -2]
  positions :=
    ![(1, 14), (11, 24)]
  constraints :=
    ![.entry 2 1 24, .entry 5 1 22]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse074 : block074.B * block074.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective074 : Function.Injective block074.positions := by
  decide +kernel

private theorem blockSupport074 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block074.degree k) ↔
      ∃ q, block074.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 74, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock074 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 3, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block074.eq_zero blockLeftInverse074 blockPositionsInjective074
    blockSupport074 hX (by simpa [block074] using hhom) hq hi

private def block075 : HomogeneousBlock 1 where
  degree := ![0, 0, -2, 2]
  positions :=
    ![(24, 1)]
  constraints :=
    ![.entry 0 10 1]
  B := binaryMatrix ![1]

private theorem blockLeftInverse075 : block075.B * block075.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective075 : Function.Injective block075.positions := by
  decide +kernel

private theorem blockSupport075 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block075.degree k) ↔
      ∃ q, block075.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 75, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock075 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, -2, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block075.eq_zero blockLeftInverse075 blockPositionsInjective075
    blockSupport075 hX (by simpa [block075] using hhom) hq hi

private def block076 : HomogeneousBlock 2 where
  degree := ![0, 0, -2, 3]
  positions :=
    ![(10, 1), (24, 15)]
  constraints :=
    ![.entry 0 10 15, .entry 1 5 7]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse076 : block076.B * block076.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective076 : Function.Injective block076.positions := by
  decide +kernel

private theorem blockSupport076 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block076.degree k) ↔
      ∃ q, block076.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 76, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock076 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, -2, 3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block076.eq_zero blockLeftInverse076 blockPositionsInjective076
    blockSupport076 hX (by simpa [block076] using hhom) hq hi

private def block077 : HomogeneousBlock 1 where
  degree := ![0, 0, -2, 4]
  positions :=
    ![(10, 15)]
  constraints :=
    ![.entry 1 0 15]
  B := binaryMatrix ![1]

private theorem blockLeftInverse077 : block077.B * block077.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective077 : Function.Injective block077.positions := by
  decide +kernel

private theorem blockSupport077 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block077.degree k) ↔
      ∃ q, block077.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 77, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock077 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, -2, 4] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block077.eq_zero blockLeftInverse077 blockPositionsInjective077
    blockSupport077 hX (by simpa [block077] using hhom) hq hi

private def block078 : HomogeneousBlock 2 where
  degree := ![0, 0, -1, 0]
  positions :=
    ![(24, 0), (25, 1)]
  constraints :=
    ![.entry 0 12 1, .entry 0 13 1]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse078 : block078.B * block078.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective078 : Function.Injective block078.positions := by
  decide +kernel

private theorem blockSupport078 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block078.degree k) ↔
      ∃ q, block078.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 78, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock078 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, -1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block078.eq_zero blockLeftInverse078 blockPositionsInjective078
    blockSupport078 hX (by simpa [block078] using hhom) hq hi

private def block079 : HomogeneousBlock 12 where
  degree := ![0, 0, -1, 1]
  positions :=
    ![(10, 0), (12, 1), (13, 1), (14, 2), (16, 3), (18, 4), (21, 7), (22, 9), (23, 11),
      (24, 12), (24, 13), (25, 15)]
  constraints :=
    ![.entry 0 0 1, .entry 0 5 7, .entry 0 6 9, .entry 0 8 11, .entry 0 10 12, .entry 0 10 13,
      .entry 0 12 15, .entry 0 14 17, .entry 0 16 19, .entry 0 18 20, .entry 1 2 2, .ideal 24]
  B := binaryMatrix ![2048, 3200, 2049, 2176, 2304, 2560, 2050, 2052, 2056, 2064, 2080, 3264]

private theorem blockLeftInverse079 : block079.B * block079.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective079 : Function.Injective block079.positions := by
  decide +kernel

private theorem blockSupport079 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block079.degree k) ↔
      ∃ q, block079.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 79, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock079 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, -1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block079.eq_zero blockLeftInverse079 blockPositionsInjective079
    blockSupport079 hX (by simpa [block079] using hhom) hq hi

private def block080 : HomogeneousBlock 12 where
  degree := ![0, 0, -1, 2]
  positions :=
    ![(0, 1), (5, 7), (6, 9), (8, 11), (10, 12), (10, 13), (12, 15), (13, 15), (14, 17),
      (16, 19), (18, 20), (24, 25)]
  constraints :=
    ![.entry 0 0 15, .entry 0 10 25, .entry 1 0 12, .entry 1 0 13, .entry 1 1 15,
      .entry 1 2 17, .entry 1 3 19, .entry 1 4 20, .entry 1 5 21, .entry 1 6 22,
      .entry 1 8 23, .ideal 10]
  B := binaryMatrix ![2048, 2304, 2560, 3072, 2052, 8, 17, 2049, 2080, 2112, 2176, 2054]

private theorem blockLeftInverse080 : block080.B * block080.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective080 : Function.Injective block080.positions := by
  decide +kernel

private theorem blockSupport080 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block080.degree k) ↔
      ∃ q, block080.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 80, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock080 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, -1, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block080.eq_zero blockLeftInverse080 blockPositionsInjective080
    blockSupport080 hX (by simpa [block080] using hhom) hq hi

private def block081 : HomogeneousBlock 2 where
  degree := ![0, 0, -1, 3]
  positions :=
    ![(0, 15), (10, 25)]
  constraints :=
    ![.entry 1 0 25, .entry 7 0 20]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse081 : block081.B * block081.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective081 : Function.Injective block081.positions := by
  decide +kernel

private theorem blockSupport081 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block081.degree k) ↔
      ∃ q, block081.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 81, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock081 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, -1, 3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block081.eq_zero blockLeftInverse081 blockPositionsInjective081
    blockSupport081 hX (by simpa [block081] using hhom) hq hi

private def block082 : HomogeneousBlock 1 where
  degree := ![0, 0, 0, -2]
  positions :=
    ![(25, 0)]
  constraints :=
    ![.entry 0 15 1]
  B := binaryMatrix ![1]

private theorem blockLeftInverse082 : block082.B * block082.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective082 : Function.Injective block082.positions := by
  decide +kernel

private theorem blockSupport082 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block082.degree k) ↔
      ∃ q, block082.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 82, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock082 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 0, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block082.eq_zero blockLeftInverse082 blockPositionsInjective082
    blockSupport082 hX (by simpa [block082] using hhom) hq hi

private def block083 : HomogeneousBlock 12 where
  degree := ![0, 0, 0, -1]
  positions :=
    ![(12, 0), (13, 0), (15, 1), (17, 2), (19, 3), (20, 4), (21, 5), (22, 6), (23, 8),
      (24, 10), (25, 12), (25, 13)]
  constraints :=
    ![.entry 0 1 1, .entry 0 2 2, .entry 0 3 3, .entry 0 4 4, .entry 0 5 5, .entry 0 6 6,
      .entry 0 7 7, .entry 0 8 8, .entry 0 10 10, .entry 0 12 12, .entry 0 12 13, .ideal 25]
  B := binaryMatrix ![2048, 64, 2113, 2050, 2052, 2056, 2128, 2144, 2240, 2304, 512, 3072]

private theorem blockLeftInverse083 : block083.B * block083.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective083 : Function.Injective block083.positions := by
  decide +kernel

private theorem blockSupport083 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block083.degree k) ↔
      ∃ q, block083.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 83, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock083 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 0, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block083.eq_zero blockLeftInverse083 blockPositionsInjective083
    blockSupport083 hX (by simpa [block083] using hhom) hq hi

end TauCeti.F4ShortRoot
