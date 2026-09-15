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

private def block056 : HomogeneousBlock 2 where
  degree := ![-1, 2, -1, -1]
  positions :=
    ![(2, 16), (9, 23)]
  constraints :=
    ![.entry 3 1 23, .entry 3 2 24]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse056 : block056.B * block056.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective056 : Function.Injective block056.positions := by
  decide +kernel

private theorem blockSupport056 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block056.degree k) ↔
      ∃ q, block056.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 56, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock056 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 2, -1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block056.eq_zero blockLeftInverse056 blockPositionsInjective056
    blockSupport056 hX (by simpa [block056] using hhom) hq hi

private def block057 : HomogeneousBlock 1 where
  degree := ![0, -2, 2, 0]
  positions :=
    ![(23, 2)]
  constraints :=
    ![.entry 0 8 2]
  B := binaryMatrix ![1]

private theorem blockLeftInverse057 : block057.B * block057.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective057 : Function.Injective block057.positions := by
  decide +kernel

private theorem blockSupport057 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block057.degree k) ↔
      ∃ q, block057.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 57, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock057 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -2, 2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block057.eq_zero blockLeftInverse057 blockPositionsInjective057
    blockSupport057 hX (by simpa [block057] using hhom) hq hi

private def block058 : HomogeneousBlock 2 where
  degree := ![0, -2, 2, 1]
  positions :=
    ![(8, 2), (23, 17)]
  constraints :=
    ![.entry 0 8 17, .entry 1 8 14]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse058 : block058.B * block058.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective058 : Function.Injective block058.positions := by
  decide +kernel

private theorem blockSupport058 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block058.degree k) ↔
      ∃ q, block058.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 58, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock058 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -2, 2, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block058.eq_zero blockLeftInverse058 blockPositionsInjective058
    blockSupport058 hX (by simpa [block058] using hhom) hq hi

private def block059 : HomogeneousBlock 1 where
  degree := ![0, -2, 2, 2]
  positions :=
    ![(8, 17)]
  constraints :=
    ![.entry 2 0 17]
  B := binaryMatrix ![1]

private theorem blockLeftInverse059 : block059.B * block059.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective059 : Function.Injective block059.positions := by
  decide +kernel

private theorem blockSupport059 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block059.degree k) ↔
      ∃ q, block059.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 59, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock059 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -2, 2, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block059.eq_zero blockLeftInverse059 blockPositionsInjective059
    blockSupport059 hX (by simpa [block059] using hhom) hq hi

private def block060 : HomogeneousBlock 2 where
  degree := ![0, -2, 3, -1]
  positions :=
    ![(11, 2), (23, 14)]
  constraints :=
    ![.entry 0 8 14, .entry 0 11 17]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse060 : block060.B * block060.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective060 : Function.Injective block060.positions := by
  decide +kernel

private theorem blockSupport060 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block060.degree k) ↔
      ∃ q, block060.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 60, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock060 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -2, 3, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block060.eq_zero blockLeftInverse060 blockPositionsInjective060
    blockSupport060 hX (by simpa [block060] using hhom) hq hi

private def block061 : HomogeneousBlock 2 where
  degree := ![0, -2, 3, 0]
  positions :=
    ![(8, 14), (11, 17)]
  constraints :=
    ![.entry 2 0 14, .entry 2 1 17]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse061 : block061.B * block061.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective061 : Function.Injective block061.positions := by
  decide +kernel

private theorem blockSupport061 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block061.degree k) ↔
      ∃ q, block061.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 61, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock061 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -2, 3, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block061.eq_zero blockLeftInverse061 blockPositionsInjective061
    blockSupport061 hX (by simpa [block061] using hhom) hq hi

private def block062 : HomogeneousBlock 1 where
  degree := ![0, -2, 4, -2]
  positions :=
    ![(11, 14)]
  constraints :=
    ![.entry 2 1 14]
  B := binaryMatrix ![1]

private theorem blockLeftInverse062 : block062.B * block062.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective062 : Function.Injective block062.positions := by
  decide +kernel

private theorem blockSupport062 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block062.degree k) ↔
      ∃ q, block062.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 62, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock062 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -2, 4, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block062.eq_zero blockLeftInverse062 blockPositionsInjective062
    blockSupport062 hX (by simpa [block062] using hhom) hq hi

private def block063 : HomogeneousBlock 2 where
  degree := ![0, -1, 0, 1]
  positions :=
    ![(23, 1), (24, 2)]
  constraints :=
    ![.entry 0 8 1, .entry 0 10 2]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse063 : block063.B * block063.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective063 : Function.Injective block063.positions := by
  decide +kernel

private theorem blockSupport063 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block063.degree k) ↔
      ∃ q, block063.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 63, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock063 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 0, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block063.eq_zero blockLeftInverse063 blockPositionsInjective063
    blockSupport063 hX (by simpa [block063] using hhom) hq hi

private def block064 : HomogeneousBlock 6 where
  degree := ![0, -1, 0, 2]
  positions :=
    ![(8, 1), (10, 2), (16, 7), (18, 9), (23, 15), (24, 17)]
  constraints :=
    ![.entry 0 8 15, .entry 0 10 17, .entry 1 0 2, .entry 1 3 7, .entry 1 4 9, .quotient 21]
  B := binaryMatrix ![32, 36, 40, 48, 33, 38]

private theorem blockLeftInverse064 : block064.B * block064.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective064 : Function.Injective block064.positions := by
  decide +kernel

private theorem blockSupport064 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block064.degree k) ↔
      ∃ q, block064.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 64, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock064 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 0, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block064.eq_zero blockLeftInverse064 blockPositionsInjective064
    blockSupport064 hX (by simpa [block064] using hhom) hq hi

private def block065 : HomogeneousBlock 2 where
  degree := ![0, -1, 0, 3]
  positions :=
    ![(8, 15), (10, 17)]
  constraints :=
    ![.entry 1 0 17, .entry 1 8 25]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse065 : block065.B * block065.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective065 : Function.Injective block065.positions := by
  decide +kernel

private theorem blockSupport065 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block065.degree k) ↔
      ∃ q, block065.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 65, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock065 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 0, 3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block065.eq_zero blockLeftInverse065 blockPositionsInjective065
    blockSupport065 hX (by simpa [block065] using hhom) hq hi

private def block066 : HomogeneousBlock 2 where
  degree := ![0, -1, 1, -1]
  positions :=
    ![(23, 0), (25, 2)]
  constraints :=
    ![.entry 0 11 1, .entry 0 12 2]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse066 : block066.B * block066.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective066 : Function.Injective block066.positions := by
  decide +kernel

private theorem blockSupport066 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block066.degree k) ↔
      ∃ q, block066.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 66, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock066 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block066.eq_zero blockLeftInverse066 blockPositionsInjective066
    blockSupport066 hX (by simpa [block066] using hhom) hq hi

private def block067 : HomogeneousBlock 12 where
  degree := ![0, -1, 1, 0]
  positions :=
    ![(8, 0), (11, 1), (12, 2), (13, 2), (16, 5), (18, 6), (19, 7), (20, 9), (23, 12),
      (23, 13), (24, 14), (25, 17)]
  constraints :=
    ![.entry 0 0 2, .entry 0 3 7, .entry 0 4 9, .entry 0 8 12, .entry 0 8 13, .entry 0 10 14,
      .entry 0 11 15, .entry 0 12 17, .entry 0 16 21, .entry 0 18 22, .entry 1 1 2, .ideal 23]
  B := binaryMatrix ![2048, 2112, 1089, 2049, 2304, 2560, 2050, 2052, 2056, 16, 2080, 3265]

private theorem blockLeftInverse067 : block067.B * block067.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective067 : Function.Injective block067.positions := by
  decide +kernel

private theorem blockSupport067 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block067.degree k) ↔
      ∃ q, block067.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 67, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock067 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block067.eq_zero blockLeftInverse067 blockPositionsInjective067
    blockSupport067 hX (by simpa [block067] using hhom) hq hi

private def block068 : HomogeneousBlock 12 where
  degree := ![0, -1, 1, 1]
  positions :=
    ![(0, 2), (3, 7), (4, 9), (8, 12), (8, 13), (10, 14), (11, 15), (12, 17), (13, 17),
      (16, 21), (18, 22), (23, 25)]
  constraints :=
    ![.entry 0 0 17, .entry 0 8 25, .entry 1 0 14, .entry 1 1 17, .entry 1 3 21, .entry 1 4 22,
      .entry 1 8 24, .entry 1 11 25, .entry 2 0 12, .entry 2 3 19, .entry 2 4 20, .ideal 8]
  B := binaryMatrix ![2048, 2560, 3072, 2304, 2368, 2052, 2434, 2057, 2049, 2576, 3104, 2306]

private theorem blockLeftInverse068 : block068.B * block068.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective068 : Function.Injective block068.positions := by
  decide +kernel

private theorem blockSupport068 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block068.degree k) ↔
      ∃ q, block068.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 68, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock068 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block068.eq_zero blockLeftInverse068 blockPositionsInjective068
    blockSupport068 hX (by simpa [block068] using hhom) hq hi

private def block069 : HomogeneousBlock 2 where
  degree := ![0, -1, 1, 2]
  positions :=
    ![(0, 17), (8, 25)]
  constraints :=
    ![.entry 2 0 25, .entry 7 0 22]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse069 : block069.B * block069.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective069 : Function.Injective block069.positions := by
  decide +kernel

private theorem blockSupport069 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block069.degree k) ↔
      ∃ q, block069.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 69, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock069 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, -1, 1, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block069.eq_zero blockLeftInverse069 blockPositionsInjective069
    blockSupport069 hX (by simpa [block069] using hhom) hq hi

end TauCeti.F4ShortRoot
