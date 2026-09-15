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

private def block028 : HomogeneousBlock 6 where
  degree := ![-1, 0, 0, 0]
  positions :=
    ![(18, 0), (20, 1), (22, 2), (23, 3), (24, 5), (25, 7)]
  constraints :=
    ![.entry 0 4 1, .entry 0 6 2, .entry 0 8 3, .entry 0 10 5, .entry 0 12 7, .quotient 25]
  B := binaryMatrix ![32, 33, 34, 36, 40, 48]

private theorem blockLeftInverse028 : block028.B * block028.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective028 : Function.Injective block028.positions := by
  decide +kernel

private theorem blockSupport028 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block028.degree k) ↔
      ∃ q, block028.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 28, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock028 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, 0, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block028.eq_zero blockLeftInverse028 blockPositionsInjective028
    blockSupport028 hX (by simpa [block028] using hhom) hq hi

private def block029 : HomogeneousBlock 12 where
  degree := ![-1, 0, 0, 1]
  positions :=
    ![(4, 1), (6, 2), (8, 3), (10, 5), (12, 7), (13, 7), (18, 12), (18, 13), (20, 15),
      (22, 17), (23, 19), (24, 21)]
  constraints :=
    ![.entry 0 0 7, .entry 0 4 15, .entry 0 6 17, .entry 0 8 19, .entry 0 10 21,
      .entry 0 18 25, .entry 1 0 5, .entry 1 1 7, .entry 1 4 13, .entry 1 6 14,
      .entry 1 8 16, .ideal 18]
  B := binaryMatrix ![2048, 2560, 3072, 2112, 2177, 1, 32, 2304, 2050, 2564, 3080, 2128]

private theorem blockLeftInverse029 : block029.B * block029.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective029 : Function.Injective block029.positions := by
  decide +kernel

private theorem blockSupport029 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block029.degree k) ↔
      ∃ q, block029.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 29, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock029 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, 0, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block029.eq_zero blockLeftInverse029 blockPositionsInjective029
    blockSupport029 hX (by simpa [block029] using hhom) hq hi

private def block030 : HomogeneousBlock 6 where
  degree := ![-1, 0, 0, 2]
  positions :=
    ![(0, 7), (4, 15), (6, 17), (8, 19), (10, 21), (18, 25)]
  constraints :=
    ![.entry 1 0 21, .entry 1 4 25, .entry 2 0 19, .entry 2 6 25, .entry 3 0 17, .quotient 7]
  B := binaryMatrix ![32, 58, 48, 36, 33, 56]

private theorem blockLeftInverse030 : block030.B * block030.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective030 : Function.Injective block030.positions := by
  decide +kernel

private theorem blockSupport030 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block030.degree k) ↔
      ∃ q, block030.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 30, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock030 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, 0, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block030.eq_zero blockLeftInverse030 blockPositionsInjective030
    blockSupport030 hX (by simpa [block030] using hhom) hq hi

private def block031 : HomogeneousBlock 2 where
  degree := ![-1, 0, 1, -2]
  positions :=
    ![(20, 0), (25, 5)]
  constraints :=
    ![.entry 0 9 2, .entry 0 12 5]
  B := binaryMatrix ![1, 3]

private theorem blockLeftInverse031 : block031.B * block031.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective031 : Function.Injective block031.positions := by
  decide +kernel

private theorem blockSupport031 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block031.degree k) ↔
      ∃ q, block031.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 31, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock031 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, 1, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block031.eq_zero blockLeftInverse031 blockPositionsInjective031
    blockSupport031 hX (by simpa [block031] using hhom) hq hi

private def block032 : HomogeneousBlock 12 where
  degree := ![-1, 0, 1, -1]
  positions :=
    ![(4, 0), (9, 2), (11, 3), (12, 5), (13, 5), (15, 7), (18, 10), (20, 12), (20, 13),
      (22, 14), (23, 16), (25, 21)]
  constraints :=
    ![.entry 0 0 5, .entry 0 1 7, .entry 0 4 12, .entry 0 4 13, .entry 0 6 14, .entry 0 8 16,
      .entry 0 9 17, .entry 0 11 19, .entry 0 12 21, .entry 0 18 24, .entry 1 1 5, .ideal 20]
  B := binaryMatrix ![2048, 2112, 2176, 3073, 2049, 2050, 2560, 2052, 2056, 2064, 2080, 3329]

private theorem blockLeftInverse032 : block032.B * block032.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective032 : Function.Injective block032.positions := by
  decide +kernel

private theorem blockSupport032 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block032.degree k) ↔
      ∃ q, block032.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 32, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock032 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, 1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block032.eq_zero blockLeftInverse032 blockPositionsInjective032
    blockSupport032 hX (by simpa [block032] using hhom) hq hi

private def block033 : HomogeneousBlock 12 where
  degree := ![-1, 0, 1, 0]
  positions :=
    ![(0, 5), (1, 7), (4, 12), (4, 13), (6, 14), (8, 16), (9, 17), (11, 19), (12, 21),
      (13, 21), (18, 24), (20, 25)]
  constraints :=
    ![.entry 0 0 21, .entry 0 4 25, .entry 1 1 21, .entry 1 4 24, .entry 2 0 16, .entry 2 1 19,
      .entry 2 2 21, .entry 2 4 23, .entry 2 6 24, .entry 2 9 25, .entry 3 0 14, .ideal 4]
  B := binaryMatrix ![2048, 2117, 3464, 128, 3072, 2064, 3978, 2149, 64, 2049, 3328, 3466]

private theorem blockLeftInverse033 : block033.B * block033.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective033 : Function.Injective block033.positions := by
  decide +kernel

private theorem blockSupport033 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block033.degree k) ↔
      ∃ q, block033.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 33, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock033 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, 1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block033.eq_zero blockLeftInverse033 blockPositionsInjective033
    blockSupport033 hX (by simpa [block033] using hhom) hq hi

private def block034 : HomogeneousBlock 2 where
  degree := ![-1, 0, 1, 1]
  positions :=
    ![(0, 21), (4, 25)]
  constraints :=
    ![.entry 5 0 25, .entry 7 0 24]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse034 : block034.B * block034.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective034 : Function.Injective block034.positions := by
  decide +kernel

private theorem blockSupport034 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block034.degree k) ↔
      ∃ q, block034.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 34, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock034 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, 1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block034.eq_zero blockLeftInverse034 blockPositionsInjective034
    blockSupport034 hX (by simpa [block034] using hhom) hq hi

private def block035 : HomogeneousBlock 2 where
  degree := ![-1, 0, 2, -3]
  positions :=
    ![(15, 5), (20, 10)]
  constraints :=
    ![.entry 0 1 5, .entry 0 4 10]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse035 : block035.B * block035.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective035 : Function.Injective block035.positions := by
  decide +kernel

private theorem blockSupport035 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block035.degree k) ↔
      ∃ q, block035.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 35, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock035 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, 2, -3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block035.eq_zero blockLeftInverse035 blockPositionsInjective035
    blockSupport035 hX (by simpa [block035] using hhom) hq hi

private def block036 : HomogeneousBlock 6 where
  degree := ![-1, 0, 2, -2]
  positions :=
    ![(1, 5), (4, 10), (9, 14), (11, 16), (15, 21), (20, 24)]
  constraints :=
    ![.entry 0 1 21, .entry 0 4 24, .entry 2 1 16, .entry 2 9 24, .entry 3 1 14, .quotient 9]
  B := binaryMatrix ![32, 58, 48, 36, 33, 56]

private theorem blockLeftInverse036 : block036.B * block036.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective036 : Function.Injective block036.positions := by
  decide +kernel

private theorem blockSupport036 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block036.degree k) ↔
      ∃ q, block036.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 36, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock036 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, 2, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block036.eq_zero blockLeftInverse036 blockPositionsInjective036
    blockSupport036 hX (by simpa [block036] using hhom) hq hi

private def block037 : HomogeneousBlock 2 where
  degree := ![-1, 0, 2, -1]
  positions :=
    ![(1, 21), (4, 24)]
  constraints :=
    ![.entry 5 0 24, .entry 5 1 25]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse037 : block037.B * block037.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective037 : Function.Injective block037.positions := by
  decide +kernel

private theorem blockSupport037 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block037.degree k) ↔
      ∃ q, block037.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 37, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock037 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, 2, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block037.eq_zero blockLeftInverse037 blockPositionsInjective037
    blockSupport037 hX (by simpa [block037] using hhom) hq hi

private def block038 : HomogeneousBlock 2 where
  degree := ![-1, 1, -2, 1]
  positions :=
    ![(22, 1), (24, 3)]
  constraints :=
    ![.entry 0 6 1, .entry 0 10 3]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse038 : block038.B * block038.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective038 : Function.Injective block038.positions := by
  decide +kernel

private theorem blockSupport038 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block038.degree k) ↔
      ∃ q, block038.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 38, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock038 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, -2, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block038.eq_zero blockLeftInverse038 blockPositionsInjective038
    blockSupport038 hX (by simpa [block038] using hhom) hq hi

private def block039 : HomogeneousBlock 6 where
  degree := ![-1, 1, -2, 2]
  positions :=
    ![(6, 1), (10, 3), (14, 7), (18, 11), (22, 15), (24, 19)]
  constraints :=
    ![.entry 0 6 15, .entry 0 10 19, .entry 1 0 3, .entry 1 2 7, .entry 1 4 11, .quotient 19]
  B := binaryMatrix ![32, 36, 40, 48, 33, 38]

private theorem blockLeftInverse039 : block039.B * block039.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective039 : Function.Injective block039.positions := by
  decide +kernel

private theorem blockSupport039 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block039.degree k) ↔
      ∃ q, block039.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 39, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock039 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, -2, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block039.eq_zero blockLeftInverse039 blockPositionsInjective039
    blockSupport039 hX (by simpa [block039] using hhom) hq hi

private def block040 : HomogeneousBlock 2 where
  degree := ![-1, 1, -2, 3]
  positions :=
    ![(6, 15), (10, 19)]
  constraints :=
    ![.entry 1 0 19, .entry 1 6 25]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse040 : block040.B * block040.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective040 : Function.Injective block040.positions := by
  decide +kernel

private theorem blockSupport040 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block040.degree k) ↔
      ∃ q, block040.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 40, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock040 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, -2, 3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block040.eq_zero blockLeftInverse040 blockPositionsInjective040
    blockSupport040 hX (by simpa [block040] using hhom) hq hi

private def block041 : HomogeneousBlock 2 where
  degree := ![-1, 1, -1, -1]
  positions :=
    ![(22, 0), (25, 3)]
  constraints :=
    ![.entry 0 9 1, .entry 0 12 3]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse041 : block041.B * block041.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective041 : Function.Injective block041.positions := by
  decide +kernel

private theorem blockSupport041 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block041.degree k) ↔
      ∃ q, block041.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 41, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock041 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, -1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block041.eq_zero blockLeftInverse041 blockPositionsInjective041
    blockSupport041 hX (by simpa [block041] using hhom) hq hi

end TauCeti.F4ShortRoot
