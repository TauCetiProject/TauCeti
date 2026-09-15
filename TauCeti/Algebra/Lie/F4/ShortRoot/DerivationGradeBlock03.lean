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

private def block042 : HomogeneousBlock 12 where
  degree := ![-1, 1, -1, 0]
  positions :=
    ![(6, 0), (9, 1), (12, 3), (13, 3), (14, 5), (17, 7), (18, 8), (20, 11), (22, 12),
      (22, 13), (24, 16), (25, 19)]
  constraints :=
    ![.entry 0 0 3, .entry 0 2 7, .entry 0 4 11, .entry 0 6 12, .entry 0 6 13, .entry 0 9 15,
      .entry 0 10 16, .entry 0 12 19, .entry 0 14 21, .entry 0 18 23, .entry 1 1 3, .ideal 22]
  B := binaryMatrix ![2048, 2080, 1057, 2049, 2304, 2050, 2560, 2052, 2056, 16, 2112, 3233]

private theorem blockLeftInverse042 : block042.B * block042.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective042 : Function.Injective block042.positions := by
  decide +kernel

private theorem blockSupport042 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block042.degree k) ↔
      ∃ q, block042.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 42, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock042 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, -1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block042.eq_zero blockLeftInverse042 blockPositionsInjective042
    blockSupport042 hX (by simpa [block042] using hhom) hq hi

private def block043 : HomogeneousBlock 12 where
  degree := ![-1, 1, -1, 1]
  positions :=
    ![(0, 3), (2, 7), (4, 11), (6, 12), (6, 13), (9, 15), (10, 16), (12, 19), (13, 19),
      (14, 21), (18, 23), (22, 25)]
  constraints :=
    ![.entry 0 0 19, .entry 0 6 25, .entry 1 0 16, .entry 1 1 19, .entry 1 2 21, .entry 1 4 23,
      .entry 1 6 24, .entry 1 9 25, .entry 2 2 19, .entry 2 6 23, .entry 3 0 12, .ideal 6]
  B := binaryMatrix ![2048, 2313, 3680, 3072, 3136, 3202, 2052, 2057, 2049, 2329, 3648, 3074]

private theorem blockLeftInverse043 : block043.B * block043.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective043 : Function.Injective block043.positions := by
  decide +kernel

private theorem blockSupport043 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block043.degree k) ↔
      ∃ q, block043.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 43, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock043 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, -1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block043.eq_zero blockLeftInverse043 blockPositionsInjective043
    blockSupport043 hX (by simpa [block043] using hhom) hq hi

private def block044 : HomogeneousBlock 2 where
  degree := ![-1, 1, -1, 2]
  positions :=
    ![(0, 19), (6, 25)]
  constraints :=
    ![.entry 3 0 25, .entry 7 0 23]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse044 : block044.B * block044.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective044 : Function.Injective block044.positions := by
  decide +kernel

private theorem blockSupport044 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block044.degree k) ↔
      ∃ q, block044.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 44, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock044 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, -1, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block044.eq_zero blockLeftInverse044 blockPositionsInjective044
    blockSupport044 hX (by simpa [block044] using hhom) hq hi

private def block045 : HomogeneousBlock 6 where
  degree := ![-1, 1, 0, -2]
  positions :=
    ![(9, 0), (15, 3), (17, 5), (20, 8), (22, 10), (25, 16)]
  constraints :=
    ![.entry 0 1 3, .entry 0 2 5, .entry 0 4 8, .entry 0 6 10, .entry 0 12 16, .quotient 20]
  B := binaryMatrix ![32, 33, 34, 36, 40, 48]

private theorem blockLeftInverse045 : block045.B * block045.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective045 : Function.Injective block045.positions := by
  decide +kernel

private theorem blockSupport045 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block045.degree k) ↔
      ∃ q, block045.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 45, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock045 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, 0, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block045.eq_zero blockLeftInverse045 blockPositionsInjective045
    blockSupport045 hX (by simpa [block045] using hhom) hq hi

private def block046 : HomogeneousBlock 12 where
  degree := ![-1, 1, 0, -1]
  positions :=
    ![(1, 3), (2, 5), (4, 8), (6, 10), (9, 12), (9, 13), (12, 16), (13, 16), (15, 19),
      (17, 21), (20, 23), (22, 24)]
  constraints :=
    ![.entry 0 0 16, .entry 0 1 19, .entry 0 2 21, .entry 0 4 23, .entry 0 6 24, .entry 0 9 25,
      .entry 1 1 16, .entry 1 9 24, .entry 2 2 16, .entry 2 9 23, .entry 3 0 10, .ideal 9]
  B := binaryMatrix ![2048, 2369, 3768, 3072, 32, 3248, 2113, 1, 2050, 2373, 3760, 3088]

private theorem blockLeftInverse046 : block046.B * block046.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective046 : Function.Injective block046.positions := by
  decide +kernel

private theorem blockSupport046 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block046.degree k) ↔
      ∃ q, block046.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 46, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock046 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, 0, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block046.eq_zero blockLeftInverse046 blockPositionsInjective046
    blockSupport046 hX (by simpa [block046] using hhom) hq hi

private def block047 : HomogeneousBlock 6 where
  degree := ![-1, 1, 0, 0]
  positions :=
    ![(0, 16), (1, 19), (2, 21), (4, 23), (6, 24), (9, 25)]
  constraints :=
    ![.entry 3 0 24, .entry 3 1 25, .entry 5 0 23, .entry 5 2 25, .entry 7 1 23, .quotient 1]
  B := binaryMatrix ![32, 52, 62, 36, 33, 54]

private theorem blockLeftInverse047 : block047.B * block047.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective047 : Function.Injective block047.positions := by
  decide +kernel

private theorem blockSupport047 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block047.degree k) ↔
      ∃ q, block047.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 47, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock047 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, 0, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block047.eq_zero blockLeftInverse047 blockPositionsInjective047
    blockSupport047 hX (by simpa [block047] using hhom) hq hi

private def block048 : HomogeneousBlock 2 where
  degree := ![-1, 1, 1, -3]
  positions :=
    ![(9, 10), (15, 16)]
  constraints :=
    ![.entry 0 1 16, .entry 0 9 24]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse048 : block048.B * block048.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective048 : Function.Injective block048.positions := by
  decide +kernel

private theorem blockSupport048 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block048.degree k) ↔
      ∃ q, block048.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 48, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock048 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, 1, -3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block048.eq_zero blockLeftInverse048 blockPositionsInjective048
    blockSupport048 hX (by simpa [block048] using hhom) hq hi

private def block049 : HomogeneousBlock 2 where
  degree := ![-1, 1, 1, -2]
  positions :=
    ![(1, 16), (9, 24)]
  constraints :=
    ![.entry 3 1 24, .entry 5 1 23]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse049 : block049.B * block049.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective049 : Function.Injective block049.positions := by
  decide +kernel

private theorem blockSupport049 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block049.degree k) ↔
      ∃ q, block049.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 49, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock049 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 1, 1, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block049.eq_zero blockLeftInverse049 blockPositionsInjective049
    blockSupport049 hX (by simpa [block049] using hhom) hq hi

private def block050 : HomogeneousBlock 2 where
  degree := ![-1, 2, -3, 1]
  positions :=
    ![(14, 3), (22, 11)]
  constraints :=
    ![.entry 0 6 11, .entry 0 14 19]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse050 : block050.B * block050.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective050 : Function.Injective block050.positions := by
  decide +kernel

private theorem blockSupport050 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block050.degree k) ↔
      ∃ q, block050.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 50, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock050 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 2, -3, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block050.eq_zero blockLeftInverse050 blockPositionsInjective050
    blockSupport050 hX (by simpa [block050] using hhom) hq hi

private def block051 : HomogeneousBlock 2 where
  degree := ![-1, 2, -3, 2]
  positions :=
    ![(6, 11), (14, 19)]
  constraints :=
    ![.entry 1 2 19, .entry 1 6 23]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse051 : block051.B * block051.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective051 : Function.Injective block051.positions := by
  decide +kernel

private theorem blockSupport051 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block051.degree k) ↔
      ∃ q, block051.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 51, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock051 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 2, -3, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block051.eq_zero blockLeftInverse051 blockPositionsInjective051
    blockSupport051 hX (by simpa [block051] using hhom) hq hi

private def block052 : HomogeneousBlock 2 where
  degree := ![-1, 2, -2, -1]
  positions :=
    ![(17, 3), (22, 8)]
  constraints :=
    ![.entry 0 2 3, .entry 0 6 8]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse052 : block052.B * block052.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective052 : Function.Injective block052.positions := by
  decide +kernel

private theorem blockSupport052 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block052.degree k) ↔
      ∃ q, block052.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 52, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock052 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 2, -2, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block052.eq_zero blockLeftInverse052 blockPositionsInjective052
    blockSupport052 hX (by simpa [block052] using hhom) hq hi

private def block053 : HomogeneousBlock 6 where
  degree := ![-1, 2, -2, 0]
  positions :=
    ![(2, 3), (6, 8), (9, 11), (14, 16), (17, 19), (22, 23)]
  constraints :=
    ![.entry 0 2 19, .entry 0 6 23, .entry 1 2 16, .entry 1 9 23, .entry 3 0 8, .quotient 11]
  B := binaryMatrix ![32, 48, 58, 36, 33, 50]

private theorem blockLeftInverse053 : block053.B * block053.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective053 : Function.Injective block053.positions := by
  decide +kernel

private theorem blockSupport053 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block053.degree k) ↔
      ∃ q, block053.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 53, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock053 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 2, -2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block053.eq_zero blockLeftInverse053 blockPositionsInjective053
    blockSupport053 hX (by simpa [block053] using hhom) hq hi

private def block054 : HomogeneousBlock 2 where
  degree := ![-1, 2, -2, 1]
  positions :=
    ![(2, 19), (6, 23)]
  constraints :=
    ![.entry 3 0 23, .entry 3 2 25]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse054 : block054.B * block054.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective054 : Function.Injective block054.positions := by
  decide +kernel

private theorem blockSupport054 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block054.degree k) ↔
      ∃ q, block054.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 54, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock054 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 2, -2, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block054.eq_zero blockLeftInverse054 blockPositionsInjective054
    blockSupport054 hX (by simpa [block054] using hhom) hq hi

private def block055 : HomogeneousBlock 2 where
  degree := ![-1, 2, -1, -2]
  positions :=
    ![(9, 8), (17, 16)]
  constraints :=
    ![.entry 0 2 16, .entry 0 9 23]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse055 : block055.B * block055.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective055 : Function.Injective block055.positions := by
  decide +kernel

private theorem blockSupport055 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block055.degree k) ↔
      ∃ q, block055.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 55, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock055 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 2, -1, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block055.eq_zero blockLeftInverse055 blockPositionsInjective055
    blockSupport055 hX (by simpa [block055] using hhom) hq hi

end TauCeti.F4ShortRoot
