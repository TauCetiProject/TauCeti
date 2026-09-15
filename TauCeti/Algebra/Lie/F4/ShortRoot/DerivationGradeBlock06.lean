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

private def block084 : HomogeneousBlock 12 where
  degree := ![0, 0, 0, 1]
  positions :=
    ![(0, 12), (0, 13), (1, 15), (2, 17), (3, 19), (4, 20), (5, 21), (6, 22), (8, 23),
      (10, 24), (12, 25), (13, 25)]
  constraints :=
    ![.entry 0 0 25, .entry 1 0 24, .entry 1 1 25, .entry 2 0 23, .entry 2 2 25, .entry 3 0 22,
      .entry 3 3 25, .entry 4 0 21, .entry 4 4 25, .entry 5 0 20, .entry 7 0 18, .ideal 0]
  B := binaryMatrix ![1024, 2048, 2821, 3856, 3904, 3584, 2176, 2080, 2056, 3074, 3840, 1025]

private theorem blockLeftInverse084 : block084.B * block084.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective084 : Function.Injective block084.positions := by
  decide +kernel

private theorem blockSupport084 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block084.degree k) ↔
      ∃ q, block084.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 84, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock084 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 0, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block084.eq_zero blockLeftInverse084 blockPositionsInjective084
    blockSupport084 hX (by simpa [block084] using hhom) hq hi

private def block085 : HomogeneousBlock 1 where
  degree := ![0, 0, 0, 2]
  positions :=
    ![(0, 25)]
  constraints :=
    ![.entry 15 0 24]
  B := binaryMatrix ![1]

private theorem blockLeftInverse085 : block085.B * block085.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective085 : Function.Injective block085.positions := by
  decide +kernel

private theorem blockSupport085 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block085.degree k) ↔
      ∃ q, block085.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 85, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock085 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 0, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block085.eq_zero blockLeftInverse085 blockPositionsInjective085
    blockSupport085 hX (by simpa [block085] using hhom) hq hi

private def block086 : HomogeneousBlock 2 where
  degree := ![0, 0, 1, -3]
  positions :=
    ![(15, 0), (25, 10)]
  constraints :=
    ![.entry 0 7 5, .entry 0 12 10]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse086 : block086.B * block086.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective086 : Function.Injective block086.positions := by
  decide +kernel

private theorem blockSupport086 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block086.degree k) ↔
      ∃ q, block086.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 86, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock086 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 1, -3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block086.eq_zero blockLeftInverse086 blockPositionsInjective086
    blockSupport086 hX (by simpa [block086] using hhom) hq hi

private def block087 : HomogeneousBlock 12 where
  degree := ![0, 0, 1, -2]
  positions :=
    ![(1, 0), (7, 5), (9, 6), (11, 8), (12, 10), (13, 10), (15, 12), (15, 13), (17, 14),
      (19, 16), (20, 18), (25, 24)]
  constraints :=
    ![.entry 0 0 10, .entry 0 1 12, .entry 0 1 13, .entry 0 2 14, .entry 0 3 16, .entry 0 4 18,
      .entry 0 7 21, .entry 0 9 22, .entry 0 11 23, .entry 0 12 24, .entry 1 1 10, .ideal 15]
  B := binaryMatrix ![2048, 2112, 2176, 2304, 1025, 2049, 2050, 4, 2056, 2064, 2080, 3585]

private theorem blockLeftInverse087 : block087.B * block087.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective087 : Function.Injective block087.positions := by
  decide +kernel

private theorem blockSupport087 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block087.degree k) ↔
      ∃ q, block087.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 87, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock087 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 1, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block087.eq_zero blockLeftInverse087 blockPositionsInjective087
    blockSupport087 hX (by simpa [block087] using hhom) hq hi

private def block088 : HomogeneousBlock 12 where
  degree := ![0, 0, 1, -1]
  positions :=
    ![(0, 10), (1, 12), (1, 13), (2, 14), (3, 16), (4, 18), (7, 21), (9, 22), (11, 23),
      (12, 24), (13, 24), (15, 25)]
  constraints :=
    ![.entry 0 0 24, .entry 0 1 25, .entry 1 1 24, .entry 2 1 23, .entry 2 2 24, .entry 3 1 22,
      .entry 3 3 24, .entry 4 1 21, .entry 4 4 24, .entry 5 0 18, .entry 5 2 22, .ideal 1]
  B := binaryMatrix ![2048, 3125, 3888, 2832, 2880, 2560, 4016, 3856, 3896, 2816, 2049, 3127]

private theorem blockLeftInverse088 : block088.B * block088.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective088 : Function.Injective block088.positions := by
  decide +kernel

private theorem blockSupport088 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block088.degree k) ↔
      ∃ q, block088.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 88, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock088 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block088.eq_zero blockLeftInverse088 blockPositionsInjective088
    blockSupport088 hX (by simpa [block088] using hhom) hq hi

private def block089 : HomogeneousBlock 2 where
  degree := ![0, 0, 1, 0]
  positions :=
    ![(0, 24), (1, 25)]
  constraints :=
    ![.entry 10 0 25, .entry 12 0 24]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse089 : block089.B * block089.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective089 : Function.Injective block089.positions := by
  decide +kernel

private theorem blockSupport089 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block089.degree k) ↔
      ∃ q, block089.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 89, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock089 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block089.eq_zero blockLeftInverse089 blockPositionsInjective089
    blockSupport089 hX (by simpa [block089] using hhom) hq hi

private def block090 : HomogeneousBlock 1 where
  degree := ![0, 0, 2, -4]
  positions :=
    ![(15, 10)]
  constraints :=
    ![.entry 0 1 10]
  B := binaryMatrix ![1]

private theorem blockLeftInverse090 : block090.B * block090.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective090 : Function.Injective block090.positions := by
  decide +kernel

private theorem blockSupport090 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block090.degree k) ↔
      ∃ q, block090.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 90, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock090 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 2, -4] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block090.eq_zero blockLeftInverse090 blockPositionsInjective090
    blockSupport090 hX (by simpa [block090] using hhom) hq hi

private def block091 : HomogeneousBlock 2 where
  degree := ![0, 0, 2, -3]
  positions :=
    ![(1, 10), (15, 24)]
  constraints :=
    ![.entry 0 1 24, .entry 5 1 18]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse091 : block091.B * block091.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective091 : Function.Injective block091.positions := by
  decide +kernel

private theorem blockSupport091 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block091.degree k) ↔
      ∃ q, block091.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 91, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock091 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 2, -3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block091.eq_zero blockLeftInverse091 blockPositionsInjective091
    blockSupport091 hX (by simpa [block091] using hhom) hq hi

private def block092 : HomogeneousBlock 1 where
  degree := ![0, 0, 2, -2]
  positions :=
    ![(1, 24)]
  constraints :=
    ![.entry 10 0 24]
  B := binaryMatrix ![1]

private theorem blockLeftInverse092 : block092.B * block092.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective092 : Function.Injective block092.positions := by
  decide +kernel

private theorem blockSupport092 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block092.degree k) ↔
      ∃ q, block092.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 92, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock092 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 0, 2, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block092.eq_zero blockLeftInverse092 blockPositionsInjective092
    blockSupport092 hX (by simpa [block092] using hhom) hq hi

private def block093 : HomogeneousBlock 2 where
  degree := ![0, 1, -3, 2]
  positions :=
    ![(14, 1), (24, 11)]
  constraints :=
    ![.entry 0 10 11, .entry 0 14 15]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse093 : block093.B * block093.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective093 : Function.Injective block093.positions := by
  decide +kernel

private theorem blockSupport093 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block093.degree k) ↔
      ∃ q, block093.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 93, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock093 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, -3, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block093.eq_zero blockLeftInverse093 blockPositionsInjective093
    blockSupport093 hX (by simpa [block093] using hhom) hq hi

private def block094 : HomogeneousBlock 2 where
  degree := ![0, 1, -3, 3]
  positions :=
    ![(10, 11), (14, 15)]
  constraints :=
    ![.entry 1 0 11, .entry 1 2 15]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse094 : block094.B * block094.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective094 : Function.Injective block094.positions := by
  decide +kernel

private theorem blockSupport094 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block094.degree k) ↔
      ∃ q, block094.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 94, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock094 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, -3, 3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block094.eq_zero blockLeftInverse094 blockPositionsInjective094
    blockSupport094 hX (by simpa [block094] using hhom) hq hi

private def block095 : HomogeneousBlock 6 where
  degree := ![0, 1, -2, 0]
  positions :=
    ![(14, 0), (17, 1), (21, 3), (22, 4), (24, 8), (25, 11)]
  constraints :=
    ![.entry 0 2 1, .entry 0 5 3, .entry 0 6 4, .entry 0 10 8, .entry 0 12 11, .quotient 23]
  B := binaryMatrix ![32, 33, 34, 36, 40, 48]

private theorem blockLeftInverse095 : block095.B * block095.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective095 : Function.Injective block095.positions := by
  decide +kernel

private theorem blockSupport095 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block095.degree k) ↔
      ∃ q, block095.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 95, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock095 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, -2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block095.eq_zero blockLeftInverse095 blockPositionsInjective095
    blockSupport095 hX (by simpa [block095] using hhom) hq hi

private def block096 : HomogeneousBlock 12 where
  degree := ![0, 1, -2, 1]
  positions :=
    ![(2, 1), (5, 3), (6, 4), (10, 8), (12, 11), (13, 11), (14, 12), (14, 13), (17, 15),
      (21, 19), (22, 20), (24, 23)]
  constraints :=
    ![.entry 0 0 11, .entry 0 2 15, .entry 0 5 19, .entry 0 6 20, .entry 0 10 23,
      .entry 0 14 25, .entry 1 0 8, .entry 1 1 11, .entry 1 2 13, .entry 1 5 16,
      .entry 1 6 18, .ideal 14]
  B := binaryMatrix ![2048, 2560, 3072, 2112, 2177, 1, 32, 2304, 2050, 2564, 3080, 2128]

private theorem blockLeftInverse096 : block096.B * block096.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective096 : Function.Injective block096.positions := by
  decide +kernel

private theorem blockSupport096 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block096.degree k) ↔
      ∃ q, block096.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 96, a root degree with 12 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock096 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, -2, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block096.eq_zero blockLeftInverse096 blockPositionsInjective096
    blockSupport096 hX (by simpa [block096] using hhom) hq hi

private def block097 : HomogeneousBlock 6 where
  degree := ![0, 1, -2, 2]
  positions :=
    ![(0, 11), (2, 15), (5, 19), (6, 20), (10, 23), (14, 25)]
  constraints :=
    ![.entry 1 0 23, .entry 1 2 25, .entry 3 0 20, .entry 3 5 25, .entry 4 0 19, .quotient 3]
  B := binaryMatrix ![32, 58, 48, 36, 33, 56]

private theorem blockLeftInverse097 : block097.B * block097.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective097 : Function.Injective block097.positions := by
  decide +kernel

private theorem blockSupport097 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block097.degree k) ↔
      ∃ q, block097.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 97, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock097 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![0, 1, -2, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block097.eq_zero blockLeftInverse097 blockPositionsInjective097
    blockSupport097 hX (by simpa [block097] using hhom) hq hi

end TauCeti.F4ShortRoot
