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

private def block140 : HomogeneousBlock 2 where
  degree := ![1, 0, 1, -3]
  positions :=
    ![(7, 10), (15, 18)]
  constraints :=
    ![.entry 0 1 18, .entry 0 7 24]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse140 : block140.B * block140.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective140 : Function.Injective block140.positions := by
  decide +kernel

private theorem blockSupport140 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block140.degree k) ↔
      ∃ q, block140.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 140, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock140 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, 1, -3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block140.eq_zero blockLeftInverse140 blockPositionsInjective140
    blockSupport140 hX (by simpa [block140] using hhom) hq hi

private def block141 : HomogeneousBlock 2 where
  degree := ![1, 0, 1, -2]
  positions :=
    ![(1, 18), (7, 24)]
  constraints :=
    ![.entry 4 1 24, .entry 6 1 23]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse141 : block141.B * block141.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective141 : Function.Injective block141.positions := by
  decide +kernel

private theorem blockSupport141 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block141.degree k) ↔
      ∃ q, block141.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 141, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock141 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 0, 1, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block141.eq_zero blockLeftInverse141 blockPositionsInjective141
    blockSupport141 hX (by simpa [block141] using hhom) hq hi

private def block142 : HomogeneousBlock 2 where
  degree := ![1, 1, -3, 1]
  positions :=
    ![(14, 4), (21, 11)]
  constraints :=
    ![.entry 0 5 11, .entry 0 14 20]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse142 : block142.B * block142.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective142 : Function.Injective block142.positions := by
  decide +kernel

private theorem blockSupport142 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block142.degree k) ↔
      ∃ q, block142.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 142, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock142 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 1, -3, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block142.eq_zero blockLeftInverse142 blockPositionsInjective142
    blockSupport142 hX (by simpa [block142] using hhom) hq hi

private def block143 : HomogeneousBlock 2 where
  degree := ![1, 1, -3, 2]
  positions :=
    ![(5, 11), (14, 20)]
  constraints :=
    ![.entry 1 2 20, .entry 1 5 23]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse143 : block143.B * block143.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective143 : Function.Injective block143.positions := by
  decide +kernel

private theorem blockSupport143 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block143.degree k) ↔
      ∃ q, block143.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 143, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock143 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 1, -3, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block143.eq_zero blockLeftInverse143 blockPositionsInjective143
    blockSupport143 hX (by simpa [block143] using hhom) hq hi

private def block144 : HomogeneousBlock 2 where
  degree := ![1, 1, -2, -1]
  positions :=
    ![(17, 4), (21, 8)]
  constraints :=
    ![.entry 0 2 4, .entry 0 5 8]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse144 : block144.B * block144.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective144 : Function.Injective block144.positions := by
  decide +kernel

private theorem blockSupport144 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block144.degree k) ↔
      ∃ q, block144.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 144, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock144 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 1, -2, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block144.eq_zero blockLeftInverse144 blockPositionsInjective144
    blockSupport144 hX (by simpa [block144] using hhom) hq hi

private def block145 : HomogeneousBlock 6 where
  degree := ![1, 1, -2, 0]
  positions :=
    ![(2, 4), (5, 8), (7, 11), (14, 18), (17, 20), (21, 23)]
  constraints :=
    ![.entry 0 2 20, .entry 0 5 23, .entry 1 2 18, .entry 1 7 23, .entry 3 5 18, .quotient 8]
  B := binaryMatrix ![32, 52, 62, 36, 33, 54]

private theorem blockLeftInverse145 : block145.B * block145.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective145 : Function.Injective block145.positions := by
  decide +kernel

private theorem blockSupport145 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block145.degree k) ↔
      ∃ q, block145.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 145, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock145 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 1, -2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block145.eq_zero blockLeftInverse145 blockPositionsInjective145
    blockSupport145 hX (by simpa [block145] using hhom) hq hi

private def block146 : HomogeneousBlock 2 where
  degree := ![1, 1, -2, 1]
  positions :=
    ![(2, 20), (5, 23)]
  constraints :=
    ![.entry 4 0 23, .entry 4 2 25]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse146 : block146.B * block146.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective146 : Function.Injective block146.positions := by
  decide +kernel

private theorem blockSupport146 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block146.degree k) ↔
      ∃ q, block146.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 146, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock146 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 1, -2, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block146.eq_zero blockLeftInverse146 blockPositionsInjective146
    blockSupport146 hX (by simpa [block146] using hhom) hq hi

private def block147 : HomogeneousBlock 2 where
  degree := ![1, 1, -1, -2]
  positions :=
    ![(7, 8), (17, 18)]
  constraints :=
    ![.entry 0 2 18, .entry 0 7 23]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse147 : block147.B * block147.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective147 : Function.Injective block147.positions := by
  decide +kernel

private theorem blockSupport147 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block147.degree k) ↔
      ∃ q, block147.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 147, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock147 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 1, -1, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block147.eq_zero blockLeftInverse147 blockPositionsInjective147
    blockSupport147 hX (by simpa [block147] using hhom) hq hi

private def block148 : HomogeneousBlock 2 where
  degree := ![1, 1, -1, -1]
  positions :=
    ![(2, 18), (7, 23)]
  constraints :=
    ![.entry 4 1 23, .entry 4 2 24]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse148 : block148.B * block148.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective148 : Function.Injective block148.positions := by
  decide +kernel

private theorem blockSupport148 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block148.degree k) ↔
      ∃ q, block148.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 148, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock148 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![1, 1, -1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block148.eq_zero blockLeftInverse148 blockPositionsInjective148
    blockSupport148 hX (by simpa [block148] using hhom) hq hi

private def block149 : HomogeneousBlock 1 where
  degree := ![2, -2, 0, 2]
  positions :=
    ![(16, 9)]
  constraints :=
    ![.entry 1 3 9]
  B := binaryMatrix ![1]

private theorem blockLeftInverse149 : block149.B * block149.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective149 : Function.Injective block149.positions := by
  decide +kernel

private theorem blockSupport149 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block149.degree k) ↔
      ∃ q, block149.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 149, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock149 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -2, 0, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block149.eq_zero blockLeftInverse149 blockPositionsInjective149
    blockSupport149 hX (by simpa [block149] using hhom) hq hi

private def block150 : HomogeneousBlock 2 where
  degree := ![2, -2, 1, 0]
  positions :=
    ![(16, 6), (19, 9)]
  constraints :=
    ![.entry 0 3 9, .entry 0 16 22]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse150 : block150.B * block150.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective150 : Function.Injective block150.positions := by
  decide +kernel

private theorem blockSupport150 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block150.degree k) ↔
      ∃ q, block150.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 150, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock150 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -2, 1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block150.eq_zero blockLeftInverse150 blockPositionsInjective150
    blockSupport150 hX (by simpa [block150] using hhom) hq hi

private def block151 : HomogeneousBlock 2 where
  degree := ![2, -2, 1, 1]
  positions :=
    ![(3, 9), (16, 22)]
  constraints :=
    ![.entry 1 3 22, .entry 2 3 20]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse151 : block151.B * block151.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective151 : Function.Injective block151.positions := by
  decide +kernel

private theorem blockSupport151 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block151.degree k) ↔
      ∃ q, block151.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 151, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock151 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -2, 1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block151.eq_zero blockLeftInverse151 blockPositionsInjective151
    blockSupport151 hX (by simpa [block151] using hhom) hq hi

private def block152 : HomogeneousBlock 1 where
  degree := ![2, -2, 2, -2]
  positions :=
    ![(19, 6)]
  constraints :=
    ![.entry 0 3 6]
  B := binaryMatrix ![1]

private theorem blockLeftInverse152 : block152.B * block152.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective152 : Function.Injective block152.positions := by
  decide +kernel

private theorem blockSupport152 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block152.degree k) ↔
      ∃ q, block152.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 152, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock152 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -2, 2, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block152.eq_zero blockLeftInverse152 blockPositionsInjective152
    blockSupport152 hX (by simpa [block152] using hhom) hq hi

private def block153 : HomogeneousBlock 2 where
  degree := ![2, -2, 2, -1]
  positions :=
    ![(3, 6), (19, 22)]
  constraints :=
    ![.entry 0 3 22, .entry 2 3 18]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse153 : block153.B * block153.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective153 : Function.Injective block153.positions := by
  decide +kernel

private theorem blockSupport153 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block153.degree k) ↔
      ∃ q, block153.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 153, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock153 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -2, 2, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block153.eq_zero blockLeftInverse153 blockPositionsInjective153
    blockSupport153 hX (by simpa [block153] using hhom) hq hi

end TauCeti.F4ShortRoot
