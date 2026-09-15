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

private def block154 : HomogeneousBlock 1 where
  degree := ![2, -2, 2, 0]
  positions :=
    ![(3, 22)]
  constraints :=
    ![.entry 6 0 22]
  B := binaryMatrix ![1]

private theorem blockLeftInverse154 : block154.B * block154.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective154 : Function.Injective block154.positions := by
  decide +kernel

private theorem blockSupport154 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block154.degree k) ↔
      ∃ q, block154.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 154, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock154 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -2, 2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block154.eq_zero blockLeftInverse154 blockPositionsInjective154
    blockSupport154 hX (by simpa [block154] using hhom) hq hi

private def block155 : HomogeneousBlock 2 where
  degree := ![2, -1, -1, 1]
  positions :=
    ![(16, 4), (21, 9)]
  constraints :=
    ![.entry 0 5 9, .entry 0 16 20]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse155 : block155.B * block155.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective155 : Function.Injective block155.positions := by
  decide +kernel

private theorem blockSupport155 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block155.degree k) ↔
      ∃ q, block155.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 155, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock155 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -1, -1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block155.eq_zero blockLeftInverse155 blockPositionsInjective155
    blockSupport155 hX (by simpa [block155] using hhom) hq hi

private def block156 : HomogeneousBlock 2 where
  degree := ![2, -1, -1, 2]
  positions :=
    ![(5, 9), (16, 20)]
  constraints :=
    ![.entry 1 3 20, .entry 1 5 22]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse156 : block156.B * block156.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective156 : Function.Injective block156.positions := by
  decide +kernel

private theorem blockSupport156 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block156.degree k) ↔
      ∃ q, block156.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 156, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock156 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -1, -1, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block156.eq_zero blockLeftInverse156 blockPositionsInjective156
    blockSupport156 hX (by simpa [block156] using hhom) hq hi

private def block157 : HomogeneousBlock 2 where
  degree := ![2, -1, 0, -1]
  positions :=
    ![(19, 4), (21, 6)]
  constraints :=
    ![.entry 0 3 4, .entry 0 5 6]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse157 : block157.B * block157.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective157 : Function.Injective block157.positions := by
  decide +kernel

private theorem blockSupport157 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block157.degree k) ↔
      ∃ q, block157.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 157, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock157 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -1, 0, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block157.eq_zero blockLeftInverse157 blockPositionsInjective157
    blockSupport157 hX (by simpa [block157] using hhom) hq hi

private def block158 : HomogeneousBlock 6 where
  degree := ![2, -1, 0, 0]
  positions :=
    ![(3, 4), (5, 6), (7, 9), (16, 18), (19, 20), (21, 22)]
  constraints :=
    ![.entry 0 3 20, .entry 0 5 22, .entry 1 3 18, .entry 1 7 22, .entry 2 5 18, .quotient 10]
  B := binaryMatrix ![32, 52, 62, 36, 33, 54]

private theorem blockLeftInverse158 : block158.B * block158.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective158 : Function.Injective block158.positions := by
  decide +kernel

private theorem blockSupport158 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block158.degree k) ↔
      ∃ q, block158.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 158, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock158 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -1, 0, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block158.eq_zero blockLeftInverse158 blockPositionsInjective158
    blockSupport158 hX (by simpa [block158] using hhom) hq hi

private def block159 : HomogeneousBlock 2 where
  degree := ![2, -1, 0, 1]
  positions :=
    ![(3, 20), (5, 22)]
  constraints :=
    ![.entry 4 0 22, .entry 4 3 25]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse159 : block159.B * block159.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective159 : Function.Injective block159.positions := by
  decide +kernel

private theorem blockSupport159 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block159.degree k) ↔
      ∃ q, block159.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 159, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock159 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -1, 0, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block159.eq_zero blockLeftInverse159 blockPositionsInjective159
    blockSupport159 hX (by simpa [block159] using hhom) hq hi

private def block160 : HomogeneousBlock 2 where
  degree := ![2, -1, 1, -2]
  positions :=
    ![(7, 6), (19, 18)]
  constraints :=
    ![.entry 0 3 18, .entry 0 7 22]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse160 : block160.B * block160.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective160 : Function.Injective block160.positions := by
  decide +kernel

private theorem blockSupport160 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block160.degree k) ↔
      ∃ q, block160.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 160, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock160 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -1, 1, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block160.eq_zero blockLeftInverse160 blockPositionsInjective160
    blockSupport160 hX (by simpa [block160] using hhom) hq hi

private def block161 : HomogeneousBlock 2 where
  degree := ![2, -1, 1, -1]
  positions :=
    ![(3, 18), (7, 22)]
  constraints :=
    ![.entry 4 1 22, .entry 4 3 24]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse161 : block161.B * block161.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective161 : Function.Injective block161.positions := by
  decide +kernel

private theorem blockSupport161 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block161.degree k) ↔
      ∃ q, block161.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 161, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock161 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, -1, 1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block161.eq_zero blockLeftInverse161 blockPositionsInjective161
    blockSupport161 hX (by simpa [block161] using hhom) hq hi

private def block162 : HomogeneousBlock 1 where
  degree := ![2, 0, -2, 0]
  positions :=
    ![(21, 4)]
  constraints :=
    ![.entry 0 5 4]
  B := binaryMatrix ![1]

private theorem blockLeftInverse162 : block162.B * block162.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective162 : Function.Injective block162.positions := by
  decide +kernel

private theorem blockSupport162 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block162.degree k) ↔
      ∃ q, block162.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 162, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock162 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, 0, -2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block162.eq_zero blockLeftInverse162 blockPositionsInjective162
    blockSupport162 hX (by simpa [block162] using hhom) hq hi

private def block163 : HomogeneousBlock 2 where
  degree := ![2, 0, -2, 1]
  positions :=
    ![(5, 4), (21, 20)]
  constraints :=
    ![.entry 0 5 20, .entry 1 5 18]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse163 : block163.B * block163.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective163 : Function.Injective block163.positions := by
  decide +kernel

private theorem blockSupport163 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block163.degree k) ↔
      ∃ q, block163.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 163, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock163 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, 0, -2, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block163.eq_zero blockLeftInverse163 blockPositionsInjective163
    blockSupport163 hX (by simpa [block163] using hhom) hq hi

private def block164 : HomogeneousBlock 1 where
  degree := ![2, 0, -2, 2]
  positions :=
    ![(5, 20)]
  constraints :=
    ![.entry 4 0 20]
  B := binaryMatrix ![1]

private theorem blockLeftInverse164 : block164.B * block164.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective164 : Function.Injective block164.positions := by
  decide +kernel

private theorem blockSupport164 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block164.degree k) ↔
      ∃ q, block164.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 164, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock164 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, 0, -2, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block164.eq_zero blockLeftInverse164 blockPositionsInjective164
    blockSupport164 hX (by simpa [block164] using hhom) hq hi

private def block165 : HomogeneousBlock 2 where
  degree := ![2, 0, -1, -1]
  positions :=
    ![(7, 4), (21, 18)]
  constraints :=
    ![.entry 0 5 18, .entry 0 7 20]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse165 : block165.B * block165.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective165 : Function.Injective block165.positions := by
  decide +kernel

private theorem blockSupport165 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block165.degree k) ↔
      ∃ q, block165.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 165, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock165 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, 0, -1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block165.eq_zero blockLeftInverse165 blockPositionsInjective165
    blockSupport165 hX (by simpa [block165] using hhom) hq hi

private def block166 : HomogeneousBlock 2 where
  degree := ![2, 0, -1, 0]
  positions :=
    ![(5, 18), (7, 20)]
  constraints :=
    ![.entry 4 0 18, .entry 4 1 20]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse166 : block166.B * block166.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective166 : Function.Injective block166.positions := by
  decide +kernel

private theorem blockSupport166 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block166.degree k) ↔
      ∃ q, block166.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 166, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock166 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, 0, -1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block166.eq_zero blockLeftInverse166 blockPositionsInjective166
    blockSupport166 hX (by simpa [block166] using hhom) hq hi

private def block167 : HomogeneousBlock 1 where
  degree := ![2, 0, 0, -2]
  positions :=
    ![(7, 18)]
  constraints :=
    ![.entry 4 1 18]
  B := binaryMatrix ![1]

private theorem blockLeftInverse167 : block167.B * block167.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective167 : Function.Injective block167.positions := by
  decide +kernel

private theorem blockSupport167 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block167.degree k) ↔
      ∃ q, block167.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 167, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock167 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![2, 0, 0, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block167.eq_zero blockLeftInverse167 blockPositionsInjective167
    blockSupport167 hX (by simpa [block167] using hhom) hq hi

end TauCeti.F4ShortRoot
