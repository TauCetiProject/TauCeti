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

private def block014 : HomogeneousBlock 2 where
  degree := ![-2, 2, -2, 1]
  positions :=
    ![(6, 3), (22, 19)]
  constraints :=
    ![.entry 0 6 19, .entry 1 6 16]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse014 : block014.B * block014.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective014 : Function.Injective block014.positions := by
  decide +kernel

private theorem blockSupport014 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block014.degree k) ↔
      ∃ q, block014.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 14, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock014 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 2, -2, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block014.eq_zero blockLeftInverse014 blockPositionsInjective014
    blockSupport014 hX (by simpa [block014] using hhom) hq hi

private def block015 : HomogeneousBlock 1 where
  degree := ![-2, 2, -2, 2]
  positions :=
    ![(6, 19)]
  constraints :=
    ![.entry 3 0 19]
  B := binaryMatrix ![1]

private theorem blockLeftInverse015 : block015.B * block015.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective015 : Function.Injective block015.positions := by
  decide +kernel

private theorem blockSupport015 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block015.degree k) ↔
      ∃ q, block015.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 15, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock015 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 2, -2, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block015.eq_zero blockLeftInverse015 blockPositionsInjective015
    blockSupport015 hX (by simpa [block015] using hhom) hq hi

private def block016 : HomogeneousBlock 2 where
  degree := ![-2, 2, -1, -1]
  positions :=
    ![(9, 3), (22, 16)]
  constraints :=
    ![.entry 0 6 16, .entry 0 9 19]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse016 : block016.B * block016.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective016 : Function.Injective block016.positions := by
  decide +kernel

private theorem blockSupport016 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block016.degree k) ↔
      ∃ q, block016.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 16, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock016 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 2, -1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block016.eq_zero blockLeftInverse016 blockPositionsInjective016
    blockSupport016 hX (by simpa [block016] using hhom) hq hi

private def block017 : HomogeneousBlock 2 where
  degree := ![-2, 2, -1, 0]
  positions :=
    ![(6, 16), (9, 19)]
  constraints :=
    ![.entry 3 0 16, .entry 3 1 19]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse017 : block017.B * block017.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective017 : Function.Injective block017.positions := by
  decide +kernel

private theorem blockSupport017 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block017.degree k) ↔
      ∃ q, block017.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 17, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock017 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 2, -1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block017.eq_zero blockLeftInverse017 blockPositionsInjective017
    blockSupport017 hX (by simpa [block017] using hhom) hq hi

private def block018 : HomogeneousBlock 1 where
  degree := ![-2, 2, 0, -2]
  positions :=
    ![(9, 16)]
  constraints :=
    ![.entry 3 1 16]
  B := binaryMatrix ![1]

private theorem blockLeftInverse018 : block018.B * block018.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective018 : Function.Injective block018.positions := by
  decide +kernel

private theorem blockSupport018 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block018.degree k) ↔
      ∃ q, block018.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 18, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock018 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 2, 0, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block018.eq_zero blockLeftInverse018 blockPositionsInjective018
    blockSupport018 hX (by simpa [block018] using hhom) hq hi

private def block019 : HomogeneousBlock 2 where
  degree := ![-1, -1, 1, 1]
  positions :=
    ![(18, 2), (23, 7)]
  constraints :=
    ![.entry 0 8 7, .entry 0 18 17]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse019 : block019.B * block019.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective019 : Function.Injective block019.positions := by
  decide +kernel

private theorem blockSupport019 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block019.degree k) ↔
      ∃ q, block019.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 19, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock019 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, -1, 1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block019.eq_zero blockLeftInverse019 blockPositionsInjective019
    blockSupport019 hX (by simpa [block019] using hhom) hq hi

private def block020 : HomogeneousBlock 2 where
  degree := ![-1, -1, 1, 2]
  positions :=
    ![(8, 7), (18, 17)]
  constraints :=
    ![.entry 1 4 17, .entry 1 8 21]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse020 : block020.B * block020.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective020 : Function.Injective block020.positions := by
  decide +kernel

private theorem blockSupport020 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block020.degree k) ↔
      ∃ q, block020.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 20, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock020 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, -1, 1, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block020.eq_zero blockLeftInverse020 blockPositionsInjective020
    blockSupport020 hX (by simpa [block020] using hhom) hq hi

private def block021 : HomogeneousBlock 2 where
  degree := ![-1, -1, 2, -1]
  positions :=
    ![(20, 2), (23, 5)]
  constraints :=
    ![.entry 0 4 2, .entry 0 8 5]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse021 : block021.B * block021.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective021 : Function.Injective block021.positions := by
  decide +kernel

private theorem blockSupport021 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block021.degree k) ↔
      ∃ q, block021.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 21, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock021 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, -1, 2, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block021.eq_zero blockLeftInverse021 blockPositionsInjective021
    blockSupport021 hX (by simpa [block021] using hhom) hq hi

private def block022 : HomogeneousBlock 6 where
  degree := ![-1, -1, 2, 0]
  positions :=
    ![(4, 2), (8, 5), (11, 7), (18, 14), (20, 17), (23, 21)]
  constraints :=
    ![.entry 0 4 17, .entry 0 8 21, .entry 1 4 14, .entry 1 11 21, .entry 2 0 5, .quotient 17]
  B := binaryMatrix ![32, 48, 58, 36, 33, 50]

private theorem blockLeftInverse022 : block022.B * block022.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective022 : Function.Injective block022.positions := by
  decide +kernel

private theorem blockSupport022 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block022.degree k) ↔
      ∃ q, block022.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 22, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock022 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, -1, 2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block022.eq_zero blockLeftInverse022 blockPositionsInjective022
    blockSupport022 hX (by simpa [block022] using hhom) hq hi

private def block023 : HomogeneousBlock 2 where
  degree := ![-1, -1, 2, 1]
  positions :=
    ![(4, 17), (8, 21)]
  constraints :=
    ![.entry 2 0 21, .entry 2 4 25]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse023 : block023.B * block023.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective023 : Function.Injective block023.positions := by
  decide +kernel

private theorem blockSupport023 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block023.degree k) ↔
      ∃ q, block023.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 23, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock023 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, -1, 2, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block023.eq_zero blockLeftInverse023 blockPositionsInjective023
    blockSupport023 hX (by simpa [block023] using hhom) hq hi

private def block024 : HomogeneousBlock 2 where
  degree := ![-1, -1, 3, -2]
  positions :=
    ![(11, 5), (20, 14)]
  constraints :=
    ![.entry 0 4 14, .entry 0 11 21]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse024 : block024.B * block024.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective024 : Function.Injective block024.positions := by
  decide +kernel

private theorem blockSupport024 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block024.degree k) ↔
      ∃ q, block024.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 24, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock024 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, -1, 3, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block024.eq_zero blockLeftInverse024 blockPositionsInjective024
    blockSupport024 hX (by simpa [block024] using hhom) hq hi

private def block025 : HomogeneousBlock 2 where
  degree := ![-1, -1, 3, -1]
  positions :=
    ![(4, 14), (11, 21)]
  constraints :=
    ![.entry 2 1 21, .entry 2 4 24]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse025 : block025.B * block025.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective025 : Function.Injective block025.positions := by
  decide +kernel

private theorem blockSupport025 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block025.degree k) ↔
      ∃ q, block025.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 25, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock025 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, -1, 3, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block025.eq_zero blockLeftInverse025 blockPositionsInjective025
    blockSupport025 hX (by simpa [block025] using hhom) hq hi

private def block026 : HomogeneousBlock 2 where
  degree := ![-1, 0, -1, 2]
  positions :=
    ![(18, 1), (24, 7)]
  constraints :=
    ![.entry 0 10 7, .entry 0 18 15]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse026 : block026.B * block026.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective026 : Function.Injective block026.positions := by
  decide +kernel

private theorem blockSupport026 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block026.degree k) ↔
      ∃ q, block026.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 26, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock026 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, -1, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block026.eq_zero blockLeftInverse026 blockPositionsInjective026
    blockSupport026 hX (by simpa [block026] using hhom) hq hi

private def block027 : HomogeneousBlock 2 where
  degree := ![-1, 0, -1, 3]
  positions :=
    ![(10, 7), (18, 15)]
  constraints :=
    ![.entry 1 0 7, .entry 1 4 15]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse027 : block027.B * block027.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective027 : Function.Injective block027.positions := by
  decide +kernel

private theorem blockSupport027 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block027.degree k) ↔
      ∃ q, block027.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 27, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock027 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-1, 0, -1, 3] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block027.eq_zero blockLeftInverse027 blockPositionsInjective027
    blockSupport027 hX (by simpa [block027] using hhom) hq hi

end TauCeti.F4ShortRoot
