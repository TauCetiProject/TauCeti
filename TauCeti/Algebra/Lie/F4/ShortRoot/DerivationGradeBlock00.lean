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

private def block000 : HomogeneousBlock 1 where
  degree := ![-2, 0, 0, 2]
  positions :=
    ![(18, 7)]
  constraints :=
    ![.entry 1 4 7]
  B := binaryMatrix ![1]

private theorem blockLeftInverse000 : block000.B * block000.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective000 : Function.Injective block000.positions := by
  decide +kernel

private theorem blockSupport000 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block000.degree k) ↔
      ∃ q, block000.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 0, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock000 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 0, 0, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block000.eq_zero blockLeftInverse000 blockPositionsInjective000
    blockSupport000 hX (by simpa [block000] using hhom) hq hi

private def block001 : HomogeneousBlock 2 where
  degree := ![-2, 0, 1, 0]
  positions :=
    ![(18, 5), (20, 7)]
  constraints :=
    ![.entry 0 4 7, .entry 0 18 21]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse001 : block001.B * block001.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective001 : Function.Injective block001.positions := by
  decide +kernel

private theorem blockSupport001 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block001.degree k) ↔
      ∃ q, block001.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 1, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock001 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 0, 1, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block001.eq_zero blockLeftInverse001 blockPositionsInjective001
    blockSupport001 hX (by simpa [block001] using hhom) hq hi

private def block002 : HomogeneousBlock 2 where
  degree := ![-2, 0, 1, 1]
  positions :=
    ![(4, 7), (18, 21)]
  constraints :=
    ![.entry 1 4 21, .entry 2 4 19]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse002 : block002.B * block002.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective002 : Function.Injective block002.positions := by
  decide +kernel

private theorem blockSupport002 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block002.degree k) ↔
      ∃ q, block002.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 2, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock002 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 0, 1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block002.eq_zero blockLeftInverse002 blockPositionsInjective002
    blockSupport002 hX (by simpa [block002] using hhom) hq hi

private def block003 : HomogeneousBlock 1 where
  degree := ![-2, 0, 2, -2]
  positions :=
    ![(20, 5)]
  constraints :=
    ![.entry 0 4 5]
  B := binaryMatrix ![1]

private theorem blockLeftInverse003 : block003.B * block003.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective003 : Function.Injective block003.positions := by
  decide +kernel

private theorem blockSupport003 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block003.degree k) ↔
      ∃ q, block003.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 3, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock003 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 0, 2, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block003.eq_zero blockLeftInverse003 blockPositionsInjective003
    blockSupport003 hX (by simpa [block003] using hhom) hq hi

private def block004 : HomogeneousBlock 2 where
  degree := ![-2, 0, 2, -1]
  positions :=
    ![(4, 5), (20, 21)]
  constraints :=
    ![.entry 0 4 21, .entry 2 4 16]
  B := binaryMatrix ![2, 3]

private theorem blockLeftInverse004 : block004.B * block004.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective004 : Function.Injective block004.positions := by
  decide +kernel

private theorem blockSupport004 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block004.degree k) ↔
      ∃ q, block004.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 4, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock004 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 0, 2, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block004.eq_zero blockLeftInverse004 blockPositionsInjective004
    blockSupport004 hX (by simpa [block004] using hhom) hq hi

private def block005 : HomogeneousBlock 1 where
  degree := ![-2, 0, 2, 0]
  positions :=
    ![(4, 21)]
  constraints :=
    ![.entry 5 0 21]
  B := binaryMatrix ![1]

private theorem blockLeftInverse005 : block005.B * block005.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective005 : Function.Injective block005.positions := by
  decide +kernel

private theorem blockSupport005 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block005.degree k) ↔
      ∃ q, block005.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 5, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock005 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 0, 2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block005.eq_zero blockLeftInverse005 blockPositionsInjective005
    blockSupport005 hX (by simpa [block005] using hhom) hq hi

private def block006 : HomogeneousBlock 2 where
  degree := ![-2, 1, -1, 1]
  positions :=
    ![(18, 3), (22, 7)]
  constraints :=
    ![.entry 0 6 7, .entry 0 18 19]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse006 : block006.B * block006.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective006 : Function.Injective block006.positions := by
  decide +kernel

private theorem blockSupport006 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block006.degree k) ↔
      ∃ q, block006.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 6, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock006 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 1, -1, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block006.eq_zero blockLeftInverse006 blockPositionsInjective006
    blockSupport006 hX (by simpa [block006] using hhom) hq hi

private def block007 : HomogeneousBlock 2 where
  degree := ![-2, 1, -1, 2]
  positions :=
    ![(6, 7), (18, 19)]
  constraints :=
    ![.entry 1 4 19, .entry 1 6 21]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse007 : block007.B * block007.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective007 : Function.Injective block007.positions := by
  decide +kernel

private theorem blockSupport007 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block007.degree k) ↔
      ∃ q, block007.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 7, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock007 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 1, -1, 2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block007.eq_zero blockLeftInverse007 blockPositionsInjective007
    blockSupport007 hX (by simpa [block007] using hhom) hq hi

private def block008 : HomogeneousBlock 2 where
  degree := ![-2, 1, 0, -1]
  positions :=
    ![(20, 3), (22, 5)]
  constraints :=
    ![.entry 0 4 3, .entry 0 6 5]
  B := binaryMatrix ![1, 2]

private theorem blockLeftInverse008 : block008.B * block008.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective008 : Function.Injective block008.positions := by
  decide +kernel

private theorem blockSupport008 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block008.degree k) ↔
      ∃ q, block008.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 8, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock008 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 1, 0, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block008.eq_zero blockLeftInverse008 blockPositionsInjective008
    blockSupport008 hX (by simpa [block008] using hhom) hq hi

private def block009 : HomogeneousBlock 6 where
  degree := ![-2, 1, 0, 0]
  positions :=
    ![(4, 3), (6, 5), (9, 7), (18, 16), (20, 19), (22, 21)]
  constraints :=
    ![.entry 0 4 19, .entry 0 6 21, .entry 1 4 16, .entry 1 9 21, .entry 2 6 16, .quotient 15]
  B := binaryMatrix ![32, 52, 62, 36, 33, 54]

private theorem blockLeftInverse009 : block009.B * block009.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective009 : Function.Injective block009.positions := by
  decide +kernel

private theorem blockSupport009 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block009.degree k) ↔
      ∃ q, block009.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 9, a root degree with 6 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock009 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 1, 0, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block009.eq_zero blockLeftInverse009 blockPositionsInjective009
    blockSupport009 hX (by simpa [block009] using hhom) hq hi

private def block010 : HomogeneousBlock 2 where
  degree := ![-2, 1, 0, 1]
  positions :=
    ![(4, 19), (6, 21)]
  constraints :=
    ![.entry 3 0 21, .entry 3 4 25]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse010 : block010.B * block010.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective010 : Function.Injective block010.positions := by
  decide +kernel

private theorem blockSupport010 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block010.degree k) ↔
      ∃ q, block010.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 10, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock010 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 1, 0, 1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block010.eq_zero blockLeftInverse010 blockPositionsInjective010
    blockSupport010 hX (by simpa [block010] using hhom) hq hi

private def block011 : HomogeneousBlock 2 where
  degree := ![-2, 1, 1, -2]
  positions :=
    ![(9, 5), (20, 16)]
  constraints :=
    ![.entry 0 4 16, .entry 0 9 21]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse011 : block011.B * block011.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective011 : Function.Injective block011.positions := by
  decide +kernel

private theorem blockSupport011 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block011.degree k) ↔
      ∃ q, block011.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 11, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock011 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 1, 1, -2] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block011.eq_zero blockLeftInverse011 blockPositionsInjective011
    blockSupport011 hX (by simpa [block011] using hhom) hq hi

private def block012 : HomogeneousBlock 2 where
  degree := ![-2, 1, 1, -1]
  positions :=
    ![(4, 16), (9, 21)]
  constraints :=
    ![.entry 3 1 21, .entry 3 4 24]
  B := binaryMatrix ![2, 1]

private theorem blockLeftInverse012 : block012.B * block012.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective012 : Function.Injective block012.positions := by
  decide +kernel

private theorem blockSupport012 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block012.degree k) ↔
      ∃ q, block012.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 12, a nonroot degree with 2 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock012 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 1, 1, -1] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block012.eq_zero blockLeftInverse012 blockPositionsInjective012
    blockSupport012 hX (by simpa [block012] using hhom) hq hi

private def block013 : HomogeneousBlock 1 where
  degree := ![-2, 2, -2, 0]
  positions :=
    ![(22, 3)]
  constraints :=
    ![.entry 0 6 3]
  B := binaryMatrix ![1]

private theorem blockLeftInverse013 : block013.B * block013.A = 1 := by
  decide +kernel

private theorem blockPositionsInjective013 : Function.Injective block013.positions := by
  decide +kernel

private theorem blockSupport013 (i j : Fin 26) :
    (∀ k, entryDegree i j k = block013.degree k) ↔
      ∃ q, block013.positions q = (i, j) := by
  revert i j
  decide +kernel

/-- Homogeneous block 13, a nonroot degree with 1 supported entries, has trivial kernel. -/
theorem eq_zero_of_gradeBlock013 {X : Matrix (Fin 26) (Fin 26) R} (hX : IsDerivation X)
    (hhom : IsHomogeneous ![-2, 2, -2, 0] X)
    (hq : ∀ p, quotientCoordinate p X = 0)
    (hi : ∀ a, X (idealRow a) (idealCol a) = 0) : X = 0 :=
by
  apply block013.eq_zero blockLeftInverse013 blockPositionsInjective013
    blockSupport013 hX (by simpa [block013] using hhom) hq hi

end TauCeti.F4ShortRoot
