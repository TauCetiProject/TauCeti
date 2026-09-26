/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Duplex
public import TauCeti.Algebra.Homology.Curved.SquareZeroDuplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The two-periodic complex of a square-zero duplex

The square-zero duplex has the same differential in both parities. Its associated two-periodic
complex has zero homology in both parities whenever homology exists.
-/

public section

universe w v u

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

namespace CurvedDuplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {R : Type w} [Semiring R] [Linear R C]

example (A : C) :
    ((toPeriodicComplex C R).obj (squareZero (R := R) A)).d 0 1 =
      (biprod.fst ≫ biprod.inr : A ⊞ A ⟶ A ⊞ A) := by
  simp

example (A : C) :
    ((toPeriodicComplex C R).obj (squareZero (R := R) A)).d 1 0 =
      (biprod.fst ≫ biprod.inr : A ⊞ A ⟶ A ⊞ A) := by
  simp

/-- The two-periodic complex associated to the square-zero duplex has zero homology in each
parity. -/
theorem isZero_squareZero_periodicHomology (A : C) (i : ZMod 2)
    [((toPeriodicComplex C R).obj (squareZero (R := R) A)).HasHomology i] :
    IsZero (((toPeriodicComplex C R).obj (squareZero (R := R) A)).homology i) := by
  let K := (toPeriodicComplex C R).obj (squareZero (R := R) A)
  have h : Nonempty (Homotopy (𝟙 K) 0) := by
    have h' := (nonempty_homotopy_toPeriodicComplex_map_zero_iff
      (C := C) (R := R) (𝟙 (squareZero (R := R) A))).2
        ⟨_, _, nullHomotopicMap_squareZero (R := R) A⟩
    simpa only [(toPeriodicComplex C R).map_id] using h'
  rw [IsZero.iff_id_eq_zero]
  calc
    𝟙 (K.homology i) = HomologicalComplex.homologyMap (𝟙 K) i :=
      (HomologicalComplex.homologyMap_id K i).symm
    _ = HomologicalComplex.homologyMap (0 : K ⟶ K) i := h.some.homologyMap_eq i
    _ = 0 := HomologicalComplex.homologyMap_zero K K i

end CurvedDuplex

end TauCeti
