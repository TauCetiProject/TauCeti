/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Cube.Generator
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Native identity-cube calibration examples

The square and three-cube have negative selected coordinates; the four-cube has positive
coordinate. These are the actual relative identity classes, read through the native comparison
and `singularHomologyCubeBoundaryPairIso`. The same formula works in characteristic two,
for matrix coefficients and in a larger common universe. No coefficient-transport comparison
between different universes is asserted.
-/

public section

noncomputable section
open CategoryTheory TauCeti
universe u
namespace TauCeti.Examples

/-- The integral identity square is the negative native relative generator. -/
theorem identitySquare_eq_neg_selectedGenerator :
    (TopPair.singularCubicalHomologyIso ℤ (cubeBoundaryPair.{0} 2) 2).inv
      (((cubeBoundaryPair.{0} 2).cubicalChainComplex ℤ).homologyπ 2
        (cubeBoundaryPairCycle ℤ 1)) =
      -(singularHomologyCubeBoundaryPairIso (ModuleCat.of ℤ ℤ) 2).inv (1 : ℤ) := by
  let H : ModuleCat ℤ := (cubeBoundaryPair.{0} 2).singularHomology (ModuleCat.of ℤ ℤ) 2
  let x : H := (singularHomologyCubeBoundaryPairIso (ModuleCat.of ℤ ℤ) 2).inv (1 : ℤ)
  have h := singularCubicalHomologyIso_inv_homologyπ_cubeBoundaryPairCycle ℤ 1
  have hs : (-1 : ℤ) ^ (1 * (1 + 1) / 2) = -1 := by norm_num
  -- ModuleCat may carry a definitionally different integer action; compare it with zsmul.
  exact h.trans ((int_smul_eq_zsmul H.isModule _ x).trans
    ((congrArg (fun a : ℤ ↦ a • x) hs).trans (neg_one_zsmul x)))

/-- The integral three-cube also has negative selected coordinate. -/
theorem identityThreeCube_selectedCoordinate :
    (singularHomologyCubeBoundaryPairIso (ModuleCat.of ℤ ℤ) 3).hom
      ((TopPair.singularCubicalHomologyIso ℤ (cubeBoundaryPair.{0} 3) 3).inv
        (((cubeBoundaryPair.{0} 3).cubicalChainComplex ℤ).homologyπ 3
          (cubeBoundaryPairCycle ℤ 2))) = (-1 : ℤ) := by
  simpa using singularHomologyCubeBoundaryPairIso_hom_cubeBoundaryPairCycle ℤ 2

/-- The integral four-cube has positive selected coordinate. -/
theorem identityFourCube_selectedCoordinate :
    (singularHomologyCubeBoundaryPairIso (ModuleCat.of ℤ ℤ) 4).hom
      ((TopPair.singularCubicalHomologyIso ℤ (cubeBoundaryPair.{0} 4) 4).inv
        (((cubeBoundaryPair.{0} 4).cubicalChainComplex ℤ).homologyπ 4
          (cubeBoundaryPairCycle ℤ 3))) = (1 : ℤ) := by
  simpa using singularHomologyCubeBoundaryPairIso_hom_cubeBoundaryPairCycle ℤ 3

/-- In characteristic two the actual identity square has positive coordinate. -/
theorem identitySquare_zmodTwo_selectedCoordinate :
    (singularHomologyCubeBoundaryPairIso (ModuleCat.of (ZMod 2) (ZMod 2)) 2).hom
      ((TopPair.singularCubicalHomologyIso (ZMod 2) (cubeBoundaryPair.{0} 2) 2).inv
        (((cubeBoundaryPair.{0} 2).cubicalChainComplex (ZMod 2)).homologyπ 2
          (cubeBoundaryPairCycle (ZMod 2) 1))) = (1 : ZMod 2) := by
  simpa using singularHomologyCubeBoundaryPairIso_hom_cubeBoundaryPairCycle (ZMod 2) 1

/-- Matrix coefficients test the noncommutative ring statement on the actual square class. -/
theorem identitySquare_matrix_selectedCoordinate :
    (singularHomologyCubeBoundaryPairIso
      (ModuleCat.of (Matrix (Fin 2) (Fin 2) ℤ) (Matrix (Fin 2) (Fin 2) ℤ)) 2).hom
      ((TopPair.singularCubicalHomologyIso (Matrix (Fin 2) (Fin 2) ℤ) (cubeBoundaryPair.{0} 2)
        2).inv
        (((cubeBoundaryPair.{0} 2).cubicalChainComplex (Matrix (Fin 2) (Fin 2) ℤ)).homologyπ 2
          (cubeBoundaryPairCycle (Matrix (Fin 2) (Fin 2) ℤ) 1))) =
      (-1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  simpa using singularHomologyCubeBoundaryPairIso_hom_cubeBoundaryPairCycle
    (Matrix (Fin 2) (Fin 2) ℤ) 1

/-- The actual square formula holds in any common universe, without coefficient transport. -/
theorem identitySquare_selectedCoordinate (k : Type u) [Ring k] :
    (singularHomologyCubeBoundaryPairIso (ModuleCat.of k k) 2).hom
      ((TopPair.singularCubicalHomologyIso k (cubeBoundaryPair.{u} 2) 2).inv
        (((cubeBoundaryPair.{u} 2).cubicalChainComplex k).homologyπ 2
          (cubeBoundaryPairCycle k 1))) = (-1 : k) := by
  simpa using singularHomologyCubeBoundaryPairIso_hom_cubeBoundaryPairCycle k 1

end TauCeti.Examples
