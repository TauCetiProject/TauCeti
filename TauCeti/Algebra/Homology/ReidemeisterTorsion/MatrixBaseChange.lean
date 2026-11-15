/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.MatrixBaseChange
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Basic

/-!
# The torsion of the coordinate base change of a based complex

Let `C` be a `ℤ`-graded chain complex of modules over a commutative ring `A`, with an ordered
basis `c i : Basis (Fin (n i)) A (C.X i)` in each degree, and let `φ : A →+* K` be a ring
homomorphism into a field. The torsion of the coordinate base change
`HomologicalComplex.matrixBaseChange c φ` is natural in `φ`: a homomorphism of fields
`ψ : K →+* L` sends the torsion of the base change along `φ` to the torsion of the base change
along `ψ ∘ φ` (`HomologicalComplex.map_reidemeisterTorsion_matrixBaseChange`). This follows from
the scalar extension theorem `HomologicalComplex.map_reidemeisterTorsion`, because the matrices of
the differentials of the coordinate base change are the images of those of `C` by construction.

## Main results

* `HomologicalComplex.map_reidemeisterTorsion_matrixBaseChange`: naturality of the torsion of the
  coordinate base change in the field.
-/

public section

open Module

namespace HomologicalComplex

variable {A : Type*} [CommRing A] {C : ChainComplex (ModuleCat A) ℤ} {n : ℤ → ℕ}
  {c : ∀ i, Basis (Fin (n i)) A (C.X i)} {K L : Type*} [Field K] [Field L] (φ : A →+* K)
  (ψ : K →+* L)

/-- The torsion of the coordinate base change is natural in the field: a homomorphism of fields
`ψ : K →+* L` sends the torsion of the base change along `φ` to the torsion of the base change
along `ψ ∘ φ`. -/
theorem map_reidemeisterTorsion_matrixBaseChange :
    ψ ((C.matrixBaseChange c φ).reidemeisterTorsion (C.matrixBaseChangeBasis c φ)) =
      (C.matrixBaseChange c (ψ.comp φ)).reidemeisterTorsion
        (C.matrixBaseChangeBasis c (ψ.comp φ)) :=
  map_reidemeisterTorsion ψ fun i ↦ by
    rw [toMatrix_matrixBaseChange_d, toMatrix_matrixBaseChange_d, Matrix.map_map, RingHom.coe_comp]

end HomologicalComplex
