/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.RepresentationTheory.Basic

/-!
# Invariant bilinear forms from matrices

A matrix invariant under simultaneous action on its row and column indices gives an
invariant bilinear form on the free module. This holds for monoid actions over a
commutative semiring, without assuming that the action maps are bijective.
-/

public noncomputable section

open MonoidAlgebra Representation

namespace Matrix

variable {R Γ I : Type*} [CommSemiring R] [Monoid Γ] [MulAction Γ I]
  [Fintype I] [DecidableEq I]

/-- A matrix invariant under a monoid action induces an invariant bilinear form on the
linearized action. The action maps need not be bijective. -/
theorem toBilin_ofMulAction (A : Matrix I I R)
    (hact : ∀ (g : Γ) i j, A (g • i) (g • j) = A i j)
    (g : Γ) (x y : R[I]) :
    toBilin (MonoidAlgebra.basis I R) A
        (ofMulAction R Γ I g x) (ofMulAction R Γ I g y) =
      toBilin (MonoidAlgebra.basis I R) A x y := by
  classical
  let B := toBilin (MonoidAlgebra.basis I R) A
  have hs (i j : I) : B (MonoidAlgebra.single i 1) (MonoidAlgebra.single j 1) = A i j := by
    simpa only [LinearMap.BilinForm.toMatrix_apply, MonoidAlgebra.basis_apply] using
      congr_fun (congr_fun (LinearMap.BilinForm.toMatrix_toBilin
        (MonoidAlgebra.basis I R) A) i) j
  have hB : B.compl₁₂ (ofMulAction R Γ I g) (ofMulAction R Γ I g) = B := by
    apply (LinearMap.BilinForm.ext_iff_basis (MonoidAlgebra.basis I R)).mpr
    intro i j
    simpa [LinearMap.compl₁₂_apply, hs] using hact g i j
  exact congrArg (fun C : LinearMap.BilinForm R R[I] ↦ C x y) hB

end Matrix
