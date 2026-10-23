/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Tactic.FinCases

/-!
# The real coordinates of `ℂ²`

The `L²` product `WithLp 2 (ℂ × ℂ)` is linearly isometric to Euclidean four-space through the
real coordinates `(z, w) ↦ (Re z, Im z, Re w, Im w)`.

## Main definitions

* `TauCeti.complexProdToEuclideanFour`: the linear isometry `ℂ² ≃ ℝ⁴`.
-/

public section

noncomputable section

namespace TauCeti

/-- The linear isometry `ℂ² ≃ ℝ⁴`, `(z, w) ↦ (Re z, Im z, Re w, Im w)`, from the `L²` product
`WithLp 2 (ℂ × ℂ)` to Euclidean four-space. It applies `Complex.orthonormalBasisOneI.repr` to
each factor and then concatenates the two coordinate vectors along `finSumFinEquiv`. -/
def complexProdToEuclideanFour : WithLp 2 (ℂ × ℂ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  (LinearIsometryEquiv.withLpProdCongr 2 Complex.orthonormalBasisOneI.repr
    Complex.orthonormalBasisOneI.repr).trans
    ((PiLp.sumPiLpEquivProdLpPiLp 2 fun _ : Fin 2 ⊕ Fin 2 ↦ ℝ).symm.trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv))

@[simp]
theorem complexProdToEuclideanFour_apply (x : WithLp 2 (ℂ × ℂ)) :
    complexProdToEuclideanFour x = WithLp.toLp 2 ![x.fst.re, x.fst.im, x.snd.re, x.snd.im] := by
  ext i
  fin_cases i <;> rfl

@[simp]
theorem complexProdToEuclideanFour_symm_apply (y : EuclideanSpace ℝ (Fin 4)) :
    complexProdToEuclideanFour.symm y = WithLp.toLp 2 (⟨y 0, y 1⟩, ⟨y 2, y 3⟩) := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  ext i
  fin_cases i <;> simp

end TauCeti
