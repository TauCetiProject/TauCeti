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

/-- The real-linear equivalence `ℂ² ≃ ℝ⁴`, `(z, w) ↦ (Re z, Im z, Re w, Im w)`, underlying
`TauCeti.complexProdToEuclideanFour`. -/
private def complexProdToEuclideanFourₗ : WithLp 2 (ℂ × ℂ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 4) where
  toFun x := WithLp.toLp 2 ![x.fst.re, x.fst.im, x.snd.re, x.snd.im]
  invFun y := WithLp.toLp 2 (⟨y 0, y 1⟩, ⟨y 2, y 3⟩)
  map_add' x y := by
    ext i
    fin_cases i <;> simp
  map_smul' c x := by
    ext i
    fin_cases i <;> simp
  left_inv x := (rfl)
  right_inv y := by
    ext i
    fin_cases i <;> simp

private theorem complexProdToEuclideanFourₗ_apply (x : WithLp 2 (ℂ × ℂ)) :
    complexProdToEuclideanFourₗ x = WithLp.toLp 2 ![x.fst.re, x.fst.im, x.snd.re, x.snd.im] :=
  (rfl)

/-- The linear isometry `ℂ² ≃ ℝ⁴`, `(z, w) ↦ (Re z, Im z, Re w, Im w)`, from the `L²` product
`WithLp 2 (ℂ × ℂ)` to Euclidean four-space. -/
def complexProdToEuclideanFour : WithLp 2 (ℂ × ℂ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  ⟨complexProdToEuclideanFourₗ, fun x ↦ by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simp [complexProdToEuclideanFourₗ_apply, WithLp.prod_norm_sq_eq_of_L2,
      EuclideanSpace.norm_sq_eq, Fin.sum_univ_four, Complex.sq_norm, Complex.normSq_apply]
    ring⟩

@[simp]
theorem complexProdToEuclideanFour_apply (x : WithLp 2 (ℂ × ℂ)) :
    complexProdToEuclideanFour x = WithLp.toLp 2 ![x.fst.re, x.fst.im, x.snd.re, x.snd.im] :=
  (rfl)

@[simp]
theorem complexProdToEuclideanFour_symm_apply (y : EuclideanSpace ℝ (Fin 4)) :
    complexProdToEuclideanFour.symm y = WithLp.toLp 2 (⟨y 0, y 1⟩, ⟨y 2, y 3⟩) :=
  (rfl)

end TauCeti
