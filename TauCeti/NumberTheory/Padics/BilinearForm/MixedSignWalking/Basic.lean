/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.NumberTheory.Padics.PadicIntegers
import TauCeti.LinearAlgebra.BilinearForm.Even.Henselian
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
import TauCeti.NumberTheory.Padics.DyadicUnits
import TauCeti.NumberTheory.Padics.SerreSigns
import TauCeti.RingTheory.Henselian.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Sign walking between adjacent dyadic constituents of different types

Write `U = !![0, 1; 1, 0]` and `V = !![2, 1; 1, 2]` for the two even unimodular
planes over the dyadic integers. For every unit `a`, this file proves the integral isometry
`⟨a⟩ ⊕ 2U ≅ ⟨5a⟩ ⊕ 2V`. Thus the signs of a unary constituent and an adjacent
binary even constituent can change together. The unary oddity changes by four modulo eight.
The reverse move starting from `V` and the versions at every common scale `2ᵏ` are included.
This move is needed when comparing Jordan splittings: the individual unimodular
constituents need not be isometric even though their scaled orthogonal sums are.

The proof uses the basis `(1, 1, a), (-2, 1, 0), (-2, 0, a)`. Its determinant is `5a`,
and its binary orthogonal block, after removing the scale two, has Gram matrix
`!![2a, 3a; 3a, 2a]`. The even unimodular classification identifies that block with `V`.

## References

* D. Allcock, I. Gal and A. Mark, *The Conway–Sloane calculus for 2-adic lattices*,
  Lemma 4.2(1), for sign walking between adjacent scales of different types.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Matrix

namespace TauCeti

/-- The even unimodular plane with Gram matrix `a • !![2, 3; 3, 2]`, for a dyadic unit
`a`, is isometric to `V`. This is the binary block arising in both orientations of
mixed-type sign walking. -/
theorem equivalent_toBilin'_binary_two_three_mul {a : ℤ_[2]} (ha : IsUnit a) :
    (toBilin' !![2 * a, 3 * a; 3 * a, 2 * a]).Equivalent
      (toBilin' (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ_[2])) := by
  have h3 : IsUnit (3 : ℤ_[2]) := by
    rw [PadicInt.isUnit_iff_toZModPow_three_mul_self, map_ofNat]
    decide
  have hD : IsUnit (-5 * a ^ 2) := isUnit_five_padicInt.neg.mul (ha.pow 2)
  have hsD : (toBilin' !![2 * a, 3 * a; 3 * a, 2 * a]).IsSymm := by
    apply isSymm_toBilin'_iff_isSymm.mpr
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hsV : (toBilin' (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ_[2])).IsSymm := by
    apply isSymm_toBilin'_iff_isSymm.mpr
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have heD (x : Fin 2 → ℤ_[2]) :
      2 ∣ toBilin' !![2 * a, 3 * a; 3 * a, 2 * a] x x := by
    refine ⟨a * x 0 ^ 2 + 3 * a * x 0 * x 1 + a * x 1 ^ 2, ?_⟩
    simp [toBilin'_apply', dotProduct, mulVec, Fin.sum_univ_two]
    ring
  have heV (x : Fin 2 → ℤ_[2]) :
      2 ∣ toBilin' (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ_[2]) x x := by
    refine ⟨x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2, ?_⟩
    simp [toBilin'_apply', dotProduct, mulVec, Fin.sum_univ_two]
    ring
  have hdetD : (!![2 * a, 3 * a; 3 * a, 2 * a] : Matrix (Fin 2) (Fin 2) ℤ_[2]).det =
      -5 * a ^ 2 := by simp [det_fin_two]; ring
  have hdetV : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ_[2]).det = 3 := by
    norm_num [det_fin_two]
  apply (hsD.equivalent_iff_isSquare_det_mul_det_of_even (PadicInt.card_residueField 2)
    PadicInt.not_isSquare_neg_three hsV heD heV (Pi.basisFun ℤ_[2] (Fin 2))
    (Pi.basisFun ℤ_[2] (Fin 2)) (by simpa only [LinearMap.BilinForm.toMatrix_basisFun,
      LinearMap.BilinForm.toMatrix'_toBilin', hdetD] using hD)
    (by simpa only [LinearMap.BilinForm.toMatrix_basisFun,
      LinearMap.BilinForm.toMatrix'_toBilin', hdetV] using h3)).mpr
  simp only [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin',
    hdetD, hdetV]
  rw [PadicInt.isSquare_mul_iff_toZModPow_three_eq hD h3]
  have h := PadicInt.isUnit_iff_toZModPow_three_mul_self.mp ha
  simp only [map_mul, map_neg, map_ofNat, pow_two, h]
  decide

/-- Replacing the binary plane `a • !![2, 3; 3, 2]` by `V` preserves isometry after
any common binary scaling `s` and adjoining an unchanged orthogonal unary coefficient `c`.
This transports the binary block in both scale orderings of mixed-type sign walking. -/
theorem equivalent_toBilin'_unary_smul_binary_two_three_mul (c s : ℤ_[2])
    {a : ℤ_[2]} (ha : IsUnit a) :
    (toBilin' !![c, 0, 0; 0, s * (2 * a), s * (3 * a); 0, s * (3 * a), s * (2 * a)]).Equivalent
      (toBilin' !![c, 0, 0; 0, s * 2, s; 0, s, s * 2]) := by
  obtain ⟨e⟩ := equivalent_toBilin'_binary_two_three_mul ha
  -- Split off the unchanged unary coordinate and transport the scaled binary block.
  let split : (Fin 3 → ℤ_[2]) ≃ₗ[ℤ_[2]] ℤ_[2] × (Fin 2 → ℤ_[2]) :=
    (LinearEquiv.piCongrLeft ℤ_[2] (fun _ ↦ ℤ_[2]) (finSuccEquiv 2)) ≪≫ₗ
      LinearEquiv.piOptionEquivProd ℤ_[2]
  let f := split ≪≫ₗ (LinearEquiv.refl ℤ_[2] ℤ_[2]).prodCongr e.toLinearEquiv ≪≫ₗ split.symm
  have hf (x : Fin 3 → ℤ_[2]) : f x = Matrix.vecCons (x 0) (e (Fin.tail x)) := by
    funext i
    refine Fin.cases ?_ (fun i ↦ ?_) i <;>
      simp [f, split, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft',
        LinearEquiv.piOptionEquivProd, Equiv.piCongrLeft', Equiv.piOptionEquivProd]
    rfl
  refine ⟨⟨f, fun x y ↦ ?_⟩⟩
  have he := e.map_app (Fin.tail y) (Fin.tail x)
  simp only [LinearMap.coe_toAddHom, AddHom.toFun_eq_coe, LinearEquiv.coe_coe, hf]
  simp [toBilin'_apply', dotProduct, mulVec, Fin.sum_univ_two, Fin.sum_univ_three,
    Fin.tail, -LinearMap.BilinForm.IsometryEquiv.map_app] at he ⊢
  linear_combination s * he

private theorem mixed_sign_walking_hyperbolic {a : ℤ_[2]} (ha : IsUnit a) :
    (toBilin' !![a, 0, 0; 0, 0, 2; 0, 2, 0]).Equivalent
      (toBilin' !![5 * a, 0, 0; 0, 4, 2; 0, 2, 4]) := by
  let P : Matrix (Fin 3) (Fin 3) ℤ_[2] := !![1, -2, -2; 1, 1, 0; a, 0, a]
  have hP : IsUnit P.det := by
    have hdet : P.det = 5 * a := by simp [P, det_fin_three]; ring
    rw [hdet]
    exact isUnit_five_padicInt.mul ha
  have hfirst : (toBilin' !![a, 0, 0; 0, 0, 2; 0, 2, 0]).Equivalent
      (toBilin' !![5 * a, 0, 0; 0, 4 * a, 6 * a; 0, 6 * a, 4 * a]) := by
    have hmatrix : Pᵀ * !![a, 0, 0; 0, 0, 2; 0, 2, 0] * P =
        !![5 * a, 0, 0; 0, 4 * a, 6 * a; 0, 6 * a, 4 * a] := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [P, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
    rw [← hmatrix, ← toBilin'_comp,
      ← toLinearEquiv'_apply P (P.invertibleOfIsUnitDet hP)]
    exact ⟨(toBilin' _).isometryEquivOfCompLinearEquiv _⟩
  have hblock := equivalent_toBilin'_unary_smul_binary_two_three_mul (5 * a) 2 ha
  norm_num [← mul_assoc] at hblock
  exact hfirst.trans hblock

private theorem mixed_sign_walking_anisotropic {a : ℤ_[2]} (ha : IsUnit a) :
    (toBilin' !![a, 0, 0; 0, 4, 2; 0, 2, 4]).Equivalent
      (toBilin' !![5 * a, 0, 0; 0, 0, 2; 0, 2, 0]) := by
  have h := mixed_sign_walking_hyperbolic (isUnit_five_padicInt.mul ha)
  let P : Matrix (Fin 3) (Fin 3) ℤ_[2] := diagonal ![5, 1, 1]
  have hP : IsUnit P.det := by
    simpa [P, det_diagonal, Fin.prod_univ_three] using isUnit_five_padicInt
  have hscale : (toBilin' !![a, 0, 0; 0, 4, 2; 0, 2, 4]).Equivalent
      (toBilin' !![5 * (5 * a), 0, 0; 0, 4, 2; 0, 2, 4]) := by
    have hmatrix : Pᵀ * !![a, 0, 0; 0, 4, 2; 0, 2, 4] * P =
        !![5 * (5 * a), 0, 0; 0, 4, 2; 0, 2, 4] := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [P, Matrix.mul_apply, Fin.sum_univ_three]
      ring
    rw [← hmatrix, ← toBilin'_comp,
      ← toLinearEquiv'_apply P (P.invertibleOfIsUnitDet hP)]
    exact ⟨(toBilin' _).isometryEquivOfCompLinearEquiv _⟩
  exact hscale.trans h.symm

/-- **Mixed-type sign walking, with the hyperbolic even plane.** At adjacent scales
`2ᵏ` and `2ᵏ⁺¹`, the constituents `⟨a⟩` and `U` can be replaced by `⟨5a⟩` and `V`.
Both signs reverse, and the unary oddity increases by four modulo eight. -/
theorem equivalent_toBilin'_unary_two_hyperbolic (k : ℕ) {a : ℤ_[2]} (ha : IsUnit a) :
    (toBilin' ((2 : ℤ_[2]) ^ k • !![a, 0, 0; 0, 0, 2; 0, 2, 0])).Equivalent
      (toBilin' ((2 : ℤ_[2]) ^ k • !![5 * a, 0, 0; 0, 4, 2; 0, 2, 4])) := by
  simp only [map_smul]
  exact (LinearMap.BilinForm.equivalent_smul_iff
    (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k two_ne_zero))).mpr
      (mixed_sign_walking_hyperbolic ha)

/-- **Mixed-type sign walking, with the anisotropic even plane.** At adjacent scales
`2ᵏ` and `2ᵏ⁺¹`, the constituents `⟨a⟩` and `V` can be replaced by `⟨5a⟩` and `U`.
Together with the hyperbolic case this permits either initial sign of the even plane. -/
theorem equivalent_toBilin'_unary_two_anisotropic (k : ℕ) {a : ℤ_[2]} (ha : IsUnit a) :
    (toBilin' ((2 : ℤ_[2]) ^ k • !![a, 0, 0; 0, 4, 2; 0, 2, 4])).Equivalent
      (toBilin' ((2 : ℤ_[2]) ^ k • !![5 * a, 0, 0; 0, 0, 2; 0, 2, 0])) := by
  simp only [map_smul]
  exact (LinearMap.BilinForm.equivalent_smul_iff
    (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k two_ne_zero))).mpr
      (mixed_sign_walking_anisotropic ha)

end TauCeti
