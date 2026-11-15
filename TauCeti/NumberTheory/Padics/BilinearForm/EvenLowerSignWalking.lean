/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import TauCeti.LinearAlgebra.BilinearForm.Even.Henselian
import TauCeti.LinearAlgebra.BilinearForm.Isometry
import TauCeti.NumberTheory.Padics.DyadicUnits
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Henselian.Basic

/-!
# Mixed dyadic sign walking with the even constituent at the lower scale

Write `U = !![0,1;1,0]` and `V = !![2,1;1,2]`. For every dyadic unit `a`,
this file proves the integral bilinear-form isometries
`U ⊕ ⟨2a⟩ ≅ V ⊕ ⟨10a⟩` and `V ⊕ ⟨2a⟩ ≅ U ⊕ ⟨10a⟩`, also after a common scaling by
any power of `2`. These are the mixed-type adjacent sign walks with the type-II constituent
at the smaller scale. They exchange the two even planes and multiply the unary unit by `5`.

The basis `(-a,1,0), (-a,0,1), (2a,2,1)` of the first form has determinant `5a`.
Its even binary block has determinant `-5a²`, hence is isometric to `V` by the classification
of even unimodular dyadic forms; its remaining vector has norm `10a`.

## References

* D. Allcock, I. Gal, A. Mark, *The Conway–Sloane calculus for 2-adic lattices*,
  Lemma 4.2(1).
* J. H. Conway, N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Matrix (toBilin')
open Module

namespace TauCeti

private theorem even_lower_block {a : ℤ_[2]} (ha : IsUnit a) :
    (toBilin' !![-2 * a, -a; -a, 2 * a]).Equivalent
      (toBilin' (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ_[2])) := by
  have h5 : IsUnit (5 : ℤ_[2]) := PadicInt.isUnit_natCast_of_coprime (by decide)
  have h3 : IsUnit (3 : ℤ_[2]) := PadicInt.isUnit_natCast_of_coprime (by decide)
  have eval (x y : Fin 2 → ℤ_[2]) :
      toBilin' !![-2 * a, -a; -a, 2 * a] x y =
        -2 * a * x 0 * y 0 - a * x 0 * y 1 - a * x 1 * y 0 +
          2 * a * x 1 * y 1 := by
    simp [Matrix.toBilin'_apply, Fin.sum_univ_two]
    ring
  have evalV (x y : Fin 2 → ℤ_[2]) :
      toBilin' !![2, 1; 1, 2] x y =
        2 * x 0 * y 0 + x 0 * y 1 + x 1 * y 0 + 2 * x 1 * y 1 := by
    simp [Matrix.toBilin'_apply, Fin.sum_univ_two]
    ring
  have hdet : ((toBilin' !![-2 * a, -a; -a, 2 * a]).toMatrix
      (Pi.basisFun ℤ_[2] (Fin 2))).det = -5 * a ^ 2 := by
    simp [Matrix.det_fin_two]
    ring
  have hdetV : ((toBilin' (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℤ_[2])).toMatrix
      (Pi.basisFun ℤ_[2] (Fin 2))).det = 3 := by
    simp [Matrix.det_fin_two]
    norm_num
  refine (LinearMap.BilinForm.IsSymm.equivalent_iff_isSquare_det_mul_det_of_even
    (PadicInt.card_residueField 2) PadicInt.not_isSquare_neg_three
    (B := toBilin' !![-2 * a, -a; -a, 2 * a])
    (C := toBilin' !![2, 1; 1, 2])
    ⟨fun x y => by rw [eval, eval]; ring⟩ ⟨fun x y => by rw [evalV, evalV]; ring⟩
    (fun x => ⟨-a * x 0 ^ 2 - a * x 0 * x 1 + a * x 1 ^ 2, by rw [eval]; ring⟩)
    (fun x => ⟨x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2, by rw [evalV]; ring⟩)
    (Pi.basisFun ℤ_[2] (Fin 2)) (Pi.basisFun ℤ_[2] (Fin 2))
    (by rw [hdet]; exact h5.neg.mul (ha.pow 2)) (by rwa [hdetV])).mpr ?_
  rw [hdet, hdetV, PadicInt.isSquare_mul_iff_toZModPow_three_eq
    (h5.neg.mul (ha.pow 2)) h3]
  have hu := PadicInt.isUnit_iff_toZModPow_three_mul_self.mp ha
  simp only [map_mul, map_neg, map_ofNat, pow_two] at hu ⊢
  rw [hu]
  decide

/-- The even block in the explicit orthogonal splitting can be replaced by `V`, while the
unary coordinate is fixed. -/
private theorem even_lower_block_extension {a : ℤ_[2]} (ha : IsUnit a) :
    (toBilin' !![-2 * a, -a, 0; -a, 2 * a, 0; 0, 0, 10 * a]).Equivalent
      (toBilin' !![2, 1, 0; 1, 2, 0; 0, 0, 10 * a]) := by
  obtain ⟨f⟩ := even_lower_block ha
  let e := (LinearEquiv.funCongrLeft ℤ_[2] ℤ_[2]
    (finSumFinEquiv : Fin 2 ⊕ Fin 1 ≃ Fin 3)).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 1) ℤ_[2] ℤ_[2])
  let g := e.trans ((LinearEquiv.prodCongr f.toLinearEquiv
    (LinearEquiv.refl ℤ_[2] (Fin 1 → ℤ_[2]))).trans e.symm)
  have hg (x : Fin 3 → ℤ_[2]) :
      g x = ![f (e x).1 0, f (e x).1 1, x 2] := by
    ext i
    fin_cases i <;> rfl
  have he (x : Fin 3 → ℤ_[2]) : (e x).1 = ![x 0, x 1] := by
    ext i
    fin_cases i <;> rfl
  refine ⟨⟨g, fun x y => ?_⟩⟩
  have hf := f.map_app (e x).1 (e y).1
  simp only [Matrix.toBilin'_apply, Fin.sum_univ_two] at hf
  simp [Matrix.toBilin'_apply, Fin.sum_univ_three, hg, he] at hf ⊢
  linear_combination hf

/-- The basis with columns `(-a,1,0), (-a,0,1), (2a,2,1)` exhibits
`U ⊕ ⟨2a⟩` as an even unimodular binary block orthogonal to `⟨10a⟩`. -/
private theorem even_lower_hyperbolic {a : ℤ_[2]} (ha : IsUnit a) :
    (toBilin' !![0, 1, 0; 1, 0, 0; 0, 0, 2 * a]).Equivalent
      (toBilin' !![2, 1, 0; 1, 2, 0; 0, 0, 10 * a]) := by
  let P : Matrix (Fin 3) (Fin 3) ℤ_[2] := !![-a, -a, 2 * a; 1, 0, 2; 0, 1, 1]
  have h5 : IsUnit (5 : ℤ_[2]) := PadicInt.isUnit_natCast_of_coprime (by decide)
  have hP : IsUnit P.det := by
    convert h5.mul ha using 1
    simp [P, Matrix.det_fin_three]
    ring
  let b := (Pi.basisFun ℤ_[2] (Fin 3)).map (P.toLinearEquiv (Pi.basisFun ℤ_[2] (Fin 3)) hP)
  have hgram : (toBilin' !![0, 1, 0; 1, 0, 0; 0, 0, 2 * a]).toMatrix b =
      !![-2 * a, -a, 0; -a, 2 * a, 0; 0, 0, 10 * a] := by
    -- Coordinate simplification exposes the subring embedding; normalize its numerals for `ring`.
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b, P, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin', Matrix.toLin'_apply,
        Matrix.toBilin'_apply, LinearMap.BilinForm.toMatrix_apply, Fin.sum_univ_three] <;>
        simp only [show ((2 : ℤ_[2]) : ℚ_[2]) = 2 from rfl,
          show ((10 : ℤ_[2]) : ℚ_[2]) = 10 from rfl] <;> ring
  have hsplit : (toBilin' !![0, 1, 0; 1, 0, 0; 0, 0, 2 * a]).Equivalent
      (toBilin' !![-2 * a, -a, 0; -a, 2 * a, 0; 0, 0, 10 * a]) :=
    ⟨b.isometryEquivOfToMatrixEq (Pi.basisFun ℤ_[2] (Fin 3)) (by
      rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin']
      exact hgram)⟩
  exact hsplit.trans (even_lower_block_extension ha)

/-- **Mixed-type adjacent sign walking with the even plane at the lower scale.**
For every unit `a` of `ℤ₂`, replace `U ⊕ ⟨2a⟩` by `V ⊕ ⟨10a⟩`, also after a common
scaling by `2ᵏ`. Both constituent signs change, and the unary oddity changes by `4`. -/
theorem equivalent_toBilin'_hyperbolic_two_unary (k : ℕ) {a : ℤ_[2]} (ha : IsUnit a) :
    (toBilin' ((2 : ℤ_[2]) ^ k • !![0, 1, 0; 1, 0, 0; 0, 0, 2 * a])).Equivalent
      (toBilin' ((2 : ℤ_[2]) ^ k • !![2, 1, 0; 1, 2, 0; 0, 0, 10 * a])) := by
  simp only [map_smul]
  exact (LinearMap.BilinForm.equivalent_smul_iff
    (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k two_ne_zero))).mpr
      (even_lower_hyperbolic ha)

/-- **Mixed-type adjacent sign walking starting from the other even plane.**
For every unit `a` of `ℤ₂`, replace `V ⊕ ⟨2a⟩` by `U ⊕ ⟨10a⟩`, also after a common
scaling by `2ᵏ`. Thus either initial sign of the lower even constituent is allowed. -/
theorem equivalent_toBilin'_anisotropic_two_unary (k : ℕ) {a : ℤ_[2]} (ha : IsUnit a) :
    (toBilin' ((2 : ℤ_[2]) ^ k • !![2, 1, 0; 1, 2, 0; 0, 0, 2 * a])).Equivalent
      (toBilin' ((2 : ℤ_[2]) ^ k • !![0, 1, 0; 1, 0, 0; 0, 0, 10 * a])) := by
  simp only [map_smul]
  apply (LinearMap.BilinForm.equivalent_smul_iff
    (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k two_ne_zero))).mpr
  have h5 : IsUnit (5 : ℤ_[2]) := PadicInt.isUnit_natCast_of_coprime (by decide)
  -- Reverse the hyperbolic move at `5a`; rescaling the unary coordinate by `5` removes `25`.
  let D : Matrix (Fin 3) (Fin 3) ℤ_[2] := Matrix.diagonal ![1, 1, 5]
  have hD : IsUnit D.det := by simpa [D, Matrix.det_diagonal, Fin.prod_univ_three] using h5
  let b := (Pi.basisFun ℤ_[2] (Fin 3)).map (D.toLinearEquiv (Pi.basisFun ℤ_[2] (Fin 3)) hD)
  have hgram : (toBilin' !![2, 1, 0; 1, 2, 0; 0, 0, 2 * a]).toMatrix b =
      !![2, 1, 0; 1, 2, 0; 0, 0, 10 * (5 * a)] := by
    -- Normalize numerals in the exposed subring embedding, as in the preceding Gram calculation.
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b, D, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin', Matrix.toLin'_apply,
        Matrix.toBilin'_apply, LinearMap.BilinForm.toMatrix_apply, Fin.sum_univ_three]
    simp only [show ((2 : ℤ_[2]) : ℚ_[2]) = 2 from rfl,
      show ((5 : ℤ_[2]) : ℚ_[2]) = 5 from rfl,
      show ((10 : ℤ_[2]) : ℚ_[2]) = 10 from rfl]
    ring
  have hscale : (toBilin' !![2, 1, 0; 1, 2, 0; 0, 0, 2 * a]).Equivalent
      (toBilin' !![2, 1, 0; 1, 2, 0; 0, 0, 10 * (5 * a)]) :=
    ⟨b.isometryEquivOfToMatrixEq (Pi.basisFun ℤ_[2] (Fin 3)) (by
      rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin']
      exact hgram)⟩
  have hcoeff : (2 : ℤ_[2]) * (5 * a) = 10 * a := by ring
  simpa only [hcoeff] using hscale.trans (even_lower_hyperbolic (h5.mul ha)).symm

end TauCeti
