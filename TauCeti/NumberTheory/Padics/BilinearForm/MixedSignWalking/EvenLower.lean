/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.BilinearForm.MixedSignWalking.Basic
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
import TauCeti.NumberTheory.Padics.SerreSigns

/-!
# Mixed-type sign walking with the even constituent at the lower scale

For the even unimodular planes `U = !![0, 1; 1, 0]` and `V = !![2, 1; 1, 2]`, and
any dyadic unit `a`, this file proves

```text
U ⊕ ⟨2a⟩ ≅ V ⊕ ⟨10a⟩,     V ⊕ ⟨2a⟩ ≅ U ⊕ ⟨10a⟩.
```

Together with the moves in `MixedSignWalking.Basic`, these give both scale orderings of
mixed-type sign walking between adjacent Jordan constituents. Multiplying the odd
constituent by `5` reverses its sign and changes its oddity by four; interchanging `U` and
`V` reverses the even constituent's sign. Both moves hold after multiplication by any
common scale `2ᵏ`. In the displayed matrices below the unary coordinate is placed first.

For the first move a basis has columns `(1, 2, 2a)`, `(-1, 1, 0)` and `(-1, 0, a)`.
Its determinant is `5a`. The first vector has norm `10a`, and its orthogonal complement
has Gram matrix `a • !![2, 3; 3, 2]`, isometric to `V` by the binary calculation in
`MixedSignWalking.Basic`.

## References

* D. Allcock, I. Gal and A. Mark, *The Conway–Sloane calculus for 2-adic lattices*,
  Lemma 4.2(1), for sign walking between adjacent scales of different types.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Matrix

namespace TauCeti

private theorem even_lower_sign_walking_hyperbolic {a : ℤ_[2]} (ha : IsUnit a) :
    (toBilin' !![2 * a, 0, 0; 0, 0, 1; 0, 1, 0]).Equivalent
      (toBilin' !![10 * a, 0, 0; 0, 2, 1; 0, 1, 2]) := by
  let P : Matrix (Fin 3) (Fin 3) ℤ_[2] := !![1, -1, -1; 2, 1, 0; 2 * a, 0, a]
  have hP : IsUnit P.det := by
    have hdet : P.det = 5 * a := by simp [P, det_fin_three]; ring
    rw [hdet]
    exact isUnit_five_padicInt.mul ha
  have hfirst : (toBilin' !![2 * a, 0, 0; 0, 0, 1; 0, 1, 0]).Equivalent
      (toBilin' !![10 * a, 0, 0; 0, 2 * a, 3 * a; 0, 3 * a, 2 * a]) := by
    have hmatrix : Pᵀ * !![2 * a, 0, 0; 0, 0, 1; 0, 1, 0] * P =
        !![10 * a, 0, 0; 0, 2 * a, 3 * a; 0, 3 * a, 2 * a] := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [P, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
    rw [← hmatrix, ← toBilin'_comp,
      ← toLinearEquiv'_apply P (P.invertibleOfIsUnitDet hP)]
    exact ⟨(toBilin' _).isometryEquivOfCompLinearEquiv _⟩
  apply hfirst.trans
  simpa using equivalent_toBilin'_unary_smul_binary_two_three_mul (10 * a) 1 ha

private theorem even_lower_sign_walking_anisotropic {a : ℤ_[2]} (ha : IsUnit a) :
    (toBilin' !![2 * a, 0, 0; 0, 2, 1; 0, 1, 2]).Equivalent
      (toBilin' !![10 * a, 0, 0; 0, 0, 1; 0, 1, 0]) := by
  have h := even_lower_sign_walking_hyperbolic (isUnit_five_padicInt.mul ha)
  let P : Matrix (Fin 3) (Fin 3) ℤ_[2] := diagonal ![5, 1, 1]
  have hP : IsUnit P.det := by
    simpa [P, det_diagonal, Fin.prod_univ_three] using isUnit_five_padicInt
  have hscale : (toBilin' !![2 * a, 0, 0; 0, 2, 1; 0, 1, 2]).Equivalent
      (toBilin' !![10 * (5 * a), 0, 0; 0, 2, 1; 0, 1, 2]) := by
    have hmatrix : Pᵀ * !![2 * a, 0, 0; 0, 2, 1; 0, 1, 2] * P =
        !![10 * (5 * a), 0, 0; 0, 2, 1; 0, 1, 2] := by
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [P, Matrix.mul_apply, Fin.sum_univ_three]
      ring
    rw [← hmatrix, ← toBilin'_comp,
      ← toLinearEquiv'_apply P (P.invertibleOfIsUnitDet hP)]
    exact ⟨(toBilin' _).isometryEquivOfCompLinearEquiv _⟩
  simpa only [← mul_assoc, show (2 : ℤ_[2]) * 5 = 10 by norm_num] using hscale.trans h.symm

/-- **Mixed-type sign walking with `U` at the lower scale.** The adjacent constituents
`2ᵏ U` and `⟨2ᵏ⁺¹ a⟩` may be replaced by `2ᵏ V` and `⟨2ᵏ⁺¹ 5a⟩`.
The unary coordinate is first in these Gram matrices. -/
theorem equivalent_toBilin'_two_unary_hyperbolic (k : ℕ) {a : ℤ_[2]} (ha : IsUnit a) :
    (toBilin' ((2 : ℤ_[2]) ^ k • !![2 * a, 0, 0; 0, 0, 1; 0, 1, 0])).Equivalent
      (toBilin' ((2 : ℤ_[2]) ^ k • !![10 * a, 0, 0; 0, 2, 1; 0, 1, 2])) := by
  simp only [map_smul]
  exact (LinearMap.BilinForm.equivalent_smul_iff
    (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k two_ne_zero))).mpr
      (even_lower_sign_walking_hyperbolic ha)

/-- **Mixed-type sign walking with `V` at the lower scale.** The adjacent constituents
`2ᵏ V` and `⟨2ᵏ⁺¹ a⟩` may be replaced by `2ᵏ U` and `⟨2ᵏ⁺¹ 5a⟩`.
The unary coordinate is first in these Gram matrices. -/
theorem equivalent_toBilin'_two_unary_anisotropic (k : ℕ) {a : ℤ_[2]} (ha : IsUnit a) :
    (toBilin' ((2 : ℤ_[2]) ^ k • !![2 * a, 0, 0; 0, 2, 1; 0, 1, 2])).Equivalent
      (toBilin' ((2 : ℤ_[2]) ^ k • !![10 * a, 0, 0; 0, 0, 1; 0, 1, 0])) := by
  simp only [map_smul]
  exact (LinearMap.BilinForm.equivalent_smul_iff
    (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k two_ne_zero))).mpr
      (even_lower_sign_walking_anisotropic ha)

end TauCeti
