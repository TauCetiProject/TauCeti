/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Transvection.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Transvection
public import TauCeti.NumberTheory.Modular.Abelianization
import Mathlib.LinearAlgebra.Matrix.ToLin
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.RankOne

/-!
# Symplectic transvections in `SL(2, ℤ)` and positive factorizations

For `v ∈ ℤ²` let `ω(v, x) = v₀ x₁ - v₁ x₀` be the standard symplectic form. The symplectic
transvection `τ_v : x ↦ x + ω(v, x) v` has matrix `[[1 - v₀ v₁, v₀²], [-v₁², 1 + v₀ v₁]]` and
lies in `SL(2, ℤ)`; it is Mathlib's `LinearMap.transvection` for the form `ω(v, ·)` and the
vector `v`. On `H₁(T²; ℤ) = ℤ²` with an oriented basis `(a, b)`, `a · b = 1`, the positive Dehn
twist about a simple closed curve of primitive class `v` acts by `x ↦ x + (v · x) v`, which is
`τ_v` (Farb–Margalit, Proposition 6.3). In particular `τ_a = T = [[1, 1], [0, 1]]` and
`τ_b = S T S⁻¹ = [[1, 0], [-1, 1]]`, in column convention.

Since `SL(2, ℤ) = Sp(2, ℤ)`, `τ_v` is the case `m = 1`, `c = -1` of the general symplectic
transvection `TauCeti.GLSymplecticFin.symplecticTransvection`, and its laws specialize those of
the general one. Conjugation moves the vector: `g τ_v g⁻¹ = τ_{g v}`. Since every primitive vector
is the first column of a matrix in `SL(2, ℤ)`, every `τ_v` with `v` primitive is conjugate to `T`,
so its class in the abelianization `SL(2, ℤ)ᵃᵇ ≅ ℤ/12` is `1`. Hence a positive factorization of
the identity into such twists has length divisible by `12`. The bound is attained: `τ_a τ_b = -U`
has order six, so `(τ_a τ_b)⁶ = 1` is a positive factorization of length `12`, while
`(τ_a τ_b)³ = -1`.

## Main declarations

* `TauCeti.ModularGroup.symplecticTransvection`: the transvection `τ_v ∈ SL(2, ℤ)`.
* `TauCeti.ModularGroup.toGL_symplecticTransvection`: `τ_v` is the general symplectic
  transvection `TauCeti.GLSymplecticFin.symplecticTransvection v (-1)` of `Sp(2, ℤ) = SL(2, ℤ)`,
  whose laws give the action on vectors and the conjugation law below.
* `TauCeti.ModularGroup.toLin'_symplecticTransvection`: `τ_v` is `LinearMap.transvection`.
* `TauCeti.ModularGroup.mul_symplecticTransvection_mul_inv`: `g τ_v g⁻¹ = τ_{g v}`.
* `TauCeti.ModularGroup.isConj_T_symplecticTransvection`: for primitive `v`, `τ_v` is conjugate
  to `T`.
* `TauCeti.ModularGroup.sl2zAbelianizationMulEquiv_of_symplecticTransvection`: for primitive `v`,
  the class of `τ_v` in `ℤ/12` is `1`.
* `TauCeti.ModularGroup.twelve_dvd_length_of_prod_symplecticTransvection_eq_one`: a product of
  transvections by primitive vectors equal to `1` has length divisible by `12`.

## References

* B. Farb, D. Margalit, *A Primer on Mapping Class Groups*, Princeton University Press, 2012,
  Proposition 6.3 (the action of a Dehn twist on homology) and §2.2.4 (`Mod(T²) ≅ SL(2, ℤ)`).
* R. Gompf, A. Stipsicz, *4-Manifolds and Kirby Calculus*, Graduate Studies in Mathematics 20,
  AMS, 1999, §8.2 (monodromy factorizations into right-handed Dehn twists).
-/

public section

open scoped Matrix MatrixGroups

namespace TauCeti.ModularGroup

open _root_.ModularGroup

/-- The symplectic transvection `τ_v : x ↦ x + ω(v, x) v` of `ℤ²`, where
`ω(v, x) = v₀ x₁ - v₁ x₀`, as an element of `SL(2, ℤ)`. For primitive `v` it is the action on
`H₁(T²; ℤ)` of the positive Dehn twist about a curve of class `v`. -/
def symplecticTransvection (v : Fin 2 → ℤ) : SL(2, ℤ) :=
  .mk !![1 - v 0 * v 1, v 0 ^ 2; -v 1 ^ 2, 1 + v 0 * v 1] (by
    rw [Matrix.det_fin_two_of]; ring)

/-- The matrix of the symplectic transvection `τ_v`. -/
@[simp]
theorem coe_symplecticTransvection (v : Fin 2 → ℤ) :
    (symplecticTransvection v : Matrix (Fin 2) (Fin 2) ℤ) =
      !![1 - v 0 * v 1, v 0 ^ 2; -v 1 ^ 2, 1 + v 0 * v 1] :=
  Matrix.SpecialLinearGroup.coe_mk _

/-- The symplectic transvection `τ_v` is the general symplectic transvection
`TauCeti.GLSymplecticFin.symplecticTransvection v (-1)` of `Sp(2, ℤ)`. The parameter is `-1`
because the general one is built from the form `vᵀ J x = v₁ x₀ - v₀ x₁ = -ω(v, x)`. -/
theorem toGL_symplecticTransvection (v : Fin 2 → ℤ) :
    Matrix.SpecialLinearGroup.toGL (symplecticTransvection v) =
      (GLSymplecticFin.symplecticTransvection (m := 1) v (-1) : GL (Fin (1 + 1)) ℤ) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, GLSymplecticFin.coe_symplecticTransvection,
    JFin_one_eq]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.vecHead, Matrix.vecTail] <;> ring

/-- The symplectic transvection acts by `x ↦ x + ω(v, x) v`. -/
theorem symplecticTransvection_mulVec (v x : Fin 2 → ℤ) :
    (symplecticTransvection v : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ x =
      x + (v 0 * x 1 - v 1 * x 0) • v := by
  rw [← Matrix.SpecialLinearGroup.coe_GL_coe_matrix, toGL_symplecticTransvection,
    GLSymplecticFin.coe_symplecticTransvection_mulVec, JFin_one_eq]
  simp [dotProduct, Fin.sum_univ_two]
  ring

/-- The symplectic transvection `τ_v` is Mathlib's transvection for the linear form
`ω(v, ·) = v₀ x₁ - v₁ x₀` and the vector `v`. -/
theorem toLin'_symplecticTransvection (v : Fin 2 → ℤ) :
    Matrix.toLin' (symplecticTransvection v : Matrix (Fin 2) (Fin 2) ℤ) =
      LinearMap.transvection (v 0 • LinearMap.proj 1 - v 1 • LinearMap.proj 0) v := by
  refine LinearMap.ext fun x ↦ ?_
  rw [Matrix.toLin'_apply, symplecticTransvection_mulVec, LinearMap.transvection.apply]
  simp

/-- **Conjugating a transvection moves its vector**: `g τ_v g⁻¹ = τ_{g v}` in `SL(2, ℤ)`. This is
`TauCeti.GLSymplecticFin.mul_symplecticTransvection_mul_inv`, since `SL(2, ℤ) = Sp(2, ℤ)`
(`Matrix.SpecialLinearGroup.toGL_mem_GLSymplecticFin`). -/
theorem mul_symplecticTransvection_mul_inv (g : SL(2, ℤ)) (v : Fin 2 → ℤ) :
    g * symplecticTransvection v * g⁻¹ =
      symplecticTransvection ((g : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) := by
  refine Matrix.SpecialLinearGroup.toGL_injective ?_
  have h := GLSymplecticFin.mul_symplecticTransvection_mul_inv
    (⟨Matrix.SpecialLinearGroup.toGL g, g.toGL_mem_GLSymplecticFin⟩ : GLSymplecticFin 1 ℤ) v (-1)
  rw [map_mul, map_mul, map_inv, toGL_symplecticTransvection, toGL_symplecticTransvection]
  exact congrArg Subtype.val h

/-- The transvection along the first basis vector is `T = [[1, 1], [0, 1]]`. -/
@[simp]
theorem symplecticTransvection_one_zero : symplecticTransvection ![1, 0] = T := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The transvection along the second basis vector is `S T S⁻¹ = [[1, 0], [-1, 1]]`. -/
theorem symplecticTransvection_zero_one : symplecticTransvection ![0, 1] = S * T * S⁻¹ := by
  rw [← symplecticTransvection_one_zero, mul_symplecticTransvection_mul_inv]
  congr 1
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The product of the transvections along the two basis vectors is `-U = [[0, 1], [-1, 1]]`,
the order-six generator of the amalgam presentation `TauCeti.ModularGroup.sl2zPresentationEquiv`.
-/
theorem symplecticTransvection_one_zero_mul_zero_one :
    symplecticTransvection ![1, 0] * symplecticTransvection ![0, 1] = -U := by
  rw [symplecticTransvection_one_zero, symplecticTransvection_zero_one, T_mul_S_mul_T_mul_S_inv]

/-- The cube of `τ_a τ_b` is `-1`: a positive word of length six with product `-1`, not `1`. -/
theorem symplecticTransvection_one_zero_mul_zero_one_pow_three :
    (symplecticTransvection ![1, 0] * symplecticTransvection ![0, 1]) ^ 3 = -1 := by
  rw [symplecticTransvection_one_zero_mul_zero_one, neg_U_pow_three]

/-- The sixth power of `τ_a τ_b` is `1`: a positive factorization of the identity of length
twelve. -/
theorem symplecticTransvection_one_zero_mul_zero_one_pow_six :
    (symplecticTransvection ![1, 0] * symplecticTransvection ![0, 1]) ^ 6 = 1 := by
  rw [show 6 = 3 * 2 from rfl, pow_mul, symplecticTransvection_one_zero_mul_zero_one_pow_three,
    neg_one_sq]

/-- **Twists along primitive vectors are conjugate to `T`**: if `v₀` and `v₁` are coprime, then
`τ_v = g T g⁻¹` for any `g ∈ SL(2, ℤ)` with first column `v`. -/
theorem isConj_T_symplecticTransvection {v : Fin 2 → ℤ} (hv : IsCoprime (v 0) (v 1)) :
    IsConj T (symplecticTransvection v) := by
  obtain ⟨g, hg0, hg1⟩ := hv.exists_SL2_col 0
  refine isConj_iff.2 ⟨g, ?_⟩
  rw [← symplecticTransvection_one_zero, mul_symplecticTransvection_mul_inv]
  congr 1
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hg0, hg1]

/-- Under the abelianization `SL(2, ℤ)ᵃᵇ ≅ ℤ/12`, every transvection along a primitive vector,
the homology action of a positive Dehn twist, goes to `1`. -/
theorem sl2zAbelianizationMulEquiv_of_symplecticTransvection {v : Fin 2 → ℤ}
    (hv : IsCoprime (v 0) (v 1)) :
    sl2zAbelianizationMulEquiv (Group.Abelianization.of (symplecticTransvection v)) =
      Multiplicative.ofAdd 1 :=
  sl2zAbelianizationMulEquiv_of_of_isConj (isConj_T_symplecticTransvection hv)

/-- **Positive factorizations of the identity have length divisible by twelve**: if a product of
transvections `τ_v` along primitive vectors `v` is `1` in `SL(2, ℤ)`, the number of factors is
divisible by `12`. -/
theorem twelve_dvd_length_of_prod_symplecticTransvection_eq_one {l : List (Fin 2 → ℤ)}
    (hl : ∀ v ∈ l, IsCoprime (v 0) (v 1)) (h : (l.map symplecticTransvection).prod = 1) :
    12 ∣ l.length := by
  rw [← List.length_map symplecticTransvection]
  refine twelve_dvd_length_of_prod_eq_one (fun g hg ↦ ?_) h
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hg
  exact isConj_T_symplecticTransvection (hl v hv)

end TauCeti.ModularGroup
