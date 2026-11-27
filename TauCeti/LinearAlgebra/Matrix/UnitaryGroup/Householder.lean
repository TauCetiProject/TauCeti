/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Module
import TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec

/-!
# Householder reflections over a star ring

Let `α` be a star ring that is an algebra over a commutative ring `R` with trivial star, such as
the quaternions over `ℝ`. For a vector `v` with Hermitian square `vᴴ v = s ∈ R` and a scalar `c`
with `c² s = 2 c`, the matrix `H = 1 - c v vᴴ` is Hermitian and squares to the identity, hence
is unitary. For `s` invertible and `c = 2 / s` this is the Householder reflection in `v`. No
commutativity of `α` is assumed.

Over `ℝ` or `ℂ`, a Householder reflection and a diagonal phase correction give a special unitary
matrix with a prescribed `i`-th column `y`, for a unit vector `y` with `yᵢ ≠ 0`. Let
`ω = yᵢ / |yᵢ|` be the phase of `yᵢ`, and `u = ω eᵢ + y`, so that `uᴴ u = 2 + 2 |yᵢ|`. The
reflection `R = 1 - (1 + |yᵢ|)⁻¹ u uᴴ` in `u` sends `-ω eᵢ` to `y`, because `⟪-ω eᵢ, y⟫ = -|yᵢ|`
is real, and it has determinant `-1`. For an index `j ≠ i`, the diagonal matrix `D` with entries
`-ω` at `i`, `conj ω` at `j` and `1` elsewhere sends `eᵢ` to `-ω eᵢ` and also has determinant `-1`.
So `R D` is special unitary with `i`-th column `y`. Its entries involve only the coordinates of
`y`, their conjugates, `ω` and `(1 + |yᵢ|)⁻¹`.

## Main definitions

* `Matrix.householderSpecialUnitaryAxis`, `Matrix.householderSpecialUnitaryDiag`: the axis `u` of
  the reflection and the diagonal entries of the phase correction `D`.
* `Matrix.householderSpecialUnitary`: the matrix `R D`.

## Main results

* `Matrix.one_sub_smul_vecMulVec_mem_unitary`: the matrix `1 - c v vᴴ` is unitary when
  `vᴴ v = s` and `c² s = 2 c`.
* `Matrix.householderSpecialUnitary_mem_specialUnitaryGroup`: `R D` is special unitary.
* `Matrix.householderSpecialUnitary_mulVec_single`: the `i`-th column of `R D` is `y`.
-/

public section

open scoped Matrix

namespace Matrix

variable {R α n : Type*} [CommRing R] [StarRing R] [TrivialStar R] [Ring α] [StarRing α]
  [Algebra R α] [StarModule R α] [Fintype n] [DecidableEq n]

/-- **A Householder reflection is unitary.** If `vᴴ v = s` and `c² s = 2 c`, then
`H = 1 - c v vᴴ` is a Hermitian involution, hence unitary. -/
theorem one_sub_smul_vecMulVec_mem_unitary {v : n → α} {s c : R}
    (hvv : star v ⬝ᵥ v = algebraMap R α s) (hc : c * c * s = 2 * c) :
    1 - c • vecMulVec v (star v) ∈ unitary (Matrix n n α) := by
  set P := vecMulVec v (star v)
  have hPP : P * P = s • P := by
    rw [vecMulVec_mul_vecMulVec, hvv, algebraMap_smul, vecMulVec_smul]
  have hH : star (1 - c • P) = 1 - c • P := by
    rw [star_sub, star_one, star_smul, star_trivial, star_eq_conjTranspose,
      conjTranspose_vecMulVec, star_star]
  have hHH : (1 - c • P) * (1 - c • P) = 1 := by
    calc (1 - c • P) * (1 - c • P) = 1 - (2 * c - c * c * s) • P := by
          simp only [sub_mul, mul_sub, mul_one, one_mul, smul_mul_smul_comm, hPP, smul_smul]
          module
      _ = 1 := by rw [hc, sub_self, zero_smul, sub_zero]
  exact ⟨by rw [hH, hHH], by rw [hH, hHH]⟩

section SpecialUnitary

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] {i j : ι} {y : ι → 𝕜}

/-- The axis `ω eᵢ + y` of the Householder reflection that sends `-ω eᵢ` to `y`, for the phase
`ω = yᵢ / |yᵢ|` of the coordinate `yᵢ`. -/
noncomputable def householderSpecialUnitaryAxis (i : ι) (y : ι → 𝕜) : ι → 𝕜 :=
  (‖y i‖⁻¹ • y i) • Pi.single i 1 + y

/-- The diagonal entries `-ω` at `i`, `conj ω` at `j` and `1` elsewhere, for the phase
`ω = yᵢ / |yᵢ|` of the coordinate `yᵢ`. -/
noncomputable def householderSpecialUnitaryDiag (i j : ι) (y : ι → 𝕜) : ι → 𝕜 :=
  Function.update (Function.update 1 j (star (‖y i‖⁻¹ • y i))) i (-(‖y i‖⁻¹ • y i))

omit [Fintype ι] in
/-- The `k`-th coordinate of the axis `ω eᵢ + y`. -/
@[simp]
theorem householderSpecialUnitaryAxis_apply (i : ι) (y : ι → 𝕜) (k : ι) :
    householderSpecialUnitaryAxis i y k =
      (‖y i‖⁻¹ • y i) * (Pi.single i (1 : 𝕜) : ι → 𝕜) k + y k := by
  simp [householderSpecialUnitaryAxis]

omit [Fintype ι] in
/-- The diagonal entries are `-ω` at `i`, `conj ω` at `j ≠ i` and `1` elsewhere. -/
theorem householderSpecialUnitaryDiag_apply (i j : ι) (y : ι → 𝕜) (k : ι) :
    householderSpecialUnitaryDiag i j y k =
      if k = i then -(‖y i‖⁻¹ • y i) else if k = j then star (‖y i‖⁻¹ • y i) else 1 := by
  simp [householderSpecialUnitaryDiag, Function.update_apply]

/-- **A special unitary matrix with prescribed `i`-th column `y`.** The diagonal matrix
`diag(-ω, conj ω, 1, …, 1)` (entries at `i` and `j`) followed by the Householder reflection in the
axis `ω eᵢ + y`, for the phase `ω = yᵢ / |yᵢ|`. For a unit vector `y` with `yᵢ ≠ 0` and `j ≠ i`
it is special unitary (`Matrix.householderSpecialUnitary_mem_specialUnitaryGroup`) with `i`-th
column `y` (`Matrix.householderSpecialUnitary_mulVec_single`). -/
noncomputable def householderSpecialUnitary (i j : ι) (y : ι → 𝕜) : Matrix ι ι 𝕜 :=
  (1 - (1 + ‖y i‖)⁻¹ • vecMulVec (householderSpecialUnitaryAxis i y)
    (star (householderSpecialUnitaryAxis i y))) * diagonal (householderSpecialUnitaryDiag i j y)

private theorem ofReal_one_add_norm_ne_zero (z : 𝕜) : ((1 + ‖z‖ : ℝ) : 𝕜) ≠ 0 :=
  RCLike.ofReal_ne_zero.2 (by positivity)

private theorem ofReal_norm_ne_zero {z : 𝕜} (hz : z ≠ 0) : ((‖z‖ : ℝ) : 𝕜) ≠ 0 :=
  RCLike.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)

/-- The phase `ω = z / |z|` of a nonzero scalar `z` has `conj ω * ω = 1`. -/
private theorem star_phase_mul_self {z : 𝕜} (hz : z ≠ 0) :
    star (‖z‖⁻¹ • z) * (‖z‖⁻¹ • z) = 1 := by
  have := ofReal_norm_ne_zero hz
  rw [RCLike.real_smul_eq_coe_mul, star_mul', mul_mul_mul_comm, RCLike.star_def,
    RCLike.conj_ofReal, RCLike.conj_mul]
  push_cast
  field_simp

/-- The phase `ω = z / |z|` of a nonzero scalar `z` has `conj ω * z = |z|`. -/
private theorem star_phase_mul {z : 𝕜} (hz : z ≠ 0) : star (‖z‖⁻¹ • z) * z = (‖z‖ : 𝕜) := by
  have := ofReal_norm_ne_zero hz
  rw [RCLike.real_smul_eq_coe_mul, star_mul', mul_assoc, RCLike.star_def, RCLike.conj_ofReal,
    RCLike.conj_mul]
  push_cast
  field_simp

/-- The phase `ω = z / |z|` of a nonzero scalar `z` has `conj z * ω = |z|`. -/
private theorem star_mul_phase {z : 𝕜} (hz : z ≠ 0) : star z * (‖z‖⁻¹ • z) = (‖z‖ : 𝕜) := by
  rw [← star_star (‖z‖⁻¹ • z), ← star_mul, star_phase_mul hz, RCLike.star_def,
    RCLike.conj_ofReal]

/-- The Hermitian square of the axis `ω eᵢ + y` of a unit vector `y` is `2 + 2 |yᵢ|`. -/
private theorem star_householderSpecialUnitaryAxis_dotProduct_self (hy : star y ⬝ᵥ y = 1)
    (hi : y i ≠ 0) :
    star (householderSpecialUnitaryAxis i y) ⬝ᵥ householderSpecialUnitaryAxis i y =
      algebraMap ℝ 𝕜 (2 + 2 * ‖y i‖) := by
  have h₁ := star_phase_mul hi
  have h₂ := star_mul_phase hi
  have h₃ := star_phase_mul_self hi
  rw [householderSpecialUnitaryAxis]
  generalize ‖y i‖⁻¹ • y i = ω at h₁ h₂ h₃ ⊢
  simp only [star_add, add_dotProduct, dotProduct_add, hy,
    star_smul, smul_dotProduct, dotProduct_smul, Pi.star_single, star_one, single_dotProduct,
    dotProduct_single, one_mul, mul_one, smul_eq_mul, RCLike.algebraMap_eq_ofReal]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.star_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  push_cast
  linear_combination h₁ + h₂ + h₃

/-- The Householder reflection in the axis `ω eᵢ + y` of a unit vector `y` is unitary. -/
private theorem householderReflection_mem_unitary (hy : star y ⬝ᵥ y = 1) (hi : y i ≠ 0) :
    1 - (1 + ‖y i‖)⁻¹ • vecMulVec (householderSpecialUnitaryAxis i y)
      (star (householderSpecialUnitaryAxis i y)) ∈ unitary (Matrix ι ι 𝕜) := by
  refine one_sub_smul_vecMulVec_mem_unitary
    (star_householderSpecialUnitaryAxis_dotProduct_self hy hi) ?_
  have : (1 + ‖y i‖) ≠ 0 := by positivity
  field_simp

/-- The Householder reflection in the axis `ω eᵢ + y` of a unit vector `y` has determinant
`-1`. -/
private theorem det_householderReflection (hy : star y ⬝ᵥ y = 1) (hi : y i ≠ 0) :
    (1 - (1 + ‖y i‖)⁻¹ • vecMulVec (householderSpecialUnitaryAxis i y)
      (star (householderSpecialUnitaryAxis i y))).det = -1 := by
  rw [← smul_vecMulVec, TauCeti.det_one_sub_vecMulVec, dotProduct_smul,
    star_householderSpecialUnitaryAxis_dotProduct_self hy hi, RCLike.algebraMap_eq_ofReal,
    RCLike.real_smul_eq_coe_mul]
  have := ofReal_one_add_norm_ne_zero (y i)
  push_cast at this ⊢
  field_simp
  ring

private theorem diagonal_householderSpecialUnitaryDiag_mem_unitary (hi : y i ≠ 0) :
    diagonal (householderSpecialUnitaryDiag i j y) ∈ unitary (Matrix ι ι 𝕜) := by
  have h₁ := star_phase_mul_self hi
  rw [diagonal_mem_unitary, Unitary.mem_iff, householderSpecialUnitaryDiag]
  generalize ‖y i‖⁻¹ • y i = ω at h₁ ⊢
  have h₁' : starRingEnd 𝕜 ω * ω = 1 := h₁
  have h₂ : ω * starRingEnd 𝕜 ω = 1 := by rw [mul_comm, h₁']
  constructor <;> ext k <;>
    simp only [Pi.mul_apply, Pi.star_apply, Function.update_apply, Pi.one_apply] <;>
    split_ifs <;> simp [h₁', h₂]

private theorem det_diagonal_householderSpecialUnitaryDiag (hi : y i ≠ 0) (hji : j ≠ i) :
    (diagonal (householderSpecialUnitaryDiag i j y)).det = -1 := by
  rw [det_diagonal, householderSpecialUnitaryDiag, Finset.prod_update_of_mem (Finset.mem_univ _),
    Finset.prod_update_of_mem (by simpa using hji)]
  simp only [Pi.one_apply, Finset.prod_const_one, mul_one]
  rw [neg_mul, mul_comm, star_phase_mul_self hi]

/-- For a unit vector `y` with `yᵢ ≠ 0` and an index `j ≠ i`, the matrix
`Matrix.householderSpecialUnitary i j y` is special unitary. -/
theorem householderSpecialUnitary_mem_specialUnitaryGroup (hy : star y ⬝ᵥ y = 1) (hi : y i ≠ 0)
    (hji : j ≠ i) : householderSpecialUnitary i j y ∈ specialUnitaryGroup ι 𝕜 := by
  rw [mem_specialUnitaryGroup_iff]
  refine ⟨mul_mem (householderReflection_mem_unitary hy hi)
    (diagonal_householderSpecialUnitaryDiag_mem_unitary hi), ?_⟩
  rw [householderSpecialUnitary, det_mul, det_householderReflection hy hi,
    det_diagonal_householderSpecialUnitaryDiag hi hji]
  norm_num

/-- The `i`-th column of `Matrix.householderSpecialUnitary i j y` is `y` when `yᵢ ≠ 0`: the
diagonal factor sends `eᵢ` to `-ω eᵢ`, and the reflection sends `-ω eᵢ` to `y`. -/
theorem householderSpecialUnitary_mulVec_single (hi : y i ≠ 0) :
    householderSpecialUnitary i j y *ᵥ Pi.single i 1 = y := by
  have h₁ := star_phase_mul_self hi
  have h₂ := star_mul_phase hi
  have hc : (1 + ‖y i‖)⁻¹ • (-(1 + (‖y i‖ : 𝕜))) = -1 := by
    have := ofReal_one_add_norm_ne_zero (y i)
    rw [RCLike.real_smul_eq_coe_mul]
    push_cast at this ⊢
    field_simp
  -- The diagonal factor sends `eᵢ` to `-ω eᵢ`.
  rw [householderSpecialUnitary, ← mulVec_mulVec, diagonal_mulVec_single,
    householderSpecialUnitaryDiag, Function.update_self, mul_one, householderSpecialUnitaryAxis]
  generalize ‖y i‖⁻¹ • y i = ω at h₁ h₂ ⊢
  -- The axis `u = ω eᵢ + y` pairs with `-ω eᵢ` to `-(1 + |yᵢ|)`.
  have ha : star (ω • Pi.single i 1 + y) ⬝ᵥ Pi.single i (-ω) = -(1 + (‖y i‖ : 𝕜)) := by
    rw [dotProduct_single]
    simp only [Pi.star_apply, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one, star_add]
    linear_combination (-1 : 𝕜) * h₁ - h₂
  -- So the reflection sends `-ω eᵢ` to `-ω eᵢ + u = y`.
  rw [one_sub_smul_vecMulVec_mulVec, ha, op_smul_eq_smul, ← smul_assoc, hc]
  ext k
  by_cases hk : k = i
  · subst hk
    simp
  · simp [hk]

/-- The entries of `Matrix.householderSpecialUnitary i j y`, for the axis `u` and the diagonal
entries `d`: the `(k, l)` entry is `(δₖₗ - (1 + |yᵢ|)⁻¹ uₖ conj uₗ) dₗ`. -/
theorem householderSpecialUnitary_apply (k l : ι) :
    householderSpecialUnitary i j y k l =
      ((1 : Matrix ι ι 𝕜) k l - (1 + ‖y i‖)⁻¹ • (householderSpecialUnitaryAxis i y k *
        star (householderSpecialUnitaryAxis i y l))) * householderSpecialUnitaryDiag i j y l := by
  simp [householderSpecialUnitary, mul_diagonal, vecMulVec_apply]

end SpecialUnitary

end Matrix
