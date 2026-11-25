/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearDistortion
public import TauCeti.Analysis.InnerProductSpace.SingularValues.Planar

/-!
# Checks for the outer and inner distortion of a linear map

Worked examples for `Orientation.outerDistortion` (`q_O`) and `Orientation.innerDistortion`
(`q_I`), mostly on a real inner product plane `E` with an orthonormal basis `e`, oriented by `e`
on both sides, writing `toLin e e M` for the operator with matrix `M` in that basis. The
dimension-`3` Checks use an orthonormal basis `f` of a `3`-dimensional space `F` in the same way,
and the dimension-`1` Check an oriented line `L`:

* `diag(2, 1)` has `‖A‖ = 2`, `J(A) = 2` and `ℓ(A) = 1`, so `q_O(A) = 4 / 2 = 2` and
  `q_I(A) = 2 / 1 = 2`;
* the reflection `R = diag(-1, 1)` has `q_O(R) = ∞` and `q_I(R) = 0`, while the naive quotient
  `‖R‖² / J(R)` is `-1`; the distortion inequality `‖R‖² ≤ K J(R)` holds for `K = -1`, which is
  why its comparison with `q_O ≤ K` needs `K ≥ 0`;
* the zero map has `q_O(0) = q_I(0) = 0`;
* `R ∘ R = id` has `q_I(id) = 1`, larger than `q_I(R) q_I(R) = 0`: submultiplicativity of `q_I`
  needs `J ≥ 0`;
* `-id` has `q_O(-id) = 1` on the plane, and `q_O(-id) = ∞` on an oriented space of dimension `3`;
* the projection `diag(1, 0)` has `J = 0`, so `q_O = ∞` and `q_I = 0`;
* in dimension `3`, `diag(2, 1, 1)` has `q_O = 4 = q_I²`, `diag(1, 1, 1/2)` has `q_I = 4 = q_O²`,
  and `diag(3, 2, 1)` has `q_O = 9/2`, `q_I = 6`, with `q_I < q_O²` and `q_O < q_I²`;
* in dimension `1`, `a · id` with `a > 0` has `q_O = q_I = 1`.
-/

public section

open Module Matrix LinearMap
open scoped ENNReal

namespace TauCeti.LinearDistortionChecks

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (finrank ℝ E = 2)] (e : OrthonormalBasis (Fin 2) ℝ E)

/-- `diag(2, 1)` has outer distortion `‖A‖² / J(A) = 4 / 2 = 2` and inner distortion
`J(A) / ℓ(A)² = 2 / 1 = 2`. -/
example :
    e.toBasis.orientation.outerDistortion e.toBasis.orientation
        (toLin e.toBasis e.toBasis (diagonal ![(2 : ℝ), 1])) = 2 ∧
      e.toBasis.orientation.innerDistortion e.toBasis.orientation
        (toLin e.toBasis e.toBasis (diagonal ![(2 : ℝ), 1])) = 2 := by
  have hJ : e.toBasis.orientation.orientedJacobian e.toBasis.orientation
      (toLin e.toBasis e.toBasis (diagonal ![(2 : ℝ), 1])) = 2 := by simp
  constructor
  · rw [Orientation.outerDistortion_of_pos _ _ (by rw [hJ]; norm_num), hJ,
      norm_toContinuousLinearMap_eq_singularValues_zero,
      singularValues_toLin_diagonal_fin_two e (by norm_num)]
    norm_num
  · rw [Orientation.innerDistortion_of_pos _ _ (by rw [hJ]; norm_num), hJ, minimalStretch_def,
      finrank_eq_card_basis e.toBasis, singularValues_toLin_diagonal_fin_two e (by norm_num)]
    norm_num

/-- The reflection `R = diag(-1, 1)` has `q_O(R) = ∞` and `q_I(R) = 0`, while the naive quotient
`‖R‖² / J(R)` is `-1`. -/
example :
    e.toBasis.orientation.outerDistortion e.toBasis.orientation
        (toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1])) = ⊤ ∧
      e.toBasis.orientation.innerDistortion e.toBasis.orientation
        (toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1])) = 0 ∧
      ‖toContinuousLinearMap (toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1]))‖ ^ 2 /
        e.toBasis.orientation.orientedJacobian e.toBasis.orientation
          (toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1])) = -1 := by
  refine ⟨Orientation.outerDistortion_of_nonpos _ _ (by simp) (by simp),
    Orientation.innerDistortion_of_nonpos _ _ (by simp), ?_⟩
  rw [norm_toContinuousLinearMap_eq_singularValues_zero,
    singularValues_toLin_diagonal_fin_two e (by norm_num)]
  norm_num

/-- For `K = -1` the reflection satisfies the distortion inequality `‖R‖² ≤ K J(R)`, although
`q_O(R) = ∞`: the comparison of `‖A‖ⁿ ≤ K J(A)` with `q_O(A) ≤ K` needs `K ≥ 0`. -/
example :
    ‖toContinuousLinearMap (toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1]))‖ ^ 2 ≤
      -1 * e.toBasis.orientation.orientedJacobian e.toBasis.orientation
        (toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1])) := by
  rw [norm_toContinuousLinearMap_eq_singularValues_zero,
    singularValues_toLin_diagonal_fin_two e (by norm_num)]
  norm_num

/-- The zero map has `q_O(0) = q_I(0) = 0`; with the convention `0 / 0 = ∞` every constant map
would fail to be quasiregular. -/
example : e.toBasis.orientation.outerDistortion e.toBasis.orientation (0 : E →ₗ[ℝ] E) = 0 ∧
    e.toBasis.orientation.innerDistortion e.toBasis.orientation (0 : E →ₗ[ℝ] E) = 0 :=
  ⟨Orientation.outerDistortion_zero _ _ two_pos, Orientation.innerDistortion_zero _ _ two_pos⟩

/-- `R ∘ R = id`, and `q_I(id) = 1 > 0 = q_I(R) q_I(R)`: submultiplicativity of the inner
distortion needs `J ≥ 0`. -/
example :
    toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1]) ∘ₗ
        toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1]) = LinearMap.id ∧
      e.toBasis.orientation.innerDistortion e.toBasis.orientation (LinearMap.id : E →ₗ[ℝ] E) = 1 ∧
      e.toBasis.orientation.innerDistortion e.toBasis.orientation
          (toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1])) *
        e.toBasis.orientation.innerDistortion e.toBasis.orientation
          (toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1])) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← toLin_mul, diagonal_mul_diagonal, ← toLin_one e.toBasis]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonal]
  · have hid : (LinearIsometryEquiv.refl ℝ E : E →ₗ[ℝ] E) = LinearMap.id :=
      LinearMap.ext fun _ ↦ by simp
    rw [← hid]
    exact e.toBasis.orientation.innerDistortion_linearIsometryEquiv e.toBasis.orientation _
      (by rw [hid, Orientation.orientedJacobian_id])
  · rw [Orientation.innerDistortion_of_nonpos _ _ (by simp), zero_mul]

/-- `-id` on the plane has outer distortion `1`: `J(-id) = (-1)² = 1`. -/
example : e.toBasis.orientation.outerDistortion e.toBasis.orientation
    (-(LinearMap.id : E →ₗ[ℝ] E)) = 1 := by
  rw [← neg_one_smul ℝ (LinearMap.id : E →ₗ[ℝ] E),
    Orientation.outerDistortion_smul _ _ (by norm_num)]
  have hid : (LinearIsometryEquiv.refl ℝ E : E →ₗ[ℝ] E) = LinearMap.id :=
    LinearMap.ext fun _ ↦ by simp
  rw [← hid]
  exact e.toBasis.orientation.outerDistortion_linearIsometryEquiv e.toBasis.orientation _
    (by rw [hid, Orientation.orientedJacobian_id])

/-- `-id` on an oriented space of dimension `3` has outer distortion `∞`: `J(-id) = (-1)³ = -1`. -/
example {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [Fact (finrank ℝ F = 3)] (o : Orientation ℝ F (Fin 3)) :
    o.outerDistortion o (-(LinearMap.id : F →ₗ[ℝ] F)) = ⊤ := by
  have : Nontrivial F := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ F = 3)
  rw [← neg_one_smul ℝ (LinearMap.id : F →ₗ[ℝ] F)]
  refine o.outerDistortion_smul_of_pow_neg o (by norm_num) (by simp) fun h ↦ ?_
  obtain ⟨x, hx⟩ := exists_ne (0 : F)
  exact hx (by simpa using LinearMap.congr_fun h x)

/-- The projection `diag(1, 0)` has `J = 0`, so `q_O = ∞` and `q_I = 0`. -/
example :
    e.toBasis.orientation.outerDistortion e.toBasis.orientation
        (toLin e.toBasis e.toBasis (diagonal ![(1 : ℝ), 0])) = ⊤ ∧
      e.toBasis.orientation.innerDistortion e.toBasis.orientation
        (toLin e.toBasis e.toBasis (diagonal ![(1 : ℝ), 0])) = 0 := by
  exact ⟨Orientation.outerDistortion_of_nonpos _ _ (by simp) (by simp),
    Orientation.innerDistortion_of_nonpos _ _ (by simp)⟩

section Three

/-! ### Checks in dimension three -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [Fact (finrank ℝ F = 3)] (f : OrthonormalBasis (Fin 3) ℝ F)

omit [Fact (finrank ℝ F = 3)] in
/-- The singular values of `diag(d₀, d₁, d₂)` with `d₀ ≥ d₁ ≥ d₂ ≥ 0` are `d₀, d₁, d₂`. -/
theorem singularValues_toLin_diagonal_fin_three {d₀ d₁ d₂ : ℝ} (h₂ : 0 ≤ d₂) (h₁₂ : d₂ ≤ d₁)
    (h₀₁ : d₁ ≤ d₀) :
    (toLin f.toBasis f.toBasis (diagonal ![d₀, d₁, d₂])).singularValues 0 = d₀ ∧
      (toLin f.toBasis f.toBasis (diagonal ![d₀, d₁, d₂])).singularValues 1 = d₁ ∧
      (toLin f.toBasis f.toBasis (diagonal ![d₀, d₁, d₂])).singularValues 2 = d₂ := by
  have h₁ : 0 ≤ d₁ := h₂.trans h₁₂
  have h₀ : 0 ≤ d₀ := h₁.trans h₀₁
  have hanti : Antitone fun k ↦ ‖![d₀, d₁, d₂] (Equiv.refl (Fin 3) k)‖ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [Real.norm_eq_abs, abs_of_nonneg, Fin.le_def, h₁₂.trans h₀₁]
  have h := singularValues_toLin_diagonal f ![d₀, d₁, d₂] (Equiv.refl _) hanti
  exact ⟨by simpa [abs_of_nonneg h₀] using h 0, by simpa [abs_of_nonneg h₁] using h 1,
    by simpa [abs_of_nonneg h₂] using h 2⟩

/-- The outer and inner distortion of `diag(d₀, d₁, d₂)` with `d₀ ≥ d₁ ≥ d₂ > 0`:
`q_O = d₀³ / (d₀ d₁ d₂)` and `q_I = d₀ d₁ d₂ / d₂³`. -/
theorem outerDistortion_innerDistortion_toLin_diagonal_fin_three {d₀ d₁ d₂ : ℝ} (h₂ : 0 < d₂)
    (h₁₂ : d₂ ≤ d₁) (h₀₁ : d₁ ≤ d₀) :
    f.toBasis.orientation.outerDistortion f.toBasis.orientation
        (toLin f.toBasis f.toBasis (diagonal ![d₀, d₁, d₂])) =
        ENNReal.ofReal (d₀ ^ 3 / (d₀ * d₁ * d₂)) ∧
      f.toBasis.orientation.innerDistortion f.toBasis.orientation
        (toLin f.toBasis f.toBasis (diagonal ![d₀, d₁, d₂])) = d₀ * d₁ * d₂ / d₂ ^ 3 := by
  have hJ : f.toBasis.orientation.orientedJacobian f.toBasis.orientation
      (toLin f.toBasis f.toBasis (diagonal ![d₀, d₁, d₂])) = d₀ * d₁ * d₂ := by
    simp [Fin.prod_univ_succ, mul_assoc]
  have hJpos : 0 < d₀ * d₁ * d₂ := by
    have : 0 < d₁ := h₂.trans_le h₁₂
    have : 0 < d₀ := this.trans_le h₀₁
    positivity
  obtain ⟨h0, -, h2⟩ := singularValues_toLin_diagonal_fin_three f h₂.le h₁₂ h₀₁
  constructor
  · rw [Orientation.outerDistortion_of_pos _ _ (by rwa [hJ]), hJ,
      norm_toContinuousLinearMap_eq_singularValues_zero, h0]
  · rw [Orientation.innerDistortion_of_pos _ _ (by rwa [hJ]), hJ, minimalStretch_def,
      finrank_eq_card_basis f.toBasis, Fintype.card_fin]
    exact congrArg (fun x ↦ d₀ * d₁ * d₂ / x ^ 3) h2

/-- `diag(2, 1, 1)` has `q_O = 8 / 2 = 4` and `q_I = 2 / 1 = 2`, so `q_O = q_I²`: the case
`σ₁ = σ₂` of equality in `q_O ≤ q_I²` (singular values indexed from `0`). -/
example :
    f.toBasis.orientation.outerDistortion f.toBasis.orientation
        (toLin f.toBasis f.toBasis (diagonal ![(2 : ℝ), 1, 1])) = 4 ∧
      f.toBasis.orientation.innerDistortion f.toBasis.orientation
        (toLin f.toBasis f.toBasis (diagonal ![(2 : ℝ), 1, 1])) = 2 ∧
      f.toBasis.orientation.outerDistortion f.toBasis.orientation
          (toLin f.toBasis f.toBasis (diagonal ![(2 : ℝ), 1, 1])) =
        ENNReal.ofReal (f.toBasis.orientation.innerDistortion f.toBasis.orientation
          (toLin f.toBasis f.toBasis (diagonal ![(2 : ℝ), 1, 1])) ^ 2) := by
  obtain ⟨hO, hI⟩ := outerDistortion_innerDistortion_toLin_diagonal_fin_three f
    (d₀ := 2) (d₁ := 1) (d₂ := 1) one_pos le_rfl one_le_two
  rw [hO, hI]
  norm_num

/-- `diag(1, 1, 1/2)` has `q_O = 1 / (1/2) = 2` and `q_I = (1/2) / (1/8) = 4`, so `q_I = q_O²`:
the case `σ₀ = σ₁` of equality in `q_I ≤ q_O²` (singular values indexed from `0`). -/
example :
    f.toBasis.orientation.outerDistortion f.toBasis.orientation
        (toLin f.toBasis f.toBasis (diagonal ![(1 : ℝ), 1, 1 / 2])) = 2 ∧
      f.toBasis.orientation.innerDistortion f.toBasis.orientation
        (toLin f.toBasis f.toBasis (diagonal ![(1 : ℝ), 1, 1 / 2])) = 4 ∧
      ENNReal.ofReal (f.toBasis.orientation.innerDistortion f.toBasis.orientation
          (toLin f.toBasis f.toBasis (diagonal ![(1 : ℝ), 1, 1 / 2]))) =
        f.toBasis.orientation.outerDistortion f.toBasis.orientation
          (toLin f.toBasis f.toBasis (diagonal ![(1 : ℝ), 1, 1 / 2])) ^ 2 := by
  obtain ⟨hO, hI⟩ := outerDistortion_innerDistortion_toLin_diagonal_fin_three f
    (d₀ := 1) (d₁ := 1) (d₂ := 1 / 2) (by norm_num) (by norm_num) le_rfl
  rw [hO, hI, ← ENNReal.ofReal_pow (by norm_num)]
  norm_num

/-- `diag(3, 2, 1)` has `q_O = 27 / 6 = 9/2` and `q_I = 6`, and both comparisons are strict:
`6 < (9/2)²` and `9/2 < 6²`. -/
example :
    f.toBasis.orientation.outerDistortion f.toBasis.orientation
        (toLin f.toBasis f.toBasis (diagonal ![(3 : ℝ), 2, 1])) = ENNReal.ofReal (9 / 2) ∧
      f.toBasis.orientation.innerDistortion f.toBasis.orientation
        (toLin f.toBasis f.toBasis (diagonal ![(3 : ℝ), 2, 1])) = 6 ∧
      ENNReal.ofReal (f.toBasis.orientation.innerDistortion f.toBasis.orientation
          (toLin f.toBasis f.toBasis (diagonal ![(3 : ℝ), 2, 1]))) <
        f.toBasis.orientation.outerDistortion f.toBasis.orientation
          (toLin f.toBasis f.toBasis (diagonal ![(3 : ℝ), 2, 1])) ^ 2 ∧
      f.toBasis.orientation.outerDistortion f.toBasis.orientation
          (toLin f.toBasis f.toBasis (diagonal ![(3 : ℝ), 2, 1])) <
        ENNReal.ofReal (f.toBasis.orientation.innerDistortion f.toBasis.orientation
          (toLin f.toBasis f.toBasis (diagonal ![(3 : ℝ), 2, 1])) ^ 2) := by
  obtain ⟨hO, hI⟩ := outerDistortion_innerDistortion_toLin_diagonal_fin_three f
    (d₀ := 3) (d₁ := 2) (d₂ := 1) one_pos one_le_two (by norm_num)
  have hO' : ENNReal.ofReal ((3 : ℝ) ^ 3 / (3 * 2 * 1)) = ENNReal.ofReal (9 / 2) := by norm_num
  rw [hO, hI, hO', ← ENNReal.ofReal_pow (by norm_num)]
  refine ⟨rfl, by norm_num, ?_, ?_⟩ <;>
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

end Three

/-- In dimension `1`, `A = a · id` with `a > 0` has `q_O(A) = q_I(A) = 1`, and the exponent
`n - 1` of the comparison is `0`. -/
example {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    [Fact (finrank ℝ L = 1)] (o : Orientation ℝ L (Fin 1)) {a : ℝ} (ha : 0 < a) :
    o.outerDistortion o (a • LinearMap.id) = 1 ∧ o.innerDistortion o (a • LinearMap.id) = 1 := by
  have hid : (LinearIsometryEquiv.refl ℝ L : L →ₗ[ℝ] L) = LinearMap.id :=
    LinearMap.ext fun _ ↦ by simp
  rw [o.outerDistortion_smul o (by simpa using ha), o.innerDistortion_smul o (by simpa using ha)]
  refine ⟨o.outerDistortion_id, ?_⟩
  rw [← hid]
  exact o.innerDistortion_linearIsometryEquiv o _ (by rw [hid, Orientation.orientedJacobian_id])

end TauCeti.LinearDistortionChecks
