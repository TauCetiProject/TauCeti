/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Moments.Matrix.Laplace
import TauCeti.Analysis.Normed.Algebra.Basic
import TauCeti.Analysis.Normed.Algebra.Trotter
import TauCeti.Analysis.SpecialFunctions.Exp.QuadraticBound

/-!
# Matrix Bernstein Inequalities

This file proves the **matrix Bernstein inequalities** for sums of independent, centered,
norm-bounded random matrices over `𝕜` (`ℝ` or `ℂ`), both in the Hermitian case and for general
rectangular matrices via the Hermitian dilation `fromBlocks 0 Y Yᴴ 0`.

## Main definitions and results

* `Matrix.IsHermitian.l2_opNorm_eq_norm_eigenvalues`, `Matrix.l2_opNorm_fromBlocks_zero`.
* `Matrix.hermitianDilation`, `Matrix.l2_opNorm_hermitianDilation`.
* `Matrix.integrable_and_posSemidef_exp_smul_integral_sub`: Loewner MGF bound for a summand.
* `ProbabilityTheory.iIndepFun.measureReal_norm_sum_ge_le` / `TauCeti.matrix_bernstein`.
* `ProbabilityTheory.iIndepFun.measureReal_norm_sum_ge_le_rectangular` /
  `TauCeti.matrix_bernstein_rectangular`: sharp rectangular matrix Bernstein inequality.

## References

* [J. A. Tropp, *User-friendly tail bounds for sums of random matrices*][tropp2012]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section

namespace Matrix

variable {m₁ m₂ n₁ n₂ m n 𝕜 : Type*} [RCLike 𝕜]

/-- Every eigenvalue of a Hermitian matrix has absolute value at most its `ℓ²` operator norm. -/
theorem IsHermitian.abs_eigenvalues_le_l2_opNorm [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (i : n) : |hA.eigenvalues i| ≤ ‖A‖ := by
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  have hZ : (0 : Matrix n n 𝕜).IsHermitian := isHermitian_zero
  have h0 : hZ.eigenvalues₀ (e.symm i) = 0 := by
    simpa [IsHermitian.eigenvalues] using congrFun (hZ.eigenvalues_eq_zero_iff.mpr rfl) i
  simpa [IsHermitian.eigenvalues, h0] using hA.abs_eigenvalues₀_sub_le_norm hZ (e.symm i)

/-- The `ℓ²` operator norm of a Hermitian matrix equals the `ℓ^∞` norm of its eigenvalues. -/
theorem IsHermitian.l2_opNorm_eq_norm_eigenvalues [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) : ‖A‖ = ‖hA.eigenvalues‖ := by
  refine le_antisymm ?_
    ((pi_norm_le_iff_of_nonneg (norm_nonneg A)).mpr fun i ↦ hA.abs_eigenvalues_le_l2_opNorm i)
  let U : Matrix n n 𝕜 := hA.eigenvectorUnitary
  let D : Matrix n n 𝕜 := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hU : ‖U‖ ≤ 1 := (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp <| by
    rw [sq, ← l2_opNorm_conjTranspose_mul_self,
      show Uᴴ * U = 1 by simpa [U, star_eq_conjTranspose] using
        Unitary.coe_star_mul_self hA.eigenvectorUnitary,
      ← diagonal_one, l2_opNorm_diagonal, one_pow]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun _ ↦ by simp
  have hUh : ‖Uᴴ‖ ≤ 1 := by rwa [l2_opNorm_conjTranspose]
  have hD : ‖D‖ ≤ ‖hA.eigenvalues‖ := by
    rw [l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i ↦ by
      simpa using norm_le_pi_norm hA.eigenvalues i
  conv_lhs => rw [show A = U * D * Uᴴ by
    simpa [U, D, Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] using hA.spectral_theorem]
  exact ((l2_opNorm_mul _ _).trans
    (mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _))).trans <|
    (mul_le_mul (mul_le_mul hU hD (norm_nonneg _) zero_le_one) hUh
      (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- For a Hermitian matrix `A` on a nonempty index type, either `‖A‖` or `-‖A‖` belongs to
`spectrum ℝ A`. -/
theorem IsHermitian.norm_or_neg_norm_mem_spectrum [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
    ‖A‖ ∈ spectrum ℝ A ∨ -‖A‖ ∈ spectrum ℝ A := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  obtain ⟨k, _, hk⟩ :=
    Finset.exists_max_image Finset.univ (fun i ↦ |hA.eigenvalues i|) Finset.univ_nonempty
  have hnorm_eq : ‖A‖ = |hA.eigenvalues k| := by
    rw [hA.l2_opNorm_eq_norm_eigenvalues]
    exact le_antisymm ((pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun i ↦
      hk i (Finset.mem_univ i)) (norm_le_pi_norm hA.eigenvalues k)
  have hmem : hA.eigenvalues k ∈ spectrum ℝ A :=
    hA.spectrum_real_eq_range_eigenvalues ▸ Set.mem_range_self k
  rcases abs_cases (hA.eigenvalues k) with ⟨hpos, _⟩ | ⟨hneg, _⟩
  · exact Or.inl (hnorm_eq.trans hpos ▸ hmem)
  · exact Or.inr (by rw [hnorm_eq, hneg, neg_neg]; exact hmem)

/-- The `ℓ²` operator norm of a block-diagonal matrix `fromBlocks A 0 0 B` is `max ‖A‖ ‖B‖`. -/
@[simp]
theorem l2_opNorm_fromBlocks_zero [Fintype m₁] [Fintype m₂] [Fintype n₁] [DecidableEq n₁]
    [Fintype n₂] [DecidableEq n₂] (A : Matrix m₁ n₁ 𝕜) (B : Matrix m₂ n₂ 𝕜) :
    ‖Matrix.fromBlocks A (0 : Matrix m₁ n₂ 𝕜) (0 : Matrix m₂ n₁ 𝕜) B‖ = max ‖A‖ ‖B‖ := by
  set D := Matrix.fromBlocks A (0 : Matrix m₁ n₂ 𝕜) (0 : Matrix m₂ n₁ 𝕜) B
  let TD := (toEuclideanLin (𝕜 := 𝕜) (m := m₁ ⊕ m₂) (n := n₁ ⊕ n₂)).trans
    LinearMap.toContinuousLinearMap D
  let TA := (toEuclideanLin (𝕜 := 𝕜) (m := m₁) (n := n₁)).trans LinearMap.toContinuousLinearMap A
  let TB := (toEuclideanLin (𝕜 := 𝕜) (m := m₂) (n := n₂)).trans LinearMap.toContinuousLinearMap B
  have hTD (x : EuclideanSpace 𝕜 (n₁ ⊕ n₂)) : (TD x).ofLp = D *ᵥ x.ofLp := rfl
  have hTA (x : EuclideanSpace 𝕜 n₁) : (TA x).ofLp = A *ᵥ x.ofLp := rfl
  have hTB (x : EuclideanSpace 𝕜 n₂) : (TB x).ofLp = B *ᵥ x.ofLp := rfl
  rw [l2_opNorm_def D, l2_opNorm_def A, l2_opNorm_def B]
  refine le_antisymm ?_ (max_le_iff.mpr ⟨?_, ?_⟩)
  · refine TD.opNorm_le_bound (by positivity) fun x ↦
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
    let x₁ : EuclideanSpace 𝕜 n₁ := WithLp.toLp 2 (x.ofLp ∘ Sum.inl)
    let x₂ : EuclideanSpace 𝕜 n₂ := WithLp.toLp 2 (x.ofLp ∘ Sum.inr)
    have hA_le : ‖TA x₁‖ ≤ max ‖TA‖ ‖TB‖ * ‖x₁‖ :=
      (TA.le_opNorm x₁).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have hB_le : ‖TB x₂‖ ≤ max ‖TA‖ ‖TB‖ * ‖x₂‖ :=
      (TB.le_opNorm x₂).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    calc ‖TD x‖ ^ 2 = ‖TA x₁‖ ^ 2 + ‖TB x₂‖ ^ 2 := by
          simp [EuclideanSpace.norm_sq_eq, hTD, hTA, hTB, D, fromBlocks_mulVec,
            Fintype.sum_sum_type, x₁, x₂]
      _ ≤ (max ‖TA‖ ‖TB‖ * ‖x₁‖) ^ 2 + (max ‖TA‖ ‖TB‖ * ‖x₂‖) ^ 2 :=
          add_le_add (pow_le_pow_left₀ (norm_nonneg _) hA_le 2)
            (pow_le_pow_left₀ (norm_nonneg _) hB_le 2)
      _ = (max ‖TA‖ ‖TB‖ * ‖x‖) ^ 2 := by
          simp only [mul_pow]
          rw [show ‖x‖ ^ 2 = ‖x₁‖ ^ 2 + ‖x₂‖ ^ 2 by
            simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, x₁, x₂]]; ring
  · refine TA.opNorm_le_bound (norm_nonneg _) fun x₁ ↦ ?_
    let x : EuclideanSpace 𝕜 (n₁ ⊕ n₂) := WithLp.toLp 2 (Sum.elim x₁.ofLp 0)
    have hx : ‖x‖ = ‖x₁‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp <| by
      simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, x]
    have hDx : ‖TD x‖ = ‖TA x₁‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp <| by
      simp [EuclideanSpace.norm_sq_eq, hTD, hTA, D, fromBlocks_mulVec, Fintype.sum_sum_type, x,
        show (Sum.elim x₁.ofLp (0 : n₂ → 𝕜)) ∘ Sum.inl = x₁.ofLp from rfl,
        show (Sum.elim x₁.ofLp (0 : n₂ → 𝕜)) ∘ Sum.inr = 0 from rfl]
    exact hDx ▸ (TD.le_opNorm x).trans_eq (by rw [hx])
  · refine TB.opNorm_le_bound (norm_nonneg _) fun x₂ ↦ ?_
    let x : EuclideanSpace 𝕜 (n₁ ⊕ n₂) := WithLp.toLp 2 (Sum.elim 0 x₂.ofLp)
    have hx : ‖x‖ = ‖x₂‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp <| by
      simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, x]
    have hDx : ‖TD x‖ = ‖TB x₂‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp <| by
      simp [EuclideanSpace.norm_sq_eq, hTD, hTB, D, fromBlocks_mulVec, Fintype.sum_sum_type, x,
        show (Sum.elim (0 : n₁ → 𝕜) x₂.ofLp) ∘ Sum.inl = 0 from rfl,
        show (Sum.elim (0 : n₁ → 𝕜) x₂.ofLp) ∘ Sum.inr = x₂.ofLp from rfl]
    exact hDx ▸ (TD.le_opNorm x).trans_eq (by rw [hx])

/-- The Hermitian dilation `fromBlocks 0 A Aᴴ 0` of a rectangular `m × n` matrix `A`, producing a
square `(m ⊕ n) × (m ⊕ n)` Hermitian matrix with the same `ℓ²` operator norm. -/
def hermitianDilation (A : Matrix m n 𝕜) : Matrix (m ⊕ n) (m ⊕ n) 𝕜 :=
  Matrix.fromBlocks 0 A Aᴴ 0

/-- The Hermitian dilation of any matrix is Hermitian. -/
theorem isHermitian_hermitianDilation (A : Matrix m n 𝕜) : A.hermitianDilation.IsHermitian := by
  ext (i | i) (j | j) <;> simp [hermitianDilation]

/-- The Hermitian dilation of the zero matrix is zero. -/
@[simp]
theorem hermitianDilation_zero : (0 : Matrix m n 𝕜).hermitianDilation = 0 := by
  ext (i | i) (j | j) <;> simp [hermitianDilation]

/-- The Hermitian dilation is additive. -/
theorem hermitianDilation_add (A B : Matrix m n 𝕜) :
    (A + B).hermitianDilation = A.hermitianDilation + B.hermitianDilation := by
  simp [hermitianDilation, conjTranspose_add, fromBlocks_add]

/-- The Hermitian dilation commutes with finite sums. -/
theorem hermitianDilation_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix m n 𝕜) :
    (∑ i ∈ s, f i).hermitianDilation = ∑ i ∈ s, (f i).hermitianDilation := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t _ ih => rw [Finset.sum_cons, hermitianDilation_add, ih, Finset.sum_cons]

/-- The square of `A.hermitianDilation` is `fromBlocks (A * Aᴴ) 0 0 (Aᴴ * A)`. -/
theorem hermitianDilation_mul_self [Fintype m] [Fintype n] (A : Matrix m n 𝕜) :
    A.hermitianDilation * A.hermitianDilation = Matrix.fromBlocks (A * Aᴴ) 0 0 (Aᴴ * A) := by
  simp [hermitianDilation, fromBlocks_multiply]

/-- The Hermitian dilation preserves the `ℓ²` operator norm: `‖A.hermitianDilation‖ = ‖A‖`. -/
@[simp]
theorem l2_opNorm_hermitianDilation [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n 𝕜) : ‖A.hermitianDilation‖ = ‖A‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  have hAAh : ‖A * Aᴴ‖ = ‖A‖ ^ 2 := by
    rw [show A * Aᴴ = (Aᴴ)ᴴ * Aᴴ by rw [conjTranspose_conjTranspose],
      l2_opNorm_conjTranspose_mul_self, l2_opNorm_conjTranspose, sq]
  rw [sq, ← l2_opNorm_conjTranspose_mul_self, (isHermitian_hermitianDilation A).eq,
    hermitianDilation_mul_self, l2_opNorm_fromBlocks_zero, hAAh,
    l2_opNorm_conjTranspose_mul_self, ← sq, max_self]

/-- The Hermitian dilation map is continuous with respect to the entrywise/product topology. -/
theorem continuous_hermitianDilation :
    Continuous (hermitianDilation (m := m) (n := n) (𝕜 := 𝕜)) :=
  continuous_matrix fun
    | .inl _, .inl _ | .inr _, .inr _ => continuous_const
    | .inl p₁, .inr q₂ => (continuous_apply q₂).comp (continuous_apply p₁)
    | .inr p₂, .inl q₁ => by
      change Continuous fun A : Matrix m n 𝕜 ↦ star (A q₁ p₂)
      exact continuous_star.comp ((continuous_apply p₂).comp (continuous_apply q₁))

/-- Chiral symmetry of the Hermitian dilation: `-x ∈ spectrum ℝ D → x ∈ spectrum ℝ D`. -/
theorem mem_spectrum_hermitianDilation_of_neg_mem [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {A : Matrix m n 𝕜} {x : ℝ}
    (hx :
      letI : NormedAlgebra ℝ (Matrix (m ⊕ n) (m ⊕ n) 𝕜) := Matrix.l2OpNormedAlgebraReal;
      -x ∈ spectrum ℝ A.hermitianDilation) :
    letI : NormedAlgebra ℝ (Matrix (m ⊕ n) (m ⊕ n) 𝕜) := Matrix.l2OpNormedAlgebraReal
    x ∈ spectrum ℝ A.hermitianDilation := by
  let : NormedAlgebra ℝ (Matrix (m ⊕ n) (m ⊕ n) 𝕜) := Matrix.l2OpNormedAlgebraReal
  let J : Matrix (m ⊕ n) (m ⊕ n) 𝕜 :=
    Matrix.fromBlocks (1 : Matrix m m 𝕜) 0 0 (-1 : Matrix n n 𝕜)
  have hJJ : J * J = 1 := by simp [J, fromBlocks_multiply]
  let u : (Matrix (m ⊕ n) (m ⊕ n) 𝕜)ˣ := ⟨J, J, hJJ, hJJ⟩
  have hconj : J * A.hermitianDilation * J = -A.hermitianDilation := by
    simp [J, hermitianDilation, fromBlocks_multiply, fromBlocks_neg]
  rw [spectrum.mem_iff] at hx ⊢
  refine fun hunit ↦ hx ?_
  have hid : algebraMap ℝ (Matrix (m ⊕ n) (m ⊕ n) 𝕜) (-x) - A.hermitianDilation =
      -(J * (algebraMap ℝ (Matrix (m ⊕ n) (m ⊕ n) 𝕜) x - A.hermitianDilation) * J) := by
    rw [map_neg, Matrix.mul_sub, Matrix.sub_mul, hconj, Algebra.algebraMap_eq_smul_one,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hJJ]; abel
  exact hid ▸ IsUnit.neg ((u.isUnit.mul hunit).mul u.isUnit)

section SummandMGF

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [Fintype n] [DecidableEq n]

private def entryCLM' (i j : n) :
    letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
    Matrix n n 𝕜 →L[ℝ] 𝕜 :=
  letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  { toLinearMap := { toFun A := A i j, map_add' _ _ := rfl, map_smul' _ _ := rfl }
    cont := (continuous_apply j).comp (continuous_apply i) }

private theorem cfc_exp_smul_eq {A : Matrix n n 𝕜} (hA : A.IsHermitian) (θ : ℝ) :
    letI : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
    cfc (fun x : ℝ ↦ Real.exp (θ * x)) A = NormedSpace.exp (θ • A) := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  rw [← CFC.real_exp_eq_normedSpace_exp (hA.smul (IsSelfAdjoint.all θ)).isSelfAdjoint,
    ← cfc_smul_id (R := ℝ) θ A hA.isSelfAdjoint,
    ← cfc_comp' Real.exp (θ • ·) A Real.continuous_exp.continuousOn
      (continuous_const_smul θ).continuousOn hA.isSelfAdjoint]
  rfl

/-- **Summand MGF Loewner bound for Matrix Bernstein.** If `Z` is an a.e. Hermitian random matrix
with entrywise expectation `0` and `‖Z‖ ≤ L` a.e., then for `0 ≤ θ` with `θ * L < 3` and
`g = θ ^ 2 / (2 * (1 - θ * L / 3))`, `exp (θ • Z)` and `Z * Z` are Bochner integrable, the matrix
second moment `V = E[Z²]` is positive semidefinite, and `E[exp(θ • Z)] ≤ exp(g • V)`. -/
theorem integrable_and_posSemidef_exp_smul_integral_sub [IsProbabilityMeasure μ]
    {Z : Ω → Matrix n n 𝕜} {L θ : ℝ} (hZ_meas : AEMeasurable Z μ)
    (hZ_herm : ∀ᵐ ω ∂μ, (Z ω).IsHermitian) (hZ_mean : ∀ p q, ∫ ω, Z ω p q ∂μ = 0)
    (hZ_norm : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ L) (hθ0 : 0 ≤ θ) (hθL : θ * L < 3) :
    let g := θ ^ 2 / (2 * (1 - θ * L / 3))
    let V := Matrix.of fun p q ↦ ∫ ω, (Z ω * Z ω) p q ∂μ
    Integrable (fun ω ↦ NormedSpace.exp (θ • Z ω)) μ ∧ Integrable (fun ω ↦ Z ω * Z ω) μ ∧
      V.PosSemidef ∧
      (NormedSpace.exp (g • V) -
        Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (θ • Z ω) p q ∂μ).PosSemidef := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  obtain ⟨ω₀, hω₀⟩ := hZ_norm.exists
  have hL : 0 ≤ L := (norm_nonneg _).trans hω₀
  set g : ℝ := θ ^ 2 / (2 * (1 - θ * L / 3))
  set V : Matrix n n 𝕜 := Matrix.of fun p q ↦ ∫ ω, (Z ω * Z ω) p q ∂μ
  have hZ_int : Integrable Z μ := Integrable.of_bound hZ_meas.aestronglyMeasurable L hZ_norm
  have hZ2_int : Integrable (fun ω ↦ Z ω * Z ω) μ :=
    Integrable.of_bound (hZ_meas.aestronglyMeasurable.mul hZ_meas.aestronglyMeasurable) (L * L)
      (hZ_norm.mono fun _ hω ↦ (norm_mul_le _ _).trans (mul_le_mul hω hω (norm_nonneg _) hL))
  have hexp_int : Integrable (fun ω ↦ NormedSpace.exp (θ • Z ω)) μ := by
    refine Integrable.of_bound ((NormedSpace.exp_continuous.comp
      (continuous_const_smul θ)).comp_aestronglyMeasurable hZ_meas.aestronglyMeasurable)
      (Real.exp (θ * L) + ‖(1 : Matrix n n 𝕜)‖) (hZ_norm.mono fun ω hω ↦ ?_)
    have hexp_le : Real.exp ‖θ • Z ω‖ ≤ Real.exp (θ * L) := Real.exp_le_exp.mpr <| by
      rw [norm_smul, Real.norm_of_nonneg hθ0]; exact mul_le_mul_of_nonneg_left hω hθ0
    linarith [NormedSpace.norm_exp_sub_one_le (θ • Z ω),
      norm_le_norm_sub_add (NormedSpace.exp (θ • Z ω)) 1]
  have hV_psd : V.PosSemidef :=
    TauCeti.posSemidef_integral (hZ_herm.mono fun ω hω ↦ by
      simpa [hω.eq] using Matrix.posSemidef_conjTranspose_mul_self (Z ω))
      fun p q ↦ (entryCLM' p q).integrable_comp hZ2_int
  let W : Ω → Matrix n n 𝕜 := fun ω ↦ 1 + θ • Z ω + g • (Z ω * Z ω) - NormedSpace.exp (θ • Z ω)
  have hW_psd : ∀ᵐ ω ∂μ, (W ω).PosSemidef := by
    filter_upwards [hZ_herm, hZ_norm] with ω hω_herm hω_norm
    have ha : IsSelfAdjoint (Z ω) := hω_herm.isSelfAdjoint
    have hcfc_le : cfc (fun x : ℝ ↦ Real.exp (θ * x)) (Z ω) ≤
        cfc (fun x : ℝ ↦ (1 + θ * x) + g * x ^ 2) (Z ω) := cfc_mono fun x hx ↦ by
      obtain ⟨k, rfl⟩ := hω_herm.spectrum_real_eq_range_eigenvalues ▸ hx
      have hθxL : θ * hω_herm.eigenvalues k ≤ θ * L := mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans ((hω_herm.abs_eigenvalues_le_l2_opNorm k).trans hω_norm)) hθ0
      have hquad := Real.exp_le_one_add_add_sq_div_of_le hθxL (mul_nonneg hθ0 hL) hθL
      have hring : (θ * hω_herm.eigenvalues k) ^ 2 / (2 * (1 - θ * L / 3)) =
          g * hω_herm.eigenvalues k ^ 2 := by dsimp only [g]; ring
      linarith
    rwa [cfc_exp_smul_eq hω_herm θ, cfc_add (Z ω) (fun x : ℝ ↦ 1 + θ * x) (fun x : ℝ ↦ g * x ^ 2)
        (continuousOn_const.add (continuous_const.mul continuous_id).continuousOn)
        (continuous_const.mul (continuous_pow 2)).continuousOn,
      cfc_const_add (1 : ℝ) (fun x : ℝ ↦ θ * x) (Z ω)
        (continuous_const.mul continuous_id).continuousOn ha,
      Algebra.algebraMap_eq_smul_one, one_smul, cfc_const_mul_id θ (Z ω) ha,
      cfc_const_mul g (· ^ 2 : ℝ → ℝ) (Z ω) (continuous_pow 2).continuousOn,
      cfc_pow_id (Z ω) 2 ha, sq, Matrix.le_iff] at hcfc_le
  have hW_int : Integrable W μ :=
    (((integrable_const 1).add (hZ_int.smul θ)).add (hZ2_int.smul g)).sub hexp_int
  have hEW_psd : (Matrix.of fun p q ↦ ∫ ω, W ω p q ∂μ).PosSemidef :=
    TauCeti.posSemidef_integral hW_psd fun p q ↦ (entryCLM' p q).integrable_comp hW_int
  have hEW_eq : (Matrix.of fun p q ↦ ∫ ω, W ω p q ∂μ) =
      1 + g • V - Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (θ • Z ω) p q ∂μ := by
    have hEZ : ∫ ω, Z ω ∂μ = 0 := Matrix.ext fun p q ↦
      ((entryCLM' (𝕜 := 𝕜) p q).integral_comp_comm hZ_int).symm.trans (hZ_mean p q)
    have hEZ2 : ∫ ω, (Z ω * Z ω) ∂μ = V := Matrix.ext fun p q ↦
      ((entryCLM' (𝕜 := 𝕜) p q).integral_comp_comm hZ2_int).symm
    have hEexp : ∫ ω, NormedSpace.exp (θ • Z ω) ∂μ =
        Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (θ • Z ω) p q ∂μ := Matrix.ext fun p q ↦
      ((entryCLM' (𝕜 := 𝕜) p q).integral_comp_comm hexp_int).symm
    have h1 := integral_sub (f := fun ω ↦ (1 : Matrix n n 𝕜) + θ • Z ω + g • (Z ω * Z ω))
      (g := fun ω ↦ NormedSpace.exp (θ • Z ω))
      (((integrable_const 1).add (hZ_int.smul θ)).add (hZ2_int.smul g)) hexp_int
    have h2 := integral_add (f := fun ω ↦ (1 : Matrix n n 𝕜) + θ • Z ω)
      (g := fun ω ↦ g • (Z ω * Z ω)) ((integrable_const 1).add (hZ_int.smul θ)) (hZ2_int.smul g)
    have h3 := integral_add (f := fun _ ↦ (1 : Matrix n n 𝕜)) (g := fun ω ↦ θ • Z ω)
      (integrable_const 1) (hZ_int.smul θ)
    have hboch : ∫ ω, W ω ∂μ =
        1 + g • V - Matrix.of fun p q ↦ ∫ ω, NormedSpace.exp (θ • Z ω) p q ∂μ := by
      dsimp only [W]
      rw [h1, h2, h3, integral_const, probReal_univ, one_smul, integral_smul, hEZ, smul_zero,
        add_zero, integral_smul, hEZ2, hEexp]
    ext p q; rw [Matrix.of_apply, ← hboch]
    exact (entryCLM' (𝕜 := 𝕜) p q).integral_comp_comm hW_int
  rw [hEW_eq] at hEW_psd
  have hgV_sa : IsSelfAdjoint (g • V) := (hV_psd.1.smul (IsSelfAdjoint.all g)).isSelfAdjoint
  have hexp_ge_lin : (NormedSpace.exp (g • V) - (1 + g • V)).PosSemidef := by
    have hcfc_le : cfc (fun x : ℝ ↦ 1 + x) (g • V) ≤ cfc Real.exp (g • V) :=
      cfc_mono fun x _ ↦ by linarith [Real.add_one_le_exp x]
    rwa [cfc_const_add (1 : ℝ) (fun x : ℝ ↦ x) (g • V) continuousOn_id hgV_sa,
      Algebra.algebraMap_eq_smul_one, one_smul, cfc_id' ℝ (g • V) hgV_sa,
      CFC.real_exp_eq_normedSpace_exp hgV_sa, Matrix.le_iff] at hcfc_le
  exact ⟨hexp_int, hZ2_int, hV_psd,
    by simpa only [sub_add_sub_cancel] using hexp_ge_lin.add hEW_psd⟩

end SummandMGF

end Matrix

namespace ProbabilityTheory.iIndepFun

variable {ι Ω m n 𝕜 : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [RCLike 𝕜]

private theorem not_exists_le_eigenvalues_zero {t : ℝ} (ht : 0 < t) :
    ¬ ∃ k : n, ∃ hS : (0 : Matrix n n 𝕜).IsHermitian, t ≤ hS.eigenvalues k := fun ⟨k, hS, _⟩ ↦ by
  have h := hS.abs_eigenvalues_le_l2_opNorm k; rw [norm_zero] at h
  linarith [le_abs_self (hS.eigenvalues k)]

omit [DecidableEq n] in
private theorem re_mul_self_diag_eq_sum_norm_sq {A : Matrix n n 𝕜} (hA : A.IsHermitian) (p : n) :
    RCLike.re ((A * A) p p) = ∑ q : n, ‖A p q‖ ^ 2 := by
  rw [Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [show A q p = star (A p q) by simpa [Matrix.conjTranspose_apply] using (hA.apply q p).symm,
    RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re]

private theorem ae_eq_zero_of_integral_mul_self_eq_zero
    {Z : Ω → Matrix n n 𝕜} (hZ_herm : ∀ᵐ ω ∂μ, (Z ω).IsHermitian)
    (hZ2_int : Integrable (fun ω ↦ Z ω * Z ω) μ)
    (hV_diag : ∀ p : n, RCLike.re (∫ ω, (Z ω * Z ω) p p ∂μ) = 0) : Z =ᵐ[μ] 0 := by
  classical
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have hentry_zero (p q : n) : ∀ᵐ ω ∂μ, Z ω p q = 0 := by
    have hdiag_int := (Matrix.entryCLM' p p).integrable_comp hZ2_int
    let f : Ω → ℝ := fun ω ↦ RCLike.re ((Z ω * Z ω) p p)
    have hf_nonneg : 0 ≤ᵐ[μ] f := hZ_herm.mono fun ω hω ↦ by
      simpa only [f, Pi.zero_apply, re_mul_self_diag_eq_sum_norm_sq hω p] using
        Finset.sum_nonneg fun r _ ↦ sq_nonneg ‖Z ω p r‖
    have hf_ae_zero : f =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hf_nonneg (RCLike.reCLM.integrable_comp hdiag_int)).mp
        ((RCLike.reCLM.integral_comp_comm hdiag_int).trans (hV_diag p))
    filter_upwards [hZ_herm, hf_ae_zero] with ω hω hzero
    rw [Pi.zero_apply, show f ω = RCLike.re ((Z ω * Z ω) p p) from rfl,
      re_mul_self_diag_eq_sum_norm_sq hω p] at hzero
    exact norm_eq_zero.mp <| sq_eq_zero_iff.mp <|
      (Finset.sum_eq_zero_iff_of_nonneg fun r _ ↦ sq_nonneg _).mp hzero q (Finset.mem_univ q)
  exact (Filter.eventually_all.mpr fun p ↦ Filter.eventually_all.mpr fun q ↦ hentry_zero p q).mono
    fun ω hω ↦ Matrix.ext fun p q ↦ hω p q

/-- **Upper-tail Hermitian matrix Bernstein inequality** (Tropp 2012, Theorem 1.4): for independent
a.e.-Hermitian centered `X i` (`i ∈ s`) with `‖X i‖ ≤ L` a.e. and `v = ‖∑ i ∈ s, E[X i²]‖`,
`P(∃ k, t ≤ λ_k(∑ i ∈ s, X i)) ≤ card n * exp(-(t ^ 2 / 2) / (v + L * t / 3))` for `t > 0`. -/
theorem measureReal_exists_le_eigenvalues_sum_le_of_norm_le {X : ι → Ω → Matrix n n 𝕜}
    (h_indep : iIndepFun X μ) {s : Finset ι} {L t : ℝ} (hX_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX_herm : ∀ i ∈ s, ∀ᵐ ω ∂μ, (X i ω).IsHermitian)
    (hX_mean : ∀ i ∈ s, ∀ p q, ∫ ω, X i ω p q ∂μ = 0)
    (hX_norm : ∀ i ∈ s, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ L) (ht : 0 < t) :
    let v := ‖∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, (X i ω * X i ω) p q ∂μ‖
    μ.real {ω | ∃ k : n, ∃ hS : (∑ i ∈ s, X i ω).IsHermitian, t ≤ hS.eigenvalues k} ≤
      Fintype.card n * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  set V_i : ι → Matrix n n 𝕜 := fun i ↦ Matrix.of fun p q ↦ ∫ ω, (X i ω * X i ω) p q ∂μ
  set V : Matrix n n 𝕜 := ∑ i ∈ s, V_i i
  set v : ℝ := ‖V‖
  by_cases hs : s.Nonempty
  · by_cases hv : v = 0
    · have hV_zero : V = 0 := norm_eq_zero.mp hv
      have h0_step (i : ι) (hi : i ∈ s) :=
        Matrix.integrable_and_posSemidef_exp_smul_integral_sub (θ := 0) (hX_meas i hi)
          (hX_herm i hi) (hX_mean i hi) (hX_norm i hi) le_rfl (by norm_num)
      have hX_ae_zero (i : ι) (hi : i ∈ s) : X i =ᵐ[μ] 0 := by
        refine ae_eq_zero_of_integral_mul_self_eq_zero (hX_herm i hi) (h0_step i hi).2.1 fun p ↦ ?_
        have hdiag_nonneg (j : ι) (hj : j ∈ s) : 0 ≤ RCLike.re (V_i j p p) := by
          simpa [V_i, dotProduct, Matrix.mulVec, Pi.single_apply] using
            (RCLike.nonneg_iff.mp
              ((h0_step j hj).2.2.1.dotProduct_mulVec_nonneg (Pi.single p 1))).1
        have hsum_diag : ∑ j ∈ s, RCLike.re (V_i j p p) = 0 := by
          simpa [V, Matrix.sum_apply] using congrArg RCLike.re (congrFun₂ hV_zero p p)
        exact (Finset.sum_eq_zero_iff_of_nonneg hdiag_nonneg).mp hsum_diag i hi
      have hsum_ae_zero : ∀ᵐ ω ∂μ, ∑ i ∈ s, X i ω = 0 :=
        ((Filter.eventually_all_finset s).2 hX_ae_zero).mono fun _ ↦ Finset.sum_eq_zero
      have hev0 : μ.real {ω | ∃ k : n, ∃ hS : (∑ i ∈ s, X i ω).IsHermitian,
          t ≤ hS.eigenvalues k} = 0 := by
        rw [measureReal_eq_zero_iff]
        refine measure_mono_null (fun ω hω ↦ ?_) (ae_iff.mp hsum_ae_zero)
        intro hsum0; rw [Set.mem_ofPred, hsum0] at hω; exact not_exists_le_eigenvalues_zero ht hω
      rw [hev0]; positivity
    · have hv_pos : 0 < v := lt_of_le_of_ne (norm_nonneg V) (Ne.symm hv)
      have hL : 0 ≤ L := (norm_nonneg _).trans (hX_norm hs.choose hs.choose_spec).exists.choose_spec
      have hdenom_pos : 0 < v + L * t / 3 := by positivity
      let θ : ℝ := t / (v + L * t / 3)
      have hθ0 : 0 ≤ θ := by positivity
      have hθL : θ * L < 3 := by
        dsimp only [θ]; rw [div_mul_eq_mul_div, div_lt_iff₀ hdenom_pos]; linarith
      let g : ℝ := θ ^ 2 / (2 * (1 - θ * L / 3))
      have hg0 : 0 ≤ g := div_nonneg (sq_nonneg θ) (by linarith)
      have hstep (i : ι) (hi : i ∈ s) :=
        Matrix.integrable_and_posSemidef_exp_smul_integral_sub (hX_meas i hi) (hX_herm i hi)
          (hX_mean i hi) (hX_norm i hi) hθ0 hθL
      have hVi_psd (i : ι) (hi : i ∈ s) : (V_i i).PosSemidef := (hstep i hi).2.2.1
      have hlap := h_indep.measureReal_exists_le_eigenvalues_sum_le (t := t)
        (M := fun i ↦ g • V_i i) hX_meas hX_herm (fun i hi ↦ (hstep i hi).1)
        (fun i hi ↦ (hVi_psd i hi).1.smul (IsSelfAdjoint.all g))
        (fun i hi ↦ (hstep i hi).2.2.2) hθ0
      have hV_psd : V.PosSemidef :=
        Finset.sum_induction _ Matrix.PosSemidef (fun _ _ h₁ h₂ ↦ h₁.add h₂)
          Matrix.PosSemidef.zero hVi_psd
      have hV_le_norm : ((g * v) • (1 : Matrix n n 𝕜) - g • V).PosSemidef := by
        have hcfc_le : cfc (fun x : ℝ ↦ x) V ≤ cfc (fun _ : ℝ ↦ v) V := cfc_mono fun x hx ↦ by
          obtain ⟨k, rfl⟩ := hV_psd.1.spectrum_real_eq_range_eigenvalues ▸ hx
          exact (le_abs_self _).trans (hV_psd.1.abs_eigenvalues_le_l2_opNorm k)
        rw [cfc_id' ℝ V hV_psd.1.isSelfAdjoint, cfc_const v V hV_psd.1.isSelfAdjoint,
          Algebra.algebraMap_eq_smul_one, Matrix.le_iff] at hcfc_le
        simpa [smul_sub, smul_smul] using hcfc_le.smul hg0
      have htr_mono : RCLike.re (NormedSpace.exp (∑ i ∈ s, g • V_i i)).trace ≤
          Fintype.card n * Real.exp (g * v) := by
        rw [← Finset.smul_sum]
        refine ((hV_psd.1.smul (IsSelfAdjoint.all g)).re_trace_exp_mono
          (Matrix.isHermitian_one.smul (IsSelfAdjoint.all (g * v))) hV_le_norm).trans_eq ?_
        rw [← Algebra.algebraMap_eq_smul_one, ← NormedSpace.algebraMap_exp_comm,
          ← congr_fun Real.exp_eq_exp_ℝ (g * v), Algebra.algebraMap_eq_smul_one,
          Matrix.trace_smul, Matrix.trace_one, RCLike.smul_re, RCLike.natCast_re, mul_comm]
      have hexp_alg : -θ * t + g * v = -(t ^ 2 / 2) / (v + L * t / 3) := by
        have hsub_eq : 1 - θ * L / 3 = v / (v + L * t / 3) := by dsimp only [θ]; field_simp; ring
        dsimp only [g]; rw [hsub_eq]; dsimp only [θ]; field_simp; ring
      exact hlap.trans <| (mul_le_mul_of_nonneg_left htr_mono (Real.exp_pos _).le).trans_eq <| by
        rw [← hexp_alg, Real.exp_add]; ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    have hempty : {ω : Ω | ∃ k : n,
        ∃ hS : (∑ i ∈ (∅ : Finset ι), X i ω).IsHermitian, t ≤ hS.eigenvalues k} = ∅ :=
      Set.eq_empty_of_forall_notMem fun _ h ↦
        not_exists_le_eigenvalues_zero ht (by simpa only [Set.mem_ofPred, Finset.sum_empty] using h)
    rw [hempty, measureReal_empty]; positivity

/-- **Two-sided Hermitian matrix Bernstein inequality** over a `Finset` (Tropp 2012, Theorem 1.4):
for independent a.e.-Hermitian mean-zero `X i` (`i ∈ s`) with `‖X i‖ ≤ L` a.e. and `t > 0`,
`μ.real {ω | t ≤ ‖∑ i ∈ s, X i ω‖} ≤ 2 * card n * exp(-(t ^ 2 / 2) / (v + L * t / 3))`. -/
theorem measureReal_norm_sum_ge_le {X : ι → Ω → Matrix n n 𝕜}
    (h_indep : iIndepFun X μ) {s : Finset ι} {L t : ℝ} (hX_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX_herm : ∀ i ∈ s, ∀ᵐ ω ∂μ, (X i ω).IsHermitian)
    (hX_mean : ∀ i ∈ s, ∀ p q, ∫ ω, X i ω p q ∂μ = 0)
    (hX_norm : ∀ i ∈ s, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ L) (ht : 0 < t) :
    let v := ‖∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, (X i ω * X i ω) p q ∂μ‖
    μ.real {ω | t ≤ ‖∑ i ∈ s, X i ω‖} ≤
      2 * Fintype.card n * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  by_cases hn : Nonempty n
  · let Epos := {ω : Ω | ∃ k : n, ∃ hS : (∑ i ∈ s, X i ω).IsHermitian, t ≤ hS.eigenvalues k}
    let Eneg := {ω : Ω | ∃ k : n, ∃ hS : (∑ i ∈ s, -X i ω).IsHermitian, t ≤ hS.eigenvalues k}
    let H := {ω : Ω | ∀ i ∈ s, (X i ω).IsHermitian}
    have hHc_null : μ.real Hᶜ = 0 := by
      rw [measureReal_eq_zero_iff]
      exact ae_iff.mp ((Filter.eventually_all_finset s).2 hX_herm)
    have hsub : {ω : Ω | t ≤ ‖∑ i ∈ s, X i ω‖} ⊆ (Epos ∪ Eneg) ∪ Hᶜ := fun ω hω ↦ by
      by_cases hωH : ω ∈ H
      · left
        have hS : (∑ i ∈ s, X i ω).IsHermitian :=
          Finset.sum_induction _ Matrix.IsHermitian (fun _ _ h₁ h₂ ↦ h₁.add h₂)
            Matrix.isHermitian_zero hωH
        rcases hS.norm_or_neg_norm_mem_spectrum with hmem | hmem
        · obtain ⟨k, hk⟩ := hS.spectrum_real_eq_range_eigenvalues ▸ hmem
          exact Or.inl ⟨k, hS, hk ▸ hω⟩
        · have hS_neg : (∑ i ∈ s, -X i ω).IsHermitian := by
            rw [Finset.sum_neg_distrib]; exact hS.neg
          have hmem_neg : ‖∑ i ∈ s, X i ω‖ ∈ spectrum ℝ (∑ i ∈ s, -X i ω) := by
            rw [Finset.sum_neg_distrib, spectrum.mem_iff]; rw [spectrum.mem_iff] at hmem
            refine fun hunit ↦ hmem ?_
            rwa [← IsUnit.neg_iff, show -(algebraMap ℝ _ (-‖∑ i ∈ s, X i ω‖) - ∑ i ∈ s, X i ω) =
              algebraMap ℝ _ ‖∑ i ∈ s, X i ω‖ - -(∑ i ∈ s, X i ω) by rw [map_neg]; abel]
          obtain ⟨k, hk⟩ := hS_neg.spectrum_real_eq_range_eigenvalues ▸ hmem_neg
          exact Or.inr ⟨k, hS_neg, hk ▸ hω⟩
      · exact Or.inr hωH
    have hpos := h_indep.measureReal_exists_le_eigenvalues_sum_le_of_norm_le
      hX_meas hX_herm hX_mean hX_norm ht
    have hneg := (h_indep.comp (fun _ M ↦ -M) fun _ ↦ measurable_neg)
      |>.measureReal_exists_le_eigenvalues_sum_le_of_norm_le (L := L) (s := s)
      (fun i hi ↦ (hX_meas i hi).neg) (fun i hi ↦ (hX_herm i hi).mono fun _ h ↦ h.neg)
      (fun i hi p q ↦ by simp [integral_neg, hX_mean i hi p q])
      (fun i hi ↦ (hX_norm i hi).mono fun _ h ↦ by simpa using h) ht
    simp only [Function.comp_apply, neg_mul_neg] at hneg
    calc μ.real {ω | t ≤ ‖∑ i ∈ s, X i ω‖}
        ≤ μ.real (Epos ∪ Eneg) + μ.real Hᶜ :=
          (measureReal_mono hsub).trans (measureReal_union_le _ _)
      _ ≤ μ.real Epos + μ.real Eneg := by rw [hHc_null, add_zero]; exact measureReal_union_le _ _
      _ ≤ 2 * Fintype.card n * Real.exp (-(t ^ 2 / 2) /
            (‖∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, (X i ω * X i ω) p q ∂μ‖ + L * t / 3)) := by
          linarith
  · have : IsEmpty n := not_nonempty_iff.mp hn
    rw [show {ω : Ω | t ≤ ‖∑ i ∈ s, X i ω‖} = ∅ by
      ext ω; simp [Subsingleton.elim (∑ i ∈ s, X i ω) 0, ht], measureReal_empty]; positivity

/-- **Sharp rectangular matrix Bernstein inequality** over a `Finset` (Tropp 2012, Theorem 1.6):
for independent mean-zero `m × n` matrices `Y i` (`i ∈ s`) with `‖Y i‖ ≤ L` a.e. and `t > 0`,
`μ.real {ω | t ≤ ‖∑ i ∈ s, Y i ω‖} ≤ (card m + card n) * exp(-(t ^ 2 / 2) / (v + L * t / 3))`. -/
theorem measureReal_norm_sum_ge_le_rectangular {Y : ι → Ω → Matrix m n 𝕜}
    (h_indep : iIndepFun Y μ) {s : Finset ι} {L t : ℝ} (hY_meas : ∀ i ∈ s, AEMeasurable (Y i) μ)
    (hY_mean : ∀ i ∈ s, ∀ p q, ∫ ω, Y i ω p q ∂μ = 0)
    (hY_norm : ∀ i ∈ s, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ L) (ht : 0 < t) :
    let v := max ‖∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, (Y i ω * (Y i ω)ᴴ) p q ∂μ‖
      ‖∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, ((Y i ω)ᴴ * Y i ω) p q ∂μ‖
    μ.real {ω | t ≤ ‖∑ i ∈ s, Y i ω‖} ≤
      (Fintype.card m + Fintype.card n) * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  let : NormedAlgebra ℝ (Matrix (m ⊕ n) (m ⊕ n) 𝕜) := Matrix.l2OpNormedAlgebraReal
  by_cases hmn : Nonempty (m ⊕ n)
  · let Z : ι → Ω → Matrix (m ⊕ n) (m ⊕ n) 𝕜 := fun i ω ↦ (Y i ω).hermitianDilation
    have hZ_indep : iIndepFun Z μ :=
      h_indep.comp (fun _ A ↦ A.hermitianDilation)
        fun _ ↦ Matrix.continuous_hermitianDilation.measurable
    have hZ_mean (i : ι) (hi : i ∈ s) (p q : m ⊕ n) : ∫ ω, Z i ω p q ∂μ = 0 := by
      cases p <;> cases q <;>
        simp [Z, Matrix.hermitianDilation, RCLike.star_def, integral_conj, hY_mean i hi]
    have hsub : {ω : Ω | t ≤ ‖∑ i ∈ s, Y i ω‖} ⊆
        {ω : Ω | ∃ k : m ⊕ n, ∃ hS : (∑ i ∈ s, Z i ω).IsHermitian, t ≤ hS.eigenvalues k} := by
      intro ω hω
      set A := ∑ i ∈ s, Y i ω
      have hsumZ : ∑ i ∈ s, Z i ω = A.hermitianDilation :=
        (Matrix.hermitianDilation_sum s fun i ↦ Y i ω).symm
      have hS : (∑ i ∈ s, Z i ω).IsHermitian := hsumZ ▸ Matrix.isHermitian_hermitianDilation A
      have hmem : ‖A.hermitianDilation‖ ∈ spectrum ℝ A.hermitianDilation :=
        (Matrix.isHermitian_hermitianDilation A).norm_or_neg_norm_mem_spectrum.elim id
          Matrix.mem_spectrum_hermitianDilation_of_neg_mem
      rw [← hsumZ, hS.spectrum_real_eq_range_eigenvalues] at hmem
      obtain ⟨k, hk⟩ := hmem
      exact ⟨k, hS, by rwa [hk, hsumZ, Matrix.l2_opNorm_hermitianDilation]⟩
    have hupper := hZ_indep.measureReal_exists_le_eigenvalues_sum_le_of_norm_le
      (fun i hi ↦ Matrix.continuous_hermitianDilation.measurable.comp_aemeasurable (hY_meas i hi))
      (fun i _ ↦ Eventually.of_forall fun ω ↦ Matrix.isHermitian_hermitianDilation (Y i ω))
      hZ_mean (fun i hi ↦ (hY_norm i hi).mono fun ω hω ↦ by simpa [Z] using hω) ht
    have hv_eq : ‖∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, (Z i ω * Z i ω) p q ∂μ‖ =
        max ‖∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, (Y i ω * (Y i ω)ᴴ) p q ∂μ‖
            ‖∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, ((Y i ω)ᴴ * Y i ω) p q ∂μ‖ := by
      rw [show (∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, (Z i ω * Z i ω) p q ∂μ) = Matrix.fromBlocks
          (∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, (Y i ω * (Y i ω)ᴴ) p q ∂μ) 0 0
          (∑ i ∈ s, Matrix.of fun p q ↦ ∫ ω, ((Y i ω)ᴴ * Y i ω) p q ∂μ) by
        ext (p | p) (q | q) <;> simp [Z, Matrix.hermitianDilation_mul_self, Matrix.sum_apply],
        Matrix.l2_opNorm_fromBlocks_zero]
    rw [hv_eq, Fintype.card_sum, Nat.cast_add] at hupper
    exact (measureReal_mono hsub).trans hupper
  · have : IsEmpty (m ⊕ n) := not_nonempty_iff.mp hmn
    have : IsEmpty m := ⟨fun x ↦ IsEmpty.false (Sum.inl x : m ⊕ n)⟩
    rw [show {ω : Ω | t ≤ ‖∑ i ∈ s, Y i ω‖} = ∅ by
      ext ω; simp [Subsingleton.elim (∑ i ∈ s, Y i ω) 0, ht], measureReal_empty]; positivity

end ProbabilityTheory.iIndepFun

namespace TauCeti

variable {ι Ω m n 𝕜 : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [Fintype ι] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- **Hermitian matrix Bernstein inequality** (Tropp 2012, Theorem 1.4) over `[Fintype ι]`:
`μ.real {ω | t ≤ ‖∑ i, X i ω‖} ≤ 2 * card n * exp(-(t ^ 2 / 2) / (v + L * t / 3))` for `t > 0`. -/
theorem matrix_bernstein {X : ι → Ω → Matrix n n 𝕜} (h_indep : iIndepFun X μ)
    (hX_meas : ∀ i, AEMeasurable (X i) μ) (hX_herm : ∀ i, ∀ᵐ ω ∂μ, (X i ω).IsHermitian)
    (hX_mean : ∀ i p q, ∫ ω, X i ω p q ∂μ = 0) {L : ℝ} (hX_norm : ∀ i, ∀ᵐ ω ∂μ, ‖X i ω‖ ≤ L)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ ‖∑ i, X i ω‖} ≤ 2 * Fintype.card n * Real.exp (-(t ^ 2 / 2) /
      (‖Matrix.of fun p q ↦ ∑ i, ∫ ω, (X i ω * X i ω) p q ∂μ‖ + L * t / 3)) := by
  have h := h_indep.measureReal_norm_sum_ge_le (s := Finset.univ)
    (fun i _ ↦ hX_meas i) (fun i _ ↦ hX_herm i) (fun i _ ↦ hX_mean i) (fun i _ ↦ hX_norm i) ht
  rwa [show (∑ i : ι, Matrix.of fun p q ↦ ∫ ω, (X i ω * X i ω) p q ∂μ) =
    Matrix.of fun p q ↦ ∑ i : ι, ∫ ω, (X i ω * X i ω) p q ∂μ by ext; simp [Matrix.sum_apply]] at h

/-- **Sharp rectangular matrix Bernstein inequality** (Tropp 2012, Theorem 1.6) over `[Fintype ι]`:
`μ.real {ω | t ≤ ‖∑ i, Y i ω‖} ≤ (card m + card n) * exp(-(t ^ 2 / 2) / (v + L * t / 3))`. -/
theorem matrix_bernstein_rectangular {Y : ι → Ω → Matrix m n 𝕜} (h_indep : iIndepFun Y μ)
    (hY_meas : ∀ i, AEMeasurable (Y i) μ) (hY_mean : ∀ i p q, ∫ ω, Y i ω p q ∂μ = 0)
    {L : ℝ} (hY_norm : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ L) {t : ℝ} (ht : 0 < t) :
    let v := max ‖Matrix.of fun p q ↦ ∑ i, ∫ ω, (Y i ω * (Y i ω)ᴴ) p q ∂μ‖
      ‖Matrix.of fun p q ↦ ∑ i, ∫ ω, ((Y i ω)ᴴ * Y i ω) p q ∂μ‖
    μ.real {ω | t ≤ ‖∑ i, Y i ω‖} ≤
      (Fintype.card m + Fintype.card n) * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := by
  have h := h_indep.measureReal_norm_sum_ge_le_rectangular (s := Finset.univ)
    (fun i _ ↦ hY_meas i) (fun i _ ↦ hY_mean i) (fun i _ ↦ hY_norm i) ht
  rwa [show (∑ i : ι, Matrix.of fun p q ↦ ∫ ω, (Y i ω * (Y i ω)ᴴ) p q ∂μ) =
      Matrix.of fun p q ↦ ∑ i : ι, ∫ ω, (Y i ω * (Y i ω)ᴴ) p q ∂μ by ext; simp [Matrix.sum_apply],
    show (∑ i : ι, Matrix.of fun p q ↦ ∫ ω, ((Y i ω)ᴴ * Y i ω) p q ∂μ) =
      Matrix.of fun p q ↦ ∑ i : ι, ∫ ω, ((Y i ω)ᴴ * Y i ω) p q ∂μ by ext; simp [Matrix.sum_apply]]
    at h

end TauCeti

end
