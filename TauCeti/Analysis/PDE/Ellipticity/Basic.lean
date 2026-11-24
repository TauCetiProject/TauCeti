/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.Calculus.Gradient
public import TauCeti.Analysis.Matrix.Contraction
public import TauCeti.LinearAlgebra.Matrix.ToQuadraticForm
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.MetricSpace.Lipschitz
import TauCeti.Analysis.Matrix.PosSemidef.Determinant
import TauCeti.Analysis.Normed.Field.Lipschitz
import TauCeti.Topology.MetricSpace.Holder

/-!
# Uniform ellipticity for divergence-form PDE coefficients

This file records the explicit-constant matrix inequalities used for uniformly elliptic
divergence-form operators. For a coefficient field
`a : X → Matrix n n ℝ` on a domain `Ω : Set X`, the predicate
`UniformlyEllipticOn Ω a λ Λ` means

`λ ‖ξ‖² ≤ ξᵀ a(x) ξ` and `|ηᵀ a(x) ξ| ≤ Λ ‖η‖ ‖ξ‖`

for every `x ∈ Ω` and all vectors `η`, `ξ`, together with the quantitative side conditions
`0 < λ` and `λ ≤ Λ`. The lower bound is the coercivity hypothesis; the bilinear upper bound
controls nonsymmetric coefficient fields for weak-form boundedness.

This is the coefficient hypothesis of the energy bilinear form and Lax--Milgram arguments:
constants are parameters, not hidden existential data.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn`: uniform lower and upper ellipticity bounds on a set.
* `TauCeti.PDE.uniformlyEllipticOn_const_one`: the identity matrix is uniformly elliptic.
* `TauCeti.PDE.le_of_mul_norm_sq_le_toQuadraticForm'_le`: two-sided bounds
  `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` force `λ ≤ Λ`.
* `TauCeti.PDE.UniformlyEllipticOn.mono_constants`: weakening constants preserves the
  predicate.
* `TauCeti.PDE.UniformlyEllipticOn.mono_set`: restriction to a smaller domain preserves the
  predicate.
* `TauCeti.PDE.UniformlyEllipticOn.congr`: replace a coefficient field by one that agrees
  on the domain.
* `TauCeti.PDE.UniformlyEllipticOn.comp`: precomposition with a map into the domain preserves
  the predicate.
* `TauCeti.PDE.matrixBilinearForm`: the bounded bilinear form `η, ξ ↦ ηᵀ A ξ` attached to
  a coefficient matrix.
* `TauCeti.PDE.norm_matrixBilinearForm_transpose`: transposing the coefficient matrix does not
  change the operator norm of the attached bilinear form.
* `TauCeti.PDE.sum_inner_mul_matrixBilinearForm`: expansion of the first argument in the
  standard orthonormal basis.
* `TauCeti.PDE.matrixBilinearForm_eq_sum_inner_transpose`: expansion of the second argument,
  `ηᵀ A ξ = ∑ⱼ ⟪η, cⱼ⟫ ξⱼ` with `cⱼ` the columns of `A`.
* `TauCeti.PDE.contDiff_matrixBilinearForm_gradient` and
  `TauCeti.PDE.tsupport_matrixBilinearForm_gradient_subset`: smoothness and support of a
  conormal component of a smooth gradient.
* `TauCeti.PDE.locallyLipschitzOn_matrixBilinearForm_of_contDiffOn`: a coefficient field with
  `C¹` entries on an open set has locally Lipschitz bilinear forms there.
* `TauCeti.PDE.holderOnWith_matrixBilinearForm_of_forall` and
  `TauCeti.PDE.exists_holderOnWith_matrixBilinearForm_of_contDiffOn`: Hölder entries give Hölder
  bilinear forms, and `C¹` entries give bilinear forms that are Hölder on compact sets.
* `TauCeti.PDE.lipschitzWith_matrixBilinearForm_of_forall`: Lipschitz entries give Lipschitz
  bilinear forms.
* `TauCeti.PDE.lipschitzOnWith_matrixBilinearForm_apply_apply`: the entries `⟪p, a(x) q⟫` of a
  coefficient field with Lipschitz bilinear forms are Lipschitz.
* `TauCeti.PDE.lipschitzOnWith_inv_matrixBilinearForm_self` and
  `TauCeti.PDE.norm_inv_matrixBilinearForm_self_le`: for a uniformly elliptic coefficient field
  with Lipschitz bilinear forms, the reciprocal of the quadratic form `a(x)(w, w)` is
  `K ‖w‖² / (λ ‖w‖²)²`-Lipschitz and bounded by `(λ ‖w‖²)⁻¹`.
* `TauCeti.PDE.exists_lipschitzWith_matrixBilinearForm_eqOn`: a coefficient field with
  Lipschitz bilinear forms on a set agrees there with one that is Lipschitz on the whole space.
* `TauCeti.PDE.matrixBilinearFormLinear`: the coefficient matrix-to-bilinear-form map as a
  continuous linear map.
* `TauCeti.PDE.aestronglyMeasurable_norm_matrixBilinearForm_sub`: the deviation
  `x ↦ ‖a(x) - A‖` of a measurable coefficient field from a constant matrix is measurable.
* `Matrix.abs_contraction_le_mul_norm_matrixBilinearForm_mul_norm`: the contraction
  `∑ᵢⱼ Mᵢⱼ ⟪H eᵢ, eⱼ⟫` is at most `n ‖M‖ ‖H‖`, with `‖M‖` the operator norm of the attached
  bilinear form.
* `TauCeti.PDE.matrixBilinearForm_opNorm_le_of_upper_bound`: a pointwise bilinear upper
  bound controls the operator norm of the attached matrix bilinear form.
* `TauCeti.PDE.norm_matrixBilinearForm_le_sum_abs`: the operator norm of the attached bilinear
  form is at most the sum of the absolute values of the entries.
* `TauCeti.PDE.norm_matrixBilinearForm_eq_norm_toEuclideanCLM`: the operator norm of the attached
  bilinear form is the operator norm of the matrix on Euclidean space.
* `TauCeti.PDE.norm_toEuclideanCLM_apply_le`: the operator norm of the attached bilinear form
  bounds the action of the matrix on Euclidean space.
* `TauCeti.PDE.abs_sum_mul_apply_single_mul_apply_single_le`: a bilinear upper bound controls
  the pairing of the matrix with the coordinates of two continuous linear functionals.
* `TauCeti.PDE.mul_sq_mul_norm_sq_le_matrixBilinearForm_add`: the pointwise absorption
  estimate used in Caccioppoli inequalities.
* `TauCeti.PDE.ellipticCLMSet`: the operators on Euclidean space which are elliptic with
  given constants; `TauCeti.PDE.convex_ellipticCLMSet` and `TauCeti.PDE.isClosed_ellipticCLMSet`:
  they form a closed convex set, with membership `TauCeti.PDE.mem_ellipticCLMSet_iff`, which
  `TauCeti.PDE.toEuclideanCLM_mem_ellipticCLMSet_iff` and
  `TauCeti.PDE.uniformlyEllipticOn_of_forall_toEuclideanCLM_mem` relate to uniform ellipticity.
* `TauCeti.PDE.UniformlyEllipticOn.isCoercive_matrixBilinearForm`: pointwise coercivity of
  the bilinear form attached to a uniformly elliptic coefficient field.
* `TauCeti.PDE.UniformlyEllipticOn.opNorm_matrixBilinearForm_le`: pointwise operator-norm
  boundedness of the bilinear form attached to a uniformly elliptic coefficient field.
* `TauCeti.PDE.UniformlyEllipticOn.isBounded_image_matrixBilinearForm`: these bilinear forms
  are bounded uniformly over the domain.
* `TauCeti.PDE.UniformlyEllipticOn.pow_card_le_det`: a symmetric uniformly elliptic coefficient
  matrix has determinant at least `λⁿ`.
* `TauCeti.PDE.uniformlyEllipticOn_const`: a constant matrix with a lower quadratic bound is
  uniformly elliptic.
* `TauCeti.PDE.UniformlyEllipticOn.const_of_mem`: a constant field uniformly elliptic on a
  nonempty set is uniformly elliptic on every set.
* `TauCeti.PDE.continuousOn_of_continuousOn_matrixBilinearForm` and
  `TauCeti.PDE.continuous_of_continuous_matrixBilinearForm`: a coefficient field whose
  bilinear forms vary continuously is continuous.
* `TauCeti.PDE.UniformlyEllipticOn.smul_add_one_sub_smul`: interpolating a uniformly elliptic
  field on `Ω` with one on the whole space through a cutoff supported in `Ω` gives a uniformly
  elliptic field on the whole space.
* `TauCeti.PDE.uniformlyEllipticOn_smul_one`: scalar, isotropic coefficient fields are
  uniformly elliptic when their scalar coefficient lies between the ellipticity constants.
* `TauCeti.PDE.UniformlyEllipticOn.add_nonneg`: adding a nonnegative bounded
  coefficient field preserves the lower ellipticity constant and adds upper constants.
* `TauCeti.PDE.UniformlyEllipticOn.add_bounded`: adding a bounded coefficient
  perturbation preserves uniform ellipticity with lower constant `λ - μ` when the
  perturbation size `μ` is smaller than `λ`.
* `TauCeti.PDE.coefficientSymmetricPart`: the symmetric part `(A + Aᵀ) / 2` of a
  coefficient matrix.
* `TauCeti.PDE.UniformlyEllipticOn.transpose` and
  `TauCeti.PDE.UniformlyEllipticOn.coefficientSymmetricPart`: transposing or replacing a
  coefficient field by its symmetric part preserves uniform ellipticity with the same
  constants.

The vectors `η`, `ξ` lie in `EuclideanSpace ℝ n`, the space of gradients of functions on
`ℝⁿ`; this type is reducibly a finite `L²` product, so Mathlib's matrix-vector API applies
directly.
-/

public section

namespace TauCeti

namespace PDE

open Matrix

/-! ### Symmetric part of a coefficient matrix -/

section SymmetricPart

variable {n : Type*}

/-- The symmetric part `(A + Aᵀ) / 2` of a coefficient matrix.

For energy estimates the diagonal quadratic form of `A` agrees with that of
`coefficientSymmetricPart A`, while the resulting matrix is symmetric. This is the
finite-dimensional bookkeeping needed before the integrated energy form is specialized to
self-adjoint elliptic operators. -/
noncomputable def coefficientSymmetricPart (A : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 2 : ℝ) • (A + Aᵀ)

/-- The symmetric part of a coefficient matrix is symmetric. -/
lemma coefficientSymmetricPart_isSymm (A : Matrix n n ℝ) : (coefficientSymmetricPart A).IsSymm :=
  (isSymm_add_transpose_self A).smul (1 / 2 : ℝ)

/-- The entries of the symmetric part are the averages of opposite entries. -/
@[simp]
lemma coefficientSymmetricPart_apply (A : Matrix n n ℝ) (i j : n) :
    coefficientSymmetricPart A i j = (A i j + A j i) / 2 := by
  simp [coefficientSymmetricPart, div_eq_mul_inv, mul_comm]

/-- A symmetric coefficient matrix is unchanged by taking its symmetric part. -/
@[simp]
lemma coefficientSymmetricPart_eq_self_of_isSymm {A : Matrix n n ℝ} (hA : A.IsSymm) :
    coefficientSymmetricPart A = A := by
  ext i j
  rw [coefficientSymmetricPart_apply, hA.apply i j]
  ring

end SymmetricPart

/-! ### The matrix bilinear form -/

section BilinearForm

variable {n : Type*} [Fintype n]

/-- The continuous bilinear form attached to a real matrix on Euclidean space.

For a coefficient matrix `A`, this is the pointwise weak-form integrand
`(η, ξ) ↦ ηᵀ A ξ`. It is bundled as a continuous bilinear map so it can feed directly into
Mathlib's bounded-bilinear-form and Lax--Milgram APIs once the corresponding Sobolev spaces
are available. -/
noncomputable def matrixBilinearForm (A : Matrix n n ℝ) :
    EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ :=
  LinearMap.toContinuousBilinearMap
    ((Matrix.toBilin'Aux A).comp (EuclideanSpace.equiv n ℝ).toLinearEquiv.toLinearMap
      (EuclideanSpace.equiv n ℝ).toLinearEquiv.toLinearMap)

/-- The matrix bilinear form is the dot-product expression `ηᵀ A ξ`. -/
@[simp]
lemma matrixBilinearForm_apply (A : Matrix n n ℝ) (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm A η ξ = η ⬝ᵥ (A *ᵥ ξ) := by
  rw [matrixBilinearForm, LinearMap.toContinuousBilinearMap_apply, LinearMap.BilinForm.comp_apply]
  simp [Matrix.toBilin'Aux, Matrix.toLinearMap₂'Aux, Matrix.mulVec, dotProduct, Finset.mul_sum,
    mul_left_comm, mul_comm]

/-- Matrix bilinear forms are linear in scalar multiplication of the coefficient matrix. -/
lemma matrixBilinearForm_smul_apply (c : ℝ) (A : Matrix n n ℝ) (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (c • A) η ξ = c * matrixBilinearForm A η ξ := by
  rw [matrixBilinearForm_apply, matrixBilinearForm_apply, smul_mulVec, dotProduct_smul]
  simp [smul_eq_mul]

/-- Matrix bilinear forms are additive in the coefficient matrix. -/
lemma matrixBilinearForm_add_apply (A B : Matrix n n ℝ) (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (A + B) η ξ = matrixBilinearForm A η ξ + matrixBilinearForm B η ξ := by
  rw [matrixBilinearForm_apply, matrixBilinearForm_apply, matrixBilinearForm_apply,
    add_mulVec, dotProduct_add]

/-- Transposing the coefficient matrix swaps the arguments of the bundled matrix bilinear
form. -/
lemma matrixBilinearForm_transpose_apply (A : Matrix n n ℝ) (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm Aᵀ η ξ = matrixBilinearForm A ξ η := by
  rw [matrixBilinearForm_apply, matrixBilinearForm_apply, Matrix.dotProduct_transpose_mulVec]

/-- Transposing the coefficient matrix does not change the operator norm of the bundled matrix
bilinear form: the form of `Aᵀ` is the flip of that of `A`. -/
@[simp]
lemma norm_matrixBilinearForm_transpose (A : Matrix n n ℝ) :
    ‖matrixBilinearForm Aᵀ‖ = ‖matrixBilinearForm A‖ := by
  rw [← ContinuousLinearMap.opNorm_flip (matrixBilinearForm A)]
  congr 1
  ext η ξ
  exact matrixBilinearForm_transpose_apply A η ξ

/-- The bundled bilinear form of the symmetric part is the average of the original bilinear
form and its transpose. -/
lemma matrixBilinearForm_coefficientSymmetricPart_apply (A : Matrix n n ℝ)
    (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (coefficientSymmetricPart A) η ξ =
      (matrixBilinearForm A η ξ + matrixBilinearForm A ξ η) / 2 := by
  rw [coefficientSymmetricPart, matrixBilinearForm_smul_apply, matrixBilinearForm_add_apply,
    matrixBilinearForm_transpose_apply]
  ring

/-- The principal coefficient matrix-to-bilinear-form map as a continuous linear map. -/
noncomputable def matrixBilinearFormLinear :
    Matrix n n ℝ →L[ℝ] EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A =>
        matrixBilinearForm A
      map_add' := by
        intro A B
        ext η ξ
        exact matrixBilinearForm_add_apply A B η ξ
      map_smul' := by
        intro r A
        ext η ξ
        exact matrixBilinearForm_smul_apply r A η ξ }

/-- Applying `matrixBilinearFormLinear` recovers `matrixBilinearForm`. -/
@[simp]
lemma matrixBilinearFormLinear_apply (A : Matrix n n ℝ) :
    matrixBilinearFormLinear (n := n) A = matrixBilinearForm A :=
  by
    ext η ξ
    simp [matrixBilinearFormLinear]

/-- Matrix bilinear forms are subtractive in the coefficient matrix. -/
@[simp]
lemma matrixBilinearForm_sub (A B : Matrix n n ℝ) :
    matrixBilinearForm (A - B) = matrixBilinearForm A - matrixBilinearForm B := by
  simp only [← matrixBilinearFormLinear_apply, map_sub]

/-- Matrix bilinear forms are additive in the coefficient matrix. -/
@[simp]
lemma matrixBilinearForm_add (A B : Matrix n n ℝ) :
    matrixBilinearForm (A + B) = matrixBilinearForm A + matrixBilinearForm B := by
  simp only [← matrixBilinearFormLinear_apply, map_add]

/-- Matrix bilinear forms are homogeneous in the coefficient matrix. -/
@[simp]
lemma matrixBilinearForm_smul (c : ℝ) (A : Matrix n n ℝ) :
    matrixBilinearForm (c • A) = c • matrixBilinearForm A := by
  simp only [← matrixBilinearFormLinear_apply, map_smul]

/-- The zero coefficient matrix has the zero bilinear form. -/
@[simp]
lemma matrixBilinearForm_zero : matrixBilinearForm (0 : Matrix n n ℝ) = 0 := by
  simp only [← matrixBilinearFormLinear_apply, map_zero]

/-- The principal coefficient-to-bilinear-form map is continuous. -/
lemma continuous_matrixBilinearForm :
    Continuous (fun A : Matrix n n ℝ => matrixBilinearForm A) :=
  (matrixBilinearFormLinear (n := n)).continuous.congr fun A =>
    matrixBilinearFormLinear_apply A

/-- The deviation `x ↦ ‖a(x) - A‖` of an a.e. strongly measurable coefficient field from a constant
matrix, in the operator norm of the attached bilinear forms, is a.e. strongly measurable. -/
theorem aestronglyMeasurable_norm_matrixBilinearForm_sub {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} {a : X → Matrix n n ℝ}
    (ha : MeasureTheory.AEStronglyMeasurable a μ) (A : Matrix n n ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun x => ‖matrixBilinearForm (a x) - matrixBilinearForm A‖) μ := by
  have h : Continuous fun M : Matrix n n ℝ => matrixBilinearForm (M - A) :=
    continuous_matrixBilinearForm.comp (continuous_sub_right A)
  simpa only [matrixBilinearForm_sub] using
    (Continuous.norm (E := EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ)
      h).comp_aestronglyMeasurable ha

section Continuity

variable {X : Type*} [TopologicalSpace X]

/-- A coefficient field is continuous on a set as soon as its matrix bilinear forms vary
continuously there: the entry `aⁱʲ(x)` is the value of `matrixBilinearForm (a x)` on the `i`-th
and `j`-th standard basis vectors. -/
lemma continuousOn_of_continuousOn_matrixBilinearForm {s : Set X} {a : X → Matrix n n ℝ}
    (ha : ContinuousOn (fun x => matrixBilinearForm (a x)) s) : ContinuousOn a s := by
  classical
  have hM : Continuous fun B : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ =>
      Matrix.of fun i j => B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
    continuous_matrix fun i j =>
      ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))).comp
        (ContinuousLinearMap.apply ℝ _ (EuclideanSpace.single i (1 : ℝ)))).continuous
  refine (hM.comp_continuousOn ha).congr fun x _ => ?_
  ext i j
  simp

/-- A coefficient field is continuous as soon as its matrix bilinear forms vary continuously. -/
lemma continuous_of_continuous_matrixBilinearForm {a : X → Matrix n n ℝ}
    (ha : Continuous fun x => matrixBilinearForm (a x)) : Continuous a :=
  continuousOn_univ.1 (continuousOn_of_continuousOn_matrixBilinearForm ha.continuousOn)

end Continuity

/-- A pointwise bilinear upper bound gives the corresponding norm estimate for the bundled
continuous bilinear form. -/
lemma norm_matrixBilinearForm_le_of_upper_bound (A : Matrix n n ℝ) {Lam : ℝ}
    (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (η ξ : EuclideanSpace ℝ n) :
    ‖matrixBilinearForm A η ξ‖ ≤ Lam * ‖η‖ * ‖ξ‖ := by
  simpa [Real.norm_eq_abs] using hA η ξ

/-- A pointwise bilinear upper bound controls the operator norm of the bundled matrix
bilinear form.

This is the matrix-coefficient specialization of Mathlib's
`ContinuousLinearMap.opNorm_le_bound₂`. -/
lemma matrixBilinearForm_opNorm_le_of_upper_bound (A : Matrix n n ℝ) {Lam : ℝ}
    (hLam_nonneg : 0 ≤ Lam) (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖) :
    ‖matrixBilinearForm A‖ ≤ Lam := by
  refine (matrixBilinearForm A).opNorm_le_bound₂ hLam_nonneg ?_
  intro η ξ
  exact norm_matrixBilinearForm_le_of_upper_bound A hA η ξ

/-- Young's inequality for a matrix bilinear form: for `C > 0`,
`ηᵀ A ξ ≤ C ‖η‖² / 2 + ‖A‖² ‖ξ‖² / (2 C)`, where `‖A‖` is the operator norm of the attached
bilinear form. -/
lemma matrixBilinearForm_apply_le_young (A : Matrix n n ℝ) {C : ℝ} (hC : 0 < C)
    (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm A η ξ ≤
      C / 2 * ‖η‖ ^ 2 + ‖matrixBilinearForm A‖ ^ 2 * ‖ξ‖ ^ 2 / (2 * C) := by
  have h := (le_abs_self _).trans ((matrixBilinearForm A).le_opNorm₂ η ξ)
  have key : 2 * C * matrixBilinearForm A η ξ ≤
      C ^ 2 * ‖η‖ ^ 2 + ‖matrixBilinearForm A‖ ^ 2 * ‖ξ‖ ^ 2 := by
    nlinarith [sq_nonneg (C * ‖η‖ - ‖matrixBilinearForm A‖ * ‖ξ‖)]
  rw [show C / 2 * ‖η‖ ^ 2 + ‖matrixBilinearForm A‖ ^ 2 * ‖ξ‖ ^ 2 / (2 * C) =
      (C ^ 2 * ‖η‖ ^ 2 + ‖matrixBilinearForm A‖ ^ 2 * ‖ξ‖ ^ 2) / (2 * C) by
    field_simp, le_div_iff₀ (by positivity)]
  linarith

/-- The operator norm of a matrix bilinear form is at most the sum of the absolute values of the
entries of the matrix. -/
lemma norm_matrixBilinearForm_le_sum_abs (A : Matrix n n ℝ) :
    ‖matrixBilinearForm A‖ ≤ ∑ i, ∑ j, |A i j| := by
  refine matrixBilinearForm_opNorm_le_of_upper_bound A (by positivity) fun η ξ => ?_
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_))
  -- `|ηᵢ Aᵢⱼ ξⱼ| ≤ |Aᵢⱼ| ‖η‖ ‖ξ‖`, since each coordinate is bounded by the Euclidean norm.
  have hη : |η i| ≤ ‖η‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le η i
  have hξ : |ξ j| ≤ ‖ξ‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le ξ j
  rw [abs_mul, abs_mul, mul_left_comm, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul hη hξ (abs_nonneg _) (norm_nonneg _))
    (abs_nonneg _)

/-- The action of a matrix on Euclidean space is bounded by the operator norm of its bilinear
form: `‖A ξ‖² = (A ξ)ᵀ A ξ ≤ ‖A‖ ‖A ξ‖ ‖ξ‖`. -/
lemma norm_toEuclideanCLM_apply_le [DecidableEq n] (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    ‖toEuclideanCLM (n := n) (𝕜 := ℝ) A ξ‖ ≤ ‖matrixBilinearForm A‖ * ‖ξ‖ := by
  set y := toEuclideanCLM (n := n) (𝕜 := ℝ) A ξ
  have hy : ‖y‖ ^ 2 ≤ ‖matrixBilinearForm A‖ * ‖y‖ * ‖ξ‖ := by
    rw [← real_inner_self_eq_norm_sq, inner_toEuclideanCLM, ← matrixBilinearForm_apply]
    exact (le_abs_self _).trans ((matrixBilinearForm A).le_opNorm₂ y ξ)
  rcases (norm_nonneg y).eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · nlinarith

/-- The operator norm of the bilinear form of a matrix is the operator norm of the matrix acting on
Euclidean space. -/
lemma norm_matrixBilinearForm_eq_norm_toEuclideanCLM [DecidableEq n] (A : Matrix n n ℝ) :
    ‖matrixBilinearForm A‖ = ‖toEuclideanCLM (n := n) (𝕜 := ℝ) A‖ := by
  refine le_antisymm ((matrixBilinearForm A).opNorm_le_bound₂
    (ContinuousLinearMap.opNorm_nonneg _) fun η ξ => ?_)
    ((toEuclideanCLM (n := n) (𝕜 := ℝ) A).opNorm_le_bound
      (ContinuousLinearMap.opNorm_nonneg _) (norm_toEuclideanCLM_apply_le A))
  rw [matrixBilinearForm_apply, ← inner_toEuclideanCLM, Real.norm_eq_abs, mul_assoc,
    mul_left_comm]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left ((toEuclideanCLM (n := n) (𝕜 := ℝ) A).le_opNorm ξ) (norm_nonneg _))

/-- A pointwise bilinear upper bound gives a radius-restricted estimate for the bundled
matrix bilinear form. -/
lemma matrixBilinearForm_apply_norm_le_of_upper_bound {A : Matrix n n ℝ} {Lam R S : ℝ}
    (hLam_nonneg : 0 ≤ Lam) (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    {η ξ : EuclideanSpace ℝ n} (hη : ‖η‖ ≤ R) (hξ : ‖ξ‖ ≤ S) :
    ‖matrixBilinearForm A η ξ‖ ≤ Lam * R * S :=
  (matrixBilinearForm A).le_of_opNorm₂_le_of_le
    (matrixBilinearForm_opNorm_le_of_upper_bound A hLam_nonneg hA) hη hξ

/-- Adding two pointwise bilinear upper bounds adds the constants. -/
lemma abs_dotProduct_add_mulVec_le {A B : Matrix n n ℝ} {Lam Mu : ℝ}
    (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hB : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (B *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖) (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ ((A + B) *ᵥ ξ)| ≤ (Lam + Mu) * ‖η‖ * ‖ξ‖ := by
  rw [add_mulVec, dotProduct_add]
  calc
    |η ⬝ᵥ (A *ᵥ ξ) + η ⬝ᵥ (B *ᵥ ξ)|
        ≤ |η ⬝ᵥ (A *ᵥ ξ)| + |η ⬝ᵥ (B *ᵥ ξ)| := abs_add_le _ _
    _ ≤ Lam * ‖η‖ * ‖ξ‖ + Mu * ‖η‖ * ‖ξ‖ := add_le_add (hA η ξ) (hB η ξ)
    _ = (Lam + Mu) * ‖η‖ * ‖ξ‖ := by ring

/-- Subtracting two pointwise bilinear upper bounds adds the constants. -/
lemma abs_dotProduct_sub_mulVec_le {A B : Matrix n n ℝ} {Lam Mu : ℝ}
    (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hB : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (B *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖) (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ ((A - B) *ᵥ ξ)| ≤ (Lam + Mu) * ‖η‖ * ‖ξ‖ := by
  rw [Matrix.sub_mulVec, dotProduct_sub]
  linarith [abs_sub (η ⬝ᵥ (A *ᵥ ξ)) (η ⬝ᵥ (B *ᵥ ξ)), hA η ξ, hB η ξ]

/-- The symmetric part of a pointwise bounded coefficient matrix satisfies the same bilinear
upper bound. -/
lemma abs_dotProduct_coefficientSymmetricPart_mulVec_le {A : Matrix n n ℝ} {Lam : ℝ}
    (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ (coefficientSymmetricPart A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ := by
  classical
  rw [← matrixBilinearForm_apply, matrixBilinearForm_coefficientSymmetricPart_apply]
  have hηξ : ‖matrixBilinearForm A η ξ‖ ≤ Lam * ‖η‖ * ‖ξ‖ :=
    norm_matrixBilinearForm_le_of_upper_bound A hA η ξ
  have hξη : ‖matrixBilinearForm A ξ η‖ ≤ Lam * ‖η‖ * ‖ξ‖ := by
    rw [mul_right_comm]
    exact norm_matrixBilinearForm_le_of_upper_bound A hA ξ η
  have hsum :
      ‖matrixBilinearForm A η ξ + matrixBilinearForm A ξ η‖
        ≤ 2 * (Lam * ‖η‖ * ‖ξ‖) := by
    calc
      ‖matrixBilinearForm A η ξ + matrixBilinearForm A ξ η‖
          ≤ ‖matrixBilinearForm A η ξ‖ + ‖matrixBilinearForm A ξ η‖ := norm_add_le _ _
      _ ≤ Lam * ‖η‖ * ‖ξ‖ + Lam * ‖η‖ * ‖ξ‖ := add_le_add hηξ hξη
      _ = 2 * (Lam * ‖η‖ * ‖ξ‖) := by ring
  rw [abs_div]
  rw [abs_of_pos (a := (2 : ℝ)) two_pos]
  exact (div_le_iff₀' two_pos).2 (by
    simpa [Real.norm_eq_abs] using hsum)

/-- If the bilinear form of `A` is bounded, `|ηᵀ A ξ| ≤ Λ ‖η‖ ‖ξ‖`, then so is its pairing with
the coordinates of two linear functionals: `|∑ᵢⱼ Aᵢⱼ L₁(eᵢ) L₂(eⱼ)| ≤ Λ ‖L₁‖ ‖L₂‖`. This bounds
the first-order cross term `∑ᵢⱼ Aᵢⱼ ∂ᵢη ∂ⱼu` of the principal part of a product. -/
lemma abs_sum_mul_apply_single_mul_apply_single_le [DecidableEq n] {A : Matrix n n ℝ} {Lam : ℝ}
    (hA : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (L₁ L₂ : EuclideanSpace ℝ n →L[ℝ] ℝ) :
    |∑ i, ∑ j, A i j * (L₁ (EuclideanSpace.single i 1) * L₂ (EuclideanSpace.single j 1))| ≤
      Lam * ‖L₁‖ * ‖L₂‖ := by
  set X := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n)).symm L₁
  set Y := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ n)).symm L₂
  have hX (i : n) : L₁ (EuclideanSpace.single i 1) = X i := by
    rw [← InnerProductSpace.toDual_symm_apply, EuclideanSpace.inner_single_right]
    simp [X]
  have hY (i : n) : L₂ (EuclideanSpace.single i 1) = Y i := by
    rw [← InnerProductSpace.toDual_symm_apply, EuclideanSpace.inner_single_right]
    simp [Y]
  have h := hA X Y
  rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
  convert h using 2
  simp only [hX, hY, dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end BilinearForm

/-! ### Matrix quadratic forms and uniform ellipticity -/

variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- The identity matrix has quadratic form `‖ξ‖²`. -/
@[simp]
lemma toQuadraticForm'_one (ξ : EuclideanSpace ℝ n) :
    (1 : Matrix n n ℝ).toQuadraticForm' ξ = ‖ξ‖ ^ 2 := by
  rw [Matrix.toQuadraticForm'_apply, one_mulVec]
  simpa [dotProduct, sq] using (EuclideanSpace.real_norm_sq_eq ξ).symm

/-- Two-sided bounds `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` on the quadratic form of a square matrix over a
nonempty index type force `λ ≤ Λ`. -/
theorem le_of_mul_norm_sq_le_toQuadraticForm'_le [Nonempty n] {A : Matrix n n ℝ} {lam Lam : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : EuclideanSpace ℝ n, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) : lam ≤ Lam := by
  simpa using (hA (EuclideanSpace.single (Classical.arbitrary n) 1)).trans (hA' _)

/-- The matrix bilinear form associated to the identity matrix is the Euclidean dot product. -/
lemma matrixBilinearForm_one_apply (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (1 : Matrix n n ℝ) η ξ = η ⬝ᵥ ξ := by
  rw [matrixBilinearForm_apply, one_mulVec]

/-- The scalar identity matrix has quadratic form `c ‖ξ‖²`. -/
lemma toQuadraticForm'_smul_one (c : ℝ) (ξ : EuclideanSpace ℝ n) :
    (c • (1 : Matrix n n ℝ)).toQuadraticForm' ξ = c * ‖ξ‖ ^ 2 := by
  rw [toQuadraticForm'_smul, _root_.smul_apply, smul_eq_mul, toQuadraticForm'_one]

/-- The matrix bilinear form associated to `c • 1` is `c` times the Euclidean dot product. -/
lemma matrixBilinearForm_smul_one_apply (c : ℝ) (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm (c • (1 : Matrix n n ℝ)) η ξ = c * (η ⬝ᵥ ξ) := by
  rw [matrixBilinearForm_smul_apply, matrixBilinearForm_one_apply]

/-- The quadratic part of the matrix bilinear form is the matrix quadratic form. -/
lemma matrixBilinearForm_self (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm A ξ ξ = A.toQuadraticForm' ξ := by
  rw [matrixBilinearForm_apply, Matrix.toQuadraticForm'_apply]

/-- The difference of two matrix bilinear forms with the same first argument `g` splits as
`gᵀ M (g + h) - gᵀ N h = gᵀ M g + gᵀ (M - N) h`. With `M` and `N` a coefficient frozen at two
functions, this is the identity behind comparison and monotonicity estimates for quasilinear
operators. -/
lemma matrixBilinearForm_add_sub_matrixBilinearForm (M N : Matrix n n ℝ)
    (g h : EuclideanSpace ℝ n) :
    matrixBilinearForm M g (g + h) - matrixBilinearForm N g h =
      M.toQuadraticForm' g + g ⬝ᵥ ((M - N) *ᵥ h) := by
  rw [map_add, matrixBilinearForm_self]
  simp only [matrixBilinearForm_apply, Matrix.sub_mulVec, dotProduct_sub]
  ring

/-- Every matrix quadratic form is bounded above by the operator norm of the matrix bilinear form
times `‖ξ‖²`. -/
lemma toQuadraticForm'_le_norm_matrixBilinearForm_mul_sq (A : Matrix n n ℝ)
    (ξ : EuclideanSpace ℝ n) : A.toQuadraticForm' ξ ≤ ‖matrixBilinearForm A‖ * ‖ξ‖ ^ 2 := by
  rw [← matrixBilinearForm_self, sq, ← mul_assoc]
  exact (Real.le_norm_self _).trans ((matrixBilinearForm A).le_opNorm₂ ξ ξ)

/-- The symmetric part has the same quadratic form as the original coefficient matrix. -/
@[simp]
lemma toQuadraticForm'_coefficientSymmetricPart (A : Matrix n n ℝ) (ξ : EuclideanSpace ℝ n) :
    (coefficientSymmetricPart A).toQuadraticForm' ξ = A.toQuadraticForm' ξ := by
  rw [coefficientSymmetricPart, toQuadraticForm'_smul, toQuadraticForm'_add_transpose, smul_smul,
    one_div_mul_cancel two_ne_zero, one_smul]

/-- A pointwise absorption estimate for matrix bilinear forms. If the quadratic form is
bounded below at `g` by `λ ‖g‖²` and the bilinear form at `(q, g)` is bounded by
`Λ ‖q‖ ‖g‖`, then the cross term in `A(g, z²g + 2zwq)` is absorbed by half of the
elliptic term and a multiple of `w²‖q‖²`. -/
theorem mul_sq_mul_norm_sq_le_matrixBilinearForm_add {A : Matrix n n ℝ} {lam Lam : ℝ}
    (hlam : 0 < lam) (z w : ℝ) (g q : EuclideanSpace ℝ n)
    (hlower : lam * ‖g‖ ^ 2 ≤ A.toQuadraticForm' g)
    (hupper : |q ⬝ᵥ (A *ᵥ g)| ≤ Lam * ‖q‖ * ‖g‖) :
    lam * (z ^ 2 * ‖g‖ ^ 2) ≤
      matrixBilinearForm A (z • (z • g + w • q) + (z * w) • q) g
        + lam / 2 * (z ^ 2 * ‖g‖ ^ 2) + 2 * Lam ^ 2 / lam * (‖q‖ ^ 2 * w ^ 2) := by
  have hexp : matrixBilinearForm A (z • (z • g + w • q) + (z * w) • q) g =
      z ^ 2 * A.toQuadraticForm' g + 2 * (z * w) * (q ⬝ᵥ (A *ᵥ g)) := by
    rw [← matrixBilinearForm_self, ← matrixBilinearForm_apply]
    simp only [map_add, map_smul, _root_.add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  -- Weighted Young inequality `2 X Y ≤ (λ/2) X² + (2/λ) Y²` for `X = |z| ‖g‖` and
  -- `Y = Λ |w| ‖q‖`: Mathlib's `two_mul_le_add_mul_sq` at weight `ε = λ/2`.
  have hyoung : 2 * (|z| * ‖g‖) * (Lam * |w| * ‖q‖) ≤
      lam / 2 * (|z| * ‖g‖) ^ 2 + 2 / lam * (Lam * |w| * ‖q‖) ^ 2 := by
    have h := two_mul_le_add_mul_sq (a := |z| * ‖g‖) (b := Lam * |w| * ‖q‖)
      (ε := lam / 2) (by linarith)
    rwa [inv_div] at h
  have hzw : |2 * (z * w) * (q ⬝ᵥ (A *ᵥ g))| ≤ 2 * (|z| * ‖g‖) * (Lam * |w| * ‖q‖) := by
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    calc 2 * (|z| * |w|) * |q ⬝ᵥ (A *ᵥ g)| ≤ 2 * (|z| * |w|) * (Lam * ‖q‖ * ‖g‖) := by
          gcongr
      _ = 2 * (|z| * ‖g‖) * (Lam * |w| * ‖q‖) := by ring
  have hsqz : |z| ^ 2 = z ^ 2 := sq_abs z
  have hsqw : |w| ^ 2 = w ^ 2 := sq_abs w
  have hyoung' : 2 * (|z| * ‖g‖) * (Lam * |w| * ‖q‖) ≤
      lam / 2 * (z ^ 2 * ‖g‖ ^ 2) + 2 * Lam ^ 2 / lam * (‖q‖ ^ 2 * w ^ 2) := by
    refine hyoung.trans_eq ?_
    rw [mul_pow, mul_pow, mul_pow, hsqz, hsqw]
    ring
  rw [hexp]
  nlinarith [neg_abs_le (2 * (z * w) * (q ⬝ᵥ (A *ᵥ g))), sq_nonneg z,
    mul_le_mul_of_nonneg_left hlower (sq_nonneg z)]

/-- A scalar multiple of the identity has operator integrand bounded by any upper bound for
the absolute value of the scalar. -/
lemma abs_dotProduct_smul_one_mulVec_le_of_abs_le {c Lam : ℝ} (hc : |c| ≤ Lam)
    (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ ((c • (1 : Matrix n n ℝ)) *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ := by
  rw [smul_mulVec, one_mulVec, dotProduct_smul]
  simp only [smul_eq_mul, abs_mul]
  calc
    |c| * |η ⬝ᵥ ξ| ≤ |c| * (‖η‖ * ‖ξ‖) := by
      gcongr
      simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
        abs_real_inner_le_norm η ξ
    _ ≤ Lam * ‖η‖ * ‖ξ‖ := by
      have hnorm : 0 ≤ ‖η‖ * ‖ξ‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hc hnorm

/-- A scalar multiple of the identity has operator integrand bounded by any upper bound for
the absolute value of the scalar. -/
lemma norm_matrixBilinearForm_smul_one_le_of_abs_le {c Lam : ℝ} (hc : |c| ≤ Lam)
    (η ξ : EuclideanSpace ℝ n) :
    ‖matrixBilinearForm (c • (1 : Matrix n n ℝ)) η ξ‖ ≤ Lam * ‖η‖ * ‖ξ‖ :=
  norm_matrixBilinearForm_le_of_upper_bound (c • (1 : Matrix n n ℝ))
    (abs_dotProduct_smul_one_mulVec_le_of_abs_le hc) η ξ

/-- Adding a nonnegative quadratic form preserves a lower quadratic bound. -/
lemma lower_bound_toQuadraticForm'_add {A B : Matrix n n ℝ} {lam : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hB : ∀ ξ : EuclideanSpace ℝ n, 0 ≤ B.toQuadraticForm' ξ) (ξ : EuclideanSpace ℝ n) :
    lam * ‖ξ‖ ^ 2 ≤ (A + B).toQuadraticForm' ξ := by
  rw [toQuadraticForm'_add, _root_.add_apply]
  exact (hA ξ).trans (le_add_of_nonneg_right (hB ξ))

/-- Adding a coefficient with a one-sided quadratic lower bound lowers a quadratic lower
bound by the size of that perturbation. -/
lemma lower_bound_toQuadraticForm'_add_of_lower_bound {A B : Matrix n n ℝ} {lam Mu : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hB : ∀ ξ : EuclideanSpace ℝ n, -(Mu * ‖ξ‖ ^ 2) ≤ B.toQuadraticForm' ξ)
    (ξ : EuclideanSpace ℝ n) : (lam - Mu) * ‖ξ‖ ^ 2 ≤ (A + B).toQuadraticForm' ξ := by
  rw [toQuadraticForm'_add, _root_.add_apply]
  have hA_lower := hA ξ
  have hB_lower := hB ξ
  nlinarith

/-- A bilinear upper bound for a coefficient matrix bounds its quadratic form in absolute
value by the same constant. -/
lemma abs_toQuadraticForm'_le_of_abs_dotProduct_mulVec_le {B : Matrix n n ℝ} {Mu : ℝ}
    (hB : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (B *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖) (ξ : EuclideanSpace ℝ n) :
    |B.toQuadraticForm' ξ| ≤ Mu * ‖ξ‖ ^ 2 := by
  rw [Matrix.toQuadraticForm'_apply]
  have h := hB ξ ξ
  simpa [sq, mul_assoc] using h

/-- A pointwise quadratic lower bound makes the associated matrix bilinear form coercive in
Mathlib's Lax--Milgram sense. -/
lemma isCoercive_matrixBilinearForm_of_lower_bound (A : Matrix n n ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) :
    IsCoercive (matrixBilinearForm A) := by
  refine ⟨lam, hlam, fun ξ => ?_⟩
  rw [matrixBilinearForm_self]
  simpa [sq, pow_two, mul_assoc] using hA ξ

/-- The identity matrix bilinear form is coercive with constant `1`. -/
lemma isCoercive_matrixBilinearForm_one :
    IsCoercive (matrixBilinearForm (1 : Matrix n n ℝ)) := by
  refine isCoercive_matrixBilinearForm_of_lower_bound (1 : Matrix n n ℝ) zero_lt_one ?_
  intro ξ
  simp

/-- A positive scalar multiple of the identity matrix gives a coercive bilinear form. -/
lemma isCoercive_matrixBilinearForm_smul_one {c : ℝ} (hc : 0 < c) :
    IsCoercive (matrixBilinearForm (c • (1 : Matrix n n ℝ))) := by
  refine isCoercive_matrixBilinearForm_of_lower_bound (c • (1 : Matrix n n ℝ)) hc ?_
  intro ξ
  simp

/-- Uniform ellipticity and boundedness with explicit constants on a domain.

The predicate says that for every `x ∈ Ω`, the matrix `a x` has quadratic form bounded below
by `λ‖ξ‖²` and bilinear form bounded above by `Λ‖η‖‖ξ‖`, uniformly in `x`, `η`, and `ξ`.
The side conditions `0 < λ` and `λ ≤ Λ` are part of the predicate so later energy estimates can
recover them directly. -/
def UniformlyEllipticOn (Ω : Set X) (a : X → Matrix n n ℝ) (lam Lam : ℝ) : Prop :=
  0 < lam ∧ lam ≤ Lam ∧
    ∀ ⦃x⦄, x ∈ Ω →
      (∀ ξ : EuclideanSpace ℝ n,
        lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) ∧
        ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖

/-- Characteristic restatement of uniform ellipticity and boundedness on a domain. -/
lemma uniformlyEllipticOn_iff :
    UniformlyEllipticOn Ω a lam Lam ↔
      0 < lam ∧ lam ≤ Lam ∧
        ∀ ⦃x⦄, x ∈ Ω →
          (∀ ξ : EuclideanSpace ℝ n,
            lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) ∧
            ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ :=
  Iff.rfl

section EllipticOperators

open scoped InnerProductSpace

/-- The operators on `EuclideanSpace ℝ n` which are elliptic with constant `λ` and bounded by
`Λ`: `λ ‖ξ‖² ≤ ⟪ξ, M ξ⟫` and `|⟪η, M ξ⟫| ≤ Λ ‖η‖ ‖ξ‖` for all `η`, `ξ`. -/
def ellipticCLMSet (lam Lam : ℝ) :
    Set (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) :=
  {M | (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, M ξ⟫_ℝ) ∧ ∀ η ξ, |⟪η, M ξ⟫_ℝ| ≤ Lam * ‖η‖ * ‖ξ‖}

omit [DecidableEq n] in
/-- An operator is elliptic with constant `λ` and bounded by `Λ` exactly when
`λ ‖ξ‖² ≤ ⟪ξ, M ξ⟫` and `|⟪η, M ξ⟫| ≤ Λ ‖η‖ ‖ξ‖` for all `η`, `ξ`. -/
theorem mem_ellipticCLMSet_iff {lam Lam : ℝ} {M : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n} :
    M ∈ ellipticCLMSet lam Lam ↔
      (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, M ξ⟫_ℝ) ∧ ∀ η ξ, |⟪η, M ξ⟫_ℝ| ≤ Lam * ‖η‖ * ‖ξ‖ :=
  Iff.rfl

omit [DecidableEq n] in
/-- The elliptic operators with constants `λ, Λ` form a convex set. -/
theorem convex_ellipticCLMSet (lam Lam : ℝ) :
    Convex ℝ (ellipticCLMSet (n := n) lam Lam) := by
  -- It is an intersection of half-spaces cut out by the linear maps `M ↦ ⟪η, M ξ⟫`.
  have hL (η ξ : EuclideanSpace ℝ n) :
      IsLinearMap ℝ fun M : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n => ⟪η, M ξ⟫_ℝ :=
    ((innerₛₗ ℝ η).comp (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ n) ξ).toLinearMap).isLinear
  simp only [ellipticCLMSet, abs_le, Set.ofPred_and, Set.ofPred_forall]
  exact (convex_iInter fun ξ => convex_halfSpace_ge (hL ξ ξ) _).inter
    (convex_iInter₂ fun η ξ => (convex_halfSpace_ge (hL η ξ) _).inter
      (convex_halfSpace_le (hL η ξ) _))

omit [DecidableEq n] in
/-- The elliptic operators with constants `λ, Λ` form a closed set. -/
theorem isClosed_ellipticCLMSet (lam Lam : ℝ) :
    IsClosed (ellipticCLMSet (n := n) lam Lam) := by
  have hc : ∀ η ξ : EuclideanSpace ℝ n, Continuous fun M :
      EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n => ⟪η, M ξ⟫_ℝ := fun η ξ =>
    continuous_const.inner (continuous_id.clm_apply continuous_const)
  simp only [ellipticCLMSet, Set.ofPred_and, Set.ofPred_forall]
  exact IsClosed.inter (isClosed_iInter fun ξ => isClosed_le continuous_const (hc ξ ξ))
    (isClosed_iInter fun η => isClosed_iInter fun ξ =>
      isClosed_le (continuous_abs.comp (hc η ξ)) continuous_const)

/-- The operator of a matrix is elliptic with constant `λ` and bounded by `Λ` exactly when the
matrix satisfies the pointwise conditions of `TauCeti.PDE.UniformlyEllipticOn`. -/
@[simp]
theorem toEuclideanCLM_mem_ellipticCLMSet_iff {lam Lam : ℝ} (A : Matrix n n ℝ) :
    toEuclideanCLM (𝕜 := ℝ) A ∈ ellipticCLMSet lam Lam ↔
      (∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) ∧
        ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (A *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ := by
  simp only [mem_ellipticCLMSet_iff, inner_toEuclideanCLM, toQuadraticForm'_apply]

/-- A coefficient field whose operators are elliptic with constants `0 < λ ≤ Λ` at every point of
`s` is uniformly elliptic on `s`. -/
theorem uniformlyEllipticOn_of_forall_toEuclideanCLM_mem {s : Set X} {a : X → Matrix n n ℝ}
    {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (h : ∀ x ∈ s, toEuclideanCLM (𝕜 := ℝ) (a x) ∈ ellipticCLMSet lam Lam) :
    UniformlyEllipticOn s a lam Lam :=
  uniformlyEllipticOn_iff.2
    ⟨hlam, hle, fun x hx => (toEuclideanCLM_mem_ellipticCLMSet_iff _).1 (h x hx)⟩

end EllipticOperators

namespace UniformlyEllipticOn

variable {Ω Ω' : Set X} {a b : X → Matrix n n ℝ}
  {lam Lam lam' Lam' : ℝ}

/-- The lower ellipticity constant is positive. -/
@[grind →]
lemma pos (h : UniformlyEllipticOn Ω a lam Lam) : 0 < lam :=
  h.1

/-- The lower ellipticity constant is no larger than the upper constant. -/
@[grind →]
lemma le (h : UniformlyEllipticOn Ω a lam Lam) : lam ≤ Lam :=
  h.2.1

/-- The upper ellipticity constant is nonnegative. -/
lemma upper_nonneg (h : UniformlyEllipticOn Ω a lam Lam) : 0 ≤ Lam :=
  h.pos.le.trans h.le

/-- The lower quadratic-form bound supplied by uniform ellipticity. -/
@[grind =>]
lemma lower_bound (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    (ξ : EuclideanSpace ℝ n) :
    lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ :=
  (h.2.2 hx).1 ξ

/-- The bilinear upper bound supplied by uniform ellipticity. -/
@[grind =>]
lemma upper_bound (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖ :=
  (h.2.2 hx).2 η ξ

/-- Uniform ellipticity implies pointwise nonnegativity of the coefficient quadratic form. -/
lemma quadraticForm_nonneg (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    (ξ : EuclideanSpace ℝ n) :
    0 ≤ (a x).toQuadraticForm' ξ := by
  exact (mul_nonneg h.pos.le (sq_nonneg ‖ξ‖)).trans (h.lower_bound hx ξ)

/-- The diagonal entries of a uniformly elliptic coefficient matrix are at most the upper
constant, so its trace is at most `card n * Λ`. -/
lemma trace_le (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) :
    (a x).trace ≤ Fintype.card n * Lam := by
  have hdiag (i : n) : a x i i ≤ Lam := by
    have h1 : |a x i i| ≤ Lam := by
      simpa using h.upper_bound hx (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
    exact (le_abs_self _).trans h1
  calc (a x).trace = ∑ i, a x i i := rfl
    _ ≤ ∑ _i : n, Lam := Finset.sum_le_sum fun i _ ↦ hdiag i
    _ = Fintype.card n * Lam := by simp

/-- Uniform ellipticity gives a positive quadratic form on every nonzero vector. -/
lemma quadraticForm_pos (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    {ξ : EuclideanSpace ℝ n} (hξ : ξ ≠ 0) :
    0 < (a x).toQuadraticForm' ξ := by
  exact (mul_pos h.pos (sq_pos_of_ne_zero (by simpa using hξ))).trans_le
    (h.lower_bound hx ξ)

/-- Restricting the domain preserves uniform ellipticity with the same constants. -/
lemma mono_set (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : Ω' ⊆ Ω) :
    UniformlyEllipticOn Ω' a lam Lam :=
  ⟨h.pos, h.le, fun {_} hx => h.2.2 (hΩ hx)⟩

/-- Weakening the lower constant and increasing the upper constant preserves uniform
ellipticity. -/
lemma mono_constants (h : UniformlyEllipticOn Ω a lam Lam) (hlam' : 0 < lam')
    (hlam'_le : lam' ≤ lam) (hLam_le : Lam ≤ Lam') :
    UniformlyEllipticOn Ω a lam' Lam' := by
  refine ⟨hlam', hlam'_le.trans (h.le.trans hLam_le), fun {x} hx => ?_⟩
  refine ⟨fun ξ => ?_, fun η ξ => ?_⟩
  · have hnorm : 0 ≤ (‖ξ‖ : ℝ) ^ 2 := sq_nonneg ‖ξ‖
    exact (mul_le_mul_of_nonneg_right hlam'_le hnorm).trans (h.lower_bound hx ξ)
  · exact (h.upper_bound hx η ξ).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLam_le (norm_nonneg _))
        (norm_nonneg _))

/-- Multiplying the coefficient field by `c > 0` multiplies both ellipticity constants by `c`, so
the ratio `Λ / λ` is unchanged. -/
lemma const_smul (h : UniformlyEllipticOn Ω a lam Lam) {c : ℝ} (hc : 0 < c) :
    UniformlyEllipticOn Ω (c • a) (c * lam) (c * Lam) := by
  refine ⟨mul_pos hc h.pos, mul_le_mul_of_nonneg_left h.le hc.le, fun {x} hx => ⟨fun ξ => ?_,
    fun η ξ => ?_⟩⟩
  · rw [Pi.smul_apply, toQuadraticForm'_smul, _root_.smul_apply, smul_eq_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.lower_bound hx ξ) hc.le
  · rw [Pi.smul_apply, smul_mulVec, dotProduct_smul, smul_eq_mul, abs_mul, abs_of_pos hc,
      mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using h.upper_bound hx η ξ) hc.le

/-- A constructor when the side conditions and pointwise quadratic-form bounds are already
available separately. -/
lemma of_bounds (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hbounds : ∀ ⦃x⦄, x ∈ Ω → ∀ ξ : EuclideanSpace ℝ n,
      lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (hupper : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖) :
    UniformlyEllipticOn Ω a lam Lam :=
  ⟨hlam, hlamLam, fun {_} hx => ⟨hbounds hx, hupper hx⟩⟩

/-- Uniform ellipticity depends only on the coefficient values on the domain. -/
lemma congr (h : UniformlyEllipticOn Ω a lam Lam) (hab : Set.EqOn b a Ω) :
    UniformlyEllipticOn Ω b lam Lam := by
  refine UniformlyEllipticOn.of_bounds h.pos h.le (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · rw [hab hx]
    exact h.lower_bound hx ξ
  · rw [hab hx]
    exact h.upper_bound hx η ξ

/-- Freezing the parameter of a family of uniformly elliptic coefficients keeps uniform
ellipticity: if every `a(·, s)` is uniformly elliptic on `Ω` with the constants `λ, Λ`, then so
is `x ↦ a(x, v x)` for every `v : X → S`. This is the frozen coefficient of a quasilinear
equation `-div (a(x, u) ∇u) = ℓ`. -/
lemma apply_of_forall {S : Type*} [Nonempty S] {a : X → S → Matrix n n ℝ}
    (h : ∀ s, UniformlyEllipticOn Ω (fun x => a x s) lam Lam) (v : X → S) :
    UniformlyEllipticOn Ω (fun x => a x (v x)) lam Lam :=
  of_bounds (h (Classical.arbitrary S)).pos (h (Classical.arbitrary S)).le
    (fun _ hx ξ => (h _).lower_bound hx ξ) (fun _ hx η ξ => (h _).upper_bound hx η ξ)

/-- Uniform ellipticity is preserved by precomposition with a map into the domain. Precomposing
with a retraction onto a subset of the domain extends a field to the whole space with the same
constants. -/
lemma comp {Y : Type*} {g : Y → X} {s : Set Y} (h : UniformlyEllipticOn Ω a lam Lam)
    (hg : Set.MapsTo g s Ω) : UniformlyEllipticOn s (a ∘ g) lam Lam :=
  of_bounds h.pos h.le (fun _ hy ξ => h.lower_bound (hg hy) ξ)
    (fun _ hy η ξ => h.upper_bound (hg hy) η ξ)

/-- At every point of the domain, uniform ellipticity gives a norm bound for the attached
matrix bilinear form. -/
@[grind =>]
lemma norm_point_matrixBilinearForm_le (h : UniformlyEllipticOn Ω a lam Lam) {x : X}
    (hx : x ∈ Ω) (η ξ : EuclideanSpace ℝ n) :
    ‖matrixBilinearForm (a x) η ξ‖ ≤ Lam * ‖η‖ * ‖ξ‖ :=
  norm_matrixBilinearForm_le_of_upper_bound (a x) (h.upper_bound hx) η ξ

/-- At every point of the domain, uniform ellipticity bounds the operator norm of the
attached matrix bilinear form by the upper ellipticity constant. -/
@[grind =>]
lemma opNorm_matrixBilinearForm_le (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) :
    ‖matrixBilinearForm (a x)‖ ≤ Lam :=
  matrixBilinearForm_opNorm_le_of_upper_bound (a x) h.upper_nonneg (h.upper_bound hx)

/-- At every point of the domain, the quadratic form is bounded above by `Λ‖ξ‖²`. -/
@[grind =>]
lemma toQuadraticForm'_le (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    (ξ : EuclideanSpace ℝ n) : (a x).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2 :=
  (toQuadraticForm'_le_norm_matrixBilinearForm_mul_sq (a x) ξ).trans
    (mul_le_mul_of_nonneg_right (h.opNorm_matrixBilinearForm_le hx) (sq_nonneg _))

/-- At every point of the domain, every entry of the coefficient matrix is bounded in absolute
value by the upper ellipticity constant. -/
lemma abs_apply_le (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) (i j : n) :
    |a x i j| ≤ Lam := by
  simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using
    h.upper_bound hx (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

/-- A symmetric uniformly elliptic coefficient matrix is positive definite. -/
lemma posDef (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) (hsymm : (a x).IsSymm) :
    (a x).PosDef :=
  Matrix.PosDef.of_toQuadraticForm' hsymm fun ξ hξ => by
    simpa using h.quadraticForm_pos hx (ξ := WithLp.toLp 2 ξ) (by simpa using hξ)

open scoped MatrixOrder in
/-- A symmetric uniformly elliptic coefficient matrix has determinant at least `λⁿ`. -/
lemma pow_card_le_det (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    (hsymm : (a x).IsSymm) : lam ^ Fintype.card n ≤ (a x).det := by
  have h1 : (lam • (1 : Matrix n n ℝ)).PosSemidef := PosSemidef.one.smul h.pos.le
  have h2 : lam • (1 : Matrix n n ℝ) ≤ a x := by
    rw [Matrix.le_iff]
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun ξ => ?_
    · exact isHermitian_iff_isSymm.2 (hsymm.sub (isSymm_one.smul lam))
    · have := h.lower_bound hx (WithLp.toLp 2 ξ)
      simp only [toQuadraticForm'_apply, EuclideanSpace.norm_sq_eq] at this
      simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec,
        dotProduct_smul, smul_eq_mul, sub_nonneg]
      simpa [dotProduct, Real.norm_eq_abs, sq_abs, sq] using this
  simpa [det_smul] using h1.det_le_det h2

/-- On the domain, the bilinear forms attached to a uniformly elliptic coefficient field form a
bounded set, of operator norm at most the upper ellipticity constant. -/
lemma isBounded_image_matrixBilinearForm (h : UniformlyEllipticOn Ω a lam Lam) :
    Bornology.IsBounded ((fun x => matrixBilinearForm (a x)) '' Ω) :=
  isBounded_iff_forall_norm_le.2 ⟨Lam, by
    rintro _ ⟨x, hx, rfl⟩
    exact h.opNorm_matrixBilinearForm_le hx⟩

/-- Uniform ellipticity gives a radius-restricted pointwise bound for the coefficient
integrand. -/
@[grind =>]
lemma norm_point_matrixBilinearForm_le_mul_of_norm_le
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) {R S : ℝ}
    {η ξ : EuclideanSpace ℝ n} (hη : ‖η‖ ≤ R) (hξ : ‖ξ‖ ≤ S) :
    ‖matrixBilinearForm (a x) η ξ‖ ≤ Lam * R * S :=
  (matrixBilinearForm (a x)).le_of_opNorm₂_le_of_le
    (h.opNorm_matrixBilinearForm_le hx) hη hξ

/-- At every point of the domain, uniform ellipticity gives coercivity of the attached matrix
bilinear form. -/
@[grind =>]
lemma isCoercive_matrixBilinearForm (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) :
    IsCoercive (matrixBilinearForm (a x)) :=
  isCoercive_matrixBilinearForm_of_lower_bound (a x) h.pos (h.lower_bound hx)

/-- Transposing the coefficient field preserves uniform ellipticity with the same constants.

The quadratic lower bound is unchanged, and the bilinear upper bound follows by swapping the
two Euclidean arguments. -/
lemma transpose (h : UniformlyEllipticOn Ω a lam Lam) :
    UniformlyEllipticOn Ω (fun x => (a x)ᵀ) lam Lam := by
  refine UniformlyEllipticOn.of_bounds h.pos h.le (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · simpa using h.lower_bound hx ξ
  · rw [Matrix.dotProduct_transpose_mulVec]
    rw [mul_right_comm]
    exact h.upper_bound hx ξ η

/-- Replacing a coefficient field by its symmetric part preserves uniform ellipticity with
the same constants.

This lets the energy-method API pass from a nonsymmetric uniformly elliptic principal
coefficient to the symmetric coefficient with the same diagonal energy, which is the
finite-dimensional prerequisite for self-adjoint model problems. -/
lemma coefficientSymmetricPart (h : UniformlyEllipticOn Ω a lam Lam) :
    UniformlyEllipticOn Ω (fun x => coefficientSymmetricPart (a x)) lam Lam := by
  refine UniformlyEllipticOn.of_bounds h.pos h.le (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · simpa using h.lower_bound hx ξ
  · exact abs_dotProduct_coefficientSymmetricPart_mulVec_le (h.upper_bound hx) η ξ

/-- Adding a pointwise nonnegative bounded coefficient field preserves uniform ellipticity.

The lower ellipticity constant is unchanged, while the upper bilinear-form constant is
increased by the upper bound for the perturbation. This is the pointwise matrix estimate
used when an energy form is split into a uniformly elliptic principal part plus a
nonnegative bounded perturbation. -/
lemma add_nonneg (h : UniformlyEllipticOn Ω a lam Lam) {b : X → Matrix n n ℝ}
    {Mu : ℝ} (hMu : 0 ≤ Mu) (hb_nonneg : ∀ ⦃x⦄, x ∈ Ω → ∀ ξ : EuclideanSpace ℝ n,
      0 ≤ (b x).toQuadraticForm' ξ)
    (hb_upper : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (b x *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖) :
    UniformlyEllipticOn Ω (fun x => a x + b x) lam (Lam + Mu) := by
  refine UniformlyEllipticOn.of_bounds h.pos ?_ (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · exact h.le.trans (le_add_of_nonneg_right hMu)
  · exact lower_bound_toQuadraticForm'_add (h.lower_bound hx) (hb_nonneg hx) ξ
  · exact abs_dotProduct_add_mulVec_le (h.upper_bound hx) (hb_upper hx) η ξ

/-- Adding a bounded coefficient perturbation preserves uniform ellipticity after reducing
the lower ellipticity constant by the perturbation size.

If `a` is uniformly elliptic with constants `λ, Λ` and `b` has pointwise bilinear bound
`μ`, then `a + b` is uniformly elliptic with constants `λ - μ, Λ + μ`, provided `μ < λ`.
This is the finite-dimensional coefficient stability estimate used when perturbing a
uniformly elliptic divergence-form operator. -/
lemma add_bounded (h : UniformlyEllipticOn Ω a lam Lam) {b : X → Matrix n n ℝ}
    {Mu : ℝ} (hMu_nonneg : 0 ≤ Mu) (hMu_lt : Mu < lam)
    (hb_upper : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (b x *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖) :
    UniformlyEllipticOn Ω (fun x => a x + b x) (lam - Mu) (Lam + Mu) := by
  refine UniformlyEllipticOn.of_bounds (sub_pos.mpr hMu_lt) ?_ (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · linarith [h.le, hMu_nonneg]
  · refine lower_bound_toQuadraticForm'_add_of_lower_bound (h.lower_bound hx) ?_ ξ
    intro ζ
    exact (neg_le_neg
      (abs_toQuadraticForm'_le_of_abs_dotProduct_mulVec_le (hb_upper hx) ζ)).trans
      (neg_abs_le ((b x).toQuadraticForm' ζ))
  · exact abs_dotProduct_add_mulVec_le (h.upper_bound hx) (hb_upper hx) η ξ

/-- Adding a bounded scalar multiple of the identity preserves uniform ellipticity after
reducing the lower ellipticity constant by the scalar bound.

This is the scalar-coefficient specialization of `UniformlyEllipticOn.add_bounded`: no sign
condition is imposed on `c`, only the pointwise bound `|c x| ≤ μ`. -/
lemma add_smul_one_bounded (h : UniformlyEllipticOn Ω a lam Lam) {c : X → ℝ} {Mu : ℝ}
    (hMu_nonneg : 0 ≤ Mu) (hMu_lt : Mu < lam) (hc_abs : ∀ ⦃x⦄, x ∈ Ω → |c x| ≤ Mu) :
    UniformlyEllipticOn Ω (fun x => a x + c x • (1 : Matrix n n ℝ)) (lam - Mu)
      (Lam + Mu) :=
  h.add_bounded hMu_nonneg hMu_lt
    (fun {_} hx η ξ => abs_dotProduct_smul_one_mulVec_le_of_abs_le (hc_abs hx) η ξ)

/-- Adding a constant bounded scalar multiple of the identity preserves uniform ellipticity
after reducing the lower ellipticity constant by the absolute value bound. -/
lemma add_const_smul_one_bounded (h : UniformlyEllipticOn Ω a lam Lam) {c Mu : ℝ}
    (hMu_lt : Mu < lam) (hc_abs : |c| ≤ Mu) :
    UniformlyEllipticOn Ω (fun y => a y + c • (1 : Matrix n n ℝ)) (lam - Mu)
      (Lam + Mu) :=
  h.add_smul_one_bounded ((abs_nonneg c).trans hc_abs) hMu_lt (fun {_} _ => hc_abs)

/-- Adding a bounded nonnegative scalar multiple of the identity preserves uniform
ellipticity, with the upper constant increased by the scalar bound. -/
lemma add_smul_one (h : UniformlyEllipticOn Ω a lam Lam) {c : X → ℝ} {Mu : ℝ}
    (hMu : 0 ≤ Mu) (hc_nonneg : ∀ ⦃x⦄, x ∈ Ω → 0 ≤ c x) (hc_upper : ∀ ⦃x⦄, x ∈ Ω → c x ≤ Mu) :
    UniformlyEllipticOn Ω (fun x => a x + c x • (1 : Matrix n n ℝ)) lam (Lam + Mu) := by
  refine h.add_nonneg hMu (fun {x} hx ξ => ?_) (fun {x} hx η ξ => ?_)
  · simp only [toQuadraticForm'_smul_one]
    exact mul_nonneg (hc_nonneg hx) (sq_nonneg ‖ξ‖)
  · have hcx_abs : |c x| ≤ Mu := by
      simpa [abs_of_nonneg (hc_nonneg hx)] using hc_upper hx
    exact abs_dotProduct_smul_one_mulVec_le_of_abs_le hcx_abs η ξ

/-- Adding a constant nonnegative scalar multiple of the identity preserves uniform
ellipticity, with the upper constant increased by that scalar. -/
lemma add_const_smul_one (h : UniformlyEllipticOn Ω a lam Lam) {c : ℝ} (hc : 0 ≤ c) :
    UniformlyEllipticOn Ω (fun x => a x + c • (1 : Matrix n n ℝ)) lam (Lam + c) :=
  h.add_smul_one hc (fun {_} _ => hc) (fun {_} _ => le_rfl)

end UniformlyEllipticOn

variable {Ω : Set X} {a b : X → Matrix n n ℝ}
  {lam Lam : ℝ}

/-- Equal coefficient fields on the domain give equivalent uniform-ellipticity hypotheses. -/
lemma uniformlyEllipticOn_congr (hab : Set.EqOn a b Ω) :
    UniformlyEllipticOn Ω a lam Lam ↔ UniformlyEllipticOn Ω b lam Lam := by
  constructor
  · intro h
    exact h.congr (fun x hx => (hab hx).symm)
  · intro h
    exact h.congr hab

/-- The constant identity coefficient field is uniformly elliptic with any constants
`λ ≤ 1 ≤ Λ` and `0 < λ`. This is the coefficient field of the Laplacian model problem. -/
lemma uniformlyEllipticOn_const_one (Ω : Set X) {lam Lam : ℝ} (hlam : 0 < lam)
    (hlam_one : lam ≤ 1) (hone_Lam : 1 ≤ Lam) :
    UniformlyEllipticOn Ω (fun _ => (1 : Matrix n n ℝ)) lam Lam := by
  refine UniformlyEllipticOn.of_bounds hlam (hlam_one.trans hone_Lam) (fun {x} _ ξ => ?_)
    (fun {x} _ η ξ => ?_)
  · have hnorm : 0 ≤ (‖ξ‖ : ℝ) ^ 2 := sq_nonneg ‖ξ‖
    simp only [toQuadraticForm'_one]
    simpa using mul_le_mul_of_nonneg_right hlam_one hnorm
  · rw [one_mulVec]
    calc
      |η ⬝ᵥ ξ| ≤ ‖η‖ * ‖ξ‖ := by
        simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
          abs_real_inner_le_norm η ξ
      _ ≤ Lam * ‖η‖ * ‖ξ‖ := by
        have hnorm : 0 ≤ ‖η‖ * ‖ξ‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right hone_Lam hnorm

/-- In particular, the identity coefficient field is uniformly elliptic with constants
`λ = Λ = 1`. -/
lemma uniformlyEllipticOn_const_one_one (Ω : Set X) :
    UniformlyEllipticOn Ω (fun _ => (1 : Matrix n n ℝ)) 1 1 :=
  uniformlyEllipticOn_const_one Ω zero_lt_one le_rfl le_rfl

/-- A constant matrix with quadratic form bounded below by `λ ‖ξ‖²` is uniformly elliptic, with
upper constant the larger of `λ` and the operator norm of its bilinear form. -/
lemma uniformlyEllipticOn_const (Ω : Set X) {A : Matrix n n ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ (A *ᵥ ξ)) :
    UniformlyEllipticOn Ω (fun _ => A) lam (max lam ‖matrixBilinearForm A‖) :=
  UniformlyEllipticOn.of_bounds hlam (le_max_left _ _)
    (fun _ _ ξ => by simpa [Matrix.toQuadraticForm'_apply] using hA ξ)
    (fun _ _ η ξ => by
      simpa [Real.norm_eq_abs] using (matrixBilinearForm A).le_of_opNorm₂_le_of_le
        (le_max_right lam _) le_rfl le_rfl)

/-- A constant coefficient field uniformly elliptic on a nonempty set is uniformly elliptic on
every set. -/
lemma UniformlyEllipticOn.const_of_mem {A : Matrix n n ℝ}
    (h : UniformlyEllipticOn Ω (fun _ => A) lam Lam) {x : X} (hx : x ∈ Ω) (S : Set X) :
    UniformlyEllipticOn S (fun _ => A) lam Lam :=
  uniformlyEllipticOn_iff.2 ⟨h.pos, h.le, fun _ _ => (uniformlyEllipticOn_iff.1 h).2.2 hx⟩

/-- An isotropic scalar coefficient field is uniformly elliptic when its scalar coefficient
lies between the lower and upper constants.

This packages the common model `a(x) = c(x) I`: if `λ ≤ c x ≤ Λ` on `Ω`, then `c x • 1`
satisfies the lower quadratic bound and the bilinear upper bound with constants `λ` and `Λ`. -/
lemma uniformlyEllipticOn_smul_one (Ω : Set X) (c : X → ℝ) {lam Lam : ℝ}
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hbound : ∀ ⦃x⦄, x ∈ Ω → lam ≤ c x ∧ c x ≤ Lam) :
    UniformlyEllipticOn Ω (fun x => c x • (1 : Matrix n n ℝ)) lam Lam := by
  refine UniformlyEllipticOn.of_bounds hlam hlamLam (fun {x} hx ξ => ?_)
    (fun {x} hx η ξ => ?_)
  · simp only [toQuadraticForm'_smul_one]
    exact mul_le_mul_of_nonneg_right (hbound hx).1 (sq_nonneg ‖ξ‖)
  · have hcx_nonneg : 0 ≤ c x := hlam.le.trans (hbound hx).1
    have hcx_abs : |c x| ≤ Lam := by simpa [abs_of_nonneg hcx_nonneg] using (hbound hx).2
    exact abs_dotProduct_smul_one_mulVec_le_of_abs_le hcx_abs η ξ

/-- A constant positive isotropic coefficient field is uniformly elliptic with matching
lower and upper constants. -/
lemma uniformlyEllipticOn_const_smul_one_self (Ω : Set X) {c : ℝ} (hc : 0 < c) :
    UniformlyEllipticOn Ω (fun _ => c • (1 : Matrix n n ℝ)) c c :=
  uniformlyEllipticOn_smul_one Ω (fun _ => c) hc le_rfl (fun {_} _ => ⟨le_rfl, le_rfl⟩)

/-- A constant isotropic coefficient field is uniformly elliptic for any explicit constants
`λ ≤ c ≤ Λ` with `0 < λ`. -/
lemma uniformlyEllipticOn_const_smul_one (Ω : Set X) {c lam Lam : ℝ} (hlam : 0 < lam)
    (hlamc : lam ≤ c) (hcLam : c ≤ Lam) :
    UniformlyEllipticOn Ω (fun _ => c • (1 : Matrix n n ℝ)) lam Lam :=
  uniformlyEllipticOn_smul_one Ω (fun _ => c) hlam (hlamc.trans hcLam)
    (fun {_} _ => ⟨hlamc, hcLam⟩)

/-- **Interpolating two uniformly elliptic fields.** Let `a` be uniformly elliptic on `Ω` and `b`
on the whole space, with the same constants `λ, Λ`, and let `χ` take values in `[0, 1]` and vanish
off `Ω`. Then `χ a + (1 - χ) b` is uniformly elliptic on the whole space with the same constants.

It agrees with `a` where `χ = 1`, so this extends a coefficient field given on `Ω` to the whole
space without changing it near a compact subset of `Ω`. -/
lemma UniformlyEllipticOn.smul_add_one_sub_smul (ha : UniformlyEllipticOn Ω a lam Lam)
    (hb : UniformlyEllipticOn Set.univ b lam Lam) {χ : X → ℝ} (hχ : ∀ x, χ x ∈ Set.Icc 0 1)
    (hχΩ : ∀ x ∉ Ω, χ x = 0) :
    UniformlyEllipticOn Set.univ (fun x => χ x • a x + (1 - χ x) • b x) lam Lam := by
  refine UniformlyEllipticOn.of_bounds ha.pos ha.le (fun {x} _ ξ => ?_) (fun {x} _ η ξ => ?_)
  · -- Off `Ω` the weight `χ x` vanishes, so the bound for `a` is only needed on `Ω`.
    have hA : χ x * (lam * ‖ξ‖ ^ 2) ≤ χ x * (a x).toQuadraticForm' ξ := by
      by_cases hx : x ∈ Ω
      · exact mul_le_mul_of_nonneg_left (ha.lower_bound hx ξ) (hχ x).1
      · simp [hχΩ x hx]
    have hB := mul_le_mul_of_nonneg_left (hb.lower_bound (Set.mem_univ x) ξ)
      (sub_nonneg.2 (hχ x).2)
    rw [toQuadraticForm'_add, _root_.add_apply, toQuadraticForm'_smul,
      toQuadraticForm'_smul]
    simp only [_root_.smul_apply, smul_eq_mul]
    linarith
  · have hA : χ x * |η ⬝ᵥ (a x *ᵥ ξ)| ≤ χ x * (Lam * ‖η‖ * ‖ξ‖) := by
      by_cases hx : x ∈ Ω
      · exact mul_le_mul_of_nonneg_left (ha.upper_bound hx η ξ) (hχ x).1
      · simp [hχΩ x hx]
    have hB := mul_le_mul_of_nonneg_left (hb.upper_bound (Set.mem_univ x) η ξ)
      (sub_nonneg.2 (hχ x).2)
    rw [add_mulVec, smul_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul,
      smul_eq_mul, smul_eq_mul]
    calc |χ x * (η ⬝ᵥ (a x *ᵥ ξ)) + (1 - χ x) * (η ⬝ᵥ (b x *ᵥ ξ))|
        ≤ χ x * |η ⬝ᵥ (a x *ᵥ ξ)| + (1 - χ x) * |η ⬝ᵥ (b x *ᵥ ξ)| := by
          refine (abs_add_le _ _).trans_eq ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (hχ x).1, abs_of_nonneg (sub_nonneg.2 (hχ x).2)]
      _ ≤ Lam * ‖η‖ * ‖ξ‖ := by linarith

/-! ### Gradient calculus and orthonormal expansion -/

section Calculus

open Set TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace NNReal

variable {n : Type*} [Fintype n]

/-- A matrix bilinear form evaluated at the `i`-th standard basis vector in its first argument
is the contraction of the `i`-th row with the second argument. -/
theorem matrixBilinearForm_basisFun_left {A : Matrix n n ℝ} (i : n)
    (ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm A (EuclideanSpace.basisFun n ℝ i) ξ =
      ∑ j, A i j * ⟪ξ, EuclideanSpace.basisFun n ℝ j⟫_ℝ := by
  classical
  simp only [EuclideanSpace.inner_basisFun_real]
  simp [matrixBilinearForm_apply, dotProduct, Matrix.mulVec, EuclideanSpace.basisFun_apply,
    PiLp.single_apply]

/-- Expanding the first argument of a matrix bilinear form in an orthonormal basis. -/
theorem sum_inner_mul_matrixBilinearForm {A : Matrix n n ℝ} (ξ η : EuclideanSpace ℝ n) :
    ∑ i, ⟪ξ, EuclideanSpace.basisFun n ℝ i⟫_ℝ *
        matrixBilinearForm A (EuclideanSpace.basisFun n ℝ i) η = matrixBilinearForm A ξ η := by
  conv_rhs => rw [← (EuclideanSpace.basisFun n ℝ).sum_repr' ξ]
  simp [map_sum, map_smul]

/-- Expanding the second argument of a matrix bilinear form in the standard basis:
`ηᵀ A ξ = ∑ⱼ ⟪η, cⱼ⟫ ξⱼ`, where `cⱼ = Aᵀ j` is the `j`-th column of `A`. -/
theorem matrixBilinearForm_eq_sum_inner_transpose (A : Matrix n n ℝ) (η ξ : EuclideanSpace ℝ n) :
    matrixBilinearForm A η ξ =
      ∑ j, ⟪η, WithLp.toLp 2 (Aᵀ j)⟫_ℝ * ⟪ξ, EuclideanSpace.basisFun n ℝ j⟫_ℝ := by
  classical
  simp only [EuclideanSpace.inner_basisFun_real]
  simp only [matrixBilinearForm_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Matrix.transpose_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The conormal component obtained by applying a matrix bilinear form to a smooth gradient is
smooth. -/
theorem contDiff_matrixBilinearForm_gradient {A : Matrix n n ℝ}
    {ψ : EuclideanSpace ℝ n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (η : EuclideanSpace ℝ n) :
    ContDiff ℝ ∞ (fun y => matrixBilinearForm A η (∇ ψ y)) :=
  (matrixBilinearForm A η).contDiff.comp (hψ.gradient_right (m := ∞) (by simp))

/-- **`Cᵏ` coefficient fields give `Cᵏ` bilinear forms.** If the entries of `a` are `Cᵏ`, then
`x ↦ η(x)ᵀ a(x) ξ(x)` is `Cᵏ` for `Cᵏ` vector fields `η` and `ξ`. -/
theorem contDiff_matrixBilinearForm_apply {k : WithTop ℕ∞}
    {a : EuclideanSpace ℝ n → Matrix n n ℝ} (ha : ∀ i j, ContDiff ℝ k fun x => a x i j)
    {η ξ : EuclideanSpace ℝ n → EuclideanSpace ℝ n} (hη : ContDiff ℝ k η) (hξ : ContDiff ℝ k ξ) :
    ContDiff ℝ k fun x => matrixBilinearForm (a x) (η x) (ξ x) := by
  simp only [matrixBilinearForm_apply, dotProduct, Matrix.mulVec]
  exact ContDiff.sum fun i _ => (contDiff_euclidean.1 hη i).mul
    (ContDiff.sum fun j _ => (ha i j).mul (contDiff_euclidean.1 hξ j))

/-- **`C¹` coefficient fields have locally Lipschitz bilinear forms.** If the entries of `a` are
continuously differentiable on an open set `s`, then `x ↦ (η, ξ ↦ ηᵀ a(x) ξ)` is locally Lipschitz
on `s` in the operator norm. -/
theorem locallyLipschitzOn_matrixBilinearForm_of_contDiffOn {a : EuclideanSpace ℝ n → Matrix n n ℝ}
    {s : Set (EuclideanSpace ℝ n)} (hs : IsOpen s)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) s) :
    LocallyLipschitzOn s fun x => matrixBilinearForm (a x) := by
  intro x hx
  -- Near `x` each entry is Lipschitz, and the operator norm is at most the sum of the entries.
  choose K t ht hKt using fun i j =>
    ((ha i j).contDiffAt (hs.mem_nhds hx)).exists_lipschitzOnWith
  refine ⟨∑ i, ∑ j, K i j, ⋂ i, ⋂ j, t i j,
    mem_nhdsWithin_of_mem_nhds (Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 (ht i)), ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
  simp only [mem_iInter] at hy hz
  rw [dist_eq_norm, ← matrixBilinearForm_sub]
  refine (norm_matrixBilinearForm_le_sum_abs _).trans ?_
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.sub_apply, ← Real.dist_eq]
  exact (hKt i j).dist_le_mul y (hy i j) z (hz i j)

/-- **Hölder entries give a Hölder bilinear form.** If every entry of a coefficient field `a` is
`α`-Hölder on `s` with constant `L i j`, then `x ↦ (η, ξ ↦ ηᵀ a(x) ξ)` is `α`-Hölder on `s` in the
operator norm, with constant `∑ᵢⱼ L i j`. -/
theorem holderOnWith_matrixBilinearForm_of_forall {X : Type*} [PseudoMetricSpace X]
    {a : X → Matrix n n ℝ} {s : Set X} {α : ℝ≥0} {L : n → n → ℝ≥0}
    (ha : ∀ i j, HolderOnWith (L i j) α (fun x => a x i j) s) :
    HolderOnWith (∑ i, ∑ j, L i j) α (fun x => matrixBilinearForm (a x)) s := by
  refine HolderOnWith.of_dist_le fun x hx y hy => ?_
  rw [dist_eq_norm, ← matrixBilinearForm_sub]
  refine (norm_matrixBilinearForm_le_sum_abs _).trans ?_
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.sub_apply, ← Real.dist_eq]
  exact (ha i j).dist_le hx hy

/-- **Lipschitz entries give a Lipschitz bilinear form.** If every entry of a coefficient field `a`
is Lipschitz with constant `L i j`, then `x ↦ (η, ξ ↦ ηᵀ a(x) ξ)` is Lipschitz in the operator
norm, with constant `∑ᵢⱼ L i j`. -/
theorem lipschitzWith_matrixBilinearForm_of_forall {X : Type*} [PseudoMetricSpace X]
    {a : X → Matrix n n ℝ} {L : n → n → ℝ≥0}
    (ha : ∀ i j, LipschitzWith (L i j) fun x => a x i j) :
    LipschitzWith (∑ i, ∑ j, L i j) fun x => matrixBilinearForm (a x) := by
  refine LipschitzWith.of_dist_le_mul fun y z => ?_
  rw [dist_eq_norm, ← matrixBilinearForm_sub]
  refine (norm_matrixBilinearForm_le_sum_abs _).trans ?_
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.sub_apply, ← Real.dist_eq]
  exact (ha i j).dist_le_mul y z

/-- **`C¹` coefficient fields have Hölder bilinear forms on compact sets.** If the entries of `a`
are continuously differentiable on an open set `s`, then on every compact `S ⊆ s` the map
`x ↦ (η, ξ ↦ ηᵀ a(x) ξ)` is `α`-Hölder in the operator norm for every `α ≤ 1`. -/
theorem exists_holderOnWith_matrixBilinearForm_of_contDiffOn
    {a : EuclideanSpace ℝ n → Matrix n n ℝ} {s : Set (EuclideanSpace ℝ n)} (hs : IsOpen s)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) s) {S : Set (EuclideanSpace ℝ n)}
    (hS : IsCompact S) (hSs : S ⊆ s) {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ K : ℝ≥0, HolderOnWith K α (fun x => matrixBilinearForm (a x)) S :=
  (locallyLipschitzOn_matrixBilinearForm_of_contDiffOn hs ha).exists_holderOnWith_of_isCompact
    hα hS hSs

/-- The coefficients `x ↦ ⟪p, a(x) q⟫` of a coefficient field that is `K`-Lipschitz on `s` as a
bilinear form are `K ‖p‖ ‖q‖`-Lipschitz on `s`. -/
theorem lipschitzOnWith_matrixBilinearForm_apply_apply {X : Type*} [PseudoEMetricSpace X]
    {a : X → Matrix n n ℝ} {s : Set X} {K : ℝ≥0}
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) s)
    (p q : EuclideanSpace ℝ n) :
    LipschitzOnWith (K * ‖p‖₊ * ‖q‖₊) (fun x => matrixBilinearForm (a x) p q) s := by
  -- This is `x ↦ a x` followed by evaluation at `p` and then at `q`.
  have h := ((ContinuousLinearMap.lipschitzWith_apply q).comp
    (ContinuousLinearMap.lipschitzWith_apply p)).comp_lipschitzOnWith hK
  have hc : ‖q‖₊ * ‖p‖₊ * K = K * ‖p‖₊ * ‖q‖₊ := by ring
  rwa [hc] at h

/-- If `a` is uniformly elliptic on `s` with lower constant `λ` and `x ↦ a(x)` is `K`-Lipschitz on
`s` as a bilinear form, then for `w ≠ 0` the reciprocal `x ↦ a(x)(w, w)⁻¹` is
`K ‖w‖² / (λ ‖w‖²)²`-Lipschitz on `s`. -/
theorem lipschitzOnWith_inv_matrixBilinearForm_self {X : Type*} [PseudoMetricSpace X]
    [DecidableEq n] {a : X → Matrix n n ℝ} {s : Set X} {K : ℝ≥0} {lam Lam : ℝ}
    (ha : UniformlyEllipticOn s a lam Lam)
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) s)
    {w : EuclideanSpace ℝ n} (hw : w ≠ 0) :
    LipschitzOnWith (K * ‖w‖₊ * ‖w‖₊ / (lam * ‖w‖ ^ 2).toNNReal ^ 2)
      (fun x => (matrixBilinearForm (a x) w w)⁻¹) s := by
  have hm : 0 < lam * ‖w‖ ^ 2 := mul_pos ha.pos (pow_pos (norm_pos_iff.2 hw) 2)
  refine (lipschitzOnWith_matrixBilinearForm_apply_apply hK w w).inv_of_le_norm
    (Real.toNNReal_pos.2 hm) fun x hx => ?_
  rw [Real.coe_toNNReal _ hm.le, matrixBilinearForm_self]
  exact (ha.lower_bound hx w).trans (Real.le_norm_self _)

/-- If `a` is uniformly elliptic on `s` with lower constant `λ`, then on `s` the reciprocal of the
quadratic form `a(x)(w, w)` is bounded by `(λ ‖w‖²)⁻¹`. -/
theorem norm_inv_matrixBilinearForm_self_le {X : Type*} [DecidableEq n] {a : X → Matrix n n ℝ}
    {s : Set X} {lam Lam : ℝ} (ha : UniformlyEllipticOn s a lam Lam) {x : X} (hx : x ∈ s)
    (w : EuclideanSpace ℝ n) :
    ‖(matrixBilinearForm (a x) w w)⁻¹‖ ≤ (lam * ‖w‖ ^ 2)⁻¹ := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hm : 0 < lam * ‖w‖ ^ 2 := mul_pos ha.pos (pow_pos (norm_pos_iff.2 hw) 2)
  have hcm : lam * ‖w‖ ^ 2 ≤ matrixBilinearForm (a x) w w := by
    simpa only [matrixBilinearForm_self] using ha.lower_bound hx w
  rw [Real.norm_eq_abs, abs_inv, abs_of_pos (hm.trans_le hcm)]
  exact inv_anti₀ hm hcm

/-- **A field that is Lipschitz on a set extends to a Lipschitz field on the whole space.** If
`x ↦ a x` is Lipschitz on `S` in the operator norm of its bilinear forms, then `a` agrees on `S`
with a field `abar` on the whole space whose bilinear forms are Lipschitz, with some constant
`K'`. -/
theorem exists_lipschitzWith_matrixBilinearForm_eqOn {X : Type*} [PseudoMetricSpace X]
    {a : X → Matrix n n ℝ} {K : ℝ≥0} {S : Set X}
    (hK : LipschitzOnWith K (fun x => matrixBilinearForm (a x)) S) :
    ∃ (abar : X → Matrix n n ℝ) (K' : ℝ≥0), EqOn abar a S ∧
      LipschitzWith K' (fun x => matrixBilinearForm (abar x)) := by
  classical
  -- Extend the entries of `a` from `S` to Lipschitz functions on the whole space.
  have hent : ∀ i j, LipschitzOnWith (K * ‖EuclideanSpace.single i (1 : ℝ)‖₊ *
      ‖EuclideanSpace.single j (1 : ℝ)‖₊) (fun x => a x i j) S := fun i j => by
    simpa [matrixBilinearForm_apply] using lipschitzOnWith_matrixBilinearForm_apply_apply hK
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j 1)
  choose g hgL hgS using fun i j => (hent i j).extend_real
  have habar : EqOn (fun x => Matrix.of fun i j => g i j x) a S := fun x hx => by
    ext i j
    exact (hgS i j hx).symm
  -- The bilinear forms of `ā` are Lipschitz, with the sum of the entrywise constants.
  exact ⟨_, _, habar, lipschitzWith_matrixBilinearForm_of_forall (a := fun x => Matrix.of
    fun i j => g i j x) hgL⟩

/-- The conormal component of a gradient, for a possibly variable coefficient field, is
supported where the function is. -/
theorem tsupport_matrixBilinearForm_gradient_subset {a : EuclideanSpace ℝ n → Matrix n n ℝ}
    (ψ : EuclideanSpace ℝ n → ℝ) (η : EuclideanSpace ℝ n) :
    tsupport (fun y => matrixBilinearForm (a y) η (∇ ψ y)) ⊆ tsupport ψ :=
  closure_minimal (fun x hx => by_contra fun hxψ => hx (by
    simp [gradient_of_notMem_tsupport hxψ])) (isClosed_tsupport ψ)

end Calculus

/-- The contraction `∑ᵢⱼ Mᵢⱼ ⟪H eᵢ, eⱼ⟫` of an endomorphism `H` of `ℝᵐ` with a matrix `M` is at
most `m ‖M‖ ‖H‖` in absolute value, where `‖M‖` is the operator norm of the bilinear form
`(η, ξ) ↦ ηᵀ M ξ` and `‖H‖` that of `H`. -/
theorem _root_.Matrix.abs_contraction_le_mul_norm_matrixBilinearForm_mul_norm {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ)
    (H : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    |Matrix.contraction M H| ≤ m * ‖matrixBilinearForm M‖ * ‖H‖ := by
  have h : Matrix.contraction M H = ∑ i, matrixBilinearForm M (EuclideanSpace.single i 1)
      (H (EuclideanSpace.single i 1)) := by
    simp [Matrix.mulVec, dotProduct, EuclideanSpace.inner_single_right]
  rw [h]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |matrixBilinearForm M (EuclideanSpace.single i 1) (H (EuclideanSpace.single i 1))|
      ≤ ∑ _i : Fin m, ‖matrixBilinearForm M‖ * ‖H‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine ((matrixBilinearForm M).le_opNorm₂ _ _).trans ?_
        simp only [PiLp.norm_single, norm_one, mul_one]
        refine mul_le_mul_of_nonneg_left ((H.le_opNorm _).trans ?_) (by positivity)
        simp
    _ = m * ‖matrixBilinearForm M‖ * ‖H‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end PDE

end TauCeti

namespace Continuous

variable {n : Type*} [Fintype n]
variable {X : Type*} [TopologicalSpace X]

/-- A continuous principal coefficient field gives a continuous field of principal bilinear
forms. -/
lemma matrixBilinearForm {a : X → Matrix n n ℝ} (ha : Continuous a) :
    Continuous (fun x => TauCeti.PDE.matrixBilinearForm (a x)) :=
  TauCeti.PDE.continuous_matrixBilinearForm.comp ha

end Continuous

namespace ContinuousOn

variable {n : Type*} [Fintype n]
variable {X : Type*} [TopologicalSpace X]

/-- A continuous principal coefficient field on a set gives a continuous field of principal
bilinear forms on that set. -/
lemma matrixBilinearForm {s : Set X} {a : X → Matrix n n ℝ} (ha : ContinuousOn a s) :
    ContinuousOn (fun x => TauCeti.PDE.matrixBilinearForm (a x)) s :=
  TauCeti.PDE.continuous_matrixBilinearForm.comp_continuousOn ha

end ContinuousOn
