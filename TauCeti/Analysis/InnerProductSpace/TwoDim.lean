/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Topology.Algebra.Module.Determinant
public import TauCeti.Analysis.InnerProductSpace.Orientation
import Mathlib.Analysis.InnerProductSpace.Trace
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.InnerProductSpace.StrictCauchySchwarz
import TauCeti.LinearAlgebra.Matrix.Alternating.Basic
import TauCeti.LinearAlgebra.Matrix.Determinant.Skew

/-!
# Oriented Euclidean planes

The quarter turn `J = o.rightAngleRotation` of an oriented Euclidean plane carries the first vector
of every positively oriented orthonormal basis `(e₀, e₁)` to the second, `J e₀ = e₁`, and hence
`J e₁ = -e₀`. So in any such basis `J` is the standard quarter turn,
`J z = ⟪z, e₀⟫ e₁ - ⟪z, e₁⟫ e₀` (`Orientation.rightAngleRotation_eq_inner_smul_sub_inner_smul`).
The area form `ω(x, y)` is nonzero exactly when `x` is nonzero and `y` is not a multiple of `x`
(`Orientation.areaForm_ne_zero_iff`).

For unit vectors `a`, `b` the inner product and the area form `ω` are the cosine and the sine of
the angle from `a` to `b`: `√(1 - ⟪a, b⟫²) = |ω(a, b)|`, so `⟪a, b⟫ ∈ (-1, 1)` whenever
`ω(a, b) ≠ 0`.

For a unit vector `e`, the pair `(e, J e)` is a positively oriented orthonormal frame. Every vector
expands in it (`Orientation.eq_inner_smul_add_inner_smul`), an operator is determined by its matrix
entries in it (`Orientation.ext_inner_frame`), and the trace is the sum of its diagonal entries
(`Orientation.trace_eq_inner_add_inner`). The quarter turn is trace-free
(`Orientation.trace_rightAngleRotation`), and every operator `A` satisfies
`J A + A† J = (trace A) J` (`Orientation.rightAngleRotation_comp_add_adjoint_comp`).

On the complex plane, the continuous oriented volume form is normalized on the standard complex
basis `(1, I)`. On a pair of vectors it is the area form `dx ∧ dy`, `(v, w) ↦ Im (conj v * w)`, and
every real two-form on `ℂ` is a multiple of it
(`ContinuousAlternatingMap.apply_eq_apply_one_I_mul_im`). So multiplying both vectors by `c`
scales it by `|c|²` (`ContinuousAlternatingMap.apply_mul_mul`); in particular it is invariant under
multiplication by `I` (`ContinuousAlternatingMap.apply_I_mul_I_mul`).

An orthonormal basis `b` of a Euclidean plane identifies the plane with `ℂ` by
`Complex.isometryOfOrthonormal b`, and the complex coordinate so defined carries the orientation of
`b` to the standard orientation of `ℂ` (`Complex.map_isometryOfOrthonormal_symm_orientation`). This
is the hypothesis under which Mathlib computes the area form, the quarter turn, the Kähler form,
the oriented angle and the rotations of an oriented plane in a complex coordinate
(`Orientation.areaForm_map_complex`, `Orientation.rightAngleRotation_map_complex`,
`Orientation.kahler_map_complex`, `Orientation.oangle_map_complex`,
`Orientation.rotation_map_complex`).

Congruence by an operator `T` multiplies a skew-adjoint operator `A` of a Euclidean plane by the
determinant, `T A T⋆ = det T • A` (`ContinuousLinearMap.mul_mul_star_eq_det_smul`). In an
orthonormal basis this is the identity `M S Mᵀ = det M • S` for `2 × 2` skew-symmetric matrices
(`Matrix.mul_mul_transpose_eq_det_smul_of_transpose_eq_neg_of_diag_eq_zero`). So an orthogonal
transformation commutes with every skew-adjoint operator when it preserves the orientation and
anticommutes with it when it reverses the orientation.
-/

public section

open ComplexConjugate

noncomputable section

namespace Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 2)]
  (o : Orientation ℝ E (Fin 2)) {b : OrthonormalBasis (Fin 2) ℝ E}

/-- The quarter turn of an oriented plane carries the first vector of a positively oriented
orthonormal basis to the second. -/
theorem rightAngleRotation_basis_zero (hb : b.toBasis.orientation = o) :
    o.rightAngleRotation (b 0) = b 1 := by
  have hω : o.areaForm (b 0) (b 1) = 1 := by
    have h : ![b 0, b 1] = b.toBasis := by
      ext i
      fin_cases i <;> simp
    rw [areaForm_to_volumeForm, o.volumeForm_robust b hb, h, Module.Basis.det_self]
  rw [← b.sum_repr' (o.rightAngleRotation (b 0)), Fin.sum_univ_two]
  simp [inner_rightAngleRotation_right, o.areaForm_swap (b 1), hω]

/-- The quarter turn of an oriented plane carries the second vector of a positively oriented
orthonormal basis to the negative of the first. -/
theorem rightAngleRotation_basis_one (hb : b.toBasis.orientation = o) :
    o.rightAngleRotation (b 1) = -b 0 := by
  rw [← o.rightAngleRotation_basis_zero hb, rightAngleRotation_rightAngleRotation]

/-- In a positively oriented orthonormal basis `(e₀, e₁)`, the quarter turn of an oriented plane
is `z ↦ ⟪z, e₀⟫ e₁ - ⟪z, e₁⟫ e₀`. -/
theorem rightAngleRotation_eq_inner_smul_sub_inner_smul (hb : b.toBasis.orientation = o)
    (z : E) : o.rightAngleRotation z = inner ℝ z (b 0) • b 1 - inner ℝ z (b 1) • b 0 := by
  conv_lhs => rw [← b.sum_repr' z, Fin.sum_univ_two]
  simp [o.rightAngleRotation_basis_zero hb, o.rightAngleRotation_basis_one hb,
    real_inner_comm z, sub_eq_add_neg]

/-- In an oriented plane, `o.areaForm a x = 0` implies the scaled identity
`‖a‖ ^ 2 • x = ⟪a, x⟫ • a`, including when `a = 0`. -/
theorem sq_norm_smul_eq_of_areaForm_eq_zero {a x : E} (h : o.areaForm a x = 0) :
    ‖a‖ ^ 2 • x = inner ℝ a x • a := by
  refine ext_inner_right ℝ fun y ↦ ?_
  rw [real_inner_smul_left, real_inner_smul_left, ← o.inner_mul_inner_add_areaForm_mul_areaForm,
    h, zero_mul, add_zero]

/-- The area form `ω(x, y)` is nonzero exactly when `x` is nonzero and `y` is not a multiple of
`x`. -/
theorem areaForm_ne_zero_iff {x y : E} :
    o.areaForm x y ≠ 0 ↔ x ≠ 0 ∧ ∀ c : ℝ, y ≠ c • x := by
  rw [← TauCeti.abs_real_inner_lt_norm_iff,
    ← pow_lt_pow_iff_left₀ (abs_nonneg _) (by positivity) two_ne_zero, sq_abs, mul_pow,
    ← o.inner_sq_add_areaForm_sq x y, lt_add_iff_pos_right, sq_pos_iff]

/-- For unit vectors `a`, `b` of an oriented plane, `√(1 - ⟪a, b⟫²) = |ω(a, b)|`: the inner
product and the area form are the cosine and the sine of the angle from `a` to `b`. -/
theorem sqrt_one_sub_inner_sq_eq_abs_areaForm {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    √(1 - inner ℝ a b ^ 2) = |o.areaForm a b| := by
  have h := o.inner_sq_add_areaForm_sq a b
  rw [ha, hb, one_pow, one_mul] at h
  rw [← Real.sqrt_sq_eq_abs, ← h, add_sub_cancel_left]

/-- Two unit vectors of an oriented plane with nonzero area form are not parallel, so their inner
product lies in `(-1, 1)`. -/
theorem inner_mem_Ioo_of_areaForm_ne_zero {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (h : o.areaForm a b ≠ 0) : inner ℝ a b ∈ Set.Ioo (-1) 1 := by
  have hsq := o.inner_sq_add_areaForm_sq a b
  rw [ha, hb, one_pow, one_mul] at hsq
  have hlt : inner ℝ a b ^ 2 < 1 := by nlinarith [sq_pos_of_ne_zero h]
  exact abs_lt.1 ((sq_lt_one_iff_abs_lt_one _).1 hlt)

section Frame

open Module
open scoped InnerProductSpace

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

local notation "J" => o.rightAngleRotation

/-- The trace in the positively oriented orthonormal frame `(e, J e)` of an oriented plane:
`trace T = ⟪e, T e⟫ + ⟪J e, T (J e)⟫`. -/
theorem trace_eq_inner_add_inner {e : E} (he : ‖e‖ = 1) (T : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E T = ⟪e, T e⟫_ℝ + ⟪J e, T (J e)⟫_ℝ := by
  have hon : Orthonormal ℝ ![e, J e] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [he]
  let b : OrthonormalBasis (Fin 2) ℝ E :=
    (o.basisRightAngleRotation e (by rintro rfl; simp at he)).toOrthonormalBasis
      (by simpa using hon)
  rw [LinearMap.trace_eq_sum_inner _ b, Fin.sum_univ_two]
  simp [b]

/-- Two linear maps of an oriented plane agree once their matrix entries in the frame `(e, J e)`
agree, for any nonzero `e`. -/
theorem ext_inner_frame {e : E} (he : e ≠ 0) {X Y : E →ₗ[ℝ] E}
    (h : ∀ v ∈ ({e, J e} : Set E), ∀ w ∈ ({e, J e} : Set E), ⟪X v, w⟫_ℝ = ⟪Y v, w⟫_ℝ) :
    X = Y := by
  set b := o.basisRightAngleRotation e he
  refine b.ext fun i ↦ InnerProductSpace.ext_inner_right_basis b fun j ↦ ?_
  have hb : ∀ k, b k ∈ ({e, J e} : Set E) := fun k ↦ by fin_cases k <;> simp [b]
  exact h _ (hb i) _ (hb j)

/-- Every vector of an oriented plane expands in the positively oriented orthonormal frame
`(e, J e)`: `v = ⟪e, v⟫ e + ⟪J e, v⟫ J e`. -/
theorem eq_inner_smul_add_inner_smul {e : E} (he : ‖e‖ = 1) (v : E) :
    v = ⟪e, v⟫_ℝ • e + ⟪J e, v⟫_ℝ • J e := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  refine InnerProductSpace.ext_inner_left_basis (o.basisRightAngleRotation e he0) fun i ↦ ?_
  fin_cases i <;>
    simp [inner_add_right, inner_smul_right, he, real_inner_comm e]

/-- The quarter turn of an oriented plane is trace-free. -/
theorem trace_rightAngleRotation :
    LinearMap.trace ℝ E ((J : E →L[ℝ] E) : E →ₗ[ℝ] E) = 0 := by
  simp [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E)]

/-- In an oriented plane, `J A + A† J = (trace A) J` for every operator `A`. -/
theorem rightAngleRotation_comp_add_adjoint_comp (A : E →L[ℝ] E) :
    (J : E →L[ℝ] E) ∘L A + ContinuousLinearMap.adjoint A ∘L (J : E →L[ℝ] E) =
      LinearMap.trace ℝ E (A : E →ₗ[ℝ] E) • (J : E →L[ℝ] E) := by
  obtain ⟨e, he⟩ : ∃ e : E, ‖e‖ = 1 :=
    ⟨_, (o.finOrthonormalBasis two_pos Fact.out).orthonormal.1 0⟩
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  rw [o.trace_eq_inner_add_inner he]
  obtain ⟨a, c, h₁⟩ : ∃ a c : ℝ, A e = a • e + c • J e :=
    ⟨_, _, o.eq_inner_smul_add_inner_smul he _⟩
  obtain ⟨b, d, h₂⟩ : ∃ b d : ℝ, A (J e) = b • e + d • J e :=
    ⟨_, _, o.eq_inner_smul_add_inner_smul he _⟩
  refine ContinuousLinearMap.coe_injective (o.ext_inner_frame he0 ?_)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  simp [ContinuousLinearMap.adjoint_inner_left, h₁, h₂, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, he, real_inner_comm e (J e)]

end Frame

end Orientation

namespace Complex

/-- The complex coordinate of a Euclidean plane given by an orthonormal basis `b`, the inverse of
`Complex.isometryOfOrthonormal b`, carries the orientation of `b` to the standard orientation of
`ℂ`. -/
theorem map_isometryOfOrthonormal_symm_orientation {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : OrthonormalBasis (Fin 2) ℝ E) :
    Orientation.map (Fin 2) (Complex.isometryOfOrthonormal b).symm.toLinearEquiv
      b.toBasis.orientation = Complex.orientation := by
  rw [← Module.Basis.orientation_map, Complex.orientation]
  congr 1
  ext i
  fin_cases i <;> simp [Complex.isometryOfOrthonormal_symm_apply]

attribute [local instance] Complex.finrank_real_complex_fact

/-- The normalized complex volume form evaluates to one on the basis `(1, I)`. -/
theorem orientation_volumeFormL_one_I :
    Complex.orientation.volumeFormL ![1, I] = 1 := by
  simpa [coe_basisOneI] using
    Complex.orientation.volumeFormL_apply_orthonormal Complex.orthonormalBasisOneI rfl

/-- The continuous volume form of `ℂ` is the area form `dx ∧ dy`: on a pair of vectors `(v, w)` it
is `Im (conj v * w)`. -/
theorem orientation_volumeFormL_apply (v : Fin 2 → ℂ) :
    Complex.orientation.volumeFormL v = (conj (v 0) * v 1).im := by
  rw [Orientation.volumeFormL_apply, ← Complex.areaForm, Orientation.areaForm_to_volumeForm]
  congr 1
  ext i
  fin_cases i <;> rfl

end Complex

namespace ContinuousAlternatingMap

open Complex

/-- Every real two-form on `ℂ` is a multiple of the area form `dx ∧ dy`: on a pair of vectors
`(v, w)` it is its value on the basis `(1, I)` times `Im (conj v * w)`. -/
theorem apply_eq_apply_one_I_mul_im (α : ℂ [⋀^Fin 2]→L[ℝ] ℝ) (v : Fin 2 → ℂ) :
    α v = α ![1, I] * (conj (v 0) * v 1).im := by
  have h := congrArg (· v) (α.toAlternatingMap.eq_smul_basis_det basisOneI)
  simp only [_root_.smul_apply, coe_toAlternatingMap, coe_basisOneI, smul_eq_mul,
    Module.Basis.det_apply, Matrix.det_fin_two, Module.Basis.toMatrix_apply, coe_basisOneI_repr,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [h]
  simp only [mul_im, conj_re, conj_im]
  ring

/-- Multiplying both vectors by `c` scales a real two-form on `ℂ` by `|c|²`:
`α(c u, c v) = |c|² α(u, v)`. -/
theorem apply_mul_mul (α : ℂ [⋀^Fin 2]→L[ℝ] ℝ) (c u v : ℂ) :
    α ![c * u, c * v] = ‖c‖ ^ 2 * α ![u, v] := by
  rw [apply_eq_apply_one_I_mul_im, apply_eq_apply_one_I_mul_im α ![u, v], ← normSq_eq_norm_sq,
    normSq_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_im, mul_re, conj_re, conj_im]
  ring

/-- Every real two-form on `ℂ` is invariant under multiplication by `I`:
`α(I u, I v) = α(u, v)`. -/
@[simp]
theorem apply_I_mul_I_mul (α : ℂ [⋀^Fin 2]→L[ℝ] ℝ) (u v : ℂ) :
    α ![I * u, I * v] = α ![u, v] := by
  rw [apply_mul_mul, norm_I, one_pow, one_mul]

/-- A real two-form on `ℂ` takes the value `α(1, I) |u|²` on the pair `(u, I u)`. -/
theorem apply_I_mul_eq_apply_one_I_mul_norm_sq (α : ℂ [⋀^Fin 2]→L[ℝ] ℝ) (u : ℂ) :
    α ![u, I * u] = α ![1, I] * ‖u‖ ^ 2 := by
  rw [mul_comm I, mul_comm (α _), ← apply_mul_mul, mul_one]

end ContinuousAlternatingMap

namespace ContinuousLinearMap

open Matrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Congruence multiplies a skew-adjoint operator of a Euclidean plane by the determinant.** For
a skew-adjoint operator `A` of a two-dimensional real inner product space and any operator `T`,
`T A T⋆ = det T • A`. In particular an orthogonal transformation commutes with `A` when it
preserves the orientation and anticommutes with it when it reverses the orientation. -/
theorem mul_mul_star_eq_det_smul (hE : Module.finrank ℝ E = 2) {A : E →L[ℝ] E}
    (hA : A ∈ skewAdjoint (E →L[ℝ] E)) (T : E →L[ℝ] E) : T * A * star T = T.det • A := by
  -- Read both sides as matrices in an orthonormal basis, through the star algebra equivalence
  -- `LinearMap.toMatrixOrthonormal`, where `A` becomes a skew-symmetric `2 × 2` matrix.
  let b : OrthonormalBasis (Fin 2) ℝ E := (stdOrthonormalBasis ℝ E).reindex (finCongr hE)
  let φ := LinearMap.toMatrixOrthonormal b
  have hA' : (φ (A : E →ₗ[ℝ] E))ᵀ = -φ (A : E →ₗ[ℝ] E) := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.star_eq_conjTranspose,
      ← map_star φ, ← toLinearMap_star, skewAdjoint.mem_iff.1 hA, toLinearMap_neg, map_neg]
  have hd := Matrix.diag_eq_zero_of_transpose_eq_neg hA' fun x hx ↦ by linarith
  have hT : T.det = (φ T).det := by
    simp [φ, LinearMap.toMatrixOrthonormal_apply, LinearMap.det_toMatrix]
  apply ContinuousLinearMap.coe_injective
  apply EquivLike.injective φ
  simpa only [toLinearMap_mul, toLinearMap_star, toLinearMap_smul, map_mul, map_star, map_smul, hT,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.mul_mul_transpose_eq_det_smul_of_transpose_eq_neg_of_diag_eq_zero (φ T) hA' hd

end ContinuousLinearMap
