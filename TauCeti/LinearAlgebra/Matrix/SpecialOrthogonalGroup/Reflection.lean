/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.Algebra.Polynomial.Laurent
import TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.QuadraticForm
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Generation

/-!
# Reflection matrices for the standard symmetric form

The reflection of `Rⁿ` in the hyperplane orthogonal to a vector `v` has the matrix
`1 - c • vecMulVec v v`, where the scalar `c` satisfies `c * (v ⬝ᵥ v) = 2`. Carrying the scalar
as data rather than as `2 * ⅟(v ⬝ᵥ v)` makes the construction available over any commutative
ring in which the norm of `v` happens to be invertible, makes it visibly natural in the
coefficient ring, and makes the invariance of a reflection under rescaling its vector a
one-line computation: putting `μ²c` on the unscaled-vector side gives the same matrix as
putting `c` on the side whose vector is scaled by `μ`.

Products of two such matrices are exactly the generators of the special orthogonal group
supplied by `TauCeti.closure_reflection_mul_eq_matrixSpecialOrthogonalGroup`, once
`toMatrix'_reflection` identifies the coordinate matrix of the reflection of the standard
quadratic form with `reflectionMatrix`. They are packaged here as `TauCeti.reflectionPair`.

The last and largest section of the file builds one-parameter families joining such a product to
the identity. Over an algebraically closed
field of characteristic different from two, `exists_laurentPath_reflectionMatrix_mul` produces
for every product of two reflections a single special orthogonal matrix over the Laurent
polynomials `K[T;T⁻¹]` together with two units `a` and `b` of `K`, such that specializing the
parameter `T` to `a` gives the identity and specializing it to `b` gives the given product; a
specialization is any `K`-algebra map `K[T;T⁻¹] →ₐ[K] K`, so the units are exactly the
admissible parameter values. The family reflects first in `v` and then in a vector moving
through the plane spanned by `v` and `w`, chosen so that the moving vector has invertible norm
throughout, and the two parameters are those at which the moving vector becomes proportional to
`v`, respectively to `w`. Consuming these families is what proves the special orthogonal group
geometrically connected: an idempotent regular function on the group is constant once right
translation by every rational point fixes it, a point joined to the identity by such a family
fixes every idempotent, and the generation theorem reduces the rational points to be handled to
the products of two reflections.

## Main declarations

* `TauCeti.reflectionMatrix`: the matrix of a reflection, with its normalizing scalar as data.
* `TauCeti.reflectionPair`: the product of two reflections, as a special orthogonal matrix.
* `TauCeti.toMatrix'_reflection`: `reflectionMatrix` is the coordinate matrix of the reflection
  of the standard quadratic form.
* `TauCeti.exists_laurentPath_reflectionMatrix_mul`: over an algebraically closed field of
  characteristic different from two, every product of two reflections is joined to the identity
  by a one-parameter family of special orthogonal matrices over the Laurent polynomials.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
* J. S. Milne, *Algebraic Groups* (2017), §2.3.
-/

public section

namespace TauCeti

open Matrix

universe u v w

variable {n : Type v} [DecidableEq n]
variable {R : Type u} [CommRing R] {S : Type w} [CommRing S]

attribute [local instance] starRingOfComm

/-- The matrix of the reflection of `Rⁿ` in the hyperplane orthogonal to `v`, for a scalar `c`
playing the role of `2 / (v ⬝ᵥ v)`. It is a reflection precisely when `c * (v ⬝ᵥ v) = 2`, which
is not part of the definition. -/
def reflectionMatrix (v : n → R) (c : R) : Matrix n n R := 1 - c • vecMulVec v v

@[simp]
theorem reflectionMatrix_apply (v : n → R) (c : R) (i j : n) :
    reflectionMatrix v c i j = (if i = j then 1 else 0) - c * (v i * v j) := by
  simp [reflectionMatrix, Matrix.one_apply, vecMulVec_apply]

@[simp]
theorem transpose_reflectionMatrix (v : n → R) (c : R) :
    (reflectionMatrix v c)ᵀ = reflectionMatrix v c := by
  simp [reflectionMatrix, Matrix.transpose_sub, Matrix.transpose_smul, transpose_vecMulVec]

/-- Reflection matrices are natural in the coefficient ring. -/
@[simp]
theorem map_reflectionMatrix (f : R →+* S) (v : n → R) (c : R) :
    (reflectionMatrix v c).map f = reflectionMatrix (f ∘ v) (f c) := by
  ext i j
  simp [reflectionMatrix_apply, apply_ite f]

/-- Scaling the vector by `μ` with scalar `c` gives the same matrix as keeping the vector
unchanged and using scalar `μ²c`. -/
theorem reflectionMatrix_smul (v : n → R) (c μ : R) :
    reflectionMatrix (fun i => μ * v i) c = reflectionMatrix v (μ * μ * c) := by
  ext i j
  simp only [reflectionMatrix_apply]
  ring_nf

/-- A reflection matrix is a rank-one perturbation of the identity, so the calculus of
`TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec` applies to it. -/
theorem reflectionMatrix_eq_one_sub_vecMulVec (v : n → R) (c : R) :
    reflectionMatrix v c = 1 - vecMulVec (c • v) v := by
  rw [reflectionMatrix, smul_vecMulVec]

/-- A reflection matrix is an involution. -/
@[simp]
theorem reflectionMatrix_mul_self [Fintype n] {v : n → R} {c : R} (hc : c * (v ⬝ᵥ v) = 2) :
    reflectionMatrix v c * reflectionMatrix v c = 1 := by
  rw [reflectionMatrix_eq_one_sub_vecMulVec,
    one_sub_vecMulVec_mul_self 1 (by rw [dotProduct_smul, smul_eq_mul, hc]; norm_num)]
  module

/-- A reflection matrix is orthogonal. -/
theorem reflectionMatrix_mem_orthogonalGroup [Fintype n] {v : n → R} {c : R}
    (hc : c * (v ⬝ᵥ v) = 2) :
    reflectionMatrix v c ∈ Matrix.orthogonalGroup n R := by
  rw [Matrix.mem_orthogonalGroup_iff, transpose_reflectionMatrix]
  exact reflectionMatrix_mul_self hc

/-- **A reflection matrix has determinant `-1`.** -/
@[simp]
theorem det_reflectionMatrix [Fintype n] {v : n → R} {c : R} (hc : c * (v ⬝ᵥ v) = 2) :
    (reflectionMatrix v c).det = -1 := by
  rw [reflectionMatrix_eq_one_sub_vecMulVec, det_one_sub_vecMulVec, dotProduct_smul,
    smul_eq_mul, hc]
  norm_num

/-! ### Comparison with the reflection of the standard quadratic form -/

section QuadraticForm

variable [Fintype n]

/-- The reflection of the standard quadratic form in a vector of invertible norm has
`reflectionMatrix` as its coordinate matrix. -/
theorem toMatrix'_reflection (v : n → R)
    [Invertible (Matrix.toQuadraticForm' (1 : Matrix n n R) v)] :
    LinearMap.toMatrix'
        (QuadraticMap.reflection (Matrix.toQuadraticForm' (1 : Matrix n n R)) v).toLinearMap =
      reflectionMatrix v (2 * ⅟(Matrix.toQuadraticForm' (1 : Matrix n n R) v)) := by
  ext i j
  rw [LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, QuadraticMap.reflection_apply,
    reflectionMatrix_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, polar_toQuadraticForm'_one,
    Pi.single_apply, dotProduct_single, mul_one]
  ring_nf

end QuadraticForm

/-! ### Products of two reflections -/

section Pair

variable [Fintype n]

/-- The product of two reflection matrices is special orthogonal. -/
theorem reflectionMatrix_mul_mem_specialOrthogonalGroup {v w : n → R} {c d : R}
    (hc : c * (v ⬝ᵥ v) = 2) (hd : d * (w ⬝ᵥ w) = 2) :
    reflectionMatrix v c * reflectionMatrix w d ∈ Matrix.specialOrthogonalGroup n R :=
  Matrix.mem_specialOrthogonalGroup_iff.mpr
    ⟨Submonoid.mul_mem _ (reflectionMatrix_mem_orthogonalGroup hc)
        (reflectionMatrix_mem_orthogonalGroup hd),
      by rw [Matrix.det_mul, det_reflectionMatrix hc, det_reflectionMatrix hd]; ring⟩

/-- **The product of the reflections in two vectors with supplied normalizing scalars**, as an
element of the matrix special orthogonal group of the standard symmetric form. The scalars satisfy
the displayed equations with the respective norms. -/
def reflectionPair (v w : n → R) (c d : R) (hc : c * (v ⬝ᵥ v) = 2) (hd : d * (w ⬝ᵥ w) = 2) :
    Matrix.specialOrthogonalGroup n R :=
  ⟨reflectionMatrix v c * reflectionMatrix w d,
    reflectionMatrix_mul_mem_specialOrthogonalGroup hc hd⟩

@[simp]
theorem coe_reflectionPair {v w : n → R} {c d : R} (hc : c * (v ⬝ᵥ v) = 2)
    (hd : d * (w ⬝ᵥ w) = 2) :
    (reflectionPair v w c d hc hd : Matrix n n R) =
      reflectionMatrix v c * reflectionMatrix w d :=
  (rfl)

/-- Products of two reflections are natural in the coefficient ring. -/
@[simp]
theorem map_reflectionPair (f : R →+* S) {v w : n → R} {c d : R} (hc : c * (v ⬝ᵥ v) = 2)
    (hd : d * (w ⬝ᵥ w) = 2) :
    Matrix.SpecialOrthogonalGroup.map f (reflectionPair v w c d hc hd) =
      reflectionPair (f ∘ v) (f ∘ w) (f c) (f d)
        (by rw [← RingHom.map_dotProduct, ← map_mul, hc, map_ofNat])
        (by rw [← RingHom.map_dotProduct, ← map_mul, hd, map_ofNat]) :=
  Subtype.ext <| by
    rw [Matrix.SpecialOrthogonalGroup.coe_map, coe_reflectionPair, coe_reflectionPair,
      Matrix.map_mul, map_reflectionMatrix, map_reflectionMatrix]

end Pair

/-! ### One-parameter families through a product of two reflections -/

section Path

open scoped LaurentPolynomial

open LaurentPolynomial

variable {K : Type u} [Field K]

/-- The constant Laurent-polynomial vector attached to a vector over the coefficient field. -/
private noncomputable def constVector (v : n → K) : n → K[T;T⁻¹] := fun i => C (v i)

/-- The Laurent-polynomial vector `X • v + Y • w`. Its two coefficients travel along the
family, and each endpoint of the family is a parameter at which one of them vanishes. -/
private noncomputable def pathVector (v w : n → K) (X Y : K[T;T⁻¹]) : n → K[T;T⁻¹] :=
  fun i => X * C (v i) + Y * C (w i)

omit [DecidableEq n] in
private theorem constVector_dotProduct [Fintype n] (v w : n → K) :
    constVector v ⬝ᵥ constVector w = C (v ⬝ᵥ w) :=
  (RingHom.map_dotProduct C v w).symm

omit [DecidableEq n] in
private theorem pathVector_dotProduct [Fintype n] (v w : n → K) (X Y X' Y' : K[T;T⁻¹]) :
    pathVector v w X Y ⬝ᵥ pathVector v w X' Y' =
      X * X' * C (v ⬝ᵥ v) + (X * Y' + Y * X') * C (v ⬝ᵥ w) + Y * Y' * C (w ⬝ᵥ w) := by
  have hC (u₁ u₂ : n → K) :
      ∑ i, (C (u₁ i) : K[T;T⁻¹]) * C (u₂ i) = C (u₁ ⬝ᵥ u₂) := by
    simpa only [constVector, dotProduct] using constVector_dotProduct u₁ u₂
  rw [dotProduct]
  -- `Finset.sum_congr` asks for the pointwise product obtained by unfolding `pathVector`.
  rw [Finset.sum_congr rfl fun i _ =>
    show pathVector v w X Y i * pathVector v w X' Y' i =
        X * X' * (C (v i) * C (v i)) + X * Y' * (C (v i) * C (w i)) +
          Y * X' * (C (w i) * C (v i)) + Y * Y' * (C (w i) * C (w i)) by
      simp only [pathVector]; ring]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hC]
  rw [dotProduct_comm w v]
  ring

/-- Away from the endpoints only the coefficients of the path vector move, so a coefficient-field
point of the family is the product of the reflection in `v` and the reflection in the
specialized path vector. -/
private theorem map_reflectionMatrix_mul [Fintype n] (φ : K[T;T⁻¹] →ₐ[K] K) (v w : n → K) (c : K)
    (X Y E : K[T;T⁻¹]) :
    (reflectionMatrix (constVector v) (C c) *
        reflectionMatrix (pathVector v w X Y) E).map (φ : K[T;T⁻¹] →+* K) =
      reflectionMatrix v c *
        reflectionMatrix ((φ : K[T;T⁻¹] →+* K) ∘ pathVector v w X Y) (φ E) := by
  rw [Matrix.map_mul, map_reflectionMatrix, map_reflectionMatrix]
  congr 1
  have h : (φ : K[T;T⁻¹] →+* K) ∘ constVector v = v := by
    funext i
    simp only [Function.comp_apply, RingHom.coe_coe, constVector, C_eq_algebraMap,
      AlgHom.commutes, Algebra.algebraMap_self_apply]
  have hc : (φ : K[T;T⁻¹] →+* K) (C c) = c := by
    simp only [RingHom.coe_coe, C_eq_algebraMap, AlgHom.commutes,
      Algebra.algebraMap_self_apply]
  rw [h, hc]

private theorem reflectionMatrix_comp_pathVector_left (φ : K[T;T⁻¹] →ₐ[K] K) {v w : n → K}
    {X Y E : K[T;T⁻¹]} {c : K} (hY : φ Y = 0) (hc : φ X * φ X * φ E = c) :
    reflectionMatrix ((φ : K[T;T⁻¹] →+* K) ∘ pathVector v w X Y) (φ E) =
      reflectionMatrix v c := by
  have h : (φ : K[T;T⁻¹] →+* K) ∘ pathVector v w X Y = fun i => φ X * v i := by
    funext i
    simp only [Function.comp_apply, RingHom.coe_coe, pathVector, map_add, map_mul,
      C_eq_algebraMap, AlgHom.commutes, Algebra.algebraMap_self_apply, hY, zero_mul, add_zero]
  rw [h, reflectionMatrix_smul, hc]

private theorem reflectionMatrix_comp_pathVector_right (φ : K[T;T⁻¹] →ₐ[K] K) {v w : n → K}
    {X Y E : K[T;T⁻¹]} {d : K} (hX : φ X = 0) (hd : φ Y * φ Y * φ E = d) :
    reflectionMatrix ((φ : K[T;T⁻¹] →+* K) ∘ pathVector v w X Y) (φ E) =
      reflectionMatrix w d := by
  have h : (φ : K[T;T⁻¹] →+* K) ∘ pathVector v w X Y = fun i => φ Y * w i := by
    funext i
    simp only [Function.comp_apply, RingHom.coe_coe, pathVector, map_add, map_mul,
      C_eq_algebraMap, AlgHom.commutes, Algebra.algebraMap_self_apply, hX, zero_mul, zero_add]
  rw [h, reflectionMatrix_smul, hd]

/-- Assembling a one-parameter family from path data: a coefficient pair `(X, Y)` for the
moving vector, a normalizing scalar `E`, and two parameters at which one of the coefficients
vanishes and the surviving reflection is the reflection in `v`, respectively in `w`. -/
private theorem exists_laurentPath_of_pathData [Fintype n] {v w : n → K}
    {c d : K} (hc : c * (v ⬝ᵥ v) = 2) (X Y E : K[T;T⁻¹]) (a b : Kˣ)
    (hE : E * (pathVector v w X Y ⬝ᵥ pathVector v w X Y) = 2)
    (ha : ∀ φ : K[T;T⁻¹] →ₐ[K] K, φ (T 1) = (a : K) → φ Y = 0 ∧ φ X * φ X * φ E = c)
    (hb : ∀ φ : K[T;T⁻¹] →ₐ[K] K, φ (T 1) = (b : K) → φ X = 0 ∧ φ Y * φ Y * φ E = d) :
    ∃ (M : Matrix.specialOrthogonalGroup n K[T;T⁻¹]) (a b : Kˣ),
      ∀ φ : K[T;T⁻¹] →ₐ[K] K,
        (φ (T 1) = (a : K) → (M : Matrix n n K[T;T⁻¹]).map (φ : K[T;T⁻¹] →+* K) = 1) ∧
        (φ (T 1) = (b : K) → (M : Matrix n n K[T;T⁻¹]).map (φ : K[T;T⁻¹] →+* K) =
          reflectionMatrix v c * reflectionMatrix w d) := by
  have hCc : (C c : K[T;T⁻¹]) * (constVector v ⬝ᵥ constVector v) = 2 := by
    rw [constVector_dotProduct, ← map_mul, hc, map_ofNat]
  refine ⟨⟨reflectionMatrix (constVector v) (C c) * reflectionMatrix (pathVector v w X Y) E,
    reflectionMatrix_mul_mem_specialOrthogonalGroup hCc hE⟩, a, b, fun φ => ⟨?_, ?_⟩⟩
  · intro hφ
    obtain ⟨hY, hX⟩ := ha φ hφ
    -- Coercing the inline subtype defining `M` exposes its underlying matrix definitionally.
    change (reflectionMatrix (constVector v) (C c) *
      reflectionMatrix (pathVector v w X Y) E).map (φ : K[T;T⁻¹] →+* K) = 1
    rw [map_reflectionMatrix_mul, reflectionMatrix_comp_pathVector_left φ hY hX,
      reflectionMatrix_mul_self hc]
  · intro hφ
    obtain ⟨hX, hY⟩ := hb φ hφ
    -- Coercing the inline subtype defining `M` exposes its underlying matrix definitionally.
    change (reflectionMatrix (constVector v) (C c) *
      reflectionMatrix (pathVector v w X Y) E).map (φ : K[T;T⁻¹] →+* K) = _
    rw [map_reflectionMatrix_mul, reflectionMatrix_comp_pathVector_right φ hX hY]

/-- **Every product of two reflections is joined to the identity by a one-parameter family of
special orthogonal matrices over the Laurent polynomials.**

Both reflection vectors are anisotropic, so they span either a degenerate or a nondegenerate
plane. In the degenerate case the two vectors are joined, up to scaling, by an affine line of
vectors of constant norm. In the nondegenerate case the plane has, over an algebraically closed
field, a basis of two isotropic vectors `e` and `f`, and `e + t • f` runs through every
anisotropic line of the plane as `t` runs through the units. Reflecting first in `v` and then in
the moving vector gives the family, and its two endpoints are the parameters at which the moving
vector is proportional to `v`, respectively to `w`. -/
theorem exists_laurentPath_reflectionMatrix_mul [Fintype n] [NeZero (2 : K)] [IsAlgClosed K]
    {v w : n → K} {c d : K} (hc : c * (v ⬝ᵥ v) = 2) (hd : d * (w ⬝ᵥ w) = 2) :
    ∃ (M : Matrix.specialOrthogonalGroup n K[T;T⁻¹]) (a b : Kˣ),
      ∀ φ : K[T;T⁻¹] →ₐ[K] K,
        (φ (T 1) = (a : K) → (M : Matrix n n K[T;T⁻¹]).map (φ : K[T;T⁻¹] →+* K) = 1) ∧
        (φ (T 1) = (b : K) → (M : Matrix n n K[T;T⁻¹]).map (φ : K[T;T⁻¹] →+* K) =
          reflectionMatrix v c * reflectionMatrix w d) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne _)
  have h2 : (2 : K) ≠ 0 := NeZero.ne (2 : K)
  have hqv : v ⬝ᵥ v ≠ 0 := fun h => h2 (by rw [← hc, h, mul_zero])
  have hqw : w ⬝ᵥ w ≠ 0 := fun h => h2 (by rw [← hd, h, mul_zero])
  have hcv : c = 2 / (v ⬝ᵥ v) := (eq_div_iff hqv).mpr hc
  have hdw : d = 2 / (w ⬝ᵥ w) := (eq_div_iff hqw).mpr hd
  have hT : (T (-1) : K[T;T⁻¹]) * T 1 = 1 := by
    rw [← T_add]
    norm_num
  by_cases hdeg : (v ⬝ᵥ w) * (v ⬝ᵥ w) - (v ⬝ᵥ v) * (w ⬝ᵥ w) = 0
  · -- The plane spanned by `v` and `w` is degenerate: an affine line of vectors of constant
    -- norm joins a multiple of `v` to a multiple of `w`.
    have hbb : (v ⬝ᵥ w) * (v ⬝ᵥ w) = (v ⬝ᵥ v) * (w ⬝ᵥ w) := sub_eq_zero.mp hdeg
    have hC : (C (v ⬝ᵥ w) : K[T;T⁻¹]) * C (v ⬝ᵥ w) = C (v ⬝ᵥ v) * C (w ⬝ᵥ w) := by
      rw [← map_mul, ← map_mul, hbb]
    have hκ : (v ⬝ᵥ v) * (v ⬝ᵥ v) * (w ⬝ᵥ w) ≠ 0 := mul_ne_zero (mul_ne_zero hqv hqv) hqw
    have hu : pathVector v w ((2 - T 1) * C (v ⬝ᵥ w)) ((T 1 - 1) * C (v ⬝ᵥ v)) ⬝ᵥ
        pathVector v w ((2 - T 1) * C (v ⬝ᵥ w)) ((T 1 - 1) * C (v ⬝ᵥ v)) =
          C ((v ⬝ᵥ v) * (v ⬝ᵥ v) * (w ⬝ᵥ w)) := by
      rw [pathVector_dotProduct, map_mul, map_mul]
      linear_combination ((2 * T 1 - T 1 * T 1) * C (v ⬝ᵥ v)) * hC
    refine exists_laurentPath_of_pathData hc ((2 - T 1) * C (v ⬝ᵥ w))
      ((T 1 - 1) * C (v ⬝ᵥ v)) (C (2 / ((v ⬝ᵥ v) * (v ⬝ᵥ v) * (w ⬝ᵥ w)))) 1
      (unitOfInvertible (2 : K)) ?_ ?_ ?_
    · rw [hu, ← map_mul, div_mul_cancel₀ _ hκ, map_ofNat]
    · intro φ hφ
      have hφ1 : φ (T 1) = 1 := by rw [hφ, Units.val_one]
      have hX : φ ((2 - T 1) * C (v ⬝ᵥ w)) = v ⬝ᵥ w := by
        rw [map_mul, map_sub, map_ofNat, hφ1, C_eq_algebraMap, AlgHom.commutes,
          Algebra.algebraMap_self_apply]
        ring
      have hY : φ ((T 1 - 1) * C (v ⬝ᵥ v)) = 0 := by
        rw [map_mul, map_sub, map_one, hφ1, C_eq_algebraMap, AlgHom.commutes,
          Algebra.algebraMap_self_apply]
        ring
      refine ⟨hY, ?_⟩
      rw [hX, C_eq_algebraMap, AlgHom.commutes, Algebra.algebraMap_self_apply, hbb, hcv]
      field_simp
    · intro φ hφ
      have hφ2 : φ (T 1) = 2 := by rw [hφ, val_unitOfInvertible]
      have hX : φ ((2 - T 1) * C (v ⬝ᵥ w)) = 0 := by
        rw [map_mul, map_sub, map_ofNat, hφ2, sub_self, zero_mul]
      have hY : φ ((T 1 - 1) * C (v ⬝ᵥ v)) = v ⬝ᵥ v := by
        rw [map_mul, map_sub, map_one, hφ2, C_eq_algebraMap, AlgHom.commutes,
          Algebra.algebraMap_self_apply]
        ring
      refine ⟨hX, ?_⟩
      rw [hY, C_eq_algebraMap, AlgHom.commutes, Algebra.algebraMap_self_apply, hdw]
      field_simp
  · -- The plane spanned by `v` and `w` is nondegenerate: it has an isotropic basis `e`, `f`,
    -- and `e + t • f` sweeps out its anisotropic lines as `t` runs through the units.
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq
      ((v ⬝ᵥ w) * (v ⬝ᵥ w) - (v ⬝ᵥ v) * (w ⬝ᵥ w)) (n := 2) (by norm_num)
    rw [pow_two] at hs
    have hs0 : s ≠ 0 := fun h => hdeg (by rw [← hs, h, mul_zero])
    have hfac : ((v ⬝ᵥ w) + s) * ((v ⬝ᵥ w) - s) = (v ⬝ᵥ v) * (w ⬝ᵥ w) := by
      linear_combination -hs
    have hqvw : (v ⬝ᵥ v) * (w ⬝ᵥ w) ≠ 0 := mul_ne_zero hqv hqw
    have hbps : (v ⬝ᵥ w) + s ≠ 0 := fun h => hqvw (by rw [← hfac, h, zero_mul])
    have hbms : (v ⬝ᵥ w) - s ≠ 0 := fun h => hqvw (by rw [← hfac, h, mul_zero])
    have hC : (C s : K[T;T⁻¹]) * C s = C (v ⬝ᵥ w) * C (v ⬝ᵥ w) - C (v ⬝ᵥ v) * C (w ⬝ᵥ w) := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_sub, hs]
    have hu : pathVector v w (-C (v ⬝ᵥ w) + C s + T 1 * (-C (v ⬝ᵥ w) - C s))
        (C (v ⬝ᵥ v) + T 1 * C (v ⬝ᵥ v)) ⬝ᵥ
          pathVector v w (-C (v ⬝ᵥ w) + C s + T 1 * (-C (v ⬝ᵥ w) - C s))
            (C (v ⬝ᵥ v) + T 1 * C (v ⬝ᵥ v)) =
          C (-(4 * (v ⬝ᵥ v) * (s * s))) * T 1 := by
      rw [pathVector_dotProduct]
      have hRHS : (C (-(4 * (v ⬝ᵥ v) * (s * s))) : K[T;T⁻¹]) =
          -(4 * C (v ⬝ᵥ v) * (C s * C s)) := by
        rw [map_neg, map_mul, map_mul, map_mul, map_ofNat]
      rw [hRHS]
      linear_combination (C (v ⬝ᵥ v) * (1 + T 1) * (1 + T 1)) * hC
    refine exists_laurentPath_of_pathData hc (-C (v ⬝ᵥ w) + C s + T 1 * (-C (v ⬝ᵥ w) - C s))
      (C (v ⬝ᵥ v) + T 1 * C (v ⬝ᵥ v)) (C (-(2 * (v ⬝ᵥ v) * (s * s))⁻¹) * T (-1)) (-1)
      (Units.mk0 (-(((v ⬝ᵥ w) - s) / ((v ⬝ᵥ w) + s))) (by
        simp only [ne_eq, neg_eq_zero, div_eq_zero_iff, not_or]
        exact ⟨hbms, hbps⟩)) ?_ ?_ ?_
    · rw [hu]
      calc C (-(2 * (v ⬝ᵥ v) * (s * s))⁻¹) * T (-1) * (C (-(4 * (v ⬝ᵥ v) * (s * s))) * T 1)
          = C (-(2 * (v ⬝ᵥ v) * (s * s))⁻¹) * C (-(4 * (v ⬝ᵥ v) * (s * s))) *
              ((T (-1) : K[T;T⁻¹]) * T 1) := by ring
        _ = C (-(2 * (v ⬝ᵥ v) * (s * s))⁻¹ * -(4 * (v ⬝ᵥ v) * (s * s))) := by
              rw [hT, mul_one, ← map_mul]
        _ = 2 := by
              -- Isolate the coefficient-field identity so `rw` can rewrite beneath `C`.
              rw [show -(2 * (v ⬝ᵥ v) * (s * s))⁻¹ * -(4 * (v ⬝ᵥ v) * (s * s)) = 2 by
                field_simp
                ring]
              exact map_ofNat C 2
    · intro φ hφ
      have hφ1 : φ (T 1) = -1 := by rw [hφ, Units.val_neg, Units.val_one]
      have hφ2 : φ (T (-1)) = -1 := by
        rw [laurentEval_unique _ φ hφ, laurentEval_T, zpow_neg, zpow_one,
          Units.val_inv_eq_inv_val, Units.val_neg, Units.val_one]
        norm_num
      have hX : φ (-C (v ⬝ᵥ w) + C s + T 1 * (-C (v ⬝ᵥ w) - C s)) = 2 * s := by
        simp only [map_add, map_neg, map_mul, map_sub, C_eq_algebraMap, AlgHom.commutes,
          Algebra.algebraMap_self_apply, hφ1]
        ring
      have hY : φ (C (v ⬝ᵥ v) + T 1 * C (v ⬝ᵥ v)) = 0 := by
        simp only [map_add, map_mul, C_eq_algebraMap, AlgHom.commutes,
          Algebra.algebraMap_self_apply, hφ1]
        ring
      have hEv : φ (C (-(2 * (v ⬝ᵥ v) * (s * s))⁻¹) * T (-1)) = (2 * (v ⬝ᵥ v) * (s * s))⁻¹ := by
        rw [map_mul, C_eq_algebraMap, AlgHom.commutes, Algebra.algebraMap_self_apply, hφ2]
        ring
      refine ⟨hY, ?_⟩
      rw [hX, hEv, hcv]
      field_simp
    · intro φ hφ
      have hφ1 : φ (T 1) = -(((v ⬝ᵥ w) - s) / ((v ⬝ᵥ w) + s)) := by rw [hφ, Units.val_mk0]
      have hφ2 : φ (T (-1)) = -(((v ⬝ᵥ w) + s) / ((v ⬝ᵥ w) - s)) := by
        rw [laurentEval_unique _ φ hφ, laurentEval_T, zpow_neg, zpow_one,
          Units.val_inv_eq_inv_val, Units.val_mk0, ← neg_inv, inv_div]
      have hX : φ (-C (v ⬝ᵥ w) + C s + T 1 * (-C (v ⬝ᵥ w) - C s)) = 0 := by
        simp only [map_add, map_neg, map_mul, map_sub, C_eq_algebraMap, AlgHom.commutes,
          Algebra.algebraMap_self_apply, hφ1]
        field_simp
        ring
      have hY : φ (C (v ⬝ᵥ v) + T 1 * C (v ⬝ᵥ v)) =
          (v ⬝ᵥ v) * (2 * s) / ((v ⬝ᵥ w) + s) := by
        simp only [map_add, map_mul, C_eq_algebraMap, AlgHom.commutes,
          Algebra.algebraMap_self_apply, hφ1]
        field_simp
        ring
      have hEv : φ (C (-(2 * (v ⬝ᵥ v) * (s * s))⁻¹) * T (-1)) =
          ((v ⬝ᵥ w) + s) / (((v ⬝ᵥ w) - s) * (2 * (v ⬝ᵥ v) * (s * s))) := by
        rw [map_mul, C_eq_algebraMap, AlgHom.commutes, Algebra.algebraMap_self_apply, hφ2]
        field_simp
      have hms : (v ⬝ᵥ w) - s = (v ⬝ᵥ v) * (w ⬝ᵥ w) / ((v ⬝ᵥ w) + s) := by
        field_simp
        linear_combination hfac
      refine ⟨hX, ?_⟩
      rw [hY, hEv, hms, hdw]
      field_simp

end Path

end TauCeti
