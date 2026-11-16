/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# The unitary group of an almost complex structure

The rotations of a quadratic form `Q` commuting with an almost complex structure `J` form a
subgroup `U(V, J)` of the special orthogonal group `SO(Q)`
(`TauCeti.AlmostComplexStructure.unitaryGroup`). For the negative definite form of an orthogonal
complex structure on a four-dimensional inner product space this is the unitary group `U(2)`.

On an inner product space, a family `f` of vectors such that `f` and `J ∘ f` together form an
orthonormal basis is a unitary frame of `(V, J)` as a complex inner product space. The complex
matrix of a real endomorphism `A` in such a frame (`TauCeti.AlmostComplexStructure.complexMatrix`)
has as `(i, k)` entry the complex coordinate `⟪f i, A (f k)⟫ + ⟪J (f i), A (f k)⟫ i` of
`A (f k)` along `f i`, where a complex number `a + b i` acts on `V` by `a + b J`. For `A` commuting
with `J` it is the matrix of `A` as a complex-linear map, and its determinant is the complex
determinant of `A`. For an orthonormal basis `(e₀, e₁, e₂, e₃)` with `J e₀ = e₁` and `J e₂ = e₃`,
the family `(e₀, e₂)` is such a frame
(`TauCeti.AlmostComplexStructure.sum_inner_smul_add_inner_apply_smul_apply_eq`).

## Main definitions

* `TauCeti.AlmostComplexStructure.unitaryGroup J Q`: the rotations of `SO(Q)` commuting with `J`.
* `TauCeti.AlmostComplexStructure.complexMatrix J f A`: the complex matrix of `A` in the frame `f`.

## Main results

* `TauCeti.AlmostComplexStructure.mem_unitaryGroup_iff`: a rotation lies in `U(V, J)` exactly when
  it commutes with `J`.
* `TauCeti.AlmostComplexStructure.apply_eq_sum_complexMatrix`: `A (f k)` is the complex combination
  of the `f i` with coefficients the `k`-th column of `complexMatrix J f A`.
* `TauCeti.AlmostComplexStructure.complexMatrix_comp`: the complex matrix is multiplicative on
  endomorphisms commuting with an orthogonal `J`.
-/

public section

open Module.End
open scoped RealInnerProductSpace

namespace TauCeti.AlmostComplexStructure

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The unitary group** `U(V, J)` of an almost complex structure `J`, inside the special
orthogonal group of a quadratic form `Q`: the rotations commuting with `J`. -/
noncomputable def unitaryGroup (J : AlmostComplexStructure V) (Q : QuadraticForm ℝ V) :
    Subgroup (QuadraticMap.specialOrthogonalGroup Q) :=
  (Subgroup.centralizer {J.linearEquiv}).comap (QuadraticMap.specialOrthogonalGroup Q).subtype

/-- A rotation lies in `U(V, J)` exactly when it commutes with `J`. -/
theorem mem_unitaryGroup_iff {J : AlmostComplexStructure V} {Q : QuadraticForm ℝ V}
    {A : QuadraticMap.specialOrthogonalGroup Q} :
    A ∈ J.unitaryGroup Q ↔ ∀ v, (A : V ≃ₗ[ℝ] V) (J v) = J ((A : V ≃ₗ[ℝ] V) v) := by
  simp only [unitaryGroup, Subgroup.mem_comap, Subgroup.coe_subtype,
    Subgroup.mem_centralizer_singleton_iff, LinearEquiv.ext_iff, mul_apply_eq_comp,
    linearEquiv_apply]

/-! ### The complex matrix in a unitary frame -/

section ComplexMatrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*}

/-- **The complex matrix of a real endomorphism in a frame of `(E, J)`.** Its `(i, k)` entry is
`⟪f i, A (f k)⟫ + ⟪J (f i), A (f k)⟫ i`, the complex coordinate of `A (f k)` along `f i`. When
`f` and `J ∘ f` together form an orthonormal basis, this expands `A (f k)` in the complex frame
`f` (`apply_eq_sum_complexMatrix`); for `A` commuting with `J` it is the matrix of `A` as a
complex-linear map. -/
noncomputable def complexMatrix (J : AlmostComplexStructure E) (f : ι → E) (A : E →ₗ[ℝ] E) :
    Matrix ι ι ℂ :=
  Matrix.of fun i k ↦ ⟪f i, A (f k)⟫ + ⟪J (f i), A (f k)⟫ * Complex.I

@[simp]
theorem complexMatrix_apply (J : AlmostComplexStructure E) (f : ι → E) (A : E →ₗ[ℝ] E) (i k : ι) :
    J.complexMatrix f A i k = ⟪f i, A (f k)⟫ + ⟪J (f i), A (f k)⟫ * Complex.I :=
  (rfl)

theorem re_complexMatrix_apply (J : AlmostComplexStructure E) (f : ι → E) (A : E →ₗ[ℝ] E)
    (i k : ι) : (J.complexMatrix f A i k).re = ⟪f i, A (f k)⟫ := by
  simp

theorem im_complexMatrix_apply (J : AlmostComplexStructure E) (f : ι → E) (A : E →ₗ[ℝ] E)
    (i k : ι) : (J.complexMatrix f A i k).im = ⟪J (f i), A (f k)⟫ := by
  simp

/-- **The columns of the complex matrix.** If `f` and `J ∘ f` expand every vector,
`v = ∑ i, (⟪f i, v⟫ • f i + ⟪J (f i), v⟫ • J (f i))`, as they do when together they form an
orthonormal basis, then `A (f k)` is the combination of the `f i` with the complex coefficients
`complexMatrix J f A i k`, a complex number `a + b i` acting by `a + b J`. -/
theorem apply_eq_sum_complexMatrix [Fintype ι] {J : AlmostComplexStructure E} {f : ι → E}
    (hf : ∀ v, ∑ i, (⟪f i, v⟫ • f i + ⟪J (f i), v⟫ • J (f i)) = v) (A : E →ₗ[ℝ] E) (k : ι) :
    A (f k) =
      ∑ i, ((J.complexMatrix f A i k).re • f i + (J.complexMatrix f A i k).im • J (f i)) := by
  simp only [re_complexMatrix_apply, im_complexMatrix_apply]
  exact (hf _).symm

/-- **The complex matrix is multiplicative** on endomorphisms commuting with an orthogonal `J`:
in a frame expanding every vector, the complex matrix of a composite `A ∘ B` with `A` commuting
with `J` is the product of the complex matrices. -/
theorem complexMatrix_comp [Fintype ι] {J : AlmostComplexStructure E} {f : ι → E}
    (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
    (hf : ∀ v, ∑ i, (⟪f i, v⟫ • f i + ⟪J (f i), v⟫ • J (f i)) = v) {A : E →ₗ[ℝ] E}
    (hA : ∀ v, A (J v) = J (A v)) (B : E →ₗ[ℝ] E) :
    J.complexMatrix f (A ∘ₗ B) = J.complexMatrix f A * J.complexMatrix f B := by
  have hJl (x y : E) : ⟪x, J y⟫ = -⟪J x, y⟫ := by
    have h := hJ (J x) y
    rw [J.apply_apply, inner_neg_left] at h
    linarith
  ext i k
  rw [complexMatrix_apply, LinearMap.comp_apply, apply_eq_sum_complexMatrix hf B k,
    Matrix.mul_apply]
  simp only [map_sum, map_add, map_smul, hA, inner_sum, inner_add_right, real_inner_smul_right,
    hJl, complexMatrix_apply, Complex.ofReal_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  apply Complex.ext <;> simp <;> ring

/-- **A unitary frame in dimension four.** If `e` is an orthonormal basis with `J e₀ = e₁` and
`J e₂ = e₃`, then `(e₀, e₂)` and its image under `J` expand every vector. -/
theorem sum_inner_smul_add_inner_apply_smul_apply_eq {e : OrthonormalBasis (Fin 4) ℝ E}
    {J : AlmostComplexStructure E} (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3) (v : E) :
    ∑ i, (⟪![e 0, e 2] i, v⟫ • ![e 0, e 2] i + ⟪J (![e 0, e 2] i), v⟫ • J (![e 0, e 2] i)) =
      v := by
  conv_rhs => rw [← e.sum_repr' v]
  simp only [Fin.sum_univ_two, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, h₀, h₂]
  abel

end ComplexMatrix

end TauCeti.AlmostComplexStructure
