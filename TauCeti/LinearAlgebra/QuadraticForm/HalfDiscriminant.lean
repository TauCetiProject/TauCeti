/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.QuadraticForm.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.LinearAlgebra.Matrix.Determinant.Half
import TauCeti.LinearAlgebra.BilinearForm.BaseChange
import TauCeti.LinearAlgebra.Matrix.BilinearForm

/-!
# The discriminant and half-discriminant of a quadratic form over a ring

Let `q` be a quadratic form on a free module `M` of finite rank `l` over a commutative ring `R`,
with basis `b`. Its *discriminant* `disc(q)` is the determinant of the Gram matrix of the polar
form `b_q`. When `l` is odd, this determinant is divisible by `2` as a universal polynomial in the
coefficients of `q`, and the *half-discriminant* `disc'(q)` is the quotient: in a basis
`q(x) = xᵀ A x` with `A` upper triangular, `b_q` has Gram matrix `A + Aᵀ`, and
`disc'(q) = Matrix.halfDet A`. It does not depend on the choice of `A` among the matrices with
`q(x) = xᵀ A x`, it is compatible with base change, and a change of basis multiplies it by the
square of a unit, like `disc(q)`.

The form is *nondegenerate* in the sense of Conrad's *Reductive group schemes* (Appendix C.1)
when `disc(q)` (`l` even) or `disc'(q)` (`l` odd) is a unit; in rank `0` every form is.
`QuadraticForm.normalizedDiscr` is `disc` in even rank and `disc'` in odd rank, and
`QuadraticForm.IsDiscrNondegenerate` asks for it to be a unit in some basis, equivalently
in every basis. No invertibility of `2` is assumed: `x²` over `𝔽₂` has `disc' = 1` and is
nondegenerate although its polar form is zero.

## Main definitions

* `QuadraticForm.polarDiscr q b`: the Gram determinant `disc(q)` of the polar form.
* `QuadraticForm.halfDiscr q b`: the half-discriminant `disc'(q)`.
* `QuadraticForm.normalizedDiscr q b`: `disc(q)` in even rank, `disc'(q)` in odd rank.
* `QuadraticForm.IsDiscrNondegenerate q`: `normalizedDiscr q b` is a unit.

## Main results

* `QuadraticForm.halfDiscr_eq_halfDet`: `disc'(q)` computed from any bilinear form `B`
  with `B(x, x) = q(x)`.
* `QuadraticForm.two_mul_halfDiscr`: `2 disc'(q) = disc(q)` in odd rank.
* `QuadraticForm.halfDiscr_basis_change`, `QuadraticForm.halfDiscr_reindex`:
  `disc'(q)` is well defined up to the square of a unit.
* `QuadraticForm.polarDiscr_baseChange`, `QuadraticForm.halfDiscr_baseChange`,
  `QuadraticForm.IsDiscrNondegenerate.baseChange`: compatibility with base change.
* `QuadraticForm.isDiscrNondegenerate_iff`: nondegeneracy can be read in any basis;
  `QuadraticForm.isDiscrNondegenerate_iff_of_even` and
  `QuadraticForm.isDiscrNondegenerate_iff_of_odd` read it on `disc(q)` and `disc'(q)`.
* `QuadraticForm.halfDiscr_sq`, `QuadraticForm.halfDiscr_proj_add_proj`: `x²` has `disc' = 1` and
  `z² + xy` has `disc' = -1`.

## References

* B. Conrad, *Reductive group schemes*, Appendix C.1.
* M.-A. Knus, *Quadratic and Hermitian forms over rings*, Chapter IV, §3.
-/

public section

open Module Matrix

namespace QuadraticForm

open _root_.QuadraticMap (polarBilin)
open LinearMap (BilinForm)

variable {R M ι κ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The discriminant `disc(q)` of a quadratic form in the basis `b`: the determinant of the Gram
matrix of its polar form `b_q(x, y) = q(x + y) - q(x) - q(y)`. -/
noncomputable def polarDiscr (q : QuadraticForm R M) (b : Basis ι R M) : R :=
  (BilinForm.toMatrix b (polarBilin q)).det

/-- `disc(q)` is the determinant of the Gram matrix of the polar form. -/
theorem polarDiscr_def (q : QuadraticForm R M) (b : Basis ι R M) :
    polarDiscr q b = (BilinForm.toMatrix b (polarBilin q)).det :=
  (rfl)

/-- The half-discriminant `disc'(q)` of a quadratic form in the basis `b`: `Matrix.halfDet A` for
the Gram matrix `A` of any bilinear form `B` with `B(x, x) = q(x)`
(`QuadraticForm.halfDiscr_eq_halfDet`). In odd rank `2 disc'(q) = disc(q)`; in even rank it is `0`
by convention. -/
noncomputable def halfDiscr (q : QuadraticForm R M) (b : Basis ι R M) : R :=
  haveI := Module.Free.of_basis b
  (BilinForm.toMatrix b (LinearMap.BilinMap.toQuadraticMap_surjective q).choose).halfDet

/-- The half-discriminant can be computed from any bilinear form `B` with `B(x, x) = q(x)`. -/
theorem halfDiscr_eq_halfDet {q : QuadraticForm R M} (b : Basis ι R M) {B : BilinForm R M}
    (hB : B.toQuadraticMap = q) : halfDiscr q b = (BilinForm.toMatrix b B).halfDet := by
  have := Module.Free.of_basis b
  have hB' := (LinearMap.BilinMap.toQuadraticMap_surjective (N := R) q).choose_spec
  obtain ⟨Z, hZ⟩ := BilinForm.exists_toMatrix_eq_sub_transpose_of_isAlt b
    (D := B - (LinearMap.BilinMap.toQuadraticMap_surjective q).choose)
    (LinearMap.BilinMap.toQuadraticMap_eq_zero.mp (by
      rw [LinearMap.BilinMap.toQuadraticMap_sub, hB, hB', sub_self]))
  rw [halfDiscr, ← halfDet_add_sub_transpose _ Z, ← hZ, ← map_add]
  congr 2
  abel

/-- In even rank, `disc'(q)` is `0` by convention. -/
theorem halfDiscr_of_not_odd (hι : ¬Odd (Fintype.card ι)) (q : QuadraticForm R M)
    (b : Basis ι R M) : halfDiscr q b = 0 := by
  rw [halfDiscr, halfDet_of_not_odd hι]

/-- In odd rank, `2 disc'(q) = disc(q)`. -/
theorem two_mul_halfDiscr (hι : Odd (Fintype.card ι)) (q : QuadraticForm R M)
    (b : Basis ι R M) : 2 * halfDiscr q b = polarDiscr q b := by
  have := Module.Free.of_basis b
  obtain ⟨B, hB⟩ := LinearMap.BilinMap.toQuadraticMap_surjective (N := R) q
  have hflip : (BilinForm.toMatrix b B)ᵀ = BilinForm.toMatrix b B.flip := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply]
  rw [halfDiscr_eq_halfDet b hB, two_mul_halfDet hι, polarDiscr, ← hB,
    LinearMap.BilinMap.polarBilin_toQuadraticMap, map_add, hflip]

/-- Changing the basis multiplies `disc(q)` by the square of the determinant of the change of
basis. -/
theorem polarDiscr_basis_change (q : QuadraticForm R M) (b b' : Basis ι R M) :
    polarDiscr q b' = b.det b' ^ 2 * polarDiscr q b := by
  rw [polarDiscr, polarDiscr, Basis.det_apply]
  exact LinearMap.BilinForm.det_toMatrix_eq_det_sq_mul_det b b' _

/-- Changing the basis multiplies `disc'(q)` by the square of the determinant of the change of
basis; so `disc'(q)` is well defined up to the square of a unit. -/
theorem halfDiscr_basis_change (q : QuadraticForm R M) (b b' : Basis ι R M) :
    halfDiscr q b' = b.det b' ^ 2 * halfDiscr q b := by
  have := Module.Free.of_basis b
  obtain ⟨B, hB⟩ := LinearMap.BilinMap.toQuadraticMap_surjective (N := R) q
  rw [halfDiscr_eq_halfDet b' hB, halfDiscr_eq_halfDet b hB,
    ← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b, halfDet_transpose_mul_mul,
    Basis.det_apply]

/-- Reindexing the basis does not change `disc(q)`. -/
@[simp]
theorem polarDiscr_reindex (q : QuadraticForm R M) (b : Basis ι R M) (e : ι ≃ κ) :
    polarDiscr q (b.reindex e) = polarDiscr q b := by
  rw [polarDiscr, polarDiscr, LinearMap.BilinForm.det_toMatrix_reindex]

/-- Reindexing the basis does not change `disc'(q)`. -/
@[simp]
theorem halfDiscr_reindex (q : QuadraticForm R M) (b : Basis ι R M) (e : ι ≃ κ) :
    halfDiscr q (b.reindex e) = halfDiscr q b := by
  have := Module.Free.of_basis b
  obtain ⟨B, hB⟩ := LinearMap.BilinMap.toQuadraticMap_surjective (N := R) q
  rw [halfDiscr_eq_halfDet _ hB, halfDiscr_eq_halfDet _ hB,
    LinearMap.BilinForm.toMatrix_reindex, reindex_apply, halfDet_submatrix_equiv_self]

/-- The discriminant is compatible with base change: for a bilinear form `B` with
`B(x, x) = q(x)`, the form `x ↦ B_A(x, x)` on `A ⊗ M`, which has the same coefficients as `q`, has
discriminant the image of `disc(q)`. -/
theorem polarDiscr_baseChange (A : Type*) [CommRing A] [Algebra R A] {q : QuadraticForm R M}
    (b : Basis ι R M) {B : BilinForm R M} (hB : B.toQuadraticMap = q) :
    polarDiscr (B.baseChange A).toQuadraticMap (b.baseChange A) =
      algebraMap R A (polarDiscr q b) := by
  -- `polarBilin_toQuadraticMap` produces `LinearMap.flip`, not the `LinearMap.BilinForm.flip`
  -- of `LinearMap.BilinForm.baseChange_flip`, so this form is proved extensionally.
  have hflip : LinearMap.flip (B.baseChange A) = BilinForm.baseChange A (LinearMap.flip B) := by
    ext x y
    simp
  rw [polarDiscr, polarDiscr, ← hB, LinearMap.BilinMap.polarBilin_toQuadraticMap,
    LinearMap.BilinMap.polarBilin_toQuadraticMap, map_add, map_add, hflip,
    LinearMap.BilinForm.toMatrix_baseChange, LinearMap.BilinForm.toMatrix_baseChange,
    ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_add, RingHom.map_det]

/-- The half-discriminant is compatible with base change: for a bilinear form `B` with
`B(x, x) = q(x)`, the form `x ↦ B_A(x, x)` on `A ⊗ M`, which has the same coefficients as `q`, has
half-discriminant the image of `disc'(q)`. -/
theorem halfDiscr_baseChange (A : Type*) [CommRing A] [Algebra R A] {q : QuadraticForm R M}
    (b : Basis ι R M) {B : BilinForm R M} (hB : B.toQuadraticMap = q) :
    halfDiscr (B.baseChange A).toQuadraticMap (b.baseChange A) =
      algebraMap R A (halfDiscr q b) := by
  rw [halfDiscr_eq_halfDet _ rfl, halfDiscr_eq_halfDet _ hB, map_halfDet,
    LinearMap.BilinForm.toMatrix_baseChange]

/-- The discriminant that decides nondegeneracy: `disc(q)` in even rank and `disc'(q)` in odd
rank. -/
noncomputable def normalizedDiscr (q : QuadraticForm R M) (b : Basis ι R M) : R :=
  if Even (Fintype.card ι) then polarDiscr q b else halfDiscr q b

/-- In even rank, `normalizedDiscr` is `disc(q)`. -/
theorem normalizedDiscr_of_even (hι : Even (Fintype.card ι)) (q : QuadraticForm R M)
    (b : Basis ι R M) : normalizedDiscr q b = polarDiscr q b := by
  simp [normalizedDiscr, hι]

/-- In odd rank, `normalizedDiscr` is `disc'(q)`. -/
theorem normalizedDiscr_of_odd (hι : Odd (Fintype.card ι)) (q : QuadraticForm R M)
    (b : Basis ι R M) : normalizedDiscr q b = halfDiscr q b := by
  simp [normalizedDiscr, Nat.not_even_iff_odd.mpr hι]

/-- Changing the basis multiplies `normalizedDiscr` by the square of a unit. -/
theorem normalizedDiscr_basis_change (q : QuadraticForm R M) (b b' : Basis ι R M) :
    normalizedDiscr q b' = b.det b' ^ 2 * normalizedDiscr q b := by
  rcases Nat.even_or_odd (Fintype.card ι) with hι | hι
  · rw [normalizedDiscr_of_even hι, normalizedDiscr_of_even hι, polarDiscr_basis_change q b b']
  · rw [normalizedDiscr_of_odd hι, normalizedDiscr_of_odd hι, halfDiscr_basis_change q b b']

/-- Reindexing the basis does not change `normalizedDiscr`. -/
@[simp]
theorem normalizedDiscr_reindex (q : QuadraticForm R M) (b : Basis ι R M) (e : ι ≃ κ) :
    normalizedDiscr q (b.reindex e) = normalizedDiscr q b := by
  rw [normalizedDiscr, normalizedDiscr, polarDiscr_reindex, halfDiscr_reindex,
    Fintype.card_congr e]

/-- `normalizedDiscr` is compatible with base change, in the form of
`QuadraticForm.polarDiscr_baseChange` and `QuadraticForm.halfDiscr_baseChange`. -/
theorem normalizedDiscr_baseChange (A : Type*) [CommRing A] [Algebra R A]
    {q : QuadraticForm R M} (b : Basis ι R M) {B : BilinForm R M} (hB : B.toQuadraticMap = q) :
    normalizedDiscr (B.baseChange A).toQuadraticMap (b.baseChange A) =
      algebraMap R A (normalizedDiscr q b) := by
  rcases Nat.even_or_odd (Fintype.card ι) with hι | hι
  · rw [normalizedDiscr_of_even hι, normalizedDiscr_of_even hι, polarDiscr_baseChange A b hB]
  · rw [normalizedDiscr_of_odd hι, normalizedDiscr_of_odd hι, halfDiscr_baseChange A b hB]

/-- A quadratic form on a free module of finite rank is *nondegenerate* (Conrad, *Reductive group
schemes*, Appendix C.1) if in some basis its discriminant (even rank) or half-discriminant (odd
rank) is a unit; then this holds in every basis (`QuadraticForm.isDiscrNondegenerate_iff`). In
rank `0` every form is nondegenerate. -/
def IsDiscrNondegenerate (q : QuadraticForm R M) : Prop :=
  ∃ (n : ℕ) (b : Basis (Fin n) R M), IsUnit (normalizedDiscr q b)

/-- Nondegeneracy can be read in any basis. -/
theorem isDiscrNondegenerate_iff {q : QuadraticForm R M} (b : Basis ι R M) :
    IsDiscrNondegenerate q ↔ IsUnit (normalizedDiscr q b) := by
  refine ⟨fun ⟨n, b', h⟩ => ?_, fun h => ⟨_, b.reindex (Fintype.equivFin ι), by
    rwa [normalizedDiscr_reindex]⟩⟩
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact isUnit_of_subsingleton _
  · rw [← normalizedDiscr_reindex q b' (b'.indexEquiv b),
      normalizedDiscr_basis_change q b] at h
    exact isUnit_of_mul_isUnit_right h

/-- In even rank, nondegeneracy says that `disc(q)` is a unit, in any basis. -/
theorem isDiscrNondegenerate_iff_of_even {q : QuadraticForm R M} (b : Basis ι R M)
    (hι : Even (Fintype.card ι)) : IsDiscrNondegenerate q ↔ IsUnit (polarDiscr q b) := by
  rw [isDiscrNondegenerate_iff b, normalizedDiscr_of_even hι]

/-- In odd rank, nondegeneracy says that `disc'(q)` is a unit, in any basis. -/
theorem isDiscrNondegenerate_iff_of_odd {q : QuadraticForm R M} (b : Basis ι R M)
    (hι : Odd (Fintype.card ι)) : IsDiscrNondegenerate q ↔ IsUnit (halfDiscr q b) := by
  rw [isDiscrNondegenerate_iff b, normalizedDiscr_of_odd hι]

/-- Nondegeneracy is preserved by base change: if `q` is nondegenerate and `B` is a bilinear form
with `B(x, x) = q(x)`, the form `x ↦ B_A(x, x)` on `A ⊗ M` is nondegenerate. -/
theorem IsDiscrNondegenerate.baseChange (A : Type*) [CommRing A] [Algebra R A]
    {q : QuadraticForm R M} (h : IsDiscrNondegenerate q) {B : BilinForm R M}
    (hB : B.toQuadraticMap = q) : IsDiscrNondegenerate (B.baseChange A).toQuadraticMap := by
  obtain ⟨n, b, hb⟩ := h
  exact ⟨n, b.baseChange A, by
    rw [normalizedDiscr_baseChange A b hB]
    exact hb.map _⟩

/-- The form `x²` on `R` has half-discriminant `1`. -/
theorem halfDiscr_sq :
    halfDiscr (QuadraticMap.sq : QuadraticForm R R) (Basis.singleton Unit R) = 1 := by
  rw [halfDiscr_eq_halfDet _ (B := LinearMap.mul R R) (by ext; simp), halfDet_unique]
  simp [LinearMap.BilinForm.toMatrix_apply]

/-- The form `z² + xy` on `R³` has half-discriminant `-1`. -/
theorem halfDiscr_proj_add_proj :
    halfDiscr (QuadraticMap.proj 2 2 + QuadraticMap.proj 0 1 : QuadraticForm R (Fin 3 → R))
      (Pi.basisFun R (Fin 3)) = -1 := by
  rw [halfDiscr_eq_halfDet _ (B := (LinearMap.mul R R).compl₁₂ (LinearMap.proj 2)
      (LinearMap.proj 2) + (LinearMap.mul R R).compl₁₂ (LinearMap.proj 0) (LinearMap.proj 1))
      (by ext; simp), halfDet_fin_three]
  simp [LinearMap.BilinForm.toMatrix_apply]

end QuadraticForm
