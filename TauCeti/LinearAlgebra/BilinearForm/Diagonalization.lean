/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import TauCeti.LinearAlgebra.BilinearForm.Ideals
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.BilinearForm.Isometry
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Diagonalization of symmetric bilinear forms in every characteristic

Over a commutative ring, an orthogonal basis gives a diagonal Gram matrix and reduces divisibility
of all pairings to divisibility of its diagonal values. For a symmetric form with `2` invertible,
it also identifies the associated quadratic form with the weighted sum of squares of its
self-pairings. The hyperbolic plane can therefore have an orthogonal basis only when `2` is a
unit. Over a local ring with `2` invertible, a pairing dividing every value can be replaced by a
self-pairing with the same property. A symmetric form with unit Gram determinant has an
orthogonal basis with unit self-pairings over any such local ring.

Over a field in which `2` is invertible, every symmetric bilinear form on a finite-dimensional
space has an orthogonal basis (`LinearMap.BilinForm.exists_orthogonal_basis`). In characteristic
two this fails: a nonzero alternating form is symmetric, and an orthogonal basis for it would make
every basis pairing vanish, hence the whole form. This file shows that the alternating forms are
the only obstruction, in every characteristic: a symmetric form has an orthogonal basis if and
only if it is zero or not alternating (`LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_iff`).

For a nondegenerate form over a field in which every element is a square, for instance a finite
field of characteristic two (`isSquare_of_charTwo'`), the orthogonal basis can be rescaled: a
symmetric form that is not alternating has an **orthonormal basis**, one in which its matrix is
the identity (`LinearMap.BilinForm.IsSymm.exists_basis_toMatrix_eq_one`). Hence it is equivalent
to the standard form `Matrix.toBilin' 1`, which is itself such a form in every positive dimension
(`Matrix.isAlt_toBilin'_one_iff` in `TauCeti.LinearAlgebra.Matrix.BilinearForm`), and any two such
forms of the same dimension are equivalent. Together with the symplectic normal form of
`TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis` this gives the dichotomy for nondegenerate
forms that are alternating or symmetric: a symplectic basis when the form is alternating, an
orthonormal basis when it is not
(`LinearMap.BilinForm.Nondegenerate.exists_basis_toMatrix_eq_J_or_toMatrix_eq_one`). Over `𝔽₂`,
where every form that is alternating is symmetric, this classifies the nondegenerate symmetric
bilinear forms, which is the input to the normal forms of one-relator pro-`2` groups.

Gram determinants transform by the square of the coordinate-map determinant. Consequently, the
product of the Gram determinants of equivalent bilinear forms is a square, without symmetry or
nondegeneracy assumptions. When `2` is invertible, symmetric bilinear forms are equivalent
exactly when their associated quadratic forms are equivalent.

## Main results

* `LinearMap.BilinForm.iIsOrtho.toMatrix_eq_diagonal`: the Gram matrix in an orthogonal basis
  is the diagonal matrix of its self-pairings.
* `LinearMap.BilinForm.IsSymm.equivalent_weightedSumSquares_of_iIsOrtho`: an orthogonal basis
  identifies the associated quadratic form with a weighted sum of squares.
* `LinearMap.BilinForm.det_toMatrix_comp`, `LinearMap.BilinForm.det_toMatrix_eq_det_sq_mul_det`:
  the Gram determinant under a linear map and under a change of basis.
* `LinearMap.BilinForm.Equivalent.isSquare_det_mul_det`: equivalent forms have square product
  of Gram determinants in any finite bases with the same index type.
* `LinearMap.BilinForm.IsSymm.equivalent_iff_toQuadraticMap_equivalent`: when `2` is invertible,
  equivalence of symmetric bilinear forms is equivalent to equivalence of their quadratic forms.
* `LinearMap.BilinForm.iIsOrtho.dvd_apply`: divisibility from diagonal values.
* `LinearMap.BilinForm.isUnit_two_of_iIsOrtho_toBilin'_hyperbolic`: an orthogonal basis of the
  hyperbolic plane forces `2` to be a unit.
* `LinearMap.BilinForm.IsSymm.exists_forall_apply_self_dvd_of_forall_dvd`: over a local ring with
  `2` a unit, a minimal pairing yields a minimal self-pairing.
* `LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_isUnit_of_isUnit_det`: over a local ring
  with `2` a unit, a unit Gram determinant gives an orthogonal basis with unit self-pairings.
* `LinearMap.BilinForm.IsSymm.exists_equivalent_weightedSumSquares_of_isUnit_det`: such a form
  is isometric to a unit diagonal quadratic form, with a determinant change-of-basis equation.
* `LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_of_isAlt_imp_eq_zero`: a symmetric form
  that is zero or not alternating has an orthogonal basis, in every characteristic.
* `LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_iff`: this condition is also necessary.
* `LinearMap.BilinForm.IsSymm.exists_basis_toMatrix_eq_one`: over a field in which every element
  is a square, a nondegenerate symmetric form that is not alternating has an orthonormal basis.
* `LinearMap.BilinForm.IsSymm.equivalent_toBilin'_one`,
  `LinearMap.BilinForm.IsSymm.equivalent_of_finrank_eq`: such a form is equivalent to the standard
  form on `Fin n → K`, so any two of them of the same dimension are equivalent.
* `LinearMap.BilinForm.Nondegenerate.exists_basis_toMatrix_eq_J_or_toMatrix_eq_one`: the
  symplectic-or-orthonormal dichotomy.

## References

* A. A. Albert, *Symmetric and alternate matrices in an arbitrary field, I*, Trans. Amer. Math.
  Soc. 43 (1938), 386–436.
* O. T. O'Meara, *Introduction to Quadratic Forms*, 92:1.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8.
-/

public section

namespace LinearMap.BilinForm

/-- The Gram matrix in an orthogonal basis is the diagonal matrix of the self-pairings. -/
theorem iIsOrtho.toMatrix_eq_diagonal {R M ι : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [Fintype ι] [DecidableEq ι] {B : LinearMap.BilinForm R M}
    {b : Module.Basis ι R M} (hb : B.iIsOrtho b) :
    B.toMatrix b = Matrix.diagonal (fun i ↦ B (b i) (b i)) := by
  ext i j
  obtain rfl | hij := eq_or_ne i j
  · simp [toMatrix_apply]
  · simp [toMatrix_apply, iIsOrtho_def.mp hb i j hij, hij]

/-- The quadratic form of a symmetric bilinear form in an orthogonal basis is isometric to
the diagonal form of its self-pairings. -/
theorem IsSymm.equivalent_weightedSumSquares_of_iIsOrtho
    {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    [Invertible (2 : R)] {B : LinearMap.BilinForm R M} (hB : B.IsSymm)
    (b : Module.Basis ι R M)
    (hb : B.iIsOrtho b) :
    B.toQuadraticMap.Equivalent
      (QuadraticMap.weightedSumSquares R (fun i ↦ B (b i) (b i))) := by
  have hassoc : QuadraticMap.associated B.toQuadraticMap = B :=
    QuadraticMap.associated_left_inverse R hB.eq
  have horth : (QuadraticMap.associated B.toQuadraticMap).IsOrthoᵢ b := by
    rw [hassoc]
    exact LinearMap.isOrthoᵢ_def.mpr (iIsOrtho_def.mp hb)
  have heq := QuadraticMap.basisRepr_eq_of_iIsOrtho B.toQuadraticMap b horth
  simp only [BilinMap.toQuadraticMap_apply] at heq
  rw [← heq]
  exact ⟨QuadraticMap.isometryEquivBasisRepr B.toQuadraticMap b⟩

open LinearMap (BilinForm)
open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M}

/-- Pulling back a bilinear form along a linear map multiplies its Gram determinant by the
square of the coordinate-map determinant. The source and target bases use the same arbitrary
finite index type; no symmetry or nondegeneracy is required. -/
theorem det_toMatrix_comp {N ι : Type*} [AddCommGroup N] [Module R N]
    [Fintype ι] [DecidableEq ι] (b : Basis ι R M) (c : Basis ι R N)
    (C : BilinForm R N) (f : M →ₗ[R] N) :
    ((C.comp f f).toMatrix b).det =
      (LinearMap.toMatrix b c f).det ^ 2 * (C.toMatrix c).det := by
  rw [toMatrix_comp c b, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- A change of basis multiplies the Gram determinant by the square of the basis-change
matrix determinant. -/
theorem det_toMatrix_eq_det_sq_mul_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b c : Basis ι R M) (B : BilinForm R M) :
    (B.toMatrix c).det = (b.toMatrix c).det ^ 2 * (B.toMatrix b).det := by
  simpa only [comp_id_id, LinearMap.toMatrix_id_eq_basis_toMatrix] using
    det_toMatrix_comp c b B LinearMap.id

/-- The product of Gram determinants of equivalent bilinear forms is a square. This holds over
any commutative ring, including for singular and nonsymmetric forms, in any caller-provided
finite bases with the same index type. -/
theorem Equivalent.isSquare_det_mul_det {N ι : Type*} [AddCommGroup N] [Module R N]
    [Fintype ι] [DecidableEq ι] {C : BilinForm R N} (h : B.Equivalent C)
    (b : Basis ι R M) (c : Basis ι R N) :
    IsSquare ((B.toMatrix b).det * (C.toMatrix c).det) := by
  obtain ⟨e⟩ := h
  have hform : B = C.comp e.toLinearEquiv.toLinearMap e.toLinearEquiv.toLinearMap := by
    ext x y
    exact (e.map_app y x).symm
  refine ⟨(LinearMap.toMatrix b c e.toLinearEquiv.toLinearMap).det * (C.toMatrix c).det,
    ?_⟩
  conv_lhs => rw [hform]
  rw [det_toMatrix_comp b c]
  ring

/-- When `2` is invertible, symmetric bilinear forms are equivalent exactly when their
associated quadratic forms are equivalent. The underlying modules need not be finite or free. -/
theorem IsSymm.equivalent_iff_toQuadraticMap_equivalent
    {N : Type*} [AddCommGroup N] [Module R N] [Invertible (2 : R)]
    {C : BilinForm R N} (hB : B.IsSymm) (hC : C.IsSymm) :
    B.Equivalent C ↔ B.toQuadraticMap.Equivalent C.toQuadraticMap := by
  constructor
  · rintro ⟨e⟩
    exact ⟨{ toLinearEquiv := e.toLinearEquiv
             map_app' := fun x ↦ e.map_app x x }⟩
  · rintro ⟨f⟩
    have hform : B.toQuadraticMap = C.toQuadraticMap.comp f.toLinearEquiv.toLinearMap := by
      ext x
      exact (f.map_app x).symm
    have hassoc := congrArg (QuadraticMap.associated (R := R)) hform
    rw [QuadraticMap.associated_comp, QuadraticMap.associated_left_inverse R hB.eq,
      QuadraticMap.associated_left_inverse R hC.eq] at hassoc
    exact ⟨{ toLinearEquiv := f.toLinearEquiv
             map_app' := fun x y ↦ (LinearMap.congr_fun (LinearMap.congr_fun hassoc x) y).symm }⟩

/-- Along an orthogonal basis, a common divisor of the diagonal values of a bilinear form divides
every value of the form. -/
theorem iIsOrtho.dvd_apply {ι : Type*} {b : Basis ι R M} (hb : B.iIsOrtho b) {d : R}
    (hd : ∀ i, d ∣ B (b i) (b i)) (x y : M) : d ∣ B x y := by
  refine dvd_apply_of_forall_dvd_basis b (fun i j ↦ ?_) x y
  obtain rfl | hij := eq_or_ne i j
  · exact hd i
  · rw [iIsOrtho_def.mp hb i j hij]
    exact dvd_zero d

/-- If the hyperbolic plane, the form with Gram matrix `!![0, 1; 1, 0]` on `R²`, has an orthogonal
basis, then `2` is a unit in `R`. So over a ring such as `ℤ_2` the hyperbolic plane is not
diagonalizable. -/
theorem isUnit_two_of_iIsOrtho_toBilin'_hyperbolic {ι : Type*} {b : Basis ι R (Fin 2 → R)}
    (hb : (Matrix.toBilin' !![(0 : R), 1; 1, 0]).iIsOrtho b) : IsUnit (2 : R) := by
  have hd : ∀ v : Fin 2 → R, (2 : R) ∣ Matrix.toBilin' !![(0 : R), 1; 1, 0] v v := fun v ↦
    ⟨v 0 * v 1, by simp [Matrix.toBilin'_apply', Matrix.vecHead, Matrix.vecTail]; ring⟩
  refine isUnit_of_dvd_one ?_
  simpa [Matrix.toBilin'_apply'] using
    hb.dvd_apply (fun i ↦ hd (b i)) (Pi.single 0 1) (Pi.single 1 1)

/-- Over a local ring in which `2` is a unit, if a value `B u w` of a symmetric bilinear form
divides every value of the form, then so does one of the self-pairings `B u u`, `B w w` and
`B (u + w) (u + w)`. -/
theorem IsSymm.exists_forall_apply_self_dvd_of_forall_dvd [IsLocalRing R]
    (hB : B.IsSymm) (h2 : IsUnit (2 : R)) {u w : M} (h : ∀ y z, B u w ∣ B y z) :
    ∃ x, ∀ y z, B x x ∣ B y z := by
  obtain ⟨s, hs⟩ := h u u
  obtain ⟨t, ht⟩ := h w w
  by_cases hsu : IsUnit s
  · exact ⟨u, fun y z ↦ (hs ▸ (Units.mul_right_dvd (u := hsu.unit)).mpr dvd_rfl).trans (h y z)⟩
  by_cases htu : IsUnit t
  · exact ⟨w, fun y z ↦ (ht ▸ (Units.mul_right_dvd (u := htu.unit)).mpr dvd_rfl).trans (h y z)⟩
  -- Both `s` and `t` lie in the maximal ideal, so `s + t + 2` is a unit.
  have hunit : IsUnit (s + t + 2) := by
    by_contra hn
    refine (mem_nonunits_iff.mp ?_) h2
    have := IsLocalRing.nonunits_add (IsLocalRing.nonunits_add hn
      (mem_nonunits_iff.mpr ((IsUnit.neg_iff s).not.mpr hsu)))
      (mem_nonunits_iff.mpr ((IsUnit.neg_iff t).not.mpr htu))
    have hsum : s + t + 2 + -s + -t = (2 : R) := by ring
    rwa [hsum] at this
  have huw : B (u + w) (u + w) = B u w * (s + t + 2) := by
    simp only [map_add, LinearMap.add_apply, hs, ht, hB.eq w u]
    ring
  exact ⟨u + w, fun y z ↦
    (huw ▸ (Units.mul_right_dvd (u := hunit.unit)).mpr dvd_rfl).trans (h y z)⟩

/-- A symmetric form with unit Gram determinant over a local ring with two invertible has
an orthogonal basis with unit self-pairings. The input basis is arbitrary. -/
theorem IsSymm.exists_orthogonal_basis_isUnit_of_isUnit_det [IsLocalRing R] (hB : B.IsSymm)
    (h2 : IsUnit (2 : R)) {n : ℕ} (b : Basis (Fin n) R M)
    (hdet : IsUnit (B.toMatrix b).det) :
    ∃ c : Basis (Fin n) R M, B.iIsOrtho c ∧ ∀ i, IsUnit (B (c i) (c i)) := by
  classical
  let := Free.of_basis b
  let := Module.Finite.of_basis b
  induction n generalizing M with
  | zero => exact ⟨b, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  | succ n ih =>
    -- A unit determinant has a unit Gram entry; a minimal self-pairing is then a unit.
    obtain ⟨j, _, hj⟩ := IsLocalRing.exists_of_isUnit_sum
      (Matrix.det_succ_row_zero (B.toMatrix b) ▸ hdet)
    have hentry : IsUnit (B (b 0) (b j)) := by
      simpa only [toMatrix_apply] using
        isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hj)
    obtain ⟨x, hx⟩ := hB.exists_forall_apply_self_dvd_of_forall_dvd h2
      (fun _ _ ↦ hentry.dvd)
    have hxx : IsUnit (B x x) := isUnit_of_dvd_unit (hx (b 0) (b j)) hentry
    let N := B.orthogonal (R ∙ x)
    have hc := B.isCompl_span_singleton_orthogonal_of_isUnit x hxx
    have : Module.Finite R N := .equiv (Submodule.quotientEquivOfIsCompl _ _ hc)
    have : Flat R N := Flat.of_retract N.subtype
      (N.projectionOnto (R ∙ x) hc.symm) (by ext; simp)
    have : Free R N := free_of_flat_of_isLocalRing
    have hli : ∀ a : R, ∀ y ∈ N, a • x + y = 0 → a = 0 := by
      intro a y hy hay
      have hxy : B x y = 0 := (mem_orthogonal_span_singleton_iff B).mp hy
      have := congrArg (B x) hay
      simp only [map_add, map_smul, smul_eq_mul, hxy, add_zero, map_zero] at this
      exact (mem_nonZeroDivisors_iff_right.mp hxx.mem_nonZeroDivisors) a this
    have hsp : ∀ z : M, ∃ a : R, z + a • x ∈ N := by
      intro z
      obtain ⟨a, ha⟩ := (hxx.dvd : B x x ∣ B x z)
      refine ⟨-a, (mem_orthogonal_span_singleton_iff B).mpr ?_⟩
      simp only [map_add, map_smul, smul_eq_mul, ha]
      ring
    -- The split basis also computes the complement's rank and its unit Gram determinant.
    let v₀ := Module.finBasis R N
    let c₀ := Basis.mkFinCons x v₀ hli hsp
    have hn : finrank R N = n := by
      have h₀ := Module.finrank_eq_card_basis c₀
      have h₁ := Module.finrank_eq_card_basis b
      simp only [Fintype.card_fin] at h₀ h₁
      omega
    let v := Module.finBasisOfFinrankEq R N hn
    let c₁ := Basis.mkFinCons x v hli hsp
    have hsplit : (B.toMatrix c₁).det = B x x * ((B.restrict N).toMatrix v).det := by
      rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
      have hzero : ∀ j : Fin n, (B.toMatrix c₁) 0 j.succ = 0 := by
        intro j
        simpa only [toMatrix_apply, c₁, Basis.coe_mkFinCons, Fin.cons_zero,
          Fin.cons_succ, Function.comp_apply] using
          (mem_orthogonal_span_singleton_iff B).mp (v j).property
      simp only [hzero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
        Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
      congr 1
      · simp only [toMatrix_apply, c₁, Basis.coe_mkFinCons, Fin.cons_zero]
      · congr 1
        ext i j
        simp only [Matrix.submatrix_apply, toMatrix_apply, c₁, Basis.coe_mkFinCons,
          Fin.cons_succ, Function.comp_apply, restrict_apply, LinearMap.domRestrict_apply]
    have hvdet : IsUnit ((B.restrict N).toMatrix v).det := by
      have hu : IsUnit (B.toMatrix c₁).det := by
        rw [det_toMatrix_eq_det_sq_mul_det b c₁]
        exact ((b.isUnit_det c₁).pow 2).mul hdet
      exact isUnit_of_mul_isUnit_right (hsplit ▸ hu)
    obtain ⟨v', hv', _⟩ := ih (B := B.restrict N) (hB.restrict N) v hvdet
    obtain ⟨c, hc, -, -⟩ := hB.isRefl.exists_orthogonal_basis_of_orthogonal_span_singleton
      hxx.mem_nonZeroDivisors (fun _ ↦ hxx.dvd) hv'
    have hunit : IsUnit (∏ i, B (c i) (c i)) := by
      rw [← Matrix.det_diagonal, ← hc.toMatrix_eq_diagonal,
        det_toMatrix_eq_det_sq_mul_det b c]
      exact ((b.isUnit_det c).pow 2).mul hdet
    exact ⟨c, hc, fun i ↦ isUnit_of_dvd_unit
      (Finset.dvd_prod_of_mem (fun j ↦ B (c j) (c j)) (Finset.mem_univ i)) hunit⟩

/-- A symmetric form with unit Gram determinant over a local ring with two invertible is
isometric to a unit diagonal form. The product of its coefficients equals the original Gram
determinant times the square of a change-of-basis determinant. -/
theorem IsSymm.exists_equivalent_weightedSumSquares_of_isUnit_det [IsLocalRing R] (hB : B.IsSymm)
    (h2 : IsUnit (2 : R)) {n : ℕ} (b : Basis (Fin n) R M)
    (hdet : IsUnit (B.toMatrix b).det) :
    ∃ w : Fin n → Rˣ, B.toQuadraticMap.Equivalent (QuadraticMap.weightedSumSquares R w) ∧
      ∃ d : R, (∏ i, (w i : R)) = d ^ 2 * (B.toMatrix b).det := by
  classical
  let := h2.invertible
  obtain ⟨c, hc, hu⟩ := hB.exists_orthogonal_basis_isUnit_of_isUnit_det h2 b hdet
  let w : Fin n → Rˣ := fun i ↦ (hu i).unit
  have hw i : (w i : R) = B (c i) (c i) := (hu i).unit_spec
  have hmatrix : B.toMatrix c = Matrix.diagonal (fun i ↦ (w i : R)) := by
    simpa only [hw] using hc.toMatrix_eq_diagonal
  refine ⟨w, ?_, (b.toMatrix c).det, ?_⟩
  · simpa only [QuadraticMap.weightedSumSquares_units, hw] using
      hB.equivalent_weightedSumSquares_of_iIsOrtho c hc
  · rw [← Matrix.det_diagonal, ← hmatrix, det_toMatrix_eq_det_sq_mul_det b c]

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

/-- If `x` is non-isotropic for a symmetric form `B` and the restriction of `B` to the orthogonal
complement of `x` is alternating and nonzero, then some non-isotropic vector has an orthogonal
complement on which `B` is not alternating: given `u, w` orthogonal to `x` with `B u w ≠ 0`, the
vector `x + u` works. -/
private theorem IsSymm.exists_apply_self_ne_zero_and_not_isAlt_restrict_orthogonal
    (hB : B.IsSymm) {x : V} (hx : B x x ≠ 0) (halt : (B.restrict (B.orthogonal (K ∙ x))).IsAlt)
    (hne : B.restrict (B.orthogonal (K ∙ x)) ≠ 0) :
    ∃ y, B y y ≠ 0 ∧ ¬ (B.restrict (B.orthogonal (K ∙ y))).IsAlt := by
  obtain ⟨u, w, huw⟩ : ∃ u w : B.orthogonal (K ∙ x), B u w ≠ 0 := by
    by_contra! h
    exact hne (LinearMap.ext fun u => LinearMap.ext fun w => by simpa using h u w)
  have hxu : B x u = 0 := (mem_orthogonal_span_singleton_iff B).1 u.2
  have hxw : B x w = 0 := (mem_orthogonal_span_singleton_iff B).1 w.2
  have huu : B u u = 0 := by simpa using halt u
  have hww : B w w = 0 := by simpa using halt w
  set z := x + u with hz
  have hzz : B z z = B x x := by simp [hz, hxu, hB.eq u x, huu]
  have hzw : B z w = B u w := by simp [hz, hxw]
  refine ⟨z, hzz ▸ hx, fun halt' => huw ?_⟩
  obtain ⟨c, hc⟩ : ∃ c, c * B z z = B z w := ⟨B z w / B z z, div_mul_cancel₀ _ (hzz ▸ hx)⟩
  have hw' : w - c • z ∈ B.orthogonal (K ∙ z) :=
    (mem_orthogonal_span_singleton_iff B).2 (by simp [hc])
  have h0 : B w w - c * B z w - c * (B z w - c * B z z) = 0 := by
    simpa [hB.eq w z] using halt' ⟨w - c • z, hw'⟩
  have hcb : c * B z w = 0 := by linear_combination -h0 + c * hc + hww
  rw [← hzw]
  rcases mul_eq_zero.1 hcb with hc0 | hb0
  · rw [← hc, hc0, zero_mul]
  · exact hb0

/-- A symmetric form that is not alternating has a non-isotropic vector `x` such that the
restriction of the form to the orthogonal complement of `x` is zero or not alternating. -/
private theorem IsSymm.exists_apply_self_ne_zero_and_restrict_orthogonal_isAlt_imp_eq_zero
    (hB : B.IsSymm) (h : ¬B.IsAlt) :
    ∃ x, B x x ≠ 0 ∧
      ((B.restrict (B.orthogonal (K ∙ x))).IsAlt → B.restrict (B.orthogonal (K ∙ x)) = 0) := by
  obtain ⟨x, hx⟩ : ∃ x, B x x ≠ 0 := by simpa [IsAlt, LinearMap.IsAlt] using h
  by_cases hW : (B.restrict (B.orthogonal (K ∙ x))).IsAlt ∧ B.restrict (B.orthogonal (K ∙ x)) ≠ 0
  · obtain ⟨y, hy, hy'⟩ :=
      hB.exists_apply_self_ne_zero_and_not_isAlt_restrict_orthogonal hx hW.1 hW.2
    exact ⟨y, hy, fun h' => (hy' h').elim⟩
  · exact ⟨x, hx, fun h' => not_not.1 (not_and.1 hW h')⟩

variable [FiniteDimensional K V]

/-- **A symmetric bilinear form that is zero or not alternating has an orthogonal basis**, in
every characteristic. Away from characteristic two the hypothesis is automatic for symmetric
forms (`TauCeti.BilinForm.eq_zero_of_isSymm_of_isAlt`), which recovers
`LinearMap.BilinForm.exists_orthogonal_basis`; in characteristic two it excludes exactly the
nonzero alternating forms. -/
theorem IsSymm.exists_orthogonal_basis_of_isAlt_imp_eq_zero (hB : B.IsSymm)
    (h : B.IsAlt → B = 0) : ∃ v : Basis (Fin (finrank K V)) K V, B.iIsOrtho v := by
  suffices ∀ d, finrank K V = d → ∃ v : Basis (Fin d) K V, B.iIsOrtho v from this _ rfl
  intro d hd
  induction d generalizing V with
  | zero => exact ⟨basisOfFinrankZero hd, fun i _ _ => i.elim0⟩
  | succ d ih =>
    obtain rfl | hB₀ := eq_or_ne B 0
    · exact ⟨finBasisOfFinrankEq K V hd, fun _ _ _ => rfl⟩
    obtain ⟨x, hx, hW⟩ :=
      hB.exists_apply_self_ne_zero_and_restrict_orthogonal_isAlt_imp_eq_zero
        fun halt => hB₀ (h halt)
    have hd' : finrank K (B.orthogonal (K ∙ x)) = d := by
      have hdim := B.finrank_orthogonal_span_singleton_add_one hx
      omega
    obtain ⟨v, hv⟩ := ih (hB.restrict _) hW hd'
    obtain ⟨b, hb, -, -⟩ := hB.isRefl.exists_orthogonal_basis_of_orthogonal_span_singleton
      (mem_nonZeroDivisors_of_ne_zero hx) (fun _ ↦ (Ne.isUnit hx).dvd) hv
    exact ⟨b, hb⟩

/-- **A symmetric bilinear form has an orthogonal basis if and only if it is zero or not
alternating.** The forward direction is the observation that an orthogonal basis of an alternating
form pairs every two basis vectors to zero. -/
theorem IsSymm.exists_orthogonal_basis_iff (hB : B.IsSymm) :
    (∃ v : Basis (Fin (finrank K V)) K V, B.iIsOrtho v) ↔ (B.IsAlt → B = 0) := by
  refine ⟨fun ⟨v, hv⟩ halt => ext_basis v fun i j => ?_,
    hB.exists_orthogonal_basis_of_isAlt_imp_eq_zero⟩
  obtain rfl | hij := eq_or_ne i j
  · simp [halt.self_eq_zero]
  · simp [iIsOrtho_def.1 hv i j hij]

/-- **A nondegenerate symmetric form that is not alternating has an orthonormal basis**, over a
field in which every element is a square: rescaling an orthogonal basis by inverse square roots of
the self-pairings makes the matrix of the form the identity. The hypothesis on squares holds in
every finite field of characteristic two (`isSquare_of_charTwo'`). -/
theorem IsSymm.exists_basis_toMatrix_eq_one (hsq : ∀ a : K, IsSquare a) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) (h : B.IsAlt → B = 0) :
    ∃ v : Basis (Fin (finrank K V)) K V, BilinForm.toMatrix v B = 1 := by
  obtain ⟨v, hv⟩ := hB.exists_orthogonal_basis_of_isAlt_imp_eq_zero h
  have hvv : ∀ i, B (v i) (v i) ≠ 0 := hv.not_isOrtho_basis_self_of_nondegenerate hnd
  choose s hs using fun i => hsq (B (v i) (v i))
  have hs0 : ∀ i, s i ≠ 0 := fun i h0 => hvv i (by rw [hs i, h0, mul_zero])
  refine ⟨v.isUnitSMul (w := fun i => (s i)⁻¹) fun i => (inv_ne_zero (hs0 i)).isUnit, ?_⟩
  ext i j
  obtain rfl | hij := eq_or_ne i j
  · simp [toMatrix_apply, Basis.isUnitSMul_apply, hs i, hs0 i]
  · simp [toMatrix_apply, Basis.isUnitSMul_apply, iIsOrtho_def.1 hv i j hij, hij]

/-- Over a field in which every element is a square, a nondegenerate symmetric form that is not
alternating is equivalent to the standard form `∑ i, x i * y i` on `Fin n → K`, for `n` the
dimension. -/
theorem IsSymm.equivalent_toBilin'_one (hsq : ∀ a : K, IsSquare a) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) (h : B.IsAlt → B = 0) :
    B.Equivalent (Matrix.toBilin' (1 : Matrix (Fin (finrank K V)) (Fin (finrank K V)) K)) := by
  obtain ⟨v, hv⟩ := hB.exists_basis_toMatrix_eq_one hsq hnd h
  exact ⟨v.isometryEquivOfToMatrixEq (Pi.basisFun K _)
    (by rw [hv, toMatrix_basisFun, toMatrix'_toBilin'])⟩

/-- Over a field in which every element is a square, two nondegenerate symmetric forms that are
not alternating, on spaces of the same dimension, are equivalent. -/
theorem IsSymm.equivalent_of_finrank_eq {V' : Type*} [AddCommGroup V'] [Module K V']
    [FiniteDimensional K V'] {B' : BilinForm K V'} (hsq : ∀ a : K, IsSquare a) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) (h : B.IsAlt → B = 0) (hB' : B'.IsSymm) (hnd' : B'.Nondegenerate)
    (h' : B'.IsAlt → B' = 0) (hdim : finrank K V = finrank K V') : B.Equivalent B' := by
  have e := hB.equivalent_toBilin'_one hsq hnd h
  rw [hdim] at e
  exact e.trans (hB'.equivalent_toBilin'_one hsq hnd' h').symm

/-- **The normal-form dichotomy for a nondegenerate form that is alternating or symmetric**, over
a field in which every element is a square: an alternating form has a symplectic basis, and a
symmetric form that is not alternating has an orthonormal basis. In characteristic two every
alternating form is symmetric, so the hypothesis is just symmetry there. -/
theorem Nondegenerate.exists_basis_toMatrix_eq_J_or_toMatrix_eq_one (hsq : ∀ a : K, IsSquare a)
    (hnd : B.Nondegenerate) (h : B.IsAlt ∨ B.IsSymm) :
    (B.IsAlt ∧
        ∃ (m : ℕ) (v : Basis (Fin m ⊕ Fin m) K V), BilinForm.toMatrix v B = Matrix.J (Fin m) K) ∨
      (¬B.IsAlt ∧ ∃ v : Basis (Fin (finrank K V)) K V, BilinForm.toMatrix v B = 1) := by
  by_cases halt : B.IsAlt
  · exact Or.inl ⟨halt, halt.exists_basis_toMatrix_eq_J hnd⟩
  · exact Or.inr ⟨halt, (h.resolve_left halt).exists_basis_toMatrix_eq_one hsq hnd
      fun h' => (halt h').elim⟩

end Field

end LinearMap.BilinForm
