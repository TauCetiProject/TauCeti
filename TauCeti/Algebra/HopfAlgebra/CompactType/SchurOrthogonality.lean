/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Dual
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Simple
public import TauCeti.Algebra.Coalgebra.Subcomodule.Dual
public import TauCeti.Algebra.HopfAlgebra.CompactType.Haar

/-!
# Algebraic Schur orthogonality for unitary comodules

For a finite-dimensional unitary comodule `(M, b)` with coefficient matrix `u` over a complex Hopf
star algebra `A` carrying a normalized two-sided invariant functional `h`, we prove:

* `S (u i j) = star (u j i)` and `coefficientMatrix b.dualBasis = u.map star`;
* orthogonality of matrix coefficients of comodules with no nonzero intertwiner;
* positivity-free weighted Schur orthogonality with a unique positive definite matrix `Ft`
  (`Ft.trace = Ft⁻¹.trace`), and `S² (u) = Ftᵀ * u * (Ftᵀ)⁻¹`;
* specialization to any `AlgebraicHaar A` state.

## Main declarations

* `TauCeti.Comodule.map_antipode_coefficientMatrix_eq_conjTranspose`,
  `TauCeti.Comodule.coefficientMatrix_dualBasis_eq_map_star`
* `LinearMap.IsRightInvariantIntegral.apply_star_coefficientMatrix_mul_eq_zero`,
  `LinearMap.IsLeftInvariantIntegral.apply_coefficientMatrix_mul_star_eq_zero`
* `LinearMap.existsUnique_posDef_schur_orthogonality`,
  `TauCeti.AlgebraicHaar.schur_orthogonality`,
  `TauCeti.AlgebraicHaar.map_antipode_antipode_coefficientMatrix`

## References

* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*,
  SMF, 2013, Theorem 1.4.3.
* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Section 3.2.
-/

public section

open Module Matrix
open scoped ComplexOrder

namespace TauCeti.Comodule

attribute [local instance] dual

section Antipode

variable {R A M ι : Type*} [CommSemiring R] [Semiring A] [StarRing A] [HopfAlgebra R A]
  [AddCommMonoid M] [Module R M] [Comodule R A M] [Fintype ι] [DecidableEq ι]

/-- For a finite basis with unitary coefficient matrix, the entrywise antipode of the coefficient
matrix is its conjugate transpose. -/
theorem map_antipode_coefficientMatrix_eq_conjTranspose (b : Basis ι R M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    (coefficientMatrix (C := A) b).map (HopfAlgebra.antipode R) =
      (coefficientMatrix (C := A) b)ᴴ :=
  left_inv_eq_right_inv (map_antipode_mul_coefficientMatrix b) (Unitary.mem_iff.mp hu).2

/-- Entrywise form of `map_antipode_coefficientMatrix_eq_conjTranspose`. -/
theorem antipode_coefficientMatrix_of_mem_unitary (b : Basis ι R M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) (i j : ι) :
    HopfAlgebra.antipode R (coefficientMatrix (C := A) b i j) =
      star (coefficientMatrix (C := A) b j i) :=
  congrFun (congrFun (map_antipode_coefficientMatrix_eq_conjTranspose b hu) i) j

/-- For a finite basis with unitary coefficient matrix, the coefficient matrix of the dual
comodule in the dual basis is the entrywise star of the original coefficient matrix. -/
theorem coefficientMatrix_dualBasis_eq_map_star [Module.Finite R M] [Module.Projective R M]
    (b : Basis ι R M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    coefficientMatrix (C := A) b.dualBasis = (coefficientMatrix (C := A) b).map star := by
  ext i j
  rw [coefficientMatrix_dualBasis, Matrix.map_apply, Matrix.transpose_apply, Matrix.map_apply]
  exact antipode_coefficientMatrix_of_mem_unitary b hu j i

end Antipode

section AntipodeSquared

variable {R A M ι : Type*} [CommRing R] [Ring A] [StarRing A] [HopfAlgebra R A]
  [AddCommGroup M] [Module R M] [Comodule R A M] [Fintype ι] [DecidableEq ι]

/-- If `u` is a unitary coefficient matrix and `Ft` is an invertible scalar matrix satisfying
`(u.map star)ᴴ * Ft * (u.map star) = Ft`, then `S²(u) = Ftᵀ * u * (Ftᵀ)⁻¹`. -/
theorem map_antipode_antipode_coefficientMatrix
    (b : Basis ι R M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {Ft : Matrix ι ι R} (hFt : IsUnit Ft.det)
    (hinv : ((coefficientMatrix (C := A) b).map star)ᴴ * Ft.map (algebraMap R A) *
        (coefficientMatrix (C := A) b).map star = Ft.map (algebraMap R A)) :
    (coefficientMatrix (C := A) b).map (HopfAlgebra.antipode R ∘ HopfAlgebra.antipode R) =
      Ftᵀ.map (algebraMap R A) * coefficientMatrix (C := A) b *
        (Ftᵀ)⁻¹.map (algebraMap R A) := by
  have : Module.Finite R M := Module.Finite.of_basis b
  have : Module.Projective R M := Module.Projective.of_basis b
  set u := coefficientMatrix (C := A) b
  set ubar := u.map star
  set f := algebraMap R A
  have hS2 : u.map (HopfAlgebra.antipode R ∘ HopfAlgebra.antipode R) =
      (ubar.map (HopfAlgebra.antipode R))ᵀ := by
    ext i j
    simpa [ubar] using congrArg (HopfAlgebra.antipode R)
      (antipode_coefficientMatrix_of_mem_unitary b hu i j)
  have hubar_inv : ubar * ubar.map (HopfAlgebra.antipode R) = 1 := by
    rw [show ubar = coefficientMatrix (C := A) b.dualBasis from
      (coefficientMatrix_dualBasis_eq_map_star b hu).symm]
    exact coefficientMatrix_mul_map_antipode b.dualBasis
  have hleft : (Ft⁻¹.map f * ubarᴴ * Ft.map f) * ubar = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc ubarᴴ, hinv, ← Matrix.map_mul,
      nonsing_inv_mul _ hFt, Matrix.map_one _ (map_zero f) (map_one f)]
  have hSbar : ubar.map (HopfAlgebra.antipode R) = Ft⁻¹.map f * ubarᴴ * Ft.map f :=
    (left_inv_eq_right_inv hleft hubar_inv).symm
  rw [hS2, hSbar, show ubarᴴ = uᵀ by ext i j; simp [ubar], ← Matrix.transpose_nonsing_inv]
  ext i j
  simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.map_apply, f,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by rw [mul_comm (Ft q i)]

end AntipodeSquared

end TauCeti.Comodule

namespace LinearMap

open TauCeti TauCeti.Comodule

attribute [local instance] Comodule.dual

section Averaging

variable {R A M N ι κ : Type*} [CommSemiring R] [StarRing R]
  [Semiring A] [StarRing A] [Bialgebra R A] [StarModule R A] [StarCoalgebra R A]
  [AddCommMonoid M] [Module R M] [Comodule R A M]
  [AddCommMonoid N] [Module R N] [Comodule R A N]
  {h : A →ₗ[R] R}

private theorem sum4_swap {R A ι κ : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
    [Fintype ι] [Fintype κ] (X : Matrix ι κ R) (c : ι → ι → κ → κ → R) (g : ι → κ → A) :
    ∑ r : κ, ∑ s : ι, ∑ p : κ, ∑ q : ι, (X q p * c q s p r) • g s r =
      ∑ p : κ, ∑ q : ι, X q p • ∑ s : ι, ∑ r : κ, c q s p r • g s r :=
  calc ∑ r, ∑ s, ∑ p, ∑ q, (X q p * c q s p r) • g s r
      = ∑ rs : κ × ι, ∑ pq : κ × ι, (X pq.2 pq.1 * c pq.2 rs.2 pq.1 rs.1) • g rs.2 rs.1 := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ pq : κ × ι, ∑ rs : κ × ι, (X pq.2 pq.1 * c pq.2 rs.2 pq.1 rs.1) • g rs.2 rs.1 :=
        Finset.sum_comm
    _ = ∑ p, ∑ q, X q p • ∑ s, ∑ r, c q s p r • g s r := by
        simp_rw [Fintype.sum_prod_type, ← smul_smul, ← Finset.smul_sum]
        exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
          congrArg _ Finset.sum_comm

private theorem mul_single_mul_apply {A α β ι κ : Type*} [Semiring A]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix α ι A) (Q : Matrix κ β A) (i : ι) (k : κ) (a : α) (b : β) :
    (P * Matrix.single i k (1 : A) * Q) a b = P a i * Q k b := by
  simp only [Matrix.mul_apply, Matrix.single, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_eq_single k (fun q _ hq ↦ by simp [Ne.symm hq]) (by simp),
    Finset.sum_eq_single i (fun p _ hp ↦ by simp [Ne.symm hp]) (by simp)]
  simp

private noncomputable def coeffRepr {R A M ι : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [Coalgebra R A] [AddCommMonoid M] [Module R M] [Comodule R A M] [Fintype ι]
    (b : Basis ι R M) (i j : ι) : Coalgebra.Repr R (coefficientMatrix (C := A) b i j) ι :=
  ⟨Finset.univ, fun k ↦ coefficientMatrix (C := A) b i k,
    fun k ↦ coefficientMatrix (C := A) b k j, (comul_coefficientMatrix_eq_sum b i j).symm⟩

/-- Right invariance of `h` implies that `Y = h (uᴴ X v)` satisfies `uᴴ Y v = Y`. -/
theorem IsRightInvariantIntegral.conjTranspose_mul_haar_avg_mul [Fintype ι] [Fintype κ]
    (hr : h.IsRightInvariantIntegral) (b : Basis ι R M) (c : Basis κ R N)
    (X : Matrix ι κ R) :
    (coefficientMatrix (C := A) b)ᴴ *
        (((coefficientMatrix (C := A) b)ᴴ * X.map (algebraMap R A) *
          coefficientMatrix (C := A) c).map h).map (algebraMap R A) *
        coefficientMatrix (C := A) c =
      (((coefficientMatrix (C := A) b)ᴴ * X.map (algebraMap R A) *
        coefficientMatrix (C := A) c).map h).map (algebraMap R A) := by
  set u := coefficientMatrix (C := A) b; set v := coefficientMatrix (C := A) c
  ext a d
  simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply,
    Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
    Finset.mul_sum, Finset.sum_mul, map_sum, map_smul, smul_eq_mul]
  rw [sum4_swap X (fun q s p r ↦ h (star (u q s) * v p r)) (fun s r ↦ star (u s a) * v r d)]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  rw [← smul_smul]; congr 1
  simpa [coeffRepr] using hr.sum_sum_mul (coeffRepr b q a).star (coeffRepr c p d)

/-- Left invariance of `h` implies that `Z = h (u X vᴴ)` satisfies `u Z vᴴ = Z`. -/
theorem IsLeftInvariantIntegral.mul_haar_avg_mul_conjTranspose [Fintype ι] [Fintype κ]
    (hl : h.IsLeftInvariantIntegral) (b : Basis ι R M) (c : Basis κ R N)
    (X : Matrix ι κ R) :
    coefficientMatrix (C := A) b *
        ((coefficientMatrix (C := A) b * X.map (algebraMap R A) *
          (coefficientMatrix (C := A) c)ᴴ).map h).map (algebraMap R A) *
        (coefficientMatrix (C := A) c)ᴴ =
      ((coefficientMatrix (C := A) b * X.map (algebraMap R A) *
        (coefficientMatrix (C := A) c)ᴴ).map h).map (algebraMap R A) := by
  set u := coefficientMatrix (C := A) b; set v := coefficientMatrix (C := A) c
  ext a d
  simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply,
    Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
    Finset.mul_sum, Finset.sum_mul, map_sum, map_smul, smul_eq_mul]
  rw [sum4_swap X (fun q s p r ↦ h (u s q * star (v r p))) (fun s r ↦ u a s * star (v d r))]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  rw [← smul_smul]; congr 1
  simpa [coeffRepr] using hl.sum_sum_mul (coeffRepr b a q) (coeffRepr c d p).star

/-- **Distinct-comodule orthogonality (first form).** If `h` is right invariant, `b` has unitary
coefficient matrix `u`, and there is no nonzero comodule morphism `N → M`, then
`h (star (u i j) * v k l) = 0`. -/
theorem IsRightInvariantIntegral.apply_star_coefficientMatrix_mul_eq_zero
    [Fintype ι] [DecidableEq ι] [Finite κ]
    (hr : h.IsRightInvariantIntegral) (b : Basis ι R M) (c : Basis κ R N)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    (hHom : ∀ g : Comodule.Hom R A N M, g = 0) (i j : ι) (k l : κ) :
    h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) c k l) = 0 := by
  have := Fintype.ofFinite κ; classical
  set u := coefficientMatrix (C := A) b; set v := coefficientMatrix (C := A) c
  let Y : Matrix ι κ R := (uᴴ * (Matrix.single i k (1 : R)).map (algebraMap R A) * v).map h
  have hcomm : u * Y.map (algebraMap R A) = Y.map (algebraMap R A) * v := by
    calc u * Y.map (algebraMap R A)
        = (u * uᴴ) * (Y.map (algebraMap R A) * v) := by
          rw [Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, hr.conjTranspose_mul_haar_avg_mul b c]
      _ = Y.map (algebraMap R A) * v := by
          rw [← Matrix.star_eq_conjTranspose, (Unitary.mem_iff.mp hu).2, Matrix.one_mul]
  have hY0 : Y j l = 0 := by
    rw [Comodule.Hom.eq_zero_of_coefficientMatrix_mul_eq c b hHom hcomm]; rfl
  simpa [Y, mul_single_mul_apply] using hY0

/-- **Distinct-comodule orthogonality (second form).** If `h` is left invariant, `c` has unitary
coefficient matrix `v`, and there is no nonzero comodule morphism `N → M`, then
`h (u i j * star (v k l)) = 0`. -/
theorem IsLeftInvariantIntegral.apply_coefficientMatrix_mul_star_eq_zero
    [Finite ι] [Fintype κ] [DecidableEq κ]
    (hl : h.IsLeftInvariantIntegral) (b : Basis ι R M) (c : Basis κ R N)
    (hv : coefficientMatrix (C := A) c ∈ unitary (Matrix κ κ A))
    (hHom : ∀ g : Comodule.Hom R A N M, g = 0) (i j : ι) (k l : κ) :
    h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) c k l)) = 0 := by
  have := Fintype.ofFinite ι; classical
  set u := coefficientMatrix (C := A) b; set v := coefficientMatrix (C := A) c
  let Z : Matrix ι κ R := (u * (Matrix.single j l (1 : R)).map (algebraMap R A) * vᴴ).map h
  have hcomm : u * Z.map (algebraMap R A) = Z.map (algebraMap R A) * v := by
    calc u * Z.map (algebraMap R A)
        = (u * Z.map (algebraMap R A) * vᴴ) * v := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
            (Unitary.mem_iff.mp hv).1, Matrix.mul_one]
      _ = Z.map (algebraMap R A) * v := by rw [hl.mul_haar_avg_mul_conjTranspose b c]
  have hZ0 : Z i k = 0 := by
    rw [Comodule.Hom.eq_zero_of_coefficientMatrix_mul_eq c b hHom hcomm]; rfl
  simpa [Z, mul_single_mul_apply] using hZ0

end Averaging

section SchurOrthogonality

variable {A M ι κ : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A]
  [StarModule ℂ A] [StarCoalgebra ℂ A]
  [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

private theorem inv_smul_of_isUnit {G : Matrix ι ι ℂ} (hG : IsUnit G) {c : ℂ} (hc : c ≠ 0) :
    (c • G)⁻¹ = c⁻¹ • G⁻¹ :=
  Matrix.inv_eq_right_inv <| by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hc, one_smul,
      mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hG)]

omit [StarCoalgebra ℂ A] in
/-- A unitary basis on the dual comodule produces a positive definite scalar matrix `G`
intertwining `u.map star` and its inverse. -/
private theorem exists_posDef_dual_invariant [Module.Finite ℂ M]
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    (c : Basis κ ℂ (Module.Dual ℂ M))
    (hc : coefficientMatrix (C := A) c ∈ unitary (Matrix κ κ A)) :
    ∃ G : Matrix ι ι ℂ, G.PosDef ∧
      ((coefficientMatrix (C := A) b).map star)ᴴ * G.map (algebraMap ℂ A) *
          (coefficientMatrix (C := A) b).map star = G.map (algebraMap ℂ A) ∧
      (coefficientMatrix (C := A) b).map star * G⁻¹.map (algebraMap ℂ A) *
          ((coefficientMatrix (C := A) b).map star)ᴴ = G⁻¹.map (algebraMap ℂ A) := by
  set f := algebraMap ℂ A
  set ubar := (coefficientMatrix (C := A) b).map star
  set v := coefficientMatrix (C := A) c
  set P : Matrix κ ι ℂ := c.toMatrix b.dualBasis
  set R : Matrix ι κ ℂ := b.dualBasis.toMatrix c
  have hPR : P * R = 1 := c.toMatrix_mul_toMatrix_flip b.dualBasis
  have hRP : R * P = 1 := b.dualBasis.toMatrix_mul_toMatrix_flip c
  have hstar : Function.Semiconj f star star := fun z ↦ algebraMap_star_comm z
  have hubar : coefficientMatrix (C := A) b.dualBasis = ubar :=
    coefficientMatrix_dualBasis_eq_map_star b hu
  have hPu : v * P.map f = P.map f * ubar := hubar ▸ c.coefficientMatrix_mul_toMatrix b.dualBasis
  have hRu : ubar * R.map f = R.map f * v := hubar ▸ b.dualBasis.coefficientMatrix_mul_toMatrix c
  refine ⟨Pᴴ * P, PosDef.conjTranspose_mul_self P fun x y hxy ↦ by
      simpa [Matrix.mulVec_mulVec, hRP] using congrArg R.mulVec hxy, ?_, ?_⟩
  · rw [Matrix.map_mul, Matrix.conjTranspose_map _ hstar]
    calc ubarᴴ * ((P.map f)ᴴ * P.map f) * ubar
        = (P.map f * ubar)ᴴ * (P.map f * ubar) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (P.map f)ᴴ * (vᴴ * v) * P.map f := by
          rw [← hPu]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (P.map f)ᴴ * P.map f := by
          rw [← Matrix.star_eq_conjTranspose, (Unitary.mem_iff.mp hc).1, Matrix.mul_one]
  · have hinv : (Pᴴ * P)⁻¹ = R * Rᴴ := Matrix.inv_eq_right_inv <| by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, hPR, Matrix.one_mul, ← Matrix.conjTranspose_mul,
        hRP, Matrix.conjTranspose_one]
    rw [hinv, Matrix.map_mul, Matrix.conjTranspose_map _ hstar]
    calc ubar * (R.map f * (R.map f)ᴴ) * ubarᴴ
        = (ubar * R.map f) * (ubar * R.map f)ᴴ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = R.map f * (v * vᴴ) * (R.map f)ᴴ := by
          rw [hRu]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = R.map f * (R.map f)ᴴ := by
          rw [← Matrix.star_eq_conjTranspose, (Unitary.mem_iff.mp hc).2, Matrix.mul_one]

/-- Rescale a positive definite complex matrix by a positive real scalar so that it and its
inverse have the same trace. -/
private theorem exists_smul_trace_eq_inv_trace [Nonempty ι] {G : Matrix ι ι ℂ} (hG : G.PosDef) :
    ∃ r : ℝ, 0 < r ∧ (((r : ℂ) • G).trace = ((r : ℂ) • G)⁻¹.trace) := by
  obtain ⟨hpos, him⟩ := Complex.lt_def.mp hG.trace_pos
  obtain ⟨hipos, hiim⟩ := Complex.lt_def.mp hG.inv.trace_pos
  let r : ℝ := Real.sqrt (G⁻¹.trace.re / G.trace.re)
  have hr : 0 < r := Real.sqrt_pos.mpr (div_pos hipos hpos)
  refine ⟨r, hr, ?_⟩
  rw [inv_smul_of_isUnit hG.isUnit (Complex.ofReal_ne_zero.mpr hr.ne'), Matrix.trace_smul,
    Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
    show G.trace = (G.trace.re : ℂ) from Complex.ext rfl him.symm,
    show G⁻¹.trace = (G⁻¹.trace.re : ℂ) from Complex.ext rfl hiim.symm]
  norm_cast
  exact mul_left_cancel₀ hr.ne' <| by
    rw [← mul_assoc, ← sq, Real.sq_sqrt (div_nonneg hipos.le hpos.le),
      div_mul_cancel₀ _ hpos.ne', ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]

/-- Two positive definite complex matrices with equal self- and inverse-traces and identical
trace-normalized entries are equal. -/
private theorem posDef_eq_of_div_trace_eq [Nonempty ι] {Ft₁ Ft₂ : Matrix ι ι ℂ}
    (hFt₁ : Ft₁.PosDef) (htr₁ : Ft₁.trace = Ft₁⁻¹.trace)
    (hFt₂ : Ft₂.PosDef) (htr₂ : Ft₂.trace = Ft₂⁻¹.trace)
    (hdiv : ∀ j l, Ft₁ j l / Ft₁.trace = Ft₂ j l / Ft₂.trace) : Ft₁ = Ft₂ := by
  have htr₁_ne : Ft₁.trace ≠ 0 := hFt₁.trace_pos.ne'
  have htr₂_ne : Ft₂.trace ≠ 0 := hFt₂.trace_pos.ne'
  set lam : ℂ := Ft₁.trace / Ft₂.trace
  have hlam_ne : lam ≠ 0 := div_ne_zero htr₁_ne htr₂_ne
  have hlam_eq : Ft₁ = lam • Ft₂ := by
    ext j l
    have hmul := congrArg (· * Ft₁.trace) (hdiv j l)
    rw [div_mul_cancel₀ _ htr₁_ne] at hmul
    simp only [Matrix.smul_apply, smul_eq_mul, lam, hmul]; ring
  have hlam_inv : lam = lam⁻¹ := mul_right_cancel₀ htr₂_ne <| by
    calc lam * Ft₂.trace = Ft₁.trace := by rw [hlam_eq, Matrix.trace_smul, smul_eq_mul]
      _ = (lam⁻¹ • Ft₂⁻¹).trace := by rw [htr₁, hlam_eq, inv_smul_of_isUnit hFt₂.isUnit hlam_ne]
      _ = lam⁻¹ * Ft₂.trace := by rw [Matrix.trace_smul, smul_eq_mul, ← htr₂]
  have hlam_sq : lam * lam = 1 := by rw [← mul_inv_cancel₀ hlam_ne, ← hlam_inv]
  obtain ⟨hre₁, him₁⟩ := Complex.lt_def.mp hFt₁.trace_pos
  obtain ⟨hre₂, him₂⟩ := Complex.lt_def.mp hFt₂.trace_pos
  have hlam_real : lam = ((Ft₁.trace.re / Ft₂.trace.re : ℝ) : ℂ) := by
    rw [Complex.ofReal_div]
    exact congrArg₂ (· / ·) (Complex.ext rfl him₁.symm) (Complex.ext rfl him₂.symm)
  have hlam_one : lam = 1 := by
    have hpos : 0 < Ft₁.trace.re / Ft₂.trace.re := div_pos hre₁ hre₂
    rw [hlam_real] at hlam_sq ⊢; norm_cast at hlam_sq ⊢; nlinarith
  rw [hlam_eq, hlam_one, one_smul]

/-- Left invariance forces `h (u i j * star (u k l)) = δ_{i, k} D j l` on a simple unitary
comodule. -/
private theorem exists_schur_right_matrix [Module.Finite ℂ M] {h : A →ₗ[ℂ] ℂ}
    (hl : h.IsLeftInvariantIntegral) [IsSimpleOrder (Subcomodule ℂ A M)]
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ∃ D : Matrix ι ι ℂ, ∀ i j k l,
      h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
        if i = k then D j l else 0 := by
  have : Nontrivial M := Subcomodule.nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
  obtain ⟨i₀⟩ := b.index_nonempty
  set u := coefficientMatrix (C := A) b; set f := algebraMap ℂ A
  refine ⟨Matrix.of fun j l ↦ h (u i₀ j * star (u i₀ l)), fun i j k l ↦ ?_⟩
  let Z : Matrix ι ι ℂ := (u * (Matrix.single j l (1 : ℂ)).map f * uᴴ).map h
  have hcomm : u * Z.map f = Z.map f * u := by
    calc u * Z.map f = (u * Z.map f * uᴴ) * u := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
            (Unitary.mem_iff.mp hu).1, Matrix.mul_one]
      _ = Z.map f * u := by rw [hl.mul_haar_avg_mul_conjTranspose b b]
  obtain ⟨d, hd⟩ := Comodule.exists_eq_smul_one_of_coefficientMatrix_comm b hcomm
  have hZ (a c' : ι) : Z a c' = h (u a j * star (u c' l)) := by simp [Z, mul_single_mul_apply]
  have hd_val : d = h (u i₀ j * star (u i₀ l)) := by
    simpa [hZ] using (congrFun (congrFun hd i₀) i₀).symm
  by_cases hik : i = k <;> simpa [hZ, hd_val, hik] using congrFun (congrFun hd i) k

/-- Right invariance forces `h (star (u i j) * u k l) = δ_{j, l} C i k` on a simple unitary
comodule. -/
private theorem exists_schur_left_matrix [Module.Finite ℂ M] {h : A →ₗ[ℂ] ℂ}
    (hr : h.IsRightInvariantIntegral) [IsSimpleOrder (Subcomodule ℂ A M)]
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ∃ C : Matrix ι ι ℂ, ∀ i j k l,
      h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
        if j = l then C i k else 0 := by
  have : Nontrivial M := Subcomodule.nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
  obtain ⟨i₀⟩ := b.index_nonempty
  set u := coefficientMatrix (C := A) b; set f := algebraMap ℂ A
  refine ⟨Matrix.of fun i k ↦ h (star (u i i₀) * u k i₀), fun i j k l ↦ ?_⟩
  let Y : Matrix ι ι ℂ := (uᴴ * (Matrix.single i k (1 : ℂ)).map f * u).map h
  have hcomm : u * Y.map f = Y.map f * u := by
    calc u * Y.map f = (u * uᴴ) * (Y.map f * u) := by
          rw [Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, hr.conjTranspose_mul_haar_avg_mul b b]
      _ = Y.map f * u := by
          rw [← Matrix.star_eq_conjTranspose, (Unitary.mem_iff.mp hu).2, Matrix.one_mul]
  obtain ⟨c0, hc0⟩ := Comodule.exists_eq_smul_one_of_coefficientMatrix_comm b hcomm
  have hY (a c' : ι) : Y a c' = h (star (u i a) * u k c') := by simp [Y, mul_single_mul_apply]
  have hc0_val : c0 = h (star (u i i₀) * u k i₀) := by
    simpa [hY] using (congrFun (congrFun hc0 i₀) i₀).symm
  by_cases hjl : j = l <;> simpa [hY, hc0_val, hjl] using congrFun (congrFun hc0 j) l

/-- Internal core of weighted Schur orthogonality: produces the unique `Ft` together with its
conjugate-invariance equation `(u.map star)ᴴ * Ft * (u.map star) = Ft`. -/
private theorem exists_schur_orthogonality_with_inv [Module.Finite ℂ M] {h : A →ₗ[ℂ] ℂ}
    (hl : h.IsLeftInvariantIntegral) (hr : h.IsRightInvariantIntegral) (h1 : h 1 = 1)
    [IsSimpleOrder (Subcomodule ℂ A M)] (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    (c : Basis κ ℂ (Module.Dual ℂ M))
    (hc : coefficientMatrix (C := A) c ∈ unitary (Matrix κ κ A)) :
    ∃ Ft : Matrix ι ι ℂ, Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
      ((coefficientMatrix (C := A) b).map star)ᴴ * Ft.map (algebraMap ℂ A) *
        (coefficientMatrix (C := A) b).map star = Ft.map (algebraMap ℂ A) ∧
      (∀ i j k l, h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l, h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
          if i = k then Ft j l / Ft.trace else 0) ∧
      (∀ Ft' : Matrix ι ι ℂ, Ft'.PosDef → Ft'.trace = Ft'⁻¹.trace →
        (∀ i j k l, h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
            if i = k then Ft' j l / Ft'.trace else 0) → Ft' = Ft) := by
  have : Nontrivial M := Subcomodule.nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
  have : Nonempty ι := b.index_nonempty
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨G, hG, hG_inv, hGinv_inv⟩ := exists_posDef_dual_invariant b hu c hc
  obtain ⟨D, hD⟩ := exists_schur_right_matrix hl b hu
  obtain ⟨C, hC⟩ := exists_schur_left_matrix hr b hu
  set u := coefficientMatrix (C := A) b; set f := algebraMap ℂ A
  obtain ⟨r, hr_pos, hr_trace⟩ := exists_smul_trace_eq_inv_trace hG
  have hrC_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_pos.ne'
  set Ft : Matrix ι ι ℂ := (r : ℂ) • G
  have hFt : Ft.PosDef := hG.smul (Complex.lt_def.mpr ⟨hr_pos, rfl⟩)
  have hFt_inv : Ft⁻¹ = (r : ℂ)⁻¹ • G⁻¹ := inv_smul_of_isUnit hG.isUnit hrC_ne
  have hFt_dual_inv : (u.map star)ᴴ * Ft.map f * u.map star = Ft.map f := by
    have hmap : Ft.map f = (r : ℂ) • G.map f := by
      ext i j; simp [Ft, f, Algebra.algebraMap_eq_smul_one, smul_smul]
    rw [hmap, Matrix.mul_smul, Matrix.smul_mul, hG_inv]
  have htrace_div {X Y : Matrix ι ι A} {K : Matrix ι ι ℂ} (L : Matrix ι ι ℂ) (hK : K.trace ≠ 0)
      (hinv : X * K.map f * Y = K.map f)
      (hdiag : ∀ a c p q, h (X a p * Y q c) = if p = q then L a c else 0) (a c : ι) :
      L a c = K a c / K.trace := by
    have heq := congrArg h (congrFun (congrFun hinv a) c)
    simp only [f, Matrix.mul_apply, Matrix.map_apply, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, mul_smul_comm, mul_one, Finset.sum_mul, map_sum, map_smul,
      smul_eq_mul, h1, hdiag] at heq
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      ← Finset.sum_mul] at heq
    exact eq_div_of_mul_eq hK (by simpa [Matrix.trace, Matrix.diag, mul_comm] using heq)
  have hD_eq (j l : ι) : D j l = Ft j l / Ft.trace := by
    rw [htrace_div D hG.trace_pos.ne' hG_inv (fun a c p q ↦ by simpa using hD p a q c)]
    simp [Ft, Matrix.trace_smul, mul_div_mul_left _ _ hrC_ne]
  have hC_eq (i k : ι) : C i k = Ft⁻¹ i k / Ft⁻¹.trace := by
    rw [htrace_div C hG.inv.trace_pos.ne' hGinv_inv (fun a c p q ↦ by simpa using hC a p c q),
      hFt_inv]
    simp [Matrix.trace_smul, mul_div_mul_left _ _ (inv_ne_zero hrC_ne)]
  refine ⟨Ft, hFt, hr_trace, hFt_dual_inv, fun i j k l ↦ by rw [hC, hC_eq],
    fun i j k l ↦ by rw [hD, hD_eq], fun Ft' hFt' htr' hSchur2' ↦
      posDef_eq_of_div_trace_eq hFt' htr' hFt hr_trace fun j l ↦ by
        simpa [hD, hD_eq] using (hSchur2' i₀ j i₀ l).symm⟩

/-- **Weighted Schur orthogonality** for a normalized two-sided invariant functional `h` on a
complex Hopf star algebra, without assuming positivity of `h`. Given a simple unitary comodule
`(M, b)` whose dual comodule admits a unitary basis, there is a unique positive definite matrix
`Ft` with `Ft.trace = Ft⁻¹.trace` controlling both quadratic Schur relations. -/
theorem existsUnique_posDef_schur_orthogonality [Module.Finite ℂ M] {h : A →ₗ[ℂ] ℂ}
    (hl : h.IsLeftInvariantIntegral) (hr : h.IsRightInvariantIntegral) (h1 : h 1 = 1)
    [IsSimpleOrder (Subcomodule ℂ A M)] (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    (c : Basis κ ℂ (Module.Dual ℂ M))
    (hc : coefficientMatrix (C := A) c ∈ unitary (Matrix κ κ A)) :
    ∃! Ft : Matrix ι ι ℂ, Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
      (∀ i j k l, h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l, h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
          if i = k then Ft j l / Ft.trace else 0) := by
  obtain ⟨Ft, hFt, htr, _, h1', h2', huniq⟩ :=
    exists_schur_orthogonality_with_inv hl hr h1 b hu c hc
  exact ⟨Ft, ⟨hFt, htr, h1', h2'⟩, fun Ft' ⟨hFt', htr', _, h2''⟩ ↦ huniq Ft' hFt' htr' h2''⟩

/-- The unique Schur matrix `Ft` satisfies `(u.map star)ᴴ * Ft * (u.map star) = Ft`, and hence
controls `S²(u) = Ftᵀ * u * (Ftᵀ)⁻¹`. -/
theorem conjTranspose_map_star_mul_eq_of_schur_orthogonality [Module.Finite ℂ M] {h : A →ₗ[ℂ] ℂ}
    (hl : h.IsLeftInvariantIntegral) (hr : h.IsRightInvariantIntegral) (h1 : h 1 = 1)
    [IsSimpleOrder (Subcomodule ℂ A M)] (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    (c : Basis κ ℂ (Module.Dual ℂ M))
    (hc : coefficientMatrix (C := A) c ∈ unitary (Matrix κ κ A))
    {Ft : Matrix ι ι ℂ} (hFt : Ft.PosDef) (htr : Ft.trace = Ft⁻¹.trace)
    (h2' : ∀ i j k l,
      h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
        if i = k then Ft j l / Ft.trace else 0) :
    ((coefficientMatrix (C := A) b).map star)ᴴ * Ft.map (algebraMap ℂ A) *
        (coefficientMatrix (C := A) b).map star = Ft.map (algebraMap ℂ A) := by
  obtain ⟨_, _, _, hinv₀, _, _, huniq⟩ :=
    exists_schur_orthogonality_with_inv hl hr h1 b hu c hc
  exact huniq Ft hFt htr h2' ▸ hinv₀

end SchurOrthogonality

end LinearMap

namespace TauCeti.AlgebraicHaar

attribute [local instance] Comodule.dual

variable {A M ι : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A]
  [StarModule ℂ A] [StarCoalgebra ℂ A]
  [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
  [Fintype ι] [DecidableEq ι]

/-- **Weighted Schur orthogonality** for a finite simple unitary comodule over a complex Hopf star
algebra with an algebraic Haar state. -/
theorem schur_orthogonality (h : AlgebraicHaar A) [IsSimpleOrder (Subcomodule ℂ A M)]
    (b : Basis ι ℂ M) (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ∃! Ft : Matrix ι ι ℂ, Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
      (∀ i j k l, h (star (Comodule.coefficientMatrix (C := A) b i j) *
            Comodule.coefficientMatrix (C := A) b k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l, h (Comodule.coefficientMatrix (C := A) b i j *
            star (Comodule.coefficientMatrix (C := A) b k l)) =
          if i = k then Ft j l / Ft.trace else 0) := by
  have : Module.Finite ℂ M := Module.Finite.of_basis b
  obtain ⟨c, hc⟩ := Comodule.exists_basis_coefficientMatrix_mem_unitary
    h.right_invariant h.functional_ne_zero h.positive b.dualBasis
  exact LinearMap.existsUnique_posDef_schur_orthogonality
    h.left_invariant h.right_invariant h.normalized b hu c hc

omit [StarModule ℂ A] [StarCoalgebra ℂ A] in
/-- The positive definite Schur matrix `Ft` with `Ft.trace = Ft⁻¹.trace` is uniquely determined
by the second Schur orthogonality relation. -/
theorem eq_of_schur_orthogonality (h : AlgebraicHaar A)
    [IsSimpleOrder (Subcomodule ℂ A M)] (b : Basis ι ℂ M)
    {Ft₁ Ft₂ : Matrix ι ι ℂ}
    (hFt₁ : Ft₁.PosDef) (htr₁ : Ft₁.trace = Ft₁⁻¹.trace)
    (h2₁ : ∀ i j k l, h (Comodule.coefficientMatrix (C := A) b i j *
          star (Comodule.coefficientMatrix (C := A) b k l)) =
        if i = k then Ft₁ j l / Ft₁.trace else 0)
    (hFt₂ : Ft₂.PosDef) (htr₂ : Ft₂.trace = Ft₂⁻¹.trace)
    (h2₂ : ∀ i j k l, h (Comodule.coefficientMatrix (C := A) b i j *
          star (Comodule.coefficientMatrix (C := A) b k l)) =
        if i = k then Ft₂ j l / Ft₂.trace else 0) : Ft₁ = Ft₂ := by
  have : Nontrivial M := Subcomodule.nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
  have : Nonempty ι := b.index_nonempty
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  exact LinearMap.posDef_eq_of_div_trace_eq hFt₁ htr₁ hFt₂ htr₂ fun j l ↦ by
    simpa using (h2₁ i₀ j i₀ l).symm.trans (h2₂ i₀ j i₀ l)

/-- The squared antipode acts on the coefficient matrix of a finite simple unitary comodule by
conjugation by the transpose of its Schur matrix: `S²(u) = Ftᵀ * u * (Ftᵀ)⁻¹`. -/
theorem map_antipode_antipode_coefficientMatrix (h : AlgebraicHaar A)
    [IsSimpleOrder (Subcomodule ℂ A M)] (b : Basis ι ℂ M)
    (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {Ft : Matrix ι ι ℂ} (hFt : Ft.PosDef) (htr : Ft.trace = Ft⁻¹.trace)
    (h2' : ∀ i j k l, h (Comodule.coefficientMatrix (C := A) b i j *
          star (Comodule.coefficientMatrix (C := A) b k l)) =
        if i = k then Ft j l / Ft.trace else 0) :
    (Comodule.coefficientMatrix (C := A) b).map
        (HopfAlgebra.antipode ℂ ∘ HopfAlgebra.antipode ℂ) =
      Ftᵀ.map (algebraMap ℂ A) * Comodule.coefficientMatrix (C := A) b *
        (Ftᵀ)⁻¹.map (algebraMap ℂ A) := by
  have : Module.Finite ℂ M := Module.Finite.of_basis b
  obtain ⟨c, hc⟩ := Comodule.exists_basis_coefficientMatrix_mem_unitary
    h.right_invariant h.functional_ne_zero h.positive b.dualBasis
  exact Comodule.map_antipode_antipode_coefficientMatrix b hu
    ((Matrix.isUnit_iff_isUnit_det _).mp hFt.isUnit)
    (LinearMap.conjTranspose_map_star_mul_eq_of_schur_orthogonality
      h.left_invariant h.right_invariant h.normalized b hu c hc hFt htr h2')

end TauCeti.AlgebraicHaar
