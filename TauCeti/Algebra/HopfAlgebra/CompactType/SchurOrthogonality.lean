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

Let `A` be a complex Hopf star algebra with a normalized two-sided invariant linear functional
`h : A →ₗ[ℂ] ℂ`. For a finite-dimensional comodule `M` with a basis `b` whose coefficient matrix
`u` is unitary, the antipode satisfies `S (u i j) = star (u j i)`, so the coefficient matrix of
the dual comodule `M*` in the dual basis `b.dualBasis` is the entrywise star `u.map star`.

From invariance of `h` alone (without assuming positivity of `h`):

* Matrix coefficients of unitary comodules with no nonzero intertwiner between them are orthogonal
  under `h` (`LinearMap.IsRightInvariantIntegral.apply_star_coefficientMatrix_mul_eq_zero` and
  `LinearMap.IsLeftInvariantIntegral.apply_coefficientMatrix_mul_star_eq_zero`).
* For a simple finite-dimensional unitary comodule `(M, b)` whose dual comodule admits a unitary
  basis, there is a unique positive definite matrix `Ft` with `Ft.trace = Ft⁻¹.trace` satisfying
  the weighted Schur orthogonality relations
  ```
  h (star (u i j) * u k l) = δ_{j, l} (Ft⁻¹ i k) / tr(Ft⁻¹)
  h (u i j * star (u k l)) = δ_{i, k} (Ft j l) / tr(Ft).
  ```
  Moreover, `S² (u) = Ftᵀ * u * (Ftᵀ)⁻¹`.

When `h` is an `AlgebraicHaar` state, algebraic unitarization supplies the unitary basis on the
dual comodule automatically, yielding `TauCeti.AlgebraicHaar.schur_orthogonality`. Keeping the
general positivity-free theorem separate lets the compact-type characterization prove positivity
of the constructed invariant integral directly from weighted Schur orthogonality.

## Main declarations

* `TauCeti.Comodule.map_antipode_coefficientMatrix_eq_conjTranspose`: `u.map S = uᴴ` for a unitary
  coefficient matrix `u`.
* `TauCeti.Comodule.coefficientMatrix_dualBasis_eq_map_star`: `coefficientMatrix b.dualBasis =
  u.map star` for a unitary coefficient matrix `u`.
* `LinearMap.IsRightInvariantIntegral.apply_star_coefficientMatrix_mul_eq_zero` and
  `LinearMap.IsLeftInvariantIntegral.apply_coefficientMatrix_mul_star_eq_zero`: vanishing of `h`
  on products of coefficients from comodules with no nonzero intertwiner.
* `LinearMap.existsUnique_posDef_schur_orthogonality`: positivity-free weighted Schur orthogonality.
* `TauCeti.AlgebraicHaar.schur_orthogonality`: weighted Schur orthogonality for an algebraic Haar
  state.
* `TauCeti.AlgebraicHaar.map_antipode_antipode_coefficientMatrix`: `S² (u) = Ftᵀ * u * (Ftᵀ)⁻¹`.

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
    simp only [Matrix.map_apply, Function.comp_apply, Matrix.transpose_apply, ubar]
    rw [antipode_coefficientMatrix_of_mem_unitary b hu i j]
  have hubar_inv : ubar * ubar.map (HopfAlgebra.antipode R) = 1 := by
    have heq : ubar = coefficientMatrix (C := A) b.dualBasis :=
      (coefficientMatrix_dualBasis_eq_map_star b hu).symm
    rw [heq]
    exact coefficientMatrix_mul_map_antipode b.dualBasis
  have hFt_inv : Ft⁻¹.map f * Ft.map f = 1 := by
    rw [← Matrix.map_mul, nonsing_inv_mul _ hFt, Matrix.map_one _ (map_zero f) (map_one f)]
  have hleft : (Ft⁻¹.map f * ubarᴴ * Ft.map f) * ubar = 1 := by
    calc (Ft⁻¹.map f * ubarᴴ * Ft.map f) * ubar
        = Ft⁻¹.map f * (ubarᴴ * Ft.map f * ubar) := by simp only [Matrix.mul_assoc]
      _ = Ft⁻¹.map f * Ft.map f := by rw [hinv]
      _ = 1 := hFt_inv
  have hSbar : ubar.map (HopfAlgebra.antipode R) = Ft⁻¹.map f * ubarᴴ * Ft.map f :=
    (left_inv_eq_right_inv hleft hubar_inv).symm
  have hubarH : ubarᴴ = uᵀ := by
    ext i j
    simp [ubar]
  rw [hS2, hSbar, hubarH]
  ext i j
  have hFtT_inv : (Ftᵀ)⁻¹ = (Ft⁻¹)ᵀ := by
    rw [Matrix.transpose_nonsing_inv]
  rw [hFtT_inv]
  simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.map_apply, f,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  rw [mul_comm (Ft q i)]

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
  set u := coefficientMatrix (C := A) b
  set v := coefficientMatrix (C := A) c
  set Y : Matrix ι κ R := (uᴴ * X.map (algebraMap R A) * v).map h
  have hY (s : ι) (r : κ) : Y s r = ∑ p, ∑ q, X q p * h (star (u q s) * v p r) := by
    simp only [Y, Matrix.map_apply, Matrix.mul_apply, conjTranspose_apply,
      Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
      Finset.sum_mul, map_sum, map_smul, smul_eq_mul]
  let ru (i j : ι) : Coalgebra.Repr R (u i j) ι :=
    ⟨Finset.univ, fun k ↦ u i k, fun k ↦ u k j, (comul_coefficientMatrix_eq_sum b i j).symm⟩
  let rv (i j : κ) : Coalgebra.Repr R (v i j) κ :=
    ⟨Finset.univ, fun k ↦ v i k, fun k ↦ v k j, (comul_coefficientMatrix_eq_sum c i j).symm⟩
  ext a d
  simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply,
    Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, Finset.sum_mul]
  simp_rw [hY, Finset.sum_smul]
  calc ∑ r, ∑ s, ∑ p, ∑ q, (X q p * h (star (u q s) * v p r)) • (star (u s a) * v r d)
      = ∑ p, ∑ q, X q p •
          ∑ s, ∑ r, h (star (u q s) * v p r) • (star (u s a) * v r d) := by
        simp_rw [← smul_smul]
        conv_lhs => enter [2, r]; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        conv_lhs => enter [2, r]; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        simp_rw [← Finset.smul_sum]
        rw [Finset.sum_comm]
    _ = ∑ p, ∑ q, X q p • (h (star (u q a) * v p d) • (1 : A)) := by
        refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
        congr 1
        simpa [ru, rv] using hr.sum_sum_mul (ru q a).star (rv p d)
    _ = ∑ p, ∑ q, (X q p * h (star (u q a) * v p d)) • (1 : A) := by
        simp_rw [smul_smul]

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
  set u := coefficientMatrix (C := A) b
  set v := coefficientMatrix (C := A) c
  set Z : Matrix ι κ R := (u * X.map (algebraMap R A) * vᴴ).map h
  have hZ (s : ι) (r : κ) : Z s r = ∑ p, ∑ q, X q p * h (u s q * star (v r p)) := by
    simp only [Z, Matrix.map_apply, Matrix.mul_apply, conjTranspose_apply,
      Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
      Finset.sum_mul, map_sum, map_smul, smul_eq_mul]
  let ru (i j : ι) : Coalgebra.Repr R (u i j) ι :=
    ⟨Finset.univ, fun k ↦ u i k, fun k ↦ u k j, (comul_coefficientMatrix_eq_sum b i j).symm⟩
  let rv (i j : κ) : Coalgebra.Repr R (v i j) κ :=
    ⟨Finset.univ, fun k ↦ v i k, fun k ↦ v k j, (comul_coefficientMatrix_eq_sum c i j).symm⟩
  ext a d
  simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply,
    Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one, Finset.sum_mul]
  simp_rw [hZ, Finset.sum_smul]
  calc ∑ r, ∑ s, ∑ p, ∑ q, (X q p * h (u s q * star (v r p))) • (u a s * star (v d r))
      = ∑ p, ∑ q, X q p •
          ∑ s, ∑ r, h (u s q * star (v r p)) • (u a s * star (v d r)) := by
        simp_rw [← smul_smul]
        conv_lhs => enter [2, r]; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ ↦ ?_
        conv_lhs => enter [2, r]; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ ↦ ?_
        simp_rw [← Finset.smul_sum]
        rw [Finset.sum_comm]
    _ = ∑ p, ∑ q, X q p • (h (u a q * star (v d p)) • (1 : A)) := by
        refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
        congr 1
        simpa [ru, rv] using hl.sum_sum_mul (ru a q) (rv d p).star
    _ = ∑ p, ∑ q, (X q p * h (u a q * star (v d p))) • (1 : A) := by
        simp_rw [smul_smul]

/-- **Distinct-comodule orthogonality (first form).** If `h` is right invariant, `b` has unitary
coefficient matrix `u`, and there is no nonzero comodule morphism `N → M`, then
`h (star (u i j) * v k l) = 0`. -/
theorem IsRightInvariantIntegral.apply_star_coefficientMatrix_mul_eq_zero
    [Fintype ι] [DecidableEq ι] [Finite κ]
    (hr : h.IsRightInvariantIntegral) (b : Basis ι R M) (c : Basis κ R N)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    (hHom : ∀ g : Comodule.Hom R A N M, g = 0) (i j : ι) (k l : κ) :
    h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) c k l) = 0 := by
  have := Fintype.ofFinite κ
  classical
  set u := coefficientMatrix (C := A) b
  set v := coefficientMatrix (C := A) c
  let X : Matrix ι κ R := Matrix.of fun p q ↦ if p = i then if q = k then 1 else 0 else 0
  let Y : Matrix ι κ R := (uᴴ * X.map (algebraMap R A) * v).map h
  have hYinv : uᴴ * Y.map (algebraMap R A) * v = Y.map (algebraMap R A) :=
    hr.conjTranspose_mul_haar_avg_mul b c X
  have huu : u * uᴴ = 1 := (Unitary.mem_iff.mp hu).2
  have hcomm : u * Y.map (algebraMap R A) = Y.map (algebraMap R A) * v := by
    calc u * Y.map (algebraMap R A)
        = u * (uᴴ * Y.map (algebraMap R A) * v) := by rw [hYinv]
      _ = (u * uᴴ) * (Y.map (algebraMap R A) * v) := by simp only [Matrix.mul_assoc]
      _ = Y.map (algebraMap R A) * v := by rw [huu, Matrix.one_mul]
  have hY0 : Y = 0 := Comodule.Hom.eq_zero_of_coefficientMatrix_mul_eq c b hHom hcomm
  have hjl : Y j l = 0 := by rw [hY0]; rfl
  have hval : Y j l = h (star (u i j) * v k l) := by
    simp only [Y, X, Matrix.map_apply, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply,
      Finset.sum_mul, map_sum]
    rw [Finset.sum_eq_single k _ (by simp)]
    · rw [Finset.sum_eq_single i _ (by simp)]
      · simp
      · intro p _ hp; simp [hp]
    · intro q _ hq
      exact Finset.sum_eq_zero fun p _ ↦ by by_cases hp : p = i <;> simp [hp, hq]
  exact hval.symm.trans hjl

/-- **Distinct-comodule orthogonality (second form).** If `h` is left invariant, `c` has unitary
coefficient matrix `v`, and there is no nonzero comodule morphism `N → M`, then
`h (u i j * star (v k l)) = 0`. -/
theorem IsLeftInvariantIntegral.apply_coefficientMatrix_mul_star_eq_zero
    [Finite ι] [Fintype κ] [DecidableEq κ]
    (hl : h.IsLeftInvariantIntegral) (b : Basis ι R M) (c : Basis κ R N)
    (hv : coefficientMatrix (C := A) c ∈ unitary (Matrix κ κ A))
    (hHom : ∀ g : Comodule.Hom R A N M, g = 0) (i j : ι) (k l : κ) :
    h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) c k l)) = 0 := by
  have := Fintype.ofFinite ι
  classical
  set u := coefficientMatrix (C := A) b
  set v := coefficientMatrix (C := A) c
  let X : Matrix ι κ R := Matrix.of fun p q ↦ if p = j then if q = l then 1 else 0 else 0
  let Z : Matrix ι κ R := (u * X.map (algebraMap R A) * vᴴ).map h
  have hZinv : u * Z.map (algebraMap R A) * vᴴ = Z.map (algebraMap R A) :=
    hl.mul_haar_avg_mul_conjTranspose b c X
  have hvv : vᴴ * v = 1 := (Unitary.mem_iff.mp hv).1
  have hcomm : u * Z.map (algebraMap R A) = Z.map (algebraMap R A) * v := by
    calc u * Z.map (algebraMap R A)
        = (u * Z.map (algebraMap R A)) * (vᴴ * v) := by rw [hvv, Matrix.mul_one]
      _ = (u * Z.map (algebraMap R A) * vᴴ) * v := by simp only [Matrix.mul_assoc]
      _ = Z.map (algebraMap R A) * v := by rw [hZinv]
  have hZ0 : Z = 0 := Comodule.Hom.eq_zero_of_coefficientMatrix_mul_eq c b hHom hcomm
  have hik : Z i k = 0 := by rw [hZ0]; rfl
  have hval : Z i k = h (u i j * star (v k l)) := by
    simp only [Z, X, Matrix.map_apply, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply,
      Finset.sum_mul, map_sum]
    rw [Finset.sum_eq_single l _ (by simp)]
    · rw [Finset.sum_eq_single j _ (by simp)]
      · simp
      · intro p _ hp; simp [hp]
    · intro q _ hq
      exact Finset.sum_eq_zero fun p _ ↦ by by_cases hp : p = j <;> simp [hp, hq]
  exact hval.symm.trans hik

end Averaging

section SchurOrthogonality

variable {A M ι κ : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A]
  [StarModule ℂ A] [StarCoalgebra ℂ A]
  [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

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
  set u := coefficientMatrix (C := A) b
  set ubar := u.map star
  set v := coefficientMatrix (C := A) c
  set P : Matrix κ ι ℂ := c.toMatrix b.dualBasis
  set R : Matrix ι κ ℂ := b.dualBasis.toMatrix c
  have hPR : P * R = 1 := c.toMatrix_mul_toMatrix_flip b.dualBasis
  have hRP : R * P = 1 := b.dualBasis.toMatrix_mul_toMatrix_flip c
  have hstar : Function.Semiconj f star star := fun z ↦ algebraMap_star_comm z
  have hubar : coefficientMatrix (C := A) b.dualBasis = ubar :=
    coefficientMatrix_dualBasis_eq_map_star b hu
  have hPu : v * P.map f = P.map f * ubar := by
    rw [← hubar]
    exact c.coefficientMatrix_mul_toMatrix b.dualBasis
  have hRu : ubar * R.map f = R.map f * v := by
    rw [← hubar]
    exact b.dualBasis.coefficientMatrix_mul_toMatrix c
  refine ⟨Pᴴ * P, ?_, ?_, ?_⟩
  · refine PosDef.conjTranspose_mul_self P fun x y hxy ↦ ?_
    have := congrArg R.mulVec hxy
    simpa [Matrix.mulVec_mulVec, hRP] using this
  · have hG : (Pᴴ * P).map f = (P.map f)ᴴ * P.map f := by
      rw [Matrix.map_mul, Matrix.conjTranspose_map _ hstar]
    have hvv : vᴴ * v = 1 := (Unitary.mem_iff.mp hc).1
    rw [hG]
    calc ubarᴴ * ((P.map f)ᴴ * P.map f) * ubar
        = (P.map f * ubar)ᴴ * (P.map f * ubar) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (v * P.map f)ᴴ * (v * P.map f) := by rw [← hPu]
      _ = (P.map f)ᴴ * (vᴴ * v) * P.map f := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (P.map f)ᴴ * P.map f := by rw [hvv, Matrix.mul_one]
  · have hinv : (Pᴴ * P)⁻¹ = R * Rᴴ := by
      apply Matrix.inv_eq_right_inv
      calc (Pᴴ * P) * (R * Rᴴ)
          = Pᴴ * (P * R) * Rᴴ := by simp only [Matrix.mul_assoc]
        _ = (R * P)ᴴ := by rw [hPR, Matrix.mul_one, Matrix.conjTranspose_mul]
        _ = 1 := by rw [hRP, Matrix.conjTranspose_one]
    have hGinv : (Pᴴ * P)⁻¹.map f = R.map f * (R.map f)ᴴ := by
      rw [hinv, Matrix.map_mul, Matrix.conjTranspose_map _ hstar]
    have hvv : v * vᴴ = 1 := (Unitary.mem_iff.mp hc).2
    rw [hGinv]
    calc ubar * (R.map f * (R.map f)ᴴ) * ubarᴴ
        = (ubar * R.map f) * (ubar * R.map f)ᴴ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (R.map f * v) * (R.map f * v)ᴴ := by rw [hRu]
      _ = R.map f * (v * vᴴ) * (R.map f)ᴴ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = R.map f * (R.map f)ᴴ := by rw [hvv, Matrix.mul_one]

/-- Rescale a positive definite complex matrix by a positive real scalar so that it and its
inverse have the same trace. -/
private theorem exists_smul_trace_eq_inv_trace [Nonempty ι] {G : Matrix ι ι ℂ} (hG : G.PosDef) :
    ∃ r : ℝ, 0 < r ∧ (((r : ℂ) • G).trace = ((r : ℂ) • G)⁻¹.trace) := by
  obtain ⟨htG_pos, htG_im⟩ := Complex.lt_def.mp hG.trace_pos
  obtain ⟨htGi_pos, htGi_im⟩ := Complex.lt_def.mp hG.inv.trace_pos
  simp only [Complex.zero_re] at htG_pos htGi_pos
  let r : ℝ := Real.sqrt (G⁻¹.trace.re / G.trace.re)
  have hr : 0 < r := Real.sqrt_pos.mpr (div_pos htGi_pos htG_pos)
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hinv_smul : ((r : ℂ) • G)⁻¹ = (r : ℂ)⁻¹ • G⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hrC, one_smul,
      mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit)]
  refine ⟨r, hr, ?_⟩
  rw [hinv_smul, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
  have hGt : G.trace = (G.trace.re : ℂ) := Complex.ext rfl htG_im.symm
  have hGit : G⁻¹.trace = (G⁻¹.trace.re : ℂ) := Complex.ext rfl htGi_im.symm
  rw [hGt, hGit]
  norm_cast
  have hsq : r ^ 2 = G⁻¹.trace.re / G.trace.re :=
    Real.sq_sqrt (div_nonneg htGi_pos.le htG_pos.le)
  exact mul_left_cancel₀ hr.ne' <| calc
    r * (r * G.trace.re) = r ^ 2 * G.trace.re := by ring
    _ = G⁻¹.trace.re := by rw [hsq, div_mul_cancel₀ _ htG_pos.ne']
    _ = r * (r⁻¹ * G⁻¹.trace.re) := by rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]

/-- Two positive definite complex matrices with equal self- and inverse-traces and identical
trace-normalized entries are equal. -/
private theorem posDef_eq_of_div_trace_eq [Nonempty ι] {Ft₁ Ft₂ : Matrix ι ι ℂ}
    (hFt₁ : Ft₁.PosDef) (htr₁ : Ft₁.trace = Ft₁⁻¹.trace)
    (hFt₂ : Ft₂.PosDef) (htr₂ : Ft₂.trace = Ft₂⁻¹.trace)
    (hdiv : ∀ j l, Ft₁ j l / Ft₁.trace = Ft₂ j l / Ft₂.trace) : Ft₁ = Ft₂ := by
  have htr₁_ne : Ft₁.trace ≠ 0 := hFt₁.trace_pos.ne'
  have htr₂_ne : Ft₂.trace ≠ 0 := hFt₂.trace_pos.ne'
  let lam : ℂ := Ft₁.trace / Ft₂.trace
  have hlam_eq : Ft₁ = lam • Ft₂ := by
    ext j l
    have hmul := congrArg (· * Ft₁.trace) (hdiv j l)
    simp only [div_mul_cancel₀ _ htr₁_ne] at hmul
    simp only [Matrix.smul_apply, smul_eq_mul, lam]
    rw [hmul]
    ring
  have hlam_ne : lam ≠ 0 := div_ne_zero htr₁_ne htr₂_ne
  have hFt₁_inv : Ft₁⁻¹ = lam⁻¹ • Ft₂⁻¹ := by
    rw [hlam_eq]
    apply Matrix.inv_eq_right_inv
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hlam_ne, one_smul,
      mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hFt₂.isUnit)]
  have hlam_sq : lam * lam = 1 := by
    have htr_lam : lam * Ft₂.trace = lam⁻¹ * Ft₂.trace := by
      calc lam * Ft₂.trace = (lam • Ft₂).trace := (Matrix.trace_smul lam Ft₂).symm
        _ = Ft₁.trace := by rw [← hlam_eq]
        _ = Ft₁⁻¹.trace := htr₁
        _ = (lam⁻¹ • Ft₂⁻¹).trace := by rw [hFt₁_inv]
        _ = lam⁻¹ * Ft₂⁻¹.trace := Matrix.trace_smul lam⁻¹ Ft₂⁻¹
        _ = lam⁻¹ * Ft₂.trace := by rw [← htr₂]
    have hlam_inv : lam = lam⁻¹ := mul_right_cancel₀ htr₂_ne htr_lam
    calc lam * lam = lam * lam⁻¹ := by rw [← hlam_inv]
      _ = 1 := mul_inv_cancel₀ hlam_ne
  obtain ⟨hFt₂_re, hFt₂_im⟩ := Complex.lt_def.mp hFt₂.trace_pos
  obtain ⟨hFt₁_re, hFt₁_im⟩ := Complex.lt_def.mp hFt₁.trace_pos
  have hlam_real : lam = ((Ft₁.trace.re / Ft₂.trace.re : ℝ) : ℂ) := by
    have hFt₂_eq : Ft₂.trace = (Ft₂.trace.re : ℂ) := Complex.ext rfl hFt₂_im.symm
    have hFt₁_eq : Ft₁.trace = (Ft₁.trace.re : ℂ) := Complex.ext rfl hFt₁_im.symm
    dsimp only [lam]
    conv_lhs => rw [hFt₁_eq, hFt₂_eq]
    push_cast
    rfl
  have hlam_re_pos : 0 < Ft₁.trace.re / Ft₂.trace.re := div_pos hFt₁_re hFt₂_re
  have hlam_one : lam = 1 := by
    rw [hlam_real] at hlam_sq ⊢
    norm_cast at hlam_sq ⊢
    nlinarith
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
  set u := coefficientMatrix (C := A) b
  set f := algebraMap ℂ A
  refine ⟨Matrix.of fun j l ↦ h (u i₀ j * star (u i₀ l)), fun i j k l ↦ ?_⟩
  let X : Matrix ι ι ℂ := Matrix.of fun p q ↦ if p = j then if q = l then 1 else 0 else 0
  let Z : Matrix ι ι ℂ := (u * X.map f * uᴴ).map h
  have hZinv : u * Z.map f * uᴴ = Z.map f := hl.mul_haar_avg_mul_conjTranspose b b X
  have huu : uᴴ * u = 1 := (Unitary.mem_iff.mp hu).1
  have hcomm : u * Z.map f = Z.map f * u := by
    calc u * Z.map f = (u * Z.map f) * (uᴴ * u) := by rw [huu, Matrix.mul_one]
      _ = (u * Z.map f * uᴴ) * u := by simp only [Matrix.mul_assoc]
      _ = Z.map f * u := by rw [hZinv]
  obtain ⟨d, hd⟩ := Comodule.exists_eq_smul_one_of_coefficientMatrix_comm b hcomm
  have hZ_entry (a c' : ι) : Z a c' = h (u a j * star (u c' l)) := by
    simp only [Z, X, Matrix.map_apply, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply,
      Finset.sum_mul, map_sum]
    rw [Finset.sum_eq_single l _ (by simp)]
    · rw [Finset.sum_eq_single j _ (by simp)]
      · simp [f]
      · intro p _ hp; simp [hp]
    · intro q _ hq
      exact Finset.sum_eq_zero fun p _ ↦ by by_cases hp : p = j <;> simp [hp, hq]
  have hd_val : d = h (u i₀ j * star (u i₀ l)) := by
    have := congrFun (congrFun hd i₀) i₀
    simpa [hZ_entry] using this.symm
  have hZ_ik := congrFun (congrFun hd i) k
  rw [hZ_entry, hd_val] at hZ_ik
  by_cases hik : i = k <;> simpa [hik] using hZ_ik

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
  set u := coefficientMatrix (C := A) b
  set f := algebraMap ℂ A
  refine ⟨Matrix.of fun i k ↦ h (star (u i i₀) * u k i₀), fun i j k l ↦ ?_⟩
  let X : Matrix ι ι ℂ := Matrix.of fun p q ↦ if p = i then if q = k then 1 else 0 else 0
  let Y : Matrix ι ι ℂ := (uᴴ * X.map f * u).map h
  have hYinv : uᴴ * Y.map f * u = Y.map f := hr.conjTranspose_mul_haar_avg_mul b b X
  have huu : u * uᴴ = 1 := (Unitary.mem_iff.mp hu).2
  have hcomm : u * Y.map f = Y.map f * u := by
    calc u * Y.map f = u * (uᴴ * Y.map f * u) := by rw [hYinv]
      _ = (u * uᴴ) * (Y.map f * u) := by simp only [Matrix.mul_assoc]
      _ = Y.map f * u := by rw [huu, Matrix.one_mul]
  obtain ⟨c0, hc0⟩ := Comodule.exists_eq_smul_one_of_coefficientMatrix_comm b hcomm
  have hY_entry (a c' : ι) : Y a c' = h (star (u i a) * u k c') := by
    simp only [Y, X, Matrix.map_apply, Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply,
      Finset.sum_mul, map_sum]
    rw [Finset.sum_eq_single k _ (by simp)]
    · rw [Finset.sum_eq_single i _ (by simp)]
      · simp [f]
      · intro p _ hp; simp [hp]
    · intro q _ hq
      exact Finset.sum_eq_zero fun p _ ↦ by by_cases hp : p = i <;> simp [hp, hq]
  have hc0_val : c0 = h (star (u i i₀) * u k i₀) := by
    have := congrFun (congrFun hc0 i₀) i₀
    simpa [hY_entry] using this.symm
  have hY_jl := congrFun (congrFun hc0 j) l
  rw [hY_entry, hc0_val] at hY_jl
  by_cases hjl : j = l <;> simpa [hjl] using hY_jl

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
      (∀ i j k l,
        h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
          if i = k then Ft j l / Ft.trace else 0) ∧
      (∀ Ft' : Matrix ι ι ℂ, Ft'.PosDef → Ft'.trace = Ft'⁻¹.trace →
        (∀ i j k l,
          h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
            if i = k then Ft' j l / Ft'.trace else 0) →
        Ft' = Ft) := by
  have : Nontrivial M := Subcomodule.nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
  have : Nonempty ι := b.index_nonempty
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨G, hG, hG_inv, hGinv_inv⟩ := exists_posDef_dual_invariant b hu c hc
  obtain ⟨D, hD⟩ := exists_schur_right_matrix hl b hu
  obtain ⟨C, hC⟩ := exists_schur_left_matrix hr b hu
  set u := coefficientMatrix (C := A) b
  set f := algebraMap ℂ A
  obtain ⟨r, hr_pos, hr_trace⟩ := exists_smul_trace_eq_inv_trace hG
  have hrC_pos : (0 : ℂ) < (r : ℂ) := Complex.lt_def.mpr ⟨hr_pos, rfl⟩
  have hrC_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_pos.ne'
  set Ft : Matrix ι ι ℂ := (r : ℂ) • G
  have hFt : Ft.PosDef := hG.smul hrC_pos
  have hFt_inv : Ft⁻¹ = (r : ℂ)⁻¹ • G⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hrC_ne, one_smul,
      mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit)]
  have hFt_dual_inv : (u.map star)ᴴ * Ft.map f * u.map star = Ft.map f := by
    have hmap : Ft.map f = (r : ℂ) • G.map f := by
      ext i j
      simp [Ft, f, Algebra.algebraMap_eq_smul_one, smul_smul]
    rw [hmap, Matrix.mul_smul, Matrix.smul_mul, hG_inv]
  -- Evaluate `h` on `ūᴴ G ū = G` to identify `D = G / tr(G) = Ft / tr(Ft)`.
  have hD_eq (j l : ι) : D j l = Ft j l / Ft.trace := by
    have htrG : G.trace ≠ 0 := hG.trace_pos.ne'
    have hjl := congrArg h (congrFun (congrFun hG_inv j) l)
    simp only [f, Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply, star_star,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_smul_comm, mul_one,
      Finset.sum_mul, map_sum, map_smul, smul_eq_mul, h1] at hjl
    have hsum : ∑ p, ∑ q, G q p * h (u q j * star (u p l)) = G.trace * D j l := by
      simp_rw [hD]
      simp [Matrix.trace, Matrix.diag, Finset.sum_mul]
    rw [hsum] at hjl
    have hD_G : D j l = G j l / G.trace := eq_div_of_mul_eq htrG (by simpa [mul_comm] using hjl)
    rw [hD_G]
    simp [Ft, Matrix.trace_smul, mul_div_mul_left _ _ hrC_ne]
  -- Evaluate `h` on `ū G⁻¹ ūᴴ = G⁻¹` to identify `C = G⁻¹ / tr(G⁻¹) = Ft⁻¹ / tr(Ft⁻¹)`.
  have hC_eq (i k : ι) : C i k = Ft⁻¹ i k / Ft⁻¹.trace := by
    have htrGi : G⁻¹.trace ≠ 0 := hG.inv.trace_pos.ne'
    have hik := congrArg h (congrFun (congrFun hGinv_inv i) k)
    simp only [f, Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply, star_star,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_smul_comm, mul_one,
      Finset.sum_mul, map_sum, map_smul, smul_eq_mul, h1] at hik
    have hsum : ∑ p, ∑ q, G⁻¹ q p * h (star (u i q) * u k p) = G⁻¹.trace * C i k := by
      simp_rw [hC]
      simp [Matrix.trace, Matrix.diag, Finset.sum_mul]
    rw [hsum] at hik
    have hC_G : C i k = G⁻¹ i k / G⁻¹.trace :=
      eq_div_of_mul_eq htrGi (by simpa [mul_comm] using hik)
    rw [hC_G, hFt_inv]
    simp [Matrix.trace_smul, mul_div_mul_left _ _ (inv_ne_zero hrC_ne)]
  refine ⟨Ft, hFt, hr_trace, hFt_dual_inv, fun i j k l ↦ by rw [hC, hC_eq],
    fun i j k l ↦ by rw [hD, hD_eq], fun Ft' hFt' htr' hSchur2' ↦
      posDef_eq_of_div_trace_eq hFt' htr' hFt hr_trace fun j l ↦ ?_⟩
  have h1' := hSchur2' i₀ j i₀ l
  have h2' : h (u i₀ j * star (u i₀ l)) = Ft j l / Ft.trace := by simp [hD, hD_eq]
  simpa using h1'.symm.trans h2'

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
      (∀ i j k l,
        h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
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
  obtain ⟨Ft₀, _, _, hinv₀, _, _, huniq⟩ :=
    exists_schur_orthogonality_with_inv hl hr h1 b hu c hc
  rw [huniq Ft hFt htr h2']
  exact hinv₀

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
      (∀ i j k l,
        h (star (Comodule.coefficientMatrix (C := A) b i j) *
            Comodule.coefficientMatrix (C := A) b k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (Comodule.coefficientMatrix (C := A) b i j *
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
    (h2₁ : ∀ i j k l,
      h (Comodule.coefficientMatrix (C := A) b i j *
          star (Comodule.coefficientMatrix (C := A) b k l)) =
        if i = k then Ft₁ j l / Ft₁.trace else 0)
    (hFt₂ : Ft₂.PosDef) (htr₂ : Ft₂.trace = Ft₂⁻¹.trace)
    (h2₂ : ∀ i j k l,
      h (Comodule.coefficientMatrix (C := A) b i j *
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
    (h2' : ∀ i j k l,
      h (Comodule.coefficientMatrix (C := A) b i j *
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
