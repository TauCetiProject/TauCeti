/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Conjugate
public import TauCeti.Algebra.Coalgebra.Comodule.Schur
public import TauCeti.Algebra.Coalgebra.Comodule.Unitarization
public import TauCeti.Algebra.HopfAlgebra.Integral.Haar
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.LinearAlgebra.Matrix.PosDef.Trace
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic

/-!
# Weighted Schur orthogonality and cross-orthogonality

For left or right invariant integrals `h : A →ₗ[R] R` on a star bialgebra `A`, contractions of
products of entries of coefficient matrices `u` and `star v` assemble into intertwiners between
right `A`-comodules `M` and `N`. Consequently, when there is no nonzero comodule morphism `N → M`,
the matrix coefficients of `M` and `N` are cross-orthogonal under `h`.

Over a complex Hopf star algebra `A`, for a simple comodule `M` with basis `b` whose coefficient
matrix `u` is unitary, any positive definite matrix `G` invariant under `u.map star` normalizes to a
unique positive definite matrix `Ft` with `Ft.trace = Ft⁻¹.trace` satisfying the weighted Schur
orthogonality relations

* `h (star (u i j) * u k l) = if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0`,
* `h (u i j * star (u k l)) = if i = k then Ft j l / Ft.trace else 0`.

When `h` is an `AlgebraicHaar` functional, the Haar Gram matrix of `b.conjugateMatrixComodule`
supplies `G`, giving `Module.Basis.schur_orthogonality` and
`TauCeti.Comodule.IsUnitary.schur_orthogonality`. Separately, for any matrix `G` invariant under
`u.map star` with `u` unitary, `Gᵀ` intertwines `u` with its double antipode `(u.map S).map S`
(`Module.Basis.map_antipode_map_antipode_mul_transpose_of_conjInvariant`); combined with
`Module.Basis.conjInvariant_of_schur_orthogonality`, this applies in particular to `Ft`.

## Main declarations

* `LinearMap.IsLeftInvariantIntegral.map_coefficientMatrix_mul_star_eq_zero` and
  `LinearMap.IsRightInvariantIntegral.map_star_coefficientMatrix_mul_eq_zero`: cross-orthogonality
  between comodules with no nonzero morphism between them.
* `Module.Basis.map_antipode_map_antipode_mul_transpose_of_conjInvariant`: for unitary `u`, any
  `G` invariant under `u.map star` has `Gᵀ` intertwining `u` with `(u.map S).map S`.
* `Module.Basis.conjInvariant_of_schur_orthogonality`: any matrix `Ft` with nonzero trace satisfying
  the right-handed Schur orthogonality relation over a star bialgebra is `u.map star`-invariant.
* `Module.Basis.existsUnique_posDef_schur_orthogonality_of_conjInvariant`: weighted Schur
  orthogonality from any positive definite conjugate-invariant matrix (without assuming positivity
  of `h` globally on `A`).
* `Module.Basis.schur_orthogonality` and `TauCeti.Comodule.IsUnitary.schur_orthogonality`:
  weighted Schur orthogonality for an `AlgebraicHaar` functional on a complex Hopf star algebra.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Proposition 3.2.9.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*, SMF,
  2013, Theorem 1.4.2.
* S. L. Woronowicz, *Compact matrix pseudogroups*, Comm. Math. Phys. 111 (1987), 613–665.
-/

public section

open Module Matrix TauCeti TauCeti.Comodule
open scoped TensorProduct ComplexOrder

section IntertwinersAndCrossOrthogonality

variable {R A M N ι κ : Type*} [CommSemiring R] [StarRing R]
  [Semiring A] [StarRing A] [Bialgebra R A] [StarModule R A] [StarCoalgebra R A]
  [AddCommMonoid M] [Module R M] [Comodule R A M]
  [AddCommMonoid N] [Module R N] [Comodule R A N]

namespace LinearMap

/-- For a left invariant integral `h` and a basis `c` whose coefficient matrix `v` satisfies
`vᴴ * v = 1`, the matrix `E m r := h (u m p * star (v r q))` intertwines `v` and `u`. -/
theorem IsLeftInvariantIntegral.coefficientMatrix_mul_map_mul_star [Fintype ι] [Fintype κ]
    [DecidableEq κ] {h : A →ₗ[R] R} (hh : h.IsLeftInvariantIntegral) (b : Basis ι R M)
    (c : Basis κ R N) (hv : (coefficientMatrix (C := A) c)ᴴ * coefficientMatrix (C := A) c = 1)
    (p : ι) (q : κ) :
    coefficientMatrix (C := A) b * (Matrix.of fun m r ↦
        h (coefficientMatrix (C := A) b m p * star (coefficientMatrix (C := A) c r q))).map
          (algebraMap R A) =
      (Matrix.of fun m r ↦
        h (coefficientMatrix (C := A) b m p * star (coefficientMatrix (C := A) c r q))).map
          (algebraMap R A) * coefficientMatrix (C := A) c := by
  set u := coefficientMatrix (C := A) b
  set v := coefficientMatrix (C := A) c
  set E : Matrix ι κ R := Matrix.of fun m r ↦ h (u m p * star (v r q))
  have hconj : u * E.map (algebraMap R A) * vᴴ = E.map (algebraMap R A) := Matrix.ext fun i k ↦ by
    have hsum := hh.sum_sum_mul (b.coefficientMatrixRepr (C := A) i p)
      (c.coefficientMatrixRepr (C := A) k q).star
    simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply, Finset.sum_mul,
      E, Matrix.of_apply, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one]
    rw [Finset.sum_comm]
    simpa [u, v] using hsum
  calc u * E.map (algebraMap R A)
      = (u * E.map (algebraMap R A) * vᴴ) * v := by rw [Matrix.mul_assoc _ vᴴ, hv, Matrix.mul_one]
    _ = E.map (algebraMap R A) * v := by rw [hconj]

/-- For a right invariant integral `h` and a basis `b` whose coefficient matrix `u` satisfies
`u * uᴴ = 1`, the matrix `B m n := h (star (u i m) * v k n)` intertwines `v` and `u`. -/
theorem IsRightInvariantIntegral.coefficientMatrix_mul_map_star_mul [Fintype ι] [Fintype κ]
    [DecidableEq ι] {h : A →ₗ[R] R} (hh : h.IsRightInvariantIntegral) (b : Basis ι R M)
    (c : Basis κ R N) (hu : coefficientMatrix (C := A) b * (coefficientMatrix (C := A) b)ᴴ = 1)
    (i : ι) (k : κ) :
    coefficientMatrix (C := A) b * (Matrix.of fun m n ↦
        h (star (coefficientMatrix (C := A) b i m) * coefficientMatrix (C := A) c k n)).map
          (algebraMap R A) =
      (Matrix.of fun m n ↦
        h (star (coefficientMatrix (C := A) b i m) * coefficientMatrix (C := A) c k n)).map
          (algebraMap R A) * coefficientMatrix (C := A) c := by
  set u := coefficientMatrix (C := A) b
  set v := coefficientMatrix (C := A) c
  set B : Matrix ι κ R := Matrix.of fun m n ↦ h (star (u i m) * v k n)
  have hconj : uᴴ * B.map (algebraMap R A) * v = B.map (algebraMap R A) := Matrix.ext fun r s ↦ by
    have hsum := hh.sum_sum_mul (b.coefficientMatrixRepr (C := A) i r).star
      (c.coefficientMatrixRepr (C := A) k s)
    simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply, Finset.sum_mul,
      B, Matrix.of_apply, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one]
    rw [Finset.sum_comm]
    simpa [u, v] using hsum
  calc u * B.map (algebraMap R A)
      = u * (uᴴ * B.map (algebraMap R A) * v) := by rw [hconj]
    _ = B.map (algebraMap R A) * v := by simp only [← Matrix.mul_assoc, hu, Matrix.one_mul]

/-- **Cross-orthogonality for left invariant integrals.** If `vᴴ * v = 1` and there is no nonzero
comodule morphism `N → M`, then `h (u i p * star (v k q)) = 0` for all basis indices. -/
theorem IsLeftInvariantIntegral.map_coefficientMatrix_mul_star_eq_zero [Finite ι] [Fintype κ]
    [DecidableEq κ] {h : A →ₗ[R] R} (hh : h.IsLeftInvariantIntegral) (b : Basis ι R M)
    (c : Basis κ R N) (hv : (coefficientMatrix (C := A) c)ᴴ * coefficientMatrix (C := A) c = 1)
    (hHom : ∀ g : Comodule.Hom R A N M, g = 0) (i p : ι) (k q : κ) :
    h (coefficientMatrix (C := A) b i p * star (coefficientMatrix (C := A) c k q)) = 0 := by
  classical
  cases nonempty_fintype ι
  let E : Matrix ι κ R := Matrix.of fun m r ↦
    h (coefficientMatrix (C := A) b m p * star (coefficientMatrix (C := A) c r q))
  let g : Comodule.Hom R A N M := ⟨Matrix.toLin c b E,
    (c.map_coact_iff_coefficientMatrix b (Matrix.toLin c b E)).mpr <| by
      simpa [LinearMap.toMatrix_toLin, E] using hh.coefficientMatrix_mul_map_mul_star b c hv p q⟩
  have hE : E = 0 := (LinearMap.toMatrix_toLin c b E).symm.trans <| by
    simpa [g] using congrArg (LinearMap.toMatrix c b ∘ Comodule.Hom.toLinearMap) (hHom g)
  simpa [E] using congrFun (congrFun hE i) k

/-- **Cross-orthogonality for right invariant integrals.** If `u * uᴴ = 1` and there is no nonzero
comodule morphism `N → M`, then `h (star (u i r) * v k s) = 0` for all basis indices. -/
theorem IsRightInvariantIntegral.map_star_coefficientMatrix_mul_eq_zero [Fintype ι] [Finite κ]
    [DecidableEq ι] {h : A →ₗ[R] R} (hh : h.IsRightInvariantIntegral) (b : Basis ι R M)
    (c : Basis κ R N) (hu : coefficientMatrix (C := A) b * (coefficientMatrix (C := A) b)ᴴ = 1)
    (hHom : ∀ g : Comodule.Hom R A N M, g = 0) (i r : ι) (k s : κ) :
    h (star (coefficientMatrix (C := A) b i r) * coefficientMatrix (C := A) c k s) = 0 := by
  classical
  cases nonempty_fintype κ
  let B : Matrix ι κ R := Matrix.of fun m n ↦
    h (star (coefficientMatrix (C := A) b i m) * coefficientMatrix (C := A) c k n)
  let g : Comodule.Hom R A N M := ⟨Matrix.toLin c b B,
    (c.map_coact_iff_coefficientMatrix b (Matrix.toLin c b B)).mpr <| by
      simpa [LinearMap.toMatrix_toLin, B] using hh.coefficientMatrix_mul_map_star_mul b c hu i k⟩
  have hB : B = 0 := (LinearMap.toMatrix_toLin c b B).symm.trans <| by
    simpa [g] using congrArg (LinearMap.toMatrix c b ∘ Comodule.Hom.toLinearMap) (hHom g)
  simpa [B] using congrFun (congrFun hB r) s

/-- Subspace form of left-invariant cross-orthogonality: if `vᴴ * v = 1` and every comodule
morphism `N → M` is zero, then `h (x * star y) = 0` for all `x` in the coefficient submodule of
`M` and `y` in the coefficient submodule of `N`. -/
theorem IsLeftInvariantIntegral.map_mul_star_eq_zero_of_mem_matrixCoefficientSubmodule
    [Finite ι] [Fintype κ] [DecidableEq κ] {h : A →ₗ[R] R} (hh : h.IsLeftInvariantIntegral)
    (b : Basis ι R M) (c : Basis κ R N)
    (hv : (coefficientMatrix (C := A) c)ᴴ * coefficientMatrix (C := A) c = 1)
    (hHom : ∀ g : Comodule.Hom R A N M, g = 0) {x y : A}
    (hx : x ∈ matrixCoefficientSubmodule (R := R) (C := A) (M := M))
    (hy : y ∈ matrixCoefficientSubmodule (R := R) (C := A) (M := N)) : h (x * star y) = 0 := by
  cases nonempty_fintype ι
  obtain ⟨X, rfl⟩ := b.mem_matrixCoefficientSubmodule_iff_exists_matrix.mp hx
  obtain ⟨Y, rfl⟩ := c.mem_matrixCoefficientSubmodule_iff_exists_matrix.mp hy
  simp only [star_sum, star_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    map_sum, map_smul, hh.map_coefficientMatrix_mul_star_eq_zero b c hv hHom, smul_zero,
    Finset.sum_const_zero]

/-- Subspace form of right-invariant cross-orthogonality: if `u * uᴴ = 1` and every comodule
morphism `N → M` is zero, then `h (star x * y) = 0` for all `x` in the coefficient submodule of
`M` and `y` in the coefficient submodule of `N`. -/
theorem IsRightInvariantIntegral.map_star_mul_eq_zero_of_mem_matrixCoefficientSubmodule
    [Fintype ι] [Finite κ] [DecidableEq ι] {h : A →ₗ[R] R} (hh : h.IsRightInvariantIntegral)
    (b : Basis ι R M) (c : Basis κ R N)
    (hu : coefficientMatrix (C := A) b * (coefficientMatrix (C := A) b)ᴴ = 1)
    (hHom : ∀ g : Comodule.Hom R A N M, g = 0) {x y : A}
    (hx : x ∈ matrixCoefficientSubmodule (R := R) (C := A) (M := M))
    (hy : y ∈ matrixCoefficientSubmodule (R := R) (C := A) (M := N)) : h (star x * y) = 0 := by
  cases nonempty_fintype κ
  obtain ⟨X, rfl⟩ := b.mem_matrixCoefficientSubmodule_iff_exists_matrix.mp hx
  obtain ⟨Y, rfl⟩ := c.mem_matrixCoefficientSubmodule_iff_exists_matrix.mp hy
  simp only [star_sum, star_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    map_sum, map_smul, hh.map_star_coefficientMatrix_mul_eq_zero b c hu hHom, smul_zero,
    Finset.sum_const_zero]

end LinearMap

end IntertwinersAndCrossOrthogonality

namespace Module.Basis

section DoubleAntipode

variable {R A M ι : Type*} [CommSemiring R] [Semiring A] [StarRing A] [HopfAlgebra R A]
  [AddCommMonoid M] [Module R M] [Comodule R A M] [Fintype ι] [DecidableEq ι]

/-- If the coefficient matrix `u` of `b` is unitary and `G` is invariant under `u.map star`, then
`Gᵀ` intertwines `u` with its double antipode `(u.map S).map S`. -/
theorem map_antipode_map_antipode_mul_transpose_of_conjInvariant
    (b : Basis ι R M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {G : Matrix ι ι R} (hG : ((coefficientMatrix (C := A) b).map star)ᴴ * G.map (algebraMap R A) *
      (coefficientMatrix (C := A) b).map star = G.map (algebraMap R A)) :
    (((coefficientMatrix (C := A) b).map (HopfAlgebra.antipode R)).map (HopfAlgebra.antipode R)) *
        Gᵀ.map (algebraMap R A) =
      Gᵀ.map (algebraMap R A) * coefficientMatrix (C := A) b := by
  set u := coefficientMatrix (C := A) b
  set S : A →ₗ[R] A := HopfAlgebra.antipode R
  obtain ⟨hu1, hu2⟩ := Matrix.mem_unitary_iff_conjTranspose.mp hu
  have huS : u.map S = uᴴ := left_inv_eq_right_inv (map_antipode_mul_coefficientMatrix b) hu2
  have hmulS (X Y : Matrix ι ι A) : ((X * Y).map S)ᵀ = (Y.map S)ᵀ * (X.map S)ᵀ :=
    Matrix.ext fun i j ↦ by simp [Matrix.mul_apply, S, _root_.HopfAlgebra.antipode_mul_antidistrib]
  have h1 := congrArg (fun X : Matrix ι ι A ↦ (X.map S)ᵀ) hG
  rw [hmulS, hmulS] at h1
  have hij (i j) : S (u i j) = star (u j i) := by simpa using congrFun (congrFun huS i) j
  have hf1 : ((u.map star).map S)ᵀ = (u.map S).map S := Matrix.ext fun i j ↦ by simp [← hij]
  have hf2 : ((G.map (algebraMap R A)).map S)ᵀ = Gᵀ.map (algebraMap R A) :=
    Matrix.ext fun i j ↦ by simp [S, Algebra.algebraMap_eq_smul_one]
  have hf3 : (((u.map star)ᴴ).map S)ᵀ = uᴴ := Matrix.ext fun i j ↦ by simp [hij]
  rw [hf1, hf2, hf3, ← Matrix.mul_assoc] at h1
  simpa only [Matrix.mul_assoc _ uᴴ, hu1, Matrix.mul_one] using congrArg (· * u) h1

end DoubleAntipode

section StarBialgebra

variable {A M ι : Type*} [Ring A] [StarRing A] [Bialgebra ℂ A] [StarModule ℂ A] [StarCoalgebra ℂ A]
  [AddCommMonoid M] [Module ℂ M] [Comodule ℂ A M] [Fintype ι] [DecidableEq ι]

/-- If `Ft` satisfies the right-handed Schur orthogonality relation for a right invariant integral
`h`, then `Ft` is invariant under `u.map star` (so when `u` is unitary over a Hopf star algebra,
`Ftᵀ` intertwines `u` with its double antipode via
`Module.Basis.map_antipode_map_antipode_mul_transpose_of_conjInvariant`). -/
theorem conjInvariant_of_schur_orthogonality {h : A →ₗ[ℂ] ℂ} (hr : h.IsRightInvariantIntegral)
    (b : Basis ι ℂ M) {Ft : Matrix ι ι ℂ} (hFt_tr : Ft.trace ≠ 0)
    (horth : ∀ i j k l,
      h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
        if i = k then Ft j l / Ft.trace else 0) :
    ((coefficientMatrix (C := A) b).map star)ᴴ * Ft.map (algebraMap ℂ A) *
      (coefficientMatrix (C := A) b).map star = Ft.map (algebraMap ℂ A) := by
  have : Nonempty ι := not_isEmpty_iff.mp fun _ ↦ hFt_tr (by simp [Matrix.trace])
  let _ : Comodule ℂ A (ι → ℂ) := b.conjugateMatrixComodule
  let G : Matrix ι ι ℂ := haarGramMatrix h (Pi.basisFun ℂ ι)
  have hGinv : ((coefficientMatrix (C := A) b).map star)ᴴ * G.map (algebraMap ℂ A) *
      (coefficientMatrix (C := A) b).map star = G.map (algebraMap ℂ A) := by
    simpa [G, b.coefficientMatrix_conjugateMatrixComodule] using
      conjTranspose_coefficientMatrix_mul_haarGramMatrix_mul hr (Pi.basisFun ℂ ι)
  have hcard : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hmap : Ft.map (algebraMap ℂ A) =
      (Ft.trace / (Fintype.card ι : ℂ)) • G.map (algebraMap ℂ A) := Matrix.ext fun j l ↦ by
    have hGjl : G j l = (Fintype.card ι : ℂ) * (Ft j l / Ft.trace) := by
      simp [G, haarGramMatrix_apply, b.coefficientMatrix_conjugateMatrixComodule, horth]
    simp only [Matrix.map_apply, Matrix.smul_apply, Algebra.smul_def, ← map_mul, hGjl]
    exact congrArg _ (by field_simp)
  rw [hmap, Matrix.mul_smul, Matrix.smul_mul, hGinv]

end StarBialgebra

section WeightedSchurOrthogonality

variable {A M ι : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A] [StarModule ℂ A]
  [StarCoalgebra ℂ A] [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
  [IsSimpleOrder (Subcomodule ℂ A M)] [Fintype ι] [DecidableEq ι]

omit [StarRing A] [StarModule ℂ A] [StarCoalgebra ℂ A] in
private theorem exists_apply_eq_ite_of_commute_coefficientMatrix (b : Basis ι ℂ M) (F : ι → ι → ℂ)
    (hF : coefficientMatrix (C := A) b * (Matrix.of F).map (algebraMap ℂ A) =
      (Matrix.of F).map (algebraMap ℂ A) * coefficientMatrix (C := A) b) :
    ∃ c : ℂ, ∀ p q, F p q = if p = q then c else 0 := by
  obtain ⟨c, hc⟩ := b.exists_eq_smul_one_of_commute_coefficientMatrix (Matrix.of F) hF
  exact ⟨c, fun p q ↦ by simpa [Matrix.one_apply] using congrFun (congrFun hc p) q⟩

omit [IsSimpleOrder (Subcomodule ℂ A M)] in
private theorem map_star_mul_inv_mul_conjTranspose_of_conjInvariant (b : Basis ι ℂ M)
    {G : Matrix ι ι ℂ} (hG : G.PosDef)
    (hGinv : ((coefficientMatrix (C := A) b).map star)ᴴ * G.map (algebraMap ℂ A) *
      (coefficientMatrix (C := A) b).map star = G.map (algebraMap ℂ A)) :
    (coefficientMatrix (C := A) b).map star * G⁻¹.map (algebraMap ℂ A) *
      ((coefficientMatrix (C := A) b).map star)ᴴ = G⁻¹.map (algebraMap ℂ A) := by
  set v := (coefficientMatrix (C := A) b).map star
  set f := algebraMap ℂ A
  have hGdet : IsUnit G.det := (isUnit_iff_isUnit_det _).mp hG.isUnit
  have hGG : G.map f * G⁻¹.map f = 1 := by
    rw [← Matrix.map_mul, mul_nonsing_inv _ hGdet, Matrix.map_one _ (map_zero f) (map_one f)]
  have hGinvG : G⁻¹.map f * G.map f = 1 := by
    rw [← Matrix.map_mul, nonsing_inv_mul _ hGdet, Matrix.map_one _ (map_zero f) (map_one f)]
  let _ : Comodule ℂ A (ι → ℂ) := b.conjugateMatrixComodule
  have hv_right : v * v.map (HopfAlgebra.antipode ℂ) = 1 := by
    simpa [v, b.coefficientMatrix_conjugateMatrixComodule] using
      coefficientMatrix_mul_map_antipode (C := A) (Pi.basisFun ℂ ι)
  have hleft : (G⁻¹.map f * vᴴ * G.map f) * v = 1 := by
    calc (G⁻¹.map f * vᴴ * G.map f) * v = G⁻¹.map f * (vᴴ * G.map f * v) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hGinv, hGinvG]
  have hright : v * (G⁻¹.map f * vᴴ * G.map f) = 1 :=
    (left_inv_eq_right_inv hleft hv_right).symm ▸ hv_right
  calc v * G⁻¹.map f * vᴴ = v * (G⁻¹.map f * vᴴ * G.map f) * G⁻¹.map f := by
        simp only [Matrix.mul_assoc, hGG, Matrix.mul_one]
    _ = G⁻¹.map f := by rw [hright, Matrix.one_mul]

omit [StarModule ℂ A] [StarCoalgebra ℂ A] in
private theorem eq_of_posDef_schur_orthogonality {h : A →ₗ[ℂ] ℂ} (b : Basis ι ℂ M)
    {Ft Ft' : Matrix ι ι ℂ} (hFt_pos : Ft.PosDef) (hFt_tr : Ft.trace = Ft⁻¹.trace)
    (hFt_orth1 : ∀ i j k l,
      h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
        if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0)
    (hFt_orth2 : ∀ i j k l,
      h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
        if i = k then Ft j l / Ft.trace else 0)
    (hFt'_pos : Ft'.PosDef) (hFt'_tr : Ft'.trace = Ft'⁻¹.trace)
    (hFt'_orth1 : ∀ i j k l,
      h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
        if j = l then Ft'⁻¹ i k / Ft'⁻¹.trace else 0)
    (hFt'_orth2 : ∀ i j k l,
      h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
        if i = k then Ft' j l / Ft'.trace else 0) : Ft' = Ft := by
  have : Nonempty ι := b.index_nonempty_of_isSimpleOrder A
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hFt'_tr_ne : Ft'.trace ≠ 0 := hFt'_pos.trace_pos.ne'
  set α : ℂ := Ft'.trace / Ft.trace
  have hFt'_eq : Ft' = α • Ft := Matrix.ext fun j l ↦ by
    have hjl := (div_eq_iff hFt'_tr_ne).mp <| by
      simpa using (hFt'_orth2 i₀ j i₀ l).symm.trans (hFt_orth2 i₀ j i₀ l)
    simp only [Matrix.smul_apply, smul_eq_mul, hjl, α]
    ring
  have hFt'_inv_eq : Ft'⁻¹ = α • Ft⁻¹ := Matrix.ext fun i k ↦ by
    have hik := (div_eq_iff (hFt'_tr ▸ hFt'_tr_ne)).mp <| by
      simpa using (hFt'_orth1 i i₀ k i₀).symm.trans (hFt_orth1 i i₀ k i₀)
    simp only [Matrix.smul_apply, smul_eq_mul, hik, ← hFt'_tr, ← hFt_tr, α]
    ring
  have hα_sq : α * α = 1 := by
    have hmul : Ft' * Ft'⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hFt'_pos.isUnit)
    rw [hFt'_inv_eq, hFt'_eq, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hFt_pos.isUnit)] at hmul
    simpa using congrFun (congrFun hmul i₀) i₀
  have hα_pos : 0 < α := by
    simpa [α, div_eq_mul_inv] using
      mul_pos hFt'_pos.trace_pos (RCLike.inv_pos_of_pos hFt_pos.trace_pos)
  refine (mul_self_eq_one_iff.mp hα_sq).elim (fun h1 ↦ by rw [hFt'_eq, h1, one_smul]) fun hm1 ↦
    absurd (hm1 ▸ hα_pos) (not_lt_of_gt (neg_lt_zero.mpr zero_lt_one))

-- Schur-orthogonality contraction step: evaluates `h` on `Vᴴ * H * V = H` when `h` contracts
-- `star (V p q) * V r s` to `δ_{p, r} K q s`.
private theorem trace_mul_eq_of_conjTranspose_mul_mul {R B κ : Type*} [CommSemiring R] [Semiring B]
    [Star B] [Algebra R B] [Fintype κ] [DecidableEq κ] {h : B →ₗ[R] R} (h1 : h 1 = 1)
    {V : Matrix κ κ B} {H K : Matrix κ κ R}
    (hinv : Vᴴ * H.map (algebraMap R B) * V = H.map (algebraMap R B))
    (horth : ∀ p q r s, h (star (V p q) * V r s) = if p = r then K q s else 0)
    (q s : κ) : H.trace * K q s = H q s := by
  have hqs := congrArg h (congrFun (congrFun hinv q) s)
  simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply, Finset.sum_mul,
    Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
    map_sum, map_smul, smul_eq_mul, horth, h1] at hqs
  simpa [Matrix.trace, Matrix.diag, Finset.sum_mul] using hqs

/-- **Weighted Schur orthogonality from a conjugate-invariant positive definite matrix.** Let `h`
be a normalized right invariant integral on a complex Hopf star algebra `A` (with no global
positivity hypothesis on `h`), `b` a finite basis of a simple comodule `M` with unitary coefficient
matrix `u`, and `G` a positive definite matrix satisfying `(u.map star)ᴴ * G * u.map star = G`.
Then there exists a unique positive definite matrix `Ft` with `Ft.trace = Ft⁻¹.trace` satisfying
both weighted Schur orthogonality relations. -/
theorem existsUnique_posDef_schur_orthogonality_of_conjInvariant
    {h : A →ₗ[ℂ] ℂ} (hr : h.IsRightInvariantIntegral) (h1 : h 1 = 1) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) {G : Matrix ι ι ℂ} (hG : G.PosDef)
    (hGinv : ((coefficientMatrix (C := A) b).map star)ᴴ * G.map (algebraMap ℂ A) *
      (coefficientMatrix (C := A) b).map star = G.map (algebraMap ℂ A)) :
    ∃! Ft : Matrix ι ι ℂ, Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
      (∀ i j k l,
        h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
          if i = k then Ft j l / Ft.trace else 0) := by
  set u := coefficientMatrix (C := A) b
  have hl : h.IsLeftInvariantIntegral := hr.isLeftInvariantIntegral h1
  obtain ⟨hu1, hu2⟩ := Matrix.mem_unitary_iff_conjTranspose.mp hu
  have : Nonempty ι := b.index_nonempty_of_isSimpleOrder A
  -- Schur's lemma diagonalizes the left- and right-contracted matrix families.
  choose C hC using fun j l ↦ b.exists_apply_eq_ite_of_commute_coefficientMatrix _
    (hl.coefficientMatrix_mul_map_mul_star b b hu1 j l)
  choose D hD using fun i k ↦ b.exists_apply_eq_ite_of_commute_coefficientMatrix _
    (hr.coefficientMatrix_mul_map_star_mul b b hu2 i k)
  -- Apply `h` entrywise to the `u.map star`-invariance identities for `G` and `G⁻¹`.
  have hCG (j l : ι) : G.trace * C j l = G j l :=
    trace_mul_eq_of_conjTranspose_mul_mul h1 hGinv (fun p q r s ↦ by simpa using hC q s p r) j l
  have hDG (i k : ι) : G⁻¹.trace * D i k = G⁻¹ i k :=
    trace_mul_eq_of_conjTranspose_mul_mul (V := (u.map star)ᴴ) h1
      (by simpa using b.map_star_mul_inv_mul_conjTranspose_of_conjInvariant hG hGinv)
      (fun p q r s ↦ by simpa using hD q s p r) i k
  -- Rescale `G` so that `(c • G).trace = (c • G)⁻¹.trace`; uniqueness follows from trace ratio.
  obtain ⟨c, hc_pos, hFt_pos, hFt_inv, hFt_tr⟩ := hG.exists_pos_smul_trace_eq_inv_trace
  have hc_ne : c ≠ 0 := hc_pos.ne'
  set Ft : Matrix ι ι ℂ := c • G
  have hFt_orth1 (i j k l : ι) :
      h (star (u i j) * u k l) = if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0 :=
    (hD i k j l).trans <| by
      simp [hFt_inv, eq_div_of_mul_eq hG.inv.trace_pos.ne' (mul_comm (D i k) G⁻¹.trace ▸ hDG i k),
        mul_div_mul_left _ _ (inv_ne_zero hc_ne)]
  have hFt_orth2 (i j k l : ι) :
      h (u i j * star (u k l)) = if i = k then Ft j l / Ft.trace else 0 :=
    (hC j l i k).trans <| by
      simp [Ft, eq_div_of_mul_eq hG.trace_pos.ne' (mul_comm (C j l) G.trace ▸ hCG j l),
        mul_div_mul_left _ _ hc_ne]
  exact ⟨Ft, ⟨hFt_pos, hFt_tr, hFt_orth1, hFt_orth2⟩, fun Ft' ⟨hp, htr, ho1, ho2⟩ ↦
    eq_of_posDef_schur_orthogonality b hFt_pos hFt_tr hFt_orth1 hFt_orth2 hp htr ho1 ho2⟩

/-- Under the hypotheses of `existsUnique_posDef_schur_orthogonality_of_conjInvariant`, the
functional `h` is nonnegative on `star x * x` for every `x` in the matrix-coefficient submodule of
`M`. -/
theorem map_star_mul_self_nonneg_of_conjInvariant
    {h : A →ₗ[ℂ] ℂ} (hr : h.IsRightInvariantIntegral) (h1 : h 1 = 1) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) {G : Matrix ι ι ℂ} (hG : G.PosDef)
    (hGinv : ((coefficientMatrix (C := A) b).map star)ᴴ * G.map (algebraMap ℂ A) *
      (coefficientMatrix (C := A) b).map star = G.map (algebraMap ℂ A))
    {x : A} (hx : x ∈ matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M)) :
    0 ≤ h (star x * x) := by
  obtain ⟨Ft, ⟨hFt_pos, -, hFt_orth1, -⟩, -⟩ :=
    b.existsUnique_posDef_schur_orthogonality_of_conjInvariant hr h1 hu hG hGinv
  have : Nonempty ι := b.index_nonempty_of_isSimpleOrder A
  have htr_inv_nonneg : 0 ≤ (Ft⁻¹.trace)⁻¹ := (RCLike.inv_pos_of_pos hFt_pos.inv.trace_pos).le
  obtain ⟨X, rfl⟩ := b.mem_matrixCoefficientSubmodule_iff_exists_matrix.mp hx
  have hexp : h (star (∑ i, ∑ j, X i j • coefficientMatrix (C := A) b i j) *
      ∑ k, ∑ l, X k l • coefficientMatrix (C := A) b k l) =
      (Ft⁻¹.trace)⁻¹ * ∑ j, star (fun i ↦ X i j) ⬝ᵥ (Ft⁻¹ *ᵥ fun k ↦ X k j) := by
    simp only [star_sum, star_smul, Finset.sum_mul]
    simp only [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, map_sum, map_smul, smul_eq_mul,
      hFt_orth1, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [Finset.sum_comm]
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, div_eq_mul_inv]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
      Finset.sum_congr rfl fun _ _ ↦ by ring
  exact hexp ▸ mul_nonneg htr_inv_nonneg
    (Finset.sum_nonneg fun _ _ ↦ hFt_pos.inv.posSemidef.dotProduct_mulVec_nonneg _)

/-- **Weighted Schur orthogonality** for a basis `b` of a simple comodule `M` whose coefficient
matrix `u` is unitary: for an `AlgebraicHaar` functional `h` on a complex Hopf star algebra `A`,
there exists a unique positive definite matrix `Ft` with `Ft.trace = Ft⁻¹.trace` satisfying both
weighted Schur orthogonality relations. -/
theorem schur_orthogonality (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ∃! Ft : Matrix ι ι ℂ, Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
      (∀ i j k l,
        h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
          if i = k then Ft j l / Ft.trace else 0) := by
  let _ : Comodule ℂ A (ι → ℂ) := b.conjugateMatrixComodule
  let G : Matrix ι ι ℂ := haarGramMatrix h.toLinearMap (Pi.basisFun ℂ ι)
  have hG : G.PosDef := posDef_haarGramMatrix (fun _ ↦ h.map_star_mul_self_pos) (Pi.basisFun ℂ ι)
  have hGinv : ((coefficientMatrix (C := A) b).map star)ᴴ * G.map (algebraMap ℂ A) *
      (coefficientMatrix (C := A) b).map star = G.map (algebraMap ℂ A) := by
    simpa [G, b.coefficientMatrix_conjugateMatrixComodule] using
      conjTranspose_coefficientMatrix_mul_haarGramMatrix_mul h.isRightInvariantIntegral
        (Pi.basisFun ℂ ι)
  exact b.existsUnique_posDef_schur_orthogonality_of_conjInvariant h.isRightInvariantIntegral
    h.map_one hu hG hGinv

end WeightedSchurOrthogonality

end Module.Basis

namespace TauCeti.Comodule.IsUnitary

variable {A H ι : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A] [StarModule ℂ A]
  [StarCoalgebra ℂ A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [Comodule ℂ A H] [IsSimpleOrder (Subcomodule ℂ A H)] [Fintype ι] [DecidableEq ι]

/-- **Weighted Schur orthogonality** for a finite-dimensional simple unitary comodule `H` in any
orthonormal basis `b`. -/
theorem schur_orthogonality (hH : IsUnitary ℂ A H) (h : AlgebraicHaar A)
    (b : OrthonormalBasis ι ℂ H) :
    ∃! Ft : Matrix ι ι ℂ, Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
      (∀ i j k l,
        h (star (coefficientMatrix (C := A) b.toBasis i j) *
          coefficientMatrix (C := A) b.toBasis k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (coefficientMatrix (C := A) b.toBasis i j *
          star (coefficientMatrix (C := A) b.toBasis k l)) =
          if i = k then Ft j l / Ft.trace else 0) :=
  b.toBasis.schur_orthogonality h (hH.coefficientMatrix_mem_unitary b)

end TauCeti.Comodule.IsUnitary
