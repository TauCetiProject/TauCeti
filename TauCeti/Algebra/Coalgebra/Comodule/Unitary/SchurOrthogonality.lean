/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Adjoin
public import TauCeti.Algebra.Coalgebra.Comodule.Unitary.UnitarizingMatrix
public import TauCeti.Algebra.HopfAlgebra.Integral.Positive
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Module
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Intertwiner
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Isotypic
import TauCeti.RingTheory.Semisimple.Schur

/-!
# Weighted Schur orthogonality for finite unitary comodules

Let `A` be a star bialgebra or Hopf star algebra equipped with invariant integrals, and let `M` and
`N` be right `A`-comodules with finite bases `b` and `c` and coefficient matrices `u` and `v`.

1. **Haar intertwiners and cross-orthogonality (star bialgebras).** When `h` is right invariant and
   `u * uᴴ = 1`, for each `i, k` the scalar matrix `(j, l) ↦ h (star (u i j) * v k l)` intertwines
   `v` with `u`; symmetrically, when `h` is left invariant and `vᴴ * v = 1`, the scalar matrix
   `(i, k) ↦ h (u i j * star (v k l))` intertwines `v` with `u`. Consequently, whenever every
   comodule morphism `N → M` is zero — in particular for inequivalent simple comodules — all
   cross-pairings `h (star (u i j) * v k l)` and `h (u i j * star (v k l))` vanish.

2. **Weighted Schur orthogonality on a simple comodule (Hopf star algebras over `ℂ`).** When `M` is
   simple, `u` is unitary, and `h` is a nonzero positive two-sided invariant integral, the
   normalized unitarizing matrix `Ft = unitarizingMatrix h b` (`PosDef Ft`, `Tr Ft = Tr Ft⁻¹`)
   governs both pairings of matrix coefficients:
   * `h (star (u i j) * u k l) = δ_{jl} * h 1 * (Ft⁻¹ i k / Tr Ft⁻¹)`;
   * `h (u i j * star (u k l)) = δ_{ik} * h 1 * (Ft j l / Tr Ft)` (requiring only left invariance).

   From the second formula and invertibility of `Ft`, the `dim(M)²` matrix coefficients `u i j` of a
   simple unitary comodule are linearly independent over `ℂ`. Specializing to `h : AlgebraicHaar A`
   sets `h 1 = 1` and shows that `Ft` is the unique positive definite matrix with `Tr Ft = Tr Ft⁻¹`
   satisfying the weighted Schur orthogonality relations.

## Main declarations

* `TauCeti.Comodule.coefficientMatrix_mul_map_apply_star_mul` and
  `TauCeti.Comodule.coefficientMatrix_mul_map_apply_mul_star`: one-sided Haar invariance produces
  intertwining scalar matrices between comodules.
* `TauCeti.Comodule.apply_star_mul_coefficientMatrix_eq_zero_of_ne` and
  `TauCeti.Comodule.apply_coefficientMatrix_mul_star_eq_zero_of_ne`: orthogonality of matrix
  coefficients of inequivalent simple comodules.
* `LinearMap.IsLeftInvariantIntegral.apply_coefficientMatrix_mul_star` and
  `TauCeti.Comodule.apply_star_mul_coefficientMatrix`: the two weighted Schur orthogonality
  formulas for an unnormalized positive invariant integral.
* `LinearMap.IsLeftInvariantIntegral.linearIndependent_coefficientMatrix`: linear independence of
  the matrix coefficients `u i j` of a simple unitary comodule.
* `TauCeti.AlgebraicHaar.existsUnique_schur_orthogonality`,
  `TauCeti.AlgebraicHaar.schur_orthogonality`, and
  `TauCeti.Comodule.IsUnitary.schur_orthogonality`: normalized weighted Schur orthogonality and
  uniqueness of the weight matrix `Ft`.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Propositions 3.2.9 and
  3.2.17, Theorem 5.4.1.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*, SMF,
  2013, Theorem 1.4.2, p. 9, and Theorem 1.6.6, Step 1, p. 18.
-/

public section

open Module Matrix
open scoped ComplexOrder

namespace TauCeti.Comodule

section BialgebraIntertwiners

variable {R A M N ι κ : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A]
  [Bialgebra R A] [StarModule R A] [StarCoalgebra R A]
  [AddCommMonoid M] [Module R M] [Comodule R A M]
  [AddCommMonoid N] [Module R N] [Comodule R A N]

/-- Coproduct representation of a basis coefficient entry `u i j`. -/
private noncomputable def coeffRepr [Fintype ι] (b : Basis ι R M) (i j : ι) :
    Coalgebra.Repr R (coefficientMatrix (C := A) b i j) ι where
  index := Finset.univ
  left p := coefficientMatrix (C := A) b i p
  right p := coefficientMatrix (C := A) b p j
  eq := (comul_coefficientMatrix_eq_sum (C := A) b i j).symm

/-- **Right-invariant Haar intertwiner.** If `h` is right invariant and `u * uᴴ = 1` for
`u = coefficientMatrix b`, then for each `i` and `k` the scalar matrix
`X j l = h (star (u i j) * v k l)` intertwines `v = coefficientMatrix c` with `u`. -/
theorem coefficientMatrix_mul_map_apply_star_mul [Fintype ι] [DecidableEq ι] [Fintype κ]
    {h : A →ₗ[R] R} (hh : h.IsRightInvariantIntegral) {b : Basis ι R M}
    (hu : coefficientMatrix (C := A) b * (coefficientMatrix (C := A) b)ᴴ = 1)
    (c : Basis κ R N) (i : ι) (k : κ) :
    coefficientMatrix (C := A) b *
        (Matrix.of fun j l ↦ h (star (coefficientMatrix (C := A) b i j) *
          coefficientMatrix (C := A) c k l)).map (algebraMap R A) =
      (Matrix.of fun j l ↦ h (star (coefficientMatrix (C := A) b i j) *
        coefficientMatrix (C := A) c k l)).map (algebraMap R A) *
        coefficientMatrix (C := A) c := by
  set u := coefficientMatrix (C := A) b
  set v := coefficientMatrix (C := A) c
  set X : Matrix ι κ R := Matrix.of fun j l ↦ h (star (u i j) * v k l)
  ext r l
  have hstep (j : ι) :
      ∑ p : ι, ∑ q : κ, h (star (u i p) * v k q) • (star (u p j) * v q l) =
        h (star (u i j) * v k l) • (1 : A) := by
    simpa only [Coalgebra.Repr.star_index, Coalgebra.Repr.star_left, Coalgebra.Repr.star_right,
      coeffRepr] using hh.sum_sum_mul (coeffRepr b i j).star (coeffRepr c k l)
  have hu_entry (p : ι) : ∑ j : ι, u r j * star (u p j) = if r = p then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.one_apply] using congr_fun (congr_fun hu r) p
  calc
    (u * X.map (algebraMap R A)) r l
      = ∑ j : ι, u r j * (h (star (u i j) * v k l) • (1 : A)) := by
          simp [X, Matrix.mul_apply, Algebra.algebraMap_eq_smul_one]
    _ = ∑ j : ι, u r j *
          ∑ p : ι, ∑ q : κ, h (star (u i p) * v k q) • (star (u p j) * v q l) := by
          simp_rw [← hstep]
    _ = ∑ p : ι, ∑ q : κ,
          h (star (u i p) * v k q) • ((∑ j : ι, u r j * star (u p j)) * v q l) := by
          simp_rw [Finset.mul_sum, mul_smul_comm, Finset.sum_mul, mul_assoc]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ ↦ ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun q _ ↦ by rw [← Finset.smul_sum]
    _ = (X.map (algebraMap R A) * v) r l := by
          simp [X, hu_entry, Matrix.mul_apply, Algebra.smul_def]

/-- **Left-invariant Haar intertwiner.** If `h` is left invariant and `vᴴ * v = 1` for
`v = coefficientMatrix c`, then for each `j` and `l` the scalar matrix
`Y i k = h (u i j * star (v k l))` intertwines `v` with `u = coefficientMatrix b`. -/
theorem coefficientMatrix_mul_map_apply_mul_star [Fintype ι] [Fintype κ] [DecidableEq κ]
    {h : A →ₗ[R] R} (hh : h.IsLeftInvariantIntegral) (b : Basis ι R M) {c : Basis κ R N}
    (hv : (coefficientMatrix (C := A) c)ᴴ * coefficientMatrix (C := A) c = 1)
    (j : ι) (l : κ) :
    coefficientMatrix (C := A) b *
        (Matrix.of fun i k ↦ h (coefficientMatrix (C := A) b i j *
          star (coefficientMatrix (C := A) c k l))).map (algebraMap R A) =
      (Matrix.of fun i k ↦ h (coefficientMatrix (C := A) b i j *
        star (coefficientMatrix (C := A) c k l))).map (algebraMap R A) *
        coefficientMatrix (C := A) c := by
  set u := coefficientMatrix (C := A) b
  set v := coefficientMatrix (C := A) c
  set Y : Matrix ι κ R := Matrix.of fun i k ↦ h (u i j * star (v k l))
  ext i s
  have hstep (k : κ) :
      ∑ p : ι, ∑ q : κ, h (u p j * star (v q l)) • (u i p * star (v k q)) =
        h (u i j * star (v k l)) • (1 : A) := by
    simpa only [Coalgebra.Repr.star_index, Coalgebra.Repr.star_left, Coalgebra.Repr.star_right,
      coeffRepr] using hh.sum_sum_mul (coeffRepr b i j) (coeffRepr c k l).star
  have hv_entry (q : κ) : ∑ k : κ, star (v k q) * v k s = if q = s then 1 else 0 := by
    simpa [Matrix.mul_apply, Matrix.one_apply] using congr_fun (congr_fun hv q) s
  symm
  calc
    (Y.map (algebraMap R A) * v) i s
      = ∑ k : κ, (h (u i j * star (v k l)) • (1 : A)) * v k s := by
          simp [Y, Matrix.mul_apply, Algebra.algebraMap_eq_smul_one]
    _ = ∑ k : κ,
          (∑ p : ι, ∑ q : κ, h (u p j * star (v q l)) • (u i p * star (v k q))) * v k s := by
          simp_rw [← hstep]
    _ = ∑ p : ι, ∑ q : κ,
          h (u p j * star (v q l)) • (u i p * ∑ k : κ, star (v k q) * v k s) := by
          simp_rw [Finset.sum_mul, smul_mul_assoc, Finset.mul_sum, mul_assoc]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ ↦ ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun q _ ↦ by rw [← Finset.smul_sum]
    _ = (u * Y.map (algebraMap R A)) i s := by
          simp [Y, hv_entry, Matrix.mul_apply, Algebra.smul_def, Algebra.commutes]

/-- When every comodule morphism `N → M` is zero, a right invariant integral kills every product
`star (u i j) * v k l` whenever `u * uᴴ = 1`. -/
theorem apply_star_mul_coefficientMatrix_eq_zero [Fintype ι] [DecidableEq ι] [Finite κ]
    {h : A →ₗ[R] R} (hh : h.IsRightInvariantIntegral) (hzero : ∀ f : Hom R A N M, f = 0)
    {b : Basis ι R M} (hu : coefficientMatrix (C := A) b * (coefficientMatrix (C := A) b)ᴴ = 1)
    (c : Basis κ R N) (i j : ι) (k l : κ) :
    h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) c k l) = 0 := by
  classical
  cases nonempty_fintype κ
  let X : Matrix ι κ R :=
    Matrix.of fun j' l' ↦ h (star (coefficientMatrix (C := A) b i j') *
      coefficientMatrix (C := A) c k l')
  let f : Hom R A N M :=
    { toLinearMap := Matrix.toLin c b X
      map_coact := (c.map_coact_iff_coefficientMatrix b _).mpr (by
        rw [LinearMap.toMatrix_toLin]
        exact coefficientMatrix_mul_map_apply_star_mul hh hu c i k) }
  have hf : Matrix.toLin c b X = 0 := congr_arg Hom.toLinearMap (hzero f)
  have hX : X = 0 := by
    rw [← LinearMap.toMatrix_toLin c b X, hf, map_zero]
  exact congr_fun (congr_fun hX j) l

/-- When every comodule morphism `N → M` is zero, a left invariant integral kills every product
`u i j * star (v k l)` whenever `vᴴ * v = 1`. -/
theorem apply_coefficientMatrix_mul_star_eq_zero [Finite ι] [Fintype κ] [DecidableEq κ]
    {h : A →ₗ[R] R} (hh : h.IsLeftInvariantIntegral) (hzero : ∀ f : Hom R A N M, f = 0)
    (b : Basis ι R M) {c : Basis κ R N}
    (hv : (coefficientMatrix (C := A) c)ᴴ * coefficientMatrix (C := A) c = 1)
    (i j : ι) (k l : κ) :
    h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) c k l)) = 0 := by
  cases nonempty_fintype ι
  let Y : Matrix ι κ R :=
    Matrix.of fun i' k' ↦ h (coefficientMatrix (C := A) b i' j *
      star (coefficientMatrix (C := A) c k' l))
  let f : Hom R A N M :=
    { toLinearMap := Matrix.toLin c b Y
      map_coact := (c.map_coact_iff_coefficientMatrix b _).mpr (by
        rw [LinearMap.toMatrix_toLin]
        exact coefficientMatrix_mul_map_apply_mul_star hh b hv j l) }
  have hf : Matrix.toLin c b Y = 0 := congr_arg Hom.toLinearMap (hzero f)
  have hY : Y = 0 := by
    rw [← LinearMap.toMatrix_toLin c b Y, hf, map_zero]
  exact congr_fun (congr_fun hY i) k

end BialgebraIntertwiners

section SimpleCrossOrthogonality

/-- Simple comodules with distinct matrix-coefficient submodules have no nonzero morphisms. -/
private theorem hom_eq_zero_of_matrixCoefficientSubmodule_ne
    {R A M N : Type*} [CommRing R] [AddCommGroup A] [Module R A] [Coalgebra R A]
    [Module.Projective R A]
    [AddCommGroup M] [Module R M] [Comodule R A M] [IsSimpleOrder (Subcomodule R A M)]
    [AddCommGroup N] [Module R N] [Comodule R A N] [IsSimpleOrder (Subcomodule R A N)]
    (hne : matrixCoefficientSubmodule (R := R) (C := A) (M := M) ≠
      matrixCoefficientSubmodule (R := R) (C := A) (M := N))
    (f : Hom R A N M) : f = 0 := by
  by_contra hf
  exact hne.symm (matrixCoefficientSubmodule_eq_of_ne_zero hf)

variable {R A M N ι κ : Type*} [CommRing R] [StarRing R] [Ring A] [StarRing A]
  [Bialgebra R A] [Module.Projective R A] [StarModule R A] [StarCoalgebra R A]
  [AddCommGroup M] [Module R M] [Comodule R A M] [IsSimpleOrder (Subcomodule R A M)]
  [AddCommGroup N] [Module R N] [Comodule R A N] [IsSimpleOrder (Subcomodule R A N)]

/-- **Cross-orthogonality (first form).** Matrix coefficients of simple comodules with distinct
coefficient spaces are orthogonal with respect to any right invariant integral `h`:
`h (star (u i j) * v k l) = 0` when `u` is unitary. -/
theorem apply_star_mul_coefficientMatrix_eq_zero_of_ne [Fintype ι] [DecidableEq ι] [Finite κ]
    {h : A →ₗ[R] R} (hh : h.IsRightInvariantIntegral)
    (hne : matrixCoefficientSubmodule (R := R) (C := A) (M := M) ≠
      matrixCoefficientSubmodule (R := R) (C := A) (M := N))
    {b : Basis ι R M} (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    (c : Basis κ R N) (i j : ι) (k l : κ) :
    h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) c k l) = 0 :=
  apply_star_mul_coefficientMatrix_eq_zero hh (hom_eq_zero_of_matrixCoefficientSubmodule_ne hne)
    (by simpa [star_eq_conjTranspose] using (Unitary.mem_iff.mp hu).2) c i j k l

/-- **Cross-orthogonality (second form).** Matrix coefficients of simple comodules with distinct
coefficient spaces satisfy `h (u i j * star (v k l)) = 0` for any left invariant integral `h` when
`v` is unitary. -/
theorem apply_coefficientMatrix_mul_star_eq_zero_of_ne [Finite ι] [Fintype κ] [DecidableEq κ]
    {h : A →ₗ[R] R} (hh : h.IsLeftInvariantIntegral)
    (hne : matrixCoefficientSubmodule (R := R) (C := A) (M := M) ≠
      matrixCoefficientSubmodule (R := R) (C := A) (M := N))
    (b : Basis ι R M) {c : Basis κ R N}
    (hv : coefficientMatrix (C := A) c ∈ unitary (Matrix κ κ A))
    (i j : ι) (k l : κ) :
    h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) c k l)) = 0 :=
  apply_coefficientMatrix_mul_star_eq_zero hh (hom_eq_zero_of_matrixCoefficientSubmodule_ne hne) b
    (by simpa [star_eq_conjTranspose] using (Unitary.mem_iff.mp hv).1) i j k l

end SimpleCrossOrthogonality

section WeightedSchur

/-- A basis of a simple complex comodule has a nonempty index type. -/
private theorem nonempty_index (A : Type*) {M ι : Type*} [Ring A] [HopfAlgebra ℂ A]
    [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M] [IsSimpleOrder (Subcomodule ℂ A M)]
    (b : Basis ι ℂ M) : Nonempty ι := by
  let _ := convolutionModule (R := ℂ) (C := A) (M := M)
  have : IsSimpleModule (WithConv (A →ₗ[ℂ] ℂ)) M :=
    isSimpleModule_convolution_iff.mpr inferInstance
  have : Nontrivial M := IsSimpleModule.nontrivial (WithConv (A →ₗ[ℂ] ℂ)) M
  exact b.index_nonempty

/-- Schur's lemma in matrix coordinates on a simple complex comodule: any scalar matrix
intertwining `coefficientMatrix b` with itself is a scalar multiple of `1`. -/
private theorem exists_eq_smul_one_of_intertwines {A M ι : Type*} [Ring A] [HopfAlgebra ℂ A]
    [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M] [IsSimpleOrder (Subcomodule ℂ A M)]
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℂ M) {X : Matrix ι ι ℂ}
    (hX : coefficientMatrix (C := A) b * X.map (algebraMap ℂ A) =
      X.map (algebraMap ℂ A) * coefficientMatrix (C := A) b) :
    ∃ c : ℂ, X = c • 1 := by
  let _ : FiniteDimensional ℂ M := Module.Finite.of_basis b
  let _ := convolutionModule (R := ℂ) (C := A) (M := M)
  have : IsSimpleModule (WithConv (A →ₗ[ℂ] ℂ)) M :=
    isSimpleModule_convolution_iff.mpr inferInstance
  let T : Hom ℂ A M M :=
    { toLinearMap := Matrix.toLin b b X
      map_coact := (b.map_coact_iff_coefficientMatrix b _).mpr
        (by rw [LinearMap.toMatrix_toLin]; exact hX) }
  set c : ℂ := endAlgEquivSelfOfIsSimpleModule (k := ℂ) T.toConvolutionLinearMap
  refine ⟨c, ?_⟩
  have hT : Matrix.toLin b b X = c • LinearMap.id :=
    LinearMap.ext fun m ↦ by
      change T m = c • m
      rw [← Hom.toConvolutionLinearMap_apply, ← endAlgEquivSelfOfIsSimpleModule_smul (k := ℂ)]
  rw [← LinearMap.toMatrix_toLin b b X, hT, map_smul, LinearMap.toMatrix_id]

variable {A M ι : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A]
  [StarModule ℂ A] [StarCoalgebra ℂ A]
  [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M] [IsSimpleOrder (Subcomodule ℂ A M)]
  [Fintype ι] [DecidableEq ι]

/-- Left invariance collapses `h (u i j * star (u k l))` to `δ_{ik} C j l` on a simple comodule. -/
private theorem exists_apply_coefficientMatrix_mul_star_eq_ite {h : A →ₗ[ℂ] ℂ}
    (hh : h.IsLeftInvariantIntegral) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ∃ C : Matrix ι ι ℂ, ∀ i j k l : ι,
      h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
        if i = k then C j l else 0 := by
  have hv : (coefficientMatrix (C := A) b)ᴴ * coefficientMatrix (C := A) b = 1 := by
    simpa [star_eq_conjTranspose] using (Unitary.mem_iff.mp hu).1
  have hex (j l : ι) : ∃ c : ℂ, ∀ i k : ι,
      h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
        if i = k then c else 0 := by
    obtain ⟨c, hc⟩ := exists_eq_smul_one_of_intertwines b
      (coefficientMatrix_mul_map_apply_mul_star hh b hv j l)
    exact ⟨c, fun i k ↦ by simpa [Matrix.one_apply] using congr_fun (congr_fun hc i) k⟩
  refine ⟨Matrix.of fun j l ↦ (hex j l).choose, fun i j k l ↦ ?_⟩
  exact (hex j l).choose_spec i k

/-- **Weighted Schur orthogonality (second form).** For a nonzero positive left invariant integral
`h` and a simple comodule `M` with unitary basis `b`,
`h (u i j * star (u k l)) = δ_{ik} * h 1 * (Ft j l / Tr Ft)` where `Ft = unitarizingMatrix h b`. -/
theorem _root_.LinearMap.IsLeftInvariantIntegral.apply_coefficientMatrix_mul_star {h : A →ₗ[ℂ] ℂ}
    (hh : h.IsLeftInvariantIntegral) (h0 : h ≠ 0) (hpos : ∀ a, 0 ≤ h (star a * a))
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    (i j k l : ι) :
    h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
      if i = k then h 1 * (unitarizingMatrix h b j l / (unitarizingMatrix h b).trace) else 0 := by
  let _ : Module.Finite ℂ M := Module.Finite.of_basis b
  let _ := dual (R := ℂ) (H := A) (M := M)
  have : Nonempty ι := nonempty_index A b
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hstrict : ∀ a, a ≠ 0 → 0 < h (star a * a) := fun a ha ↦ hh.map_star_mul_self_pos h0 hpos ha
  obtain ⟨C, hC⟩ := exists_apply_coefficientMatrix_mul_star_eq_ite hh b hu
  have hCtr : C.trace = h 1 := by
    have huu : ∑ m : ι, coefficientMatrix (C := A) b i₀ m *
        star (coefficientMatrix (C := A) b i₀ m) = 1 := by
      simpa [Matrix.mul_apply, star_eq_conjTranspose] using
        congr_fun (congr_fun (Unitary.mem_iff.mp hu).2 i₀) i₀
    calc
      C.trace = ∑ m : ι, h (coefficientMatrix (C := A) b i₀ m *
          star (coefficientMatrix (C := A) b i₀ m)) := by simp [Matrix.trace, hC]
      _ = h 1 := by rw [← map_sum, huu]
  set G := haarGramMatrix h b.dualBasis
  have hGC : G = (Fintype.card ι : ℂ) • C := by
    ext j' l'
    rw [show G = haarGramMatrix h b.dualBasis from rfl,
      haarGramMatrix_dualBasis_apply_of_mem_unitary h b hu, map_sum]
    simp [hC]
  set r : ℂ := (Real.sqrt (((G⁻¹.trace).re) / ((G.trace).re)) : ℂ)
  set α : ℂ := r * (Fintype.card ι : ℂ)
  have hFtC : unitarizingMatrix h b = α • C := by
    ext j' l'
    simp [unitarizingMatrix_eq_smul_haarGramMatrix, G, hGC, α, r, Complex.real_smul, mul_assoc]
  have htr_ne : (unitarizingMatrix h b).trace ≠ 0 :=
    (posDef_unitarizingMatrix hstrict b).trace_pos.ne'
  have htr_eq : (unitarizingMatrix h b).trace = α * h 1 := by
    rw [hFtC, trace_smul, smul_eq_mul, hCtr]
  obtain ⟨hα, hh1⟩ := mul_ne_zero_iff.mp (htr_eq ▸ htr_ne)
  rw [hC, htr_eq, hFtC, Matrix.smul_apply, smul_eq_mul]
  split_ifs
  · field_simp [hα, hh1]
  · rfl

/-- **Weighted Schur orthogonality (first form).** For a nonzero positive two-sided invariant
integral `h` and a simple comodule `M` with unitary basis `b`,
`h (star (u i j) * u k l) = δ_{jl} * h 1 * (Ft⁻¹ i k / Tr Ft⁻¹)` where `Ft = unitarizingMatrix h b`.
-/
theorem apply_star_mul_coefficientMatrix {h : A →ₗ[ℂ] ℂ}
    (hh_left : h.IsLeftInvariantIntegral) (hh_right : h.IsRightInvariantIntegral)
    (h0 : h ≠ 0) (hpos : ∀ a, 0 ≤ h (star a * a))
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    (i j k l : ι) :
    h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
      if j = l then
        h 1 * ((unitarizingMatrix h b)⁻¹ i k / (unitarizingMatrix h b)⁻¹.trace)
      else 0 := by
  have := nonempty_index A b
  have hstrict : ∀ a, a ≠ 0 → 0 < h (star a * a) :=
    fun a ha ↦ hh_left.map_star_mul_self_pos h0 hpos ha
  have hu2 : coefficientMatrix (C := A) b * (coefficientMatrix (C := A) b)ᴴ = 1 := by
    simpa [star_eq_conjTranspose] using (Unitary.mem_iff.mp hu).2
  obtain ⟨d, hd⟩ := exists_eq_smul_one_of_intertwines b
    (coefficientMatrix_mul_map_apply_star_mul hh_right hu2 b i k)
  have hd_apply (p q : ι) :
      h (star (coefficientMatrix (C := A) b i p) * coefficientMatrix (C := A) b k q) =
        if p = q then d else 0 := by
    simpa [Matrix.one_apply] using congr_fun (congr_fun hd p) q
  rw [hd_apply]
  split_ifs
  · set Ft := unitarizingMatrix h b
    have htr_ne : Ft⁻¹.trace ≠ 0 := (posDef_unitarizingMatrix hstrict b).inv.trace_pos.ne'
    have hinv_ik := congr_arg h
      (congr_fun (congr_fun (map_star_mul_unitarizingMatrix_inv_mul_conjTranspose
        hh_right b hu) i) k)
    have hsum : Ft⁻¹.trace * d = Ft⁻¹ i k * h 1 := by
      simpa [Matrix.mul_apply, Finset.sum_mul, Algebra.algebraMap_eq_smul_one,
        mul_smul_comm, smul_mul_assoc, map_sum, map_smul, hd_apply, Matrix.trace] using hinv_ik
    apply mul_left_cancel₀ htr_ne
    rw [hsum]
    field_simp [htr_ne]
  · rfl

/-- **Linear independence of irreducible unitary matrix coefficients.** On a simple comodule `M`
over `ℂ`, if `A` admits a nonzero positive left invariant integral `h` and `b` has unitary
coefficient matrix `u`, then the `dim(M)²` entries `u i j` are linearly independent over `ℂ`. -/
theorem _root_.LinearMap.IsLeftInvariantIntegral.linearIndependent_coefficientMatrix
    {h : A →ₗ[ℂ] ℂ} (hh : h.IsLeftInvariantIntegral) (h0 : h ≠ 0)
    (hpos : ∀ a, 0 ≤ h (star a * a)) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    LinearIndependent ℂ (Function.uncurry (coefficientMatrix (C := A) b)) := by
  have := nonempty_index A b
  have hstrict : ∀ a, a ≠ 0 → 0 < h (star a * a) := fun a ha ↦ hh.map_star_mul_self_pos h0 hpos ha
  have : Nontrivial A := RingHom.domain_nontrivial (Bialgebra.counitAlgHom ℂ A).toRingHom
  have hh1 : h 1 ≠ 0 := (by simpa using hstrict 1 one_ne_zero : 0 < h 1).ne'
  set Ft := unitarizingMatrix h b
  have hFt : Ft.PosDef := posDef_unitarizingMatrix hstrict b
  have htr : Ft.trace ≠ 0 := hFt.trace_pos.ne'
  rw [Fintype.linearIndependent_iff]
  rintro g hg ⟨k, j⟩
  have hg' : ∑ p : ι × ι, g p • coefficientMatrix (C := A) b p.1 p.2 = 0 := hg
  let x : ι → ℂ := fun j' ↦ g (k, j')
  have hxFt : x ᵥ* Ft = 0 := by
    ext l
    have hpair : h ((∑ p : ι × ι, g p • coefficientMatrix (C := A) b p.1 p.2) *
        star (coefficientMatrix (C := A) b k l)) = 0 := by rw [hg', zero_mul, map_zero]
    rw [Fintype.sum_prod_type, Finset.sum_comm] at hpair
    simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, smul_eq_mul,
      hh.apply_coefficientMatrix_mul_star h0 hpos b hu, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hpair
    have hmul : (h 1 / Ft.trace) * (x ᵥ* Ft) l = 0 := by
      rw [vecMul, dotProduct, Finset.mul_sum]
      refine (Finset.sum_congr rfl fun j' _ ↦ ?_).trans hpair
      dsimp [x, Ft]
      ring
    exact (mul_eq_zero.mp hmul).resolve_left (div_ne_zero hh1 htr)
  have hdet : IsUnit Ft.det := (isUnit_iff_isUnit_det Ft).mp hFt.isUnit
  have hx : x = 0 := by
    calc
      x = x ᵥ* (Ft * Ft⁻¹) := by rw [mul_nonsing_inv Ft hdet, vecMul_one]
      _ = (x ᵥ* Ft) ᵥ* Ft⁻¹ := (vecMul_vecMul x Ft Ft⁻¹).symm
      _ = 0 := by rw [hxFt, zero_vecMul]
  exact congr_fun hx j

end WeightedSchur

end TauCeti.Comodule

namespace TauCeti.AlgebraicHaar

open TauCeti.Comodule

section CrossOrthogonality

variable {A M N ι κ : Type*} [Ring A] [StarRing A] [Bialgebra ℂ A]
  [StarModule ℂ A] [StarCoalgebra ℂ A]
  [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M] [IsSimpleOrder (Subcomodule ℂ A M)]
  [AddCommGroup N] [Module ℂ N] [Comodule ℂ A N] [IsSimpleOrder (Subcomodule ℂ A N)]

/-- Cross-orthogonality `h (star (u i j) * v k l) = 0` for `h : AlgebraicHaar A` on inequivalent
simple comodules. -/
theorem apply_star_mul_coefficientMatrix_eq_zero_of_ne [Fintype ι] [DecidableEq ι] [Finite κ]
    (h : AlgebraicHaar A)
    (hne : matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M) ≠
      matrixCoefficientSubmodule (R := ℂ) (C := A) (M := N))
    {b : Basis ι ℂ M} (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    (c : Basis κ ℂ N) (i j : ι) (k l : κ) :
    h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) c k l) = 0 :=
  Comodule.apply_star_mul_coefficientMatrix_eq_zero_of_ne
    h.isRightInvariantIntegral hne hu c i j k l

/-- Cross-orthogonality `h (u i j * star (v k l)) = 0` for `h : AlgebraicHaar A` on inequivalent
simple comodules. -/
theorem apply_coefficientMatrix_mul_star_eq_zero_of_ne [Finite ι] [Fintype κ] [DecidableEq κ]
    (h : AlgebraicHaar A)
    (hne : matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M) ≠
      matrixCoefficientSubmodule (R := ℂ) (C := A) (M := N))
    (b : Basis ι ℂ M) {c : Basis κ ℂ N}
    (hv : coefficientMatrix (C := A) c ∈ unitary (Matrix κ κ A))
    (i j : ι) (k l : κ) :
    h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) c k l)) = 0 :=
  Comodule.apply_coefficientMatrix_mul_star_eq_zero_of_ne
    h.isLeftInvariantIntegral hne b hv i j k l

end CrossOrthogonality

section HopfCore

variable {A M ι : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A] [StarModule ℂ A]
  [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M] [Fintype ι] [DecidableEq ι]

/-- For `h : AlgebraicHaar A`, the unitarizing matrix of any finite basis is positive definite. -/
theorem posDef_unitarizingMatrix (h : AlgebraicHaar A) (b : Basis ι ℂ M) :
    (unitarizingMatrix h.toLinearMap b).PosDef :=
  Comodule.posDef_unitarizingMatrix (fun _ ↦ h.map_star_mul_self_pos) b

/-- For `h : AlgebraicHaar A`, the unitarizing matrix satisfies `Tr Ft = Tr Ft⁻¹`. -/
theorem trace_unitarizingMatrix_eq_trace_inv (h : AlgebraicHaar A) (b : Basis ι ℂ M) :
    (unitarizingMatrix h.toLinearMap b).trace = (unitarizingMatrix h.toLinearMap b)⁻¹.trace :=
  Comodule.trace_unitarizingMatrix_eq_trace_inv (fun _ ↦ h.map_star_mul_self_pos) b

/-- On a basis indexed by a subsingleton type (such as a one-dimensional comodule), the
unitarizing matrix with respect to `h : AlgebraicHaar A` is `1`. -/
@[simp]
theorem unitarizingMatrix_of_subsingleton [Subsingleton ι] (h : AlgebraicHaar A)
    (b : Basis ι ℂ M) :
    unitarizingMatrix h.toLinearMap b = 1 :=
  Comodule.unitarizingMatrix_of_subsingleton (fun _ ↦ h.map_star_mul_self_pos) b

variable [StarCoalgebra ℂ A] [IsSimpleOrder (Subcomodule ℂ A M)]

/-- Normalized first Schur orthogonality formula:
`h (star (u i j) * u k l) = δ_{jl} * (Ft⁻¹ i k / Tr Ft⁻¹)`. -/
theorem apply_star_mul_coefficientMatrix (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) (i j k l : ι) :
    h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
      if j = l then
        (unitarizingMatrix h.toLinearMap b)⁻¹ i k / (unitarizingMatrix h.toLinearMap b)⁻¹.trace
      else 0 := by
  simpa [map_one h] using Comodule.apply_star_mul_coefficientMatrix h.isLeftInvariantIntegral
    h.isRightInvariantIntegral h.toLinearMap_ne_zero h.apply_star_mul_self_nonneg b hu i j k l

/-- Normalized second Schur orthogonality formula:
`h (u i j * star (u k l)) = δ_{ik} * (Ft j l / Tr Ft)`. -/
theorem apply_coefficientMatrix_mul_star (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) (i j k l : ι) :
    h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
      if i = k then
        unitarizingMatrix h.toLinearMap b j l / (unitarizingMatrix h.toLinearMap b).trace
      else 0 := by
  simpa [map_one h] using h.isLeftInvariantIntegral.apply_coefficientMatrix_mul_star
    h.toLinearMap_ne_zero h.apply_star_mul_self_nonneg b hu i j k l

/-- Linear independence of the `dim(M)²` matrix coefficients of a simple unitary comodule over a
Hopf star algebra equipped with `AlgebraicHaar`. -/
theorem linearIndependent_coefficientMatrix (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    LinearIndependent ℂ (Function.uncurry (coefficientMatrix (C := A) b)) :=
  h.isLeftInvariantIntegral.linearIndependent_coefficientMatrix h.toLinearMap_ne_zero
    h.apply_star_mul_self_nonneg b hu

/-- **Existence and uniqueness in weighted Schur orthogonality.** On a simple comodule `M` with a
basis `b` whose coefficient matrix `u` is unitary, `unitarizingMatrix h.toLinearMap b` is the
unique positive definite matrix `Ft` with `Tr Ft = Tr Ft⁻¹` satisfying both weighted Schur
orthogonality formulas. -/
theorem existsUnique_schur_orthogonality (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ∃! Ft : Matrix ι ι ℂ, Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
      (∀ i j k l,
        h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
          if i = k then Ft j l / Ft.trace else 0) := by
  set Ft₀ := unitarizingMatrix h.toLinearMap b
  refine ⟨Ft₀, ⟨h.posDef_unitarizingMatrix b, h.trace_unitarizingMatrix_eq_trace_inv b,
    h.apply_star_mul_coefficientMatrix b hu, h.apply_coefficientMatrix_mul_star b hu⟩, ?_⟩
  rintro Ft ⟨hFt, htr, -, h2⟩
  have : Nonempty ι := by
    let _ := convolutionModule (R := ℂ) (C := A) (M := M)
    have : IsSimpleModule (WithConv (A →ₗ[ℂ] ℂ)) M :=
      isSimpleModule_convolution_iff.mpr inferInstance
    have : Nontrivial M := IsSimpleModule.nontrivial (WithConv (A →ₗ[ℂ] ℂ)) M
    exact b.index_nonempty
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have htrFt : Ft.trace ≠ 0 := hFt.trace_pos.ne'
  set q : ℂ := Ft.trace / Ft₀.trace
  have hsmul : Ft = q • Ft₀ := by
    ext j l
    have heq : Ft j l / Ft.trace = Ft₀ j l / Ft₀.trace := by
      simpa using (h2 i₀ j i₀ l).symm.trans (h.apply_coefficientMatrix_mul_star b hu i₀ j i₀ l)
    rw [Matrix.smul_apply, smul_eq_mul]
    rw [div_eq_iff htrFt] at heq
    calc
      Ft j l = Ft₀ j l / Ft₀.trace * Ft.trace := heq
      _ = q * Ft₀ j l := by dsimp [q]; ring
  have hmap : Ft.map (algebraMap ℂ A) = q • Ft₀.map (algebraMap ℂ A) := by
    ext j l
    rw [hsmul, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.smul_apply,
      Matrix.map_apply, Algebra.smul_def]
  refine eq_unitarizingMatrix_of_map_star h.isRightInvariantIntegral
    (fun _ ↦ h.map_star_mul_self_pos) b hu hFt htr ?_
  rw [hmap, Matrix.mul_smul, Matrix.smul_mul,
    conjTranspose_map_star_mul_unitarizingMatrix_mul h.isRightInvariantIntegral b hu]

/-- **Weighted Schur orthogonality.** On a simple comodule `M` with a basis `b` whose coefficient
matrix `u` is unitary, there exists a positive definite matrix `Ft` with `Tr Ft = Tr Ft⁻¹`
governing both pairings `h (star (u i j) * u k l)` and `h (u i j * star (u k l))`. -/
theorem schur_orthogonality (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ∃ Ft : Matrix ι ι ℂ, Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
      (∀ i j k l,
        h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
          if i = k then Ft j l / Ft.trace else 0) :=
  (h.existsUnique_schur_orthogonality b hu).exists

end HopfCore

end TauCeti.AlgebraicHaar

namespace TauCeti.Comodule.IsUnitary

variable {A M ι : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A]
  [StarModule ℂ A] [StarCoalgebra ℂ A]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
  [Comodule ℂ A M] [IsSimpleOrder (Subcomodule ℂ A M)] [Fintype ι]

/-- Linear independence of the matrix coefficients of a simple unitary comodule in an orthonormal
basis. -/
theorem linearIndependent_coefficientMatrix (hM : IsUnitary ℂ A M) (h : AlgebraicHaar A)
    (b : OrthonormalBasis ι ℂ M) :
    LinearIndependent ℂ (Function.uncurry (coefficientMatrix (C := A) b.toBasis)) := by
  classical
  exact h.linearIndependent_coefficientMatrix b.toBasis (hM.coefficientMatrix_mem_unitary b)

variable [DecidableEq ι]

/-- Normalized first Schur orthogonality formula in an orthonormal basis of a simple unitary
comodule. -/
theorem apply_star_mul_coefficientMatrix (hM : IsUnitary ℂ A M) (h : AlgebraicHaar A)
    (b : OrthonormalBasis ι ℂ M) (i j k l : ι) :
    h (star (coefficientMatrix (C := A) b.toBasis i j) *
        coefficientMatrix (C := A) b.toBasis k l) =
      if j = l then
        (unitarizingMatrix h.toLinearMap b.toBasis)⁻¹ i k /
          (unitarizingMatrix h.toLinearMap b.toBasis)⁻¹.trace
      else 0 :=
  h.apply_star_mul_coefficientMatrix b.toBasis (hM.coefficientMatrix_mem_unitary b) i j k l

/-- Normalized second Schur orthogonality formula in an orthonormal basis of a simple unitary
comodule. -/
theorem apply_coefficientMatrix_mul_star (hM : IsUnitary ℂ A M) (h : AlgebraicHaar A)
    (b : OrthonormalBasis ι ℂ M) (i j k l : ι) :
    h (coefficientMatrix (C := A) b.toBasis i j *
        star (coefficientMatrix (C := A) b.toBasis k l)) =
      if i = k then
        unitarizingMatrix h.toLinearMap b.toBasis j l /
          (unitarizingMatrix h.toLinearMap b.toBasis).trace
      else 0 :=
  h.apply_coefficientMatrix_mul_star b.toBasis (hM.coefficientMatrix_mem_unitary b) i j k l

/-- **Weighted Schur orthogonality for finite-dimensional unitary comodules.** For a simple
unitary comodule `M` in an orthonormal basis `b`, there exists a unique positive definite matrix
`Ft` with `Tr Ft = Tr Ft⁻¹` governing both matrix-coefficient pairings under `h : AlgebraicHaar A`.
-/
theorem existsUnique_schur_orthogonality (hM : IsUnitary ℂ A M) (h : AlgebraicHaar A)
    (b : OrthonormalBasis ι ℂ M) :
    ∃! Ft : Matrix ι ι ℂ, Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
      (∀ i j k l,
        h (star (coefficientMatrix (C := A) b.toBasis i j) *
            coefficientMatrix (C := A) b.toBasis k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (coefficientMatrix (C := A) b.toBasis i j *
            star (coefficientMatrix (C := A) b.toBasis k l)) =
          if i = k then Ft j l / Ft.trace else 0) :=
  h.existsUnique_schur_orthogonality b.toBasis (hM.coefficientMatrix_mem_unitary b)

/-- Existential form of weighted Schur orthogonality in an orthonormal basis of a simple unitary
comodule. -/
theorem schur_orthogonality (hM : IsUnitary ℂ A M) (h : AlgebraicHaar A)
    (b : OrthonormalBasis ι ℂ M) :
    ∃ Ft : Matrix ι ι ℂ, Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
      (∀ i j k l,
        h (star (coefficientMatrix (C := A) b.toBasis i j) *
            coefficientMatrix (C := A) b.toBasis k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (coefficientMatrix (C := A) b.toBasis i j *
            star (coefficientMatrix (C := A) b.toBasis k l)) =
          if i = k then Ft j l / Ft.trace else 0) :=
  h.schur_orthogonality b.toBasis (hM.coefficientMatrix_mem_unitary b)

end TauCeti.Comodule.IsUnitary
