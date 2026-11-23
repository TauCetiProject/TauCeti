/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Adjoin
public import TauCeti.Algebra.Coalgebra.Comodule.Unitary.Orthogonality
public import TauCeti.Algebra.Coalgebra.Comodule.Unitary.UnitarizingMatrix
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Isotypic

/-!
# Explicit weighted Schur orthogonality for finite unitary comodules

Let `A` be a star bialgebra or Hopf star algebra equipped with invariant integrals, and let `M` and
`N` be right `A`-comodules with finite bases `b` and `c` and coefficient matrices `u` and `v`.

1. **Cross-orthogonality of inequivalent simple comodules.** Combining the Haar cross-orthogonality
   of `TauCeti.Algebra.Coalgebra.Comodule.Unitary.Orthogonality` with the fact that simple
   comodules with distinct coefficient spaces admit no nonzero morphism, all cross-pairings
   `h (star (u i j) * v k l)` (for right invariant `h` and `u * uᴴ = 1`) and
   `h (u i j * star (v k l))` (for left invariant `h` and `vᴴ * v = 1`) vanish.

2. **Explicit weighted Schur orthogonality on a simple comodule (Hopf star algebras over `ℂ`).**
   When `M` is simple, `u` is unitary, and `h` is a positive one-sided invariant integral, the
   normalized unitarizing matrix `Ft = unitarizingMatrix h b` governs each pairing of matrix
   coefficients (including at `h = 0`, where both sides vanish):
   * `h (star (u i j) * u k l) = δ_{jl} * h 1 * (Ft⁻¹ i k / Tr Ft⁻¹)` (requiring only right
     invariance);
   * `h (u i j * star (u k l)) = δ_{ik} * h 1 * (Ft j l / Tr Ft)` (requiring only left invariance).

   Specializing to `h : AlgebraicHaar A` sets `h 1 = 1`, so `unitarizingMatrix h b` is an explicit
   witness for the unique matrix of `TauCeti.AlgebraicHaar.schur_orthogonality`.

## Main declarations

* `TauCeti.Comodule.apply_star_mul_coefficientMatrix_eq_zero_of_ne` and
  `TauCeti.Comodule.apply_coefficientMatrix_mul_star_eq_zero_of_ne`: orthogonality of matrix
  coefficients of inequivalent simple comodules.
* `TauCeti.Comodule.apply_coefficientMatrix_mul_star` and
  `TauCeti.Comodule.apply_star_mul_coefficientMatrix`: the two weighted Schur orthogonality
  formulas for an unnormalized positive one-sided invariant integral.
* `TauCeti.AlgebraicHaar.apply_star_mul_coefficientMatrix`,
  `TauCeti.AlgebraicHaar.apply_coefficientMatrix_mul_star`, and their
  `TauCeti.Comodule.IsUnitary` versions: the normalized formulas.

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

section SimpleCrossOrthogonality

variable {R A M N ι κ : Type*} [CommRing R] [StarRing R] [Ring A] [StarRing A]
  [Bialgebra R A] [Module.Projective R A] [StarModule R A] [StarCoalgebra R A]
  [AddCommGroup M] [Module R M] [Comodule R A M] [IsSimpleOrder (Subcomodule R A M)]
  [AddCommGroup N] [Module R N] [Comodule R A N] [IsSimpleOrder (Subcomodule R A N)]

/-- **Cross-orthogonality (first form).** Matrix coefficients of simple comodules with distinct
coefficient spaces are orthogonal with respect to any right invariant integral `h`:
`h (star (u i j) * v k l) = 0` when `u * uᴴ = 1`. -/
theorem apply_star_mul_coefficientMatrix_eq_zero_of_ne [Fintype ι] [DecidableEq ι] [Finite κ]
    {h : A →ₗ[R] R} (hh : h.IsRightInvariantIntegral)
    (hne : matrixCoefficientSubmodule (R := R) (C := A) (M := M) ≠
      matrixCoefficientSubmodule (R := R) (C := A) (M := N))
    {b : Basis ι R M} (hu : coefficientMatrix (C := A) b * (coefficientMatrix (C := A) b)ᴴ = 1)
    (c : Basis κ R N) (i j : ι) (k l : κ) :
    h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) c k l) = 0 :=
  hh.map_star_coefficientMatrix_mul_eq_zero b c hu
    (hom_eq_zero_of_matrixCoefficientSubmodule_ne hne.symm) i j k l

/-- **Cross-orthogonality (second form).** Matrix coefficients of simple comodules with distinct
coefficient spaces satisfy `h (u i j * star (v k l)) = 0` for any left invariant integral `h` when
`vᴴ * v = 1`. -/
theorem apply_coefficientMatrix_mul_star_eq_zero_of_ne [Finite ι] [Fintype κ] [DecidableEq κ]
    {h : A →ₗ[R] R} (hh : h.IsLeftInvariantIntegral)
    (hne : matrixCoefficientSubmodule (R := R) (C := A) (M := M) ≠
      matrixCoefficientSubmodule (R := R) (C := A) (M := N))
    (b : Basis ι R M) {c : Basis κ R N}
    (hv : (coefficientMatrix (C := A) c)ᴴ * coefficientMatrix (C := A) c = 1)
    (i j : ι) (k l : κ) :
    h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) c k l)) = 0 :=
  hh.map_coefficientMatrix_mul_star_eq_zero b c hv
    (hom_eq_zero_of_matrixCoefficientSubmodule_ne hne.symm) i j k l

end SimpleCrossOrthogonality

section WeightedSchur

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
    obtain ⟨c, hc⟩ := b.exists_eq_smul_one_of_commute_coefficientMatrix _
      (hh.coefficientMatrix_mul_map_mul_star b b hv j l)
    exact ⟨c, fun i k ↦ by simpa [Matrix.one_apply] using congr_fun (congr_fun hc i) k⟩
  refine ⟨Matrix.of fun j l ↦ (hex j l).choose, fun i j k l ↦ ?_⟩
  exact (hex j l).choose_spec i k

/-- **Weighted Schur orthogonality (second form).** For a positive left invariant integral `h` and
a simple comodule `M` with unitary basis `b`,
`h (u i j * star (u k l)) = δ_{ik} * h 1 * (Ft j l / Tr Ft)` where `Ft = unitarizingMatrix h b`. -/
theorem apply_coefficientMatrix_mul_star {h : A →ₗ[ℂ] ℂ}
    (hh : h.IsLeftInvariantIntegral) (hpos : ∀ a, 0 ≤ h (star a * a))
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    (i j k l : ι) :
    h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
      if i = k then h 1 * (unitarizingMatrix h b j l / (unitarizingMatrix h b).trace) else 0 := by
  by_cases h0 : h = 0
  · subst h0
    simp
  let _ : Module.Finite ℂ M := Module.Finite.of_basis b
  let _ := dual (R := ℂ) (H := A) (M := M)
  have : Nontrivial M := (Subcomodule.nontrivial_iff (R := ℂ) (C := A)).mp inferInstance
  have : Nonempty ι := b.index_nonempty
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
  set G := haarGramMatrix h b.dualBasis with hG_def
  have hGC : G = (Fintype.card ι : ℂ) • C := by
    ext j' l'
    rw [hG_def, haarGramMatrix_dualBasis_apply_of_mem_unitary h b hu, map_sum]
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

/-- **Weighted Schur orthogonality (first form).** For a positive right invariant integral `h` and
a simple comodule `M` with unitary basis `b`,
`h (star (u i j) * u k l) = δ_{jl} * h 1 * (Ft⁻¹ i k / Tr Ft⁻¹)` where
`Ft = unitarizingMatrix h b`. -/
theorem apply_star_mul_coefficientMatrix {h : A →ₗ[ℂ] ℂ}
    (hh : h.IsRightInvariantIntegral) (hpos : ∀ a, 0 ≤ h (star a * a))
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    (i j k l : ι) :
    h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
      if j = l then
        h 1 * ((unitarizingMatrix h b)⁻¹ i k / (unitarizingMatrix h b)⁻¹.trace)
      else 0 := by
  by_cases h0 : h = 0
  · subst h0
    simp
  have : Nontrivial M := (Subcomodule.nontrivial_iff (R := ℂ) (C := A)).mp inferInstance
  have : Nonempty ι := b.index_nonempty
  have hstrict : ∀ a, a ≠ 0 → 0 < h (star a * a) := fun a ha ↦ hh.map_star_mul_self_pos h0 hpos ha
  have hu2 : coefficientMatrix (C := A) b * (coefficientMatrix (C := A) b)ᴴ = 1 := by
    simpa [star_eq_conjTranspose] using (Unitary.mem_iff.mp hu).2
  obtain ⟨d, hd⟩ := b.exists_eq_smul_one_of_commute_coefficientMatrix _
    (hh.coefficientMatrix_mul_map_star_mul b b hu2 i k)
  have hd_apply (p q : ι) :
      h (star (coefficientMatrix (C := A) b i p) * coefficientMatrix (C := A) b k q) =
        if p = q then d else 0 := by
    simpa [Matrix.one_apply] using congr_fun (congr_fun hd p) q
  rw [hd_apply]
  split_ifs
  · set Ft := unitarizingMatrix h b
    set u := coefficientMatrix (C := A) b
    have htr_ne : Ft⁻¹.trace ≠ 0 := (posDef_unitarizingMatrix hstrict b).inv.trace_pos.ne'
    have hinv_ik := congr_arg h
      (congr_fun (congr_fun (map_star_mul_unitarizingMatrix_inv_mul_conjTranspose
        hh b hu) i) k)
    have hsum : Ft⁻¹.trace * d = Ft⁻¹ i k * h 1 := by
      calc
        Ft⁻¹.trace * d = ∑ q : ι, Ft⁻¹ q q * d := by
          simp only [Matrix.trace, Matrix.diag_apply, Finset.sum_mul]
        _ = ∑ q : ι, ∑ p : ι, Ft⁻¹ p q * h (star (u i p) * u k q) := by
          refine Finset.sum_congr rfl fun q _ ↦ ?_
          simp [hd_apply]
        _ = h ((u.map star * Ft⁻¹.map (algebraMap ℂ A) * (u.map star)ᴴ) i k) := by
          simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.conjTranspose_apply, star_star,
            Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one,
            Finset.sum_mul, map_sum, map_smul, smul_eq_mul]
        _ = h (Ft⁻¹.map (algebraMap ℂ A) i k) := hinv_ik
        _ = Ft⁻¹ i k * h 1 := by
          rw [Matrix.map_apply, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
    apply mul_left_cancel₀ htr_ne
    rw [hsum]
    field_simp [htr_ne]
  · rfl

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
simple comodules when `u * uᴴ = 1`. -/
theorem apply_star_mul_coefficientMatrix_eq_zero_of_ne [Fintype ι] [DecidableEq ι] [Finite κ]
    (h : AlgebraicHaar A)
    (hne : matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M) ≠
      matrixCoefficientSubmodule (R := ℂ) (C := A) (M := N))
    {b : Basis ι ℂ M} (hu : coefficientMatrix (C := A) b * (coefficientMatrix (C := A) b)ᴴ = 1)
    (c : Basis κ ℂ N) (i j : ι) (k l : κ) :
    h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) c k l) = 0 :=
  Comodule.apply_star_mul_coefficientMatrix_eq_zero_of_ne
    h.isRightInvariantIntegral hne hu c i j k l

/-- Cross-orthogonality `h (u i j * star (v k l)) = 0` for `h : AlgebraicHaar A` on inequivalent
simple comodules when `vᴴ * v = 1`. -/
theorem apply_coefficientMatrix_mul_star_eq_zero_of_ne [Finite ι] [Fintype κ] [DecidableEq κ]
    (h : AlgebraicHaar A)
    (hne : matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M) ≠
      matrixCoefficientSubmodule (R := ℂ) (C := A) (M := N))
    (b : Basis ι ℂ M) {c : Basis κ ℂ N}
    (hv : (coefficientMatrix (C := A) c)ᴴ * coefficientMatrix (C := A) c = 1)
    (i j : ι) (k l : κ) :
    h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) c k l)) = 0 :=
  Comodule.apply_coefficientMatrix_mul_star_eq_zero_of_ne
    h.isLeftInvariantIntegral hne b hv i j k l

end CrossOrthogonality

section HopfCore

variable {A M ι : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A]
  [StarModule ℂ A] [StarCoalgebra ℂ A]
  [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M] [IsSimpleOrder (Subcomodule ℂ A M)]
  [Fintype ι] [DecidableEq ι]

/-- Normalized first Schur orthogonality formula:
`h (star (u i j) * u k l) = δ_{jl} * (Ft⁻¹ i k / Tr Ft⁻¹)`. -/
theorem apply_star_mul_coefficientMatrix (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) (i j k l : ι) :
    h (star (coefficientMatrix (C := A) b i j) * coefficientMatrix (C := A) b k l) =
      if j = l then
        (unitarizingMatrix h.toLinearMap b)⁻¹ i k / (unitarizingMatrix h.toLinearMap b)⁻¹.trace
      else 0 := by
  simpa [h.map_one] using Comodule.apply_star_mul_coefficientMatrix
    h.isRightInvariantIntegral h.map_star_mul_self_nonneg b hu i j k l

/-- Normalized second Schur orthogonality formula:
`h (u i j * star (u k l)) = δ_{ik} * (Ft j l / Tr Ft)`. -/
theorem apply_coefficientMatrix_mul_star (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) (i j k l : ι) :
    h (coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b k l)) =
      if i = k then
        unitarizingMatrix h.toLinearMap b j l / (unitarizingMatrix h.toLinearMap b).trace
      else 0 := by
  simpa [h.map_one] using Comodule.apply_coefficientMatrix_mul_star
    h.isLeftInvariantIntegral h.map_star_mul_self_nonneg b hu i j k l

end HopfCore

end TauCeti.AlgebraicHaar

namespace TauCeti.Comodule.IsUnitary

variable {A M ι : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A]
  [StarModule ℂ A] [StarCoalgebra ℂ A]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
  [Comodule ℂ A M] [IsSimpleOrder (Subcomodule ℂ A M)] [Fintype ι] [DecidableEq ι]

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

end TauCeti.Comodule.IsUnitary
