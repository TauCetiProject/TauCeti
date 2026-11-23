/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Unitarization
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic
public import TauCeti.Algebra.HopfAlgebra.Integral.Haar
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.Coalgebra.Comodule.Schur
import TauCeti.Algebra.Coalgebra.Subcomodule.Dual
import TauCeti.LinearAlgebra.Matrix.Nonsingular.Inverse
import TauCeti.LinearAlgebra.Matrix.PosDef.Basic

/-!
# The normalized unitarizing matrix

Let `M` be a right comodule over a complex Hopf algebra `A` with a star structure and a finite
basis `b`. Given a linear functional `h : A →ₗ[ℂ] ℂ`, the Haar Gram matrix
`G = haarGramMatrix h b.dualBasis` of the explicit dual comodule `M*` satisfies `wᴴ G w = G` when
`h` is right invariant (for a Hopf star algebra), and is positive definite when `h` is strictly
positive. Rescaling `G` by `√(re (Tr G⁻¹) / re (Tr G))` produces the normalized unitarizing matrix
`Ft` (`TauCeti.Comodule.unitarizingMatrix`), which satisfies:

* when `h` commutes with `star`, `Ft` is Hermitian (`isHermitian_unitarizingMatrix`) and satisfies
  `Tr Ft = Tr Ft⁻¹` (`trace_unitarizingMatrix_eq_trace_inv`);
* when `h` is strictly positive, `Ft` is positive definite (`posDef_unitarizingMatrix`);
* when `h` is right invariant, `wᴴ Ft w = Ft` (`conjTranspose_dualBasis_mul_unitarizingMatrix_mul`)
  and `w Ft⁻¹ wᴴ = Ft⁻¹` (`dualBasis_mul_unitarizingMatrix_inv_mul_conjTranspose`);
* when `M` is simple and `h` is strictly positive and right invariant, `Ft` is uniquely determined
  among positive definite matrices by `Tr F = Tr F⁻¹` and `wᴴ F w = F`
  (`eq_unitarizingMatrix_of_posDef`).

## Main declarations

* `TauCeti.Comodule.unitarizingMatrix`: the normalized unitarizing matrix `Ft` of a finite basis.
* `TauCeti.Comodule.isHermitian_unitarizingMatrix`,
  `TauCeti.Comodule.trace_unitarizingMatrix_eq_trace_inv`, and
  `TauCeti.Comodule.posDef_unitarizingMatrix`: Hermiticity, trace normalization `Tr Ft = Tr Ft⁻¹`,
  and positive definiteness.
* `TauCeti.Comodule.conjTranspose_dualBasis_mul_unitarizingMatrix_mul` and
  `TauCeti.Comodule.conjTranspose_map_star_mul_unitarizingMatrix_mul`: Haar invariance
  `wᴴ Ft w = Ft` (and `(u.map star)ᴴ Ft (u.map star) = Ft` when `u` is unitary).
* `TauCeti.Comodule.eq_unitarizingMatrix_of_posDef`: uniqueness of `Ft` on a simple comodule.
* `TauCeti.AlgebraicHaar.posDef_unitarizingMatrix`,
  `TauCeti.AlgebraicHaar.trace_unitarizingMatrix_eq_trace_inv`, and
  `TauCeti.AlgebraicHaar.unitarizingMatrix_of_subsingleton`: specializations to `AlgebraicHaar A`.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Proposition 3.2.9 and
  Theorem 5.4.1.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*, SMF,
  2013, Theorem 1.4.2 and Step 1 of Theorem 1.6.6.
-/

public section

open Module Matrix
open scoped ComplexOrder

namespace TauCeti.Comodule

section UnitarizingMatrix

variable {A M ι : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A]
  [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M] [Fintype ι] [DecidableEq ι]

/-- The normalized unitarizing matrix `Ft` of a finite basis `b` with respect to `h : A →ₗ[ℂ] ℂ`.

Writing `G` for the Haar Gram matrix of the explicit dual comodule `M*` in `b.dualBasis`, `Ft` is
`√(re (Tr G⁻¹) / re (Tr G)) • G`. When `h` is right invariant, `Ft` satisfies `wᴴ Ft w = Ft` for
the dual-basis coefficient matrix `w`; when `h` commutes with `star`, `Ft` is Hermitian with
`Tr Ft = Tr Ft⁻¹`; when `h` is strictly positive, `Ft` is positive definite, so a strictly positive
right invariant integral yields a matrix `Ft` that unitarizes the dual corepresentation. -/
noncomputable def unitarizingMatrix (h : A →ₗ[ℂ] ℂ) (b : Basis ι ℂ M) : Matrix ι ι ℂ :=
  letI : Module.Finite ℂ M := Module.Finite.of_basis b
  letI := dual (R := ℂ) (H := A) (M := M)
  let G := haarGramMatrix h b.dualBasis
  Real.sqrt ((G⁻¹.trace).re / (G.trace).re) • G

/-- Unfold `unitarizingMatrix` as a nonnegative-real multiple of the dual-basis Haar Gram
matrix. -/
theorem unitarizingMatrix_eq_smul_haarGramMatrix [Module.Finite ℂ M]
    (h : A →ₗ[ℂ] ℂ) (b : Basis ι ℂ M) :
    letI := dual (R := ℂ) (H := A) (M := M)
    unitarizingMatrix h b =
      Real.sqrt (((haarGramMatrix h b.dualBasis)⁻¹.trace).re /
        ((haarGramMatrix h b.dualBasis).trace).re) • haarGramMatrix h b.dualBasis :=
  (rfl)

/-- When `b` has unitary coefficient matrix `u`, the Haar Gram matrix of `b.dualBasis` has entries
`G j l = h (∑ i, u i j * star (u i l))`. -/
theorem haarGramMatrix_dualBasis_apply_of_mem_unitary [Module.Finite ℂ M] (h : A →ₗ[ℂ] ℂ)
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) (j l : ι) :
    letI := dual (R := ℂ) (H := A) (M := M)
    haarGramMatrix h b.dualBasis j l =
      h (∑ i, coefficientMatrix (C := A) b i j * star (coefficientMatrix (C := A) b i l)) := by
  let _ := dual (R := ℂ) (H := A) (M := M)
  simp [haarGramMatrix_apply, coefficientMatrix_dualBasis_of_mem_unitary b hu]

/-- Scaling `h` by a positive real constant leaves `unitarizingMatrix` unchanged. -/
theorem unitarizingMatrix_smul (h : A →ₗ[ℂ] ℂ) {c : ℝ} (hc : 0 < c) (b : Basis ι ℂ M) :
    unitarizingMatrix (c • h) b = unitarizingMatrix h b := by
  let _ : Module.Finite ℂ M := Module.Finite.of_basis b
  let _ := dual (R := ℂ) (H := A) (M := M)
  set G := haarGramMatrix h b.dualBasis
  have hGc : haarGramMatrix (c • h) b.dualBasis = c • G := by
    ext j l
    simp [G, haarGramMatrix_apply, Complex.real_smul, Finset.mul_sum]
  rw [unitarizingMatrix_eq_smul_haarGramMatrix, unitarizingMatrix_eq_smul_haarGramMatrix,
    hGc, Matrix.nonsing_inv_smul, trace_smul, trace_smul]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  have hdiv : c⁻¹ * (G⁻¹.trace).re / (c * (G.trace).re) =
      c⁻¹ ^ 2 * ((G⁻¹.trace).re / (G.trace).re) := by
    by_cases hGtr : (G.trace).re = 0
    · simp [hGtr]
    · field_simp [hc.ne', hGtr]
  rw [hdiv, Real.sqrt_mul (sq_nonneg c⁻¹), Real.sqrt_sq (inv_nonneg.mpr hc.le), smul_smul,
    mul_right_comm, inv_mul_cancel₀ hc.ne', one_mul]

/-- The unitarizing matrix of a star-preserving functional is Hermitian. -/
theorem isHermitian_unitarizingMatrix {h : A →ₗ[ℂ] ℂ} (hstar : ∀ a, h (star a) = star (h a))
    (b : Basis ι ℂ M) :
    (unitarizingMatrix h b).IsHermitian := by
  let _ : Module.Finite ℂ M := Module.Finite.of_basis b
  let _ := dual (R := ℂ) (H := A) (M := M)
  rw [unitarizingMatrix_eq_smul_haarGramMatrix]
  refine (IsHermitian.ext fun j l ↦ ?_).smul (IsSelfAdjoint.all _)
  simp [haarGramMatrix_apply, ← hstar, star_sum]

/-- For any star-preserving functional `h`, the unitarizing matrix satisfies
`Tr Ft = Tr Ft⁻¹`. -/
theorem trace_unitarizingMatrix_eq_trace_inv {h : A →ₗ[ℂ] ℂ}
    (hstar : ∀ a, h (star a) = star (h a)) (b : Basis ι ℂ M) :
    (unitarizingMatrix h b).trace = (unitarizingMatrix h b)⁻¹.trace := by
  let _ : Module.Finite ℂ M := Module.Finite.of_basis b
  let _ := dual (R := ℂ) (H := A) (M := M)
  set G := haarGramMatrix h b.dualBasis with hG_def
  have hGherm : G.IsHermitian := IsHermitian.ext fun j l ↦ by
    simp [G, haarGramMatrix_apply, ← hstar, star_sum]
  have hre (N : Matrix ι ι ℂ) (hN : N.IsHermitian) : (N.trace.re : ℂ) = N.trace :=
    Complex.conj_eq_iff_re.mp (by rw [← Complex.star_def, ← Matrix.trace_conjTranspose, hN.eq])
  rw [unitarizingMatrix_eq_smul_haarGramMatrix, ← hG_def]
  by_cases hq : 0 < G⁻¹.trace.re / G.trace.re
  · set t := Real.sqrt (G⁻¹.trace.re / G.trace.re)
    have ht : 0 < t := Real.sqrt_pos.mpr hq
    have hGtr : G.trace.re ≠ 0 := fun h0 ↦ by simp [h0] at hq
    have htsq : t ^ 2 = G⁻¹.trace.re / G.trace.re := Real.sq_sqrt hq.le
    have hreal : t * G.trace.re = t⁻¹ * G⁻¹.trace.re := by
      apply mul_left_cancel₀ ht.ne'
      calc
        t * (t * G.trace.re) = t ^ 2 * G.trace.re := by ring
        _ = G⁻¹.trace.re := by rw [htsq, div_mul_cancel₀ _ hGtr]
        _ = t * (t⁻¹ * G⁻¹.trace.re) := by rw [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
    rw [Matrix.nonsing_inv_smul, trace_smul, trace_smul, ← hre G hGherm, ← hre G⁻¹ hGherm.inv,
      Complex.real_smul, Complex.real_smul]
    exact_mod_cast hreal
  · rw [Real.sqrt_eq_zero_of_nonpos (not_lt.mp hq), zero_smul, Matrix.inv_zero]

section StrictlyPositive

variable [StarModule ℂ A] {h : A →ₗ[ℂ] ℂ}

/-- For a strictly positive functional `h`, the unitarizing matrix `Ft` is positive definite. -/
theorem posDef_unitarizingMatrix (hpos : ∀ a, a ≠ 0 → 0 < h (star a * a)) (b : Basis ι ℂ M) :
    (unitarizingMatrix h b).PosDef := by
  let _ : Module.Finite ℂ M := Module.Finite.of_basis b
  let _ := dual (R := ℂ) (H := A) (M := M)
  rcases isEmpty_or_nonempty ι with _ | _
  · exact Matrix.PosDef.of_isEmpty _
  · rw [unitarizingMatrix_eq_smul_haarGramMatrix]
    have hG := posDef_haarGramMatrix hpos b.dualBasis
    exact hG.smul (Real.sqrt_pos.mpr
      (div_pos (Complex.pos_iff.mp hG.inv.trace_pos).1 (Complex.pos_iff.mp hG.trace_pos).1))

/-- On a basis indexed by a subsingleton type (such as a one-dimensional comodule), the normalized
unitarizing matrix of any strictly positive functional is `1`. -/
@[simp]
theorem unitarizingMatrix_of_subsingleton [Subsingleton ι]
    (hpos : ∀ a, a ≠ 0 → 0 < h (star a * a)) (b : Basis ι ℂ M) :
    unitarizingMatrix h b = 1 := by
  let _ : Module.Finite ℂ M := Module.Finite.of_basis b
  let _ := dual (R := ℂ) (H := A) (M := M)
  rcases isEmpty_or_nonempty ι with _ | hne
  · exact Subsingleton.elim _ _
  · obtain ⟨i₀⟩ := hne
    let _ : Unique ι := uniqueOfSubsingleton i₀
    set G := haarGramMatrix h b.dualBasis with hG_def
    have hG : G.PosDef := posDef_haarGramMatrix hpos b.dualBasis
    set r := G.trace.re
    have hr : 0 < r := (Complex.pos_iff.mp hG.trace_pos).1
    have hGeq : (r : ℂ) = G.trace :=
      (Complex.eq_re_of_ofReal_le (r := 0) (by simpa using hG.trace_pos.le)).symm
    have hG1 : G = r • (1 : Matrix ι ι ℂ) := by
      ext i j
      rw [Subsingleton.elim i default, Subsingleton.elim j default]
      have htr : G.trace = G default default := by simp [Matrix.trace]
      simp [Complex.real_smul, ← htr, ← hGeq]
    have hinv : G⁻¹ = r⁻¹ • (1 : Matrix ι ι ℂ) := by
      rw [hG1, Matrix.nonsing_inv_smul, inv_one]
    rw [unitarizingMatrix_eq_smul_haarGramMatrix, ← hG_def, hinv, trace_smul]
    simp only [trace_one, Fintype.card_unique, Nat.cast_one, Complex.real_smul, mul_one,
      Complex.ofReal_re]
    have hdiv : r⁻¹ / r = r⁻¹ ^ 2 := by field_simp [hr.ne']
    rw [hdiv, Real.sqrt_sq (inv_nonneg.mpr hr.le), hG1, smul_smul, inv_mul_cancel₀ hr.ne',
      one_smul]

end StrictlyPositive

section StarCoalgebra

variable [StarModule ℂ A] [StarCoalgebra ℂ A] {h : A →ₗ[ℂ] ℂ}

/-- Right Haar invariance of the unitarizing matrix on the dual basis: `wᴴ Ft w = Ft` for
`w = coefficientMatrix b.dualBasis`. -/
theorem conjTranspose_dualBasis_mul_unitarizingMatrix_mul [Module.Finite ℂ M]
    (hh : h.IsRightInvariantIntegral) (b : Basis ι ℂ M) :
    letI := dual (R := ℂ) (H := A) (M := M)
    (coefficientMatrix (C := A) b.dualBasis)ᴴ *
        (unitarizingMatrix h b).map (algebraMap ℂ A) *
        coefficientMatrix (C := A) b.dualBasis =
      (unitarizingMatrix h b).map (algebraMap ℂ A) := by
  let _ := dual (R := ℂ) (H := A) (M := M)
  set G := haarGramMatrix h b.dualBasis with hG_def
  set r := Real.sqrt ((G⁻¹.trace).re / (G.trace).re)
  have hmap : (unitarizingMatrix h b).map (algebraMap ℂ A) =
      (r : ℂ) • G.map (algebraMap ℂ A) := by
    rw [unitarizingMatrix_eq_smul_haarGramMatrix, ← hG_def]
    ext j l
    rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply,
      Complex.real_smul, map_mul, Algebra.smul_def]
  rw [hmap, Matrix.mul_smul, Matrix.smul_mul,
    conjTranspose_coefficientMatrix_mul_haarGramMatrix_mul hh b.dualBasis]

/-- For a basis `b` with unitary coefficient matrix `u`, right invariance of `h` gives the
conjugate unitarizing equation `(u.map star)ᴴ * Ft * (u.map star) = Ft`. -/
theorem conjTranspose_map_star_mul_unitarizingMatrix_mul
    (hh : h.IsRightInvariantIntegral) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ((coefficientMatrix (C := A) b).map star)ᴴ *
        (unitarizingMatrix h b).map (algebraMap ℂ A) *
        (coefficientMatrix (C := A) b).map star =
      (unitarizingMatrix h b).map (algebraMap ℂ A) := by
  let _ : Module.Finite ℂ M := Module.Finite.of_basis b
  let _ := dual (R := ℂ) (H := A) (M := M)
  rw [← coefficientMatrix_dualBasis_of_mem_unitary b hu]
  exact conjTranspose_dualBasis_mul_unitarizingMatrix_mul hh b

/-- Inverted dual-basis invariance: `w * Ft⁻¹ * wᴴ = Ft⁻¹` for any right invariant integral `h`. -/
theorem dualBasis_mul_unitarizingMatrix_inv_mul_conjTranspose [Module.Finite ℂ M]
    (hh : h.IsRightInvariantIntegral) (b : Basis ι ℂ M) :
    letI := dual (R := ℂ) (H := A) (M := M)
    coefficientMatrix (C := A) b.dualBasis *
        (unitarizingMatrix h b)⁻¹.map (algebraMap ℂ A) *
        (coefficientMatrix (C := A) b.dualBasis)ᴴ =
      (unitarizingMatrix h b)⁻¹.map (algebraMap ℂ A) := by
  let _ := dual (R := ℂ) (H := A) (M := M)
  exact Matrix.mul_map_nonsing_inv_mul (algebraMap ℂ A)
    (coefficientMatrix_mul_map_antipode b.dualBasis)
    (conjTranspose_dualBasis_mul_unitarizingMatrix_mul hh b)

/-- For a basis `b` with unitary coefficient matrix `u`, inverted conjugate invariance gives
`(u.map star) * Ft⁻¹ * (u.map star)ᴴ = Ft⁻¹` for any right invariant integral `h`. -/
theorem map_star_mul_unitarizingMatrix_inv_mul_conjTranspose
    (hh : h.IsRightInvariantIntegral) (b : Basis ι ℂ M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    (coefficientMatrix (C := A) b).map star *
        (unitarizingMatrix h b)⁻¹.map (algebraMap ℂ A) *
        ((coefficientMatrix (C := A) b).map star)ᴴ =
      (unitarizingMatrix h b)⁻¹.map (algebraMap ℂ A) := by
  let _ : Module.Finite ℂ M := Module.Finite.of_basis b
  let _ := dual (R := ℂ) (H := A) (M := M)
  rw [← coefficientMatrix_dualBasis_of_mem_unitary b hu]
  exact dualBasis_mul_unitarizingMatrix_inv_mul_conjTranspose hh b

/-- Schur-scalar step: on a simple comodule `M`, any matrix `F` satisfying `wᴴ F w = F` for
`w = coefficientMatrix b.dualBasis` is a complex scalar multiple of `unitarizingMatrix h b`. -/
private theorem exists_eq_smul_unitarizingMatrix [Module.Finite ℂ M]
    [IsSimpleOrder (Subcomodule ℂ A M)]
    (hh : h.IsRightInvariantIntegral) (hpos : ∀ a, a ≠ 0 → 0 < h (star a * a))
    (b : Basis ι ℂ M) {F : Matrix ι ι ℂ}
    (hinv :
      letI := dual (R := ℂ) (H := A) (M := M)
      (coefficientMatrix (C := A) b.dualBasis)ᴴ * F.map (algebraMap ℂ A) *
          coefficientMatrix (C := A) b.dualBasis =
        F.map (algebraMap ℂ A)) :
    ∃ c : ℂ, F = c • unitarizingMatrix h b := by
  let _ := dual (R := ℂ) (H := A) (M := M)
  have : IsSimpleOrder (Subcomodule ℂ A (Module.Dual ℂ M)) :=
    Subcomodule.isSimpleOrder_dual_iff_of_starCoalgebra.mpr inferInstance
  set Ft := unitarizingMatrix h b
  have hFt : Ft.PosDef := posDef_unitarizingMatrix hpos b
  have hFtdet : IsUnit Ft.det := (isUnit_iff_isUnit_det Ft).mp hFt.isUnit
  set w := coefficientMatrix (C := A) b.dualBasis
  set f := algebraMap ℂ A
  have hinter : w * (Ft⁻¹ * F).map f = (Ft⁻¹ * F).map f * w := by
    have hwFt := dualBasis_mul_unitarizingMatrix_inv_mul_conjTranspose hh b
    calc
      w * (Ft⁻¹ * F).map f = w * (Ft⁻¹.map f * (wᴴ * F.map f * w)) := by rw [hinv, Matrix.map_mul]
      _ = (w * Ft⁻¹.map f * wᴴ) * F.map f * w := by simp only [Matrix.mul_assoc]
      _ = (Ft⁻¹ * F).map f * w := by rw [hwFt, ← Matrix.map_mul]
  obtain ⟨c, hFtF⟩ := b.dualBasis.exists_eq_smul_one_of_commute_coefficientMatrix _ hinter
  refine ⟨c, ?_⟩
  calc
    F = Ft * (Ft⁻¹ * F) := by rw [← Matrix.mul_assoc, mul_nonsing_inv Ft hFtdet, Matrix.one_mul]
    _ = c • Ft := by rw [hFtF, Matrix.mul_smul, Matrix.mul_one]

/-- **Uniqueness of the normalized unitarizing matrix.** On a simple comodule `M`, if `h` is a
strictly positive right invariant integral, then `unitarizingMatrix h b` is the unique positive
definite matrix `F` satisfying `Tr F = Tr F⁻¹` and `wᴴ F w = F` for
`w = coefficientMatrix b.dualBasis`. -/
theorem eq_unitarizingMatrix_of_posDef [Module.Finite ℂ M]
    [IsSimpleOrder (Subcomodule ℂ A M)]
    (hh : h.IsRightInvariantIntegral) (hpos : ∀ a, a ≠ 0 → 0 < h (star a * a))
    (b : Basis ι ℂ M) {F : Matrix ι ι ℂ} (hF : F.PosDef) (htr : F.trace = F⁻¹.trace)
    (hinv :
      letI := dual (R := ℂ) (H := A) (M := M)
      (coefficientMatrix (C := A) b.dualBasis)ᴴ * F.map (algebraMap ℂ A) *
          coefficientMatrix (C := A) b.dualBasis =
        F.map (algebraMap ℂ A)) :
    F = unitarizingMatrix h b := by
  have hnonneg (a : A) : 0 ≤ h (star a * a) := by
    obtain rfl | ha := eq_or_ne a 0
    · simp
    · exact (hpos a ha).le
  obtain ⟨c, hFc⟩ := exists_eq_smul_unitarizingMatrix hh hpos b hinv
  exact hF.eq_of_eq_smul_of_trace_eq_trace_inv (posDef_unitarizingMatrix hpos b) hFc htr
    (trace_unitarizingMatrix_eq_trace_inv (StarPositiveFunctional.mk h hnonneg).map_star b)

/-- Uniqueness of `unitarizingMatrix` phrased directly in terms of
`(u.map star)ᴴ F (u.map star) = F` when `b` has unitary coefficient matrix `u`. -/
theorem eq_unitarizingMatrix_of_map_star [IsSimpleOrder (Subcomodule ℂ A M)]
    (hh : h.IsRightInvariantIntegral) (hpos : ∀ a, a ≠ 0 → 0 < h (star a * a))
    (b : Basis ι ℂ M) (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {F : Matrix ι ι ℂ} (hF : F.PosDef) (htr : F.trace = F⁻¹.trace)
    (hinv : ((coefficientMatrix (C := A) b).map star)ᴴ * F.map (algebraMap ℂ A) *
        (coefficientMatrix (C := A) b).map star = F.map (algebraMap ℂ A)) :
    F = unitarizingMatrix h b := by
  let _ : Module.Finite ℂ M := Module.Finite.of_basis b
  refine eq_unitarizingMatrix_of_posDef hh hpos b hF htr ?_
  let _ := dual (R := ℂ) (H := A) (M := M)
  rwa [coefficientMatrix_dualBasis_of_mem_unitary b hu]

end StarCoalgebra

end UnitarizingMatrix

end TauCeti.Comodule

namespace TauCeti.AlgebraicHaar

open TauCeti.Comodule

variable {A M ι : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A] [StarModule ℂ A]
  [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M] [Fintype ι] [DecidableEq ι]

/-- For `h : AlgebraicHaar A`, the unitarizing matrix of any finite basis is positive definite. -/
theorem posDef_unitarizingMatrix (h : AlgebraicHaar A) (b : Basis ι ℂ M) :
    (unitarizingMatrix h.toLinearMap b).PosDef :=
  Comodule.posDef_unitarizingMatrix (fun _ ↦ h.map_star_mul_self_pos) b

/-- For `h : AlgebraicHaar A`, the unitarizing matrix satisfies `Tr Ft = Tr Ft⁻¹`. -/
theorem trace_unitarizingMatrix_eq_trace_inv (h : AlgebraicHaar A) (b : Basis ι ℂ M) :
    (unitarizingMatrix h.toLinearMap b).trace = (unitarizingMatrix h.toLinearMap b)⁻¹.trace :=
  Comodule.trace_unitarizingMatrix_eq_trace_inv h.map_star b

/-- On a basis indexed by a subsingleton type (such as a one-dimensional comodule), the
unitarizing matrix with respect to `h : AlgebraicHaar A` is `1`. -/
@[simp]
theorem unitarizingMatrix_of_subsingleton [Subsingleton ι] (h : AlgebraicHaar A)
    (b : Basis ι ℂ M) :
    unitarizingMatrix h.toLinearMap b = 1 :=
  Comodule.unitarizingMatrix_of_subsingleton (fun _ ↦ h.map_star_mul_self_pos) b

end TauCeti.AlgebraicHaar
