/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Dual
public import TauCeti.Algebra.Coalgebra.Comodule.Unitarization
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Module
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Intertwiner
import TauCeti.Algebra.Coalgebra.Subcomodule.Dual
import TauCeti.Algebra.HopfAlgebra.Star
import TauCeti.RingTheory.Semisimple.Schur

/-!
# The conjugate corepresentation and the normalized unitarizing matrix

Let `M` be a right comodule over a Hopf star algebra `A` with a finite basis `b` whose coefficient
matrix `u = coefficientMatrix b` is unitary. Because `S(u) = uᴴ`, the explicit right dual comodule
`M*` (`TauCeti.Comodule.dual`) has coefficient matrix `w = u.map star` in the dual basis
`b.dualBasis`: the algebraic dual realizes the conjugate corepresentation. When `A` is a Hopf star
algebra, its antipode is bijective, so `M*` is simple whenever `M` is simple.

Over `ℂ`, given a linear functional `h : A →ₗ[ℂ] ℂ`, the Haar Gram matrix
`G = haarGramMatrix h b.dualBasis` of `M*` satisfies `wᴴ G w = G` when `h` is right invariant, and
is positive definite when `h` is strictly positive. Rescaling `G` by
`√(re (Tr G⁻¹) / re (Tr G))` produces the normalized unitarizing matrix `Ft`
(`TauCeti.Comodule.unitarizingMatrix`), which satisfies:

* `Ft` is positive definite (`posDef_unitarizingMatrix`);
* `Tr Ft = Tr Ft⁻¹` (`trace_unitarizingMatrix_eq_trace_inv`);
* `wᴴ Ft w = Ft` (`conjTranspose_map_star_mul_unitarizingMatrix_mul`) and
  `w Ft⁻¹ wᴴ = Ft⁻¹` (`dualBasis_mul_unitarizingMatrix_inv_mul_conjTranspose`);
* when `M` is simple, `Ft` is uniquely determined among positive definite matrices by
  `Tr F = Tr F⁻¹` and `wᴴ F w = F` (`eq_unitarizingMatrix_of_posDef`).

## Main declarations

* `TauCeti.Comodule.coefficientMatrix_dualBasis_of_mem_unitary` and
  `TauCeti.Comodule.IsUnitary.coefficientMatrix_dualBasis`: in a unitary basis, `b.dualBasis` has
  coefficient matrix `(coefficientMatrix b).map star`.
* `TauCeti.Subcomodule.isSimpleOrder_dual_iff_of_starCoalgebra`: over a Hopf star algebra over a
  field, `M*` is simple if and only if `M` is simple.
* `TauCeti.Comodule.unitarizingMatrix`: the normalized unitarizing matrix `Ft` of a finite basis.
* `TauCeti.Comodule.posDef_unitarizingMatrix` and
  `TauCeti.Comodule.trace_unitarizingMatrix_eq_trace_inv`: positive definiteness and trace
  normalization `Tr Ft = Tr Ft⁻¹`.
* `TauCeti.Comodule.conjTranspose_dualBasis_mul_unitarizingMatrix_mul` and
  `TauCeti.Comodule.conjTranspose_map_star_mul_unitarizingMatrix_mul`: Haar invariance
  `wᴴ Ft w = Ft`.
* `TauCeti.Comodule.eq_unitarizingMatrix_of_posDef`: uniqueness of `Ft` on a simple comodule.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Proposition 3.2.9 and
  Theorem 5.4.1.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*, SMF,
  2013, Theorem 1.4.2 and Step 1 of Theorem 1.6.6.
-/

public section

open Module Matrix
open scoped ComplexOrder

section ConjugateMatrix

namespace TauCeti.Comodule

variable {R A M ι : Type*} [CommRing R] [Semiring A] [StarRing A]
  [HopfAlgebra R A] [AddCommGroup M] [Module R M] [Comodule R A M]
  [Module.Finite R M] [Module.Projective R M] [Fintype ι] [DecidableEq ι]

attribute [local instance] Comodule.dual

/-- When `b` has unitary coefficient matrix `u`, the dual basis `b.dualBasis` of the explicit right
dual comodule has coefficient matrix `u.map star`, the entrywise star (conjugate matrix). -/
theorem coefficientMatrix_dualBasis_of_mem_unitary (b : Basis ι R M)
    (hu : coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    coefficientMatrix (C := A) b.dualBasis = (coefficientMatrix (C := A) b).map star := by
  have hS : (coefficientMatrix (C := A) b).map (HopfAlgebra.antipode R) =
      (coefficientMatrix (C := A) b)ᴴ :=
    left_inv_eq_right_inv (map_antipode_mul_coefficientMatrix b) (Unitary.mem_iff.mp hu).2
  ext i j
  rw [coefficientMatrix_dualBasis, hS, transpose_apply, conjTranspose_apply, Matrix.map_apply]

end TauCeti.Comodule

namespace TauCeti.Comodule.IsUnitary

variable {𝕜 A M ι : Type*} [RCLike 𝕜] [Semiring A] [StarRing A] [HopfAlgebra 𝕜 A]
  [StarModule 𝕜 A] [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [FiniteDimensional 𝕜 M]
  [Comodule 𝕜 A M] [Fintype ι] [DecidableEq ι]

attribute [local instance] Comodule.dual

/-- For a finite-dimensional unitary comodule in an orthonormal basis `b`, the dual basis
`b.toBasis.dualBasis` has coefficient matrix `(coefficientMatrix b.toBasis).map star`. -/
theorem coefficientMatrix_dualBasis (hM : IsUnitary 𝕜 A M) (b : OrthonormalBasis ι 𝕜 M) :
    coefficientMatrix (C := A) b.toBasis.dualBasis =
      (coefficientMatrix (C := A) b.toBasis).map star :=
  coefficientMatrix_dualBasis_of_mem_unitary b.toBasis (hM.coefficientMatrix_mem_unitary b)

end TauCeti.Comodule.IsUnitary

namespace TauCeti.Subcomodule

variable {k A M : Type*} [Field k] [StarRing k] [Ring A] [StarRing A]
  [HopfAlgebra k A] [StarModule k A] [StarCoalgebra k A]
  [AddCommGroup M] [Module k M] [FiniteDimensional k M] [Comodule k A M]

attribute [local instance] Comodule.dual

/-- Over a Hopf star algebra over a field, the dual of a finite-dimensional comodule is simple if
and only if the comodule itself is simple, since the antipode is bijective. -/
theorem isSimpleOrder_dual_iff_of_starCoalgebra :
    IsSimpleOrder (Subcomodule k A (Module.Dual k M)) ↔ IsSimpleOrder (Subcomodule k A M) :=
  isSimpleOrder_dual_iff TauCeti.HopfAlgebra.antipode_bijective.injective

end TauCeti.Subcomodule

end ConjugateMatrix

namespace TauCeti.Comodule

section UnitarizingMatrix

variable {A M ι : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A]
  [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M] [Fintype ι] [DecidableEq ι]

/-- The normalized unitarizing matrix `Ft` of a finite basis `b` with respect to `h : A →ₗ[ℂ] ℂ`.

Writing `G` for the Haar Gram matrix of the explicit dual comodule `M*` in `b.dualBasis`, `Ft` is
`√(re (Tr G⁻¹) / re (Tr G)) • G`. When `h` is strictly positive, `Ft` is positive definite with
`Tr Ft = Tr Ft⁻¹`, and when `h` is right invariant it unitarizes the dual corepresentation. -/
noncomputable def unitarizingMatrix (h : A →ₗ[ℂ] ℂ) (b : Basis ι ℂ M) : Matrix ι ι ℂ :=
  letI : Module.Finite ℂ M := Module.Finite.of_basis b
  letI := dual (R := ℂ) (H := A) (M := M)
  let G := haarGramMatrix h b.dualBasis
  Real.sqrt ((G⁻¹.trace).re / (G.trace).re) • G

/-- Unfold `unitarizingMatrix` as a positive-real multiple of the dual-basis Haar Gram matrix. -/
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

/-- Scaling any complex matrix by a nonzero real scalar scales its nonsingular inverse by `r⁻¹`. -/
private theorem inv_real_smul {G : Matrix ι ι ℂ} {r : ℝ} (hr : r ≠ 0) :
    (r • G)⁻¹ = r⁻¹ • G⁻¹ := by
  by_cases hdet : IsUnit G.det
  · refine inv_eq_left_inv ?_
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hr, one_smul, nonsing_inv_mul G hdet]
  · have hrdet : ¬IsUnit (r • G).det := by
      rw [show r • G = (r : ℂ) • G by ext; simp [Complex.real_smul], det_smul]
      exact fun hu ↦ hdet (isUnit_of_mul_isUnit_right hu)
    rw [nonsing_inv_apply_not_isUnit _ hrdet, nonsing_inv_apply_not_isUnit _ hdet, smul_zero]

/-- Scaling `h` by a positive real constant leaves `unitarizingMatrix` unchanged. -/
theorem unitarizingMatrix_smul (h : A →ₗ[ℂ] ℂ) {c : ℝ} (hc : 0 < c) (b : Basis ι ℂ M) :
    unitarizingMatrix (c • h) b = unitarizingMatrix h b := by
  let _ : Module.Finite ℂ M := Module.Finite.of_basis b
  let _ := dual (R := ℂ) (H := A) (M := M)
  set G := haarGramMatrix h b.dualBasis
  have hGc : haarGramMatrix (c • h) b.dualBasis = c • G := by
    ext j l
    simp [G, haarGramMatrix_apply, Complex.real_smul, Finset.mul_sum]
  change unitarizingMatrix (c • h) b = Real.sqrt ((G⁻¹.trace).re / (G.trace).re) • G
  rw [unitarizingMatrix_eq_smul_haarGramMatrix, hGc, inv_real_smul hc.ne', trace_smul, trace_smul]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  have hdiv : c⁻¹ * (G⁻¹.trace).re / (c * (G.trace).re) =
      c⁻¹ ^ 2 * ((G⁻¹.trace).re / (G.trace).re) := by
    by_cases hGtr : (G.trace).re = 0
    · simp [hGtr]
    · field_simp [hc.ne', hGtr]
  rw [hdiv, Real.sqrt_mul (sq_nonneg c⁻¹), Real.sqrt_sq (inv_nonneg.mpr hc.le), smul_smul,
    mul_right_comm, inv_mul_cancel₀ hc.ne', one_mul]

section StrictlyPositive

variable [StarModule ℂ A] {h : A →ₗ[ℂ] ℂ}

/-- Any complex number that is strictly positive in `ComplexOrder` equals its real part and has
strictly positive real part. -/
private theorem pos_re_and_eq_ofReal {z : ℂ} (hz : 0 < z) : 0 < z.re ∧ (z.re : ℂ) = z := by
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hz
  exact ⟨hre, Complex.ext (by simp) (by simp [← him])⟩

/-- On a nonempty index type, the rescaling factor `√(re (Tr G⁻¹) / re (Tr G))` of a positive
definite matrix `G` is strictly positive. -/
private theorem sqrt_re_trace_inv_div_pos [Nonempty ι] {G : Matrix ι ι ℂ} (hG : G.PosDef) :
    0 < Real.sqrt ((G⁻¹.trace).re / (G.trace).re) :=
  Real.sqrt_pos.mpr (div_pos (pos_re_and_eq_ofReal hG.inv.trace_pos).1
    (pos_re_and_eq_ofReal hG.trace_pos).1)

/-- The unitarizing matrix of a positive functional is Hermitian. -/
theorem isHermitian_unitarizingMatrix (hpos : ∀ a, 0 ≤ h (star a * a)) (b : Basis ι ℂ M) :
    (unitarizingMatrix h b).IsHermitian := by
  let _ : Module.Finite ℂ M := Module.Finite.of_basis b
  let _ := dual (R := ℂ) (H := A) (M := M)
  exact (isHermitian_haarGramMatrix hpos b.dualBasis).smul (IsSelfAdjoint.all _)

/-- For a strictly positive functional `h`, the unitarizing matrix `Ft` is positive definite. -/
theorem posDef_unitarizingMatrix (hpos : ∀ a, a ≠ 0 → 0 < h (star a * a)) (b : Basis ι ℂ M) :
    (unitarizingMatrix h b).PosDef := by
  let _ : Module.Finite ℂ M := Module.Finite.of_basis b
  let _ := dual (R := ℂ) (H := A) (M := M)
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨Subsingleton.elim _ _, fun _ hx ↦ (hx (Subsingleton.elim _ _)).elim⟩
  · have hG := posDef_haarGramMatrix hpos b.dualBasis
    exact hG.smul (sqrt_re_trace_inv_div_pos hG)

/-- For a strictly positive functional `h`, the unitarizing matrix satisfies `Tr Ft = Tr Ft⁻¹`. -/
theorem trace_unitarizingMatrix_eq_trace_inv (hpos : ∀ a, a ≠ 0 → 0 < h (star a * a))
    (b : Basis ι ℂ M) :
    (unitarizingMatrix h b).trace = (unitarizingMatrix h b)⁻¹.trace := by
  let _ : Module.Finite ℂ M := Module.Finite.of_basis b
  let _ := dual (R := ℂ) (H := A) (M := M)
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Matrix.trace]
  · set G := haarGramMatrix h b.dualBasis
    have hG : G.PosDef := posDef_haarGramMatrix hpos b.dualBasis
    obtain ⟨hGre, hGeq⟩ := pos_re_and_eq_ofReal hG.trace_pos
    obtain ⟨hGinvRe, hGinvEq⟩ := pos_re_and_eq_ofReal hG.inv.trace_pos
    set t := Real.sqrt ((G⁻¹.trace).re / (G.trace).re)
    have ht : 0 < t := sqrt_re_trace_inv_div_pos hG
    have htsq : t ^ 2 = (G⁻¹.trace).re / (G.trace).re :=
      Real.sq_sqrt (div_nonneg hGinvRe.le hGre.le)
    have hreal : t * (G.trace).re = t⁻¹ * (G⁻¹.trace).re := by
      apply mul_left_cancel₀ ht.ne'
      calc
        t * (t * (G.trace).re) = t ^ 2 * (G.trace).re := by ring
        _ = (G⁻¹.trace).re := by rw [htsq, div_mul_cancel₀ _ hGre.ne']
        _ = t * (t⁻¹ * (G⁻¹.trace).re) := by rw [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
    rw [show unitarizingMatrix h b = t • G from rfl, inv_real_smul ht.ne',
      trace_smul, trace_smul, ← hGeq, ← hGinvEq, Complex.real_smul, Complex.real_smul]
    exact_mod_cast hreal

/-- On a basis indexed by a subsingleton type (such as a one-dimensional comodule), the normalized
unitarizing matrix of any strictly positive functional is `1`. -/
theorem unitarizingMatrix_of_subsingleton [Subsingleton ι]
    (hpos : ∀ a, a ≠ 0 → 0 < h (star a * a)) (b : Basis ι ℂ M) :
    unitarizingMatrix h b = 1 := by
  let _ : Module.Finite ℂ M := Module.Finite.of_basis b
  let _ := dual (R := ℂ) (H := A) (M := M)
  rcases isEmpty_or_nonempty ι with _ | hne
  · exact Subsingleton.elim _ _
  · obtain ⟨i₀⟩ := hne
    let _ : Unique ι := uniqueOfSubsingleton i₀
    set G := haarGramMatrix h b.dualBasis
    have hG : G.PosDef := posDef_haarGramMatrix hpos b.dualBasis
    obtain ⟨hGre, hGeq⟩ := pos_re_and_eq_ofReal hG.trace_pos
    set r := (G.trace).re
    have hG1 : G = r • (1 : Matrix ι ι ℂ) := by
      ext i j
      rw [Subsingleton.elim i default, Subsingleton.elim j default]
      have htr : G.trace = G default default := by simp [Matrix.trace]
      simp [Complex.real_smul, ← htr, hGeq]
    have hinv : G⁻¹ = r⁻¹ • (1 : Matrix ι ι ℂ) := by
      rw [hG1, inv_real_smul hGre.ne', inv_one]
    change Real.sqrt ((G⁻¹.trace).re / r) • G = 1
    rw [hinv, trace_smul]
    simp only [trace_one, Fintype.card_unique, Nat.cast_one, Complex.real_smul, mul_one,
      Complex.ofReal_re]
    have hdiv : r⁻¹ / r = r⁻¹ ^ 2 := by field_simp [hGre.ne']
    rw [hdiv, Real.sqrt_sq (inv_nonneg.mpr hGre.le), hG1, smul_smul, inv_mul_cancel₀ hGre.ne',
      one_smul]

end StrictlyPositive

/-- Helper: invert an invariance equation `wᴴ * F_A * w = F_A` when `w` has a right inverse
`w_inv` (handling singular `F` via `F⁻¹ = 0`). -/
private theorem mul_inv_map_mul_conjTranspose {w w_inv : Matrix ι ι A}
    (hw1 : w * w_inv = 1) {F : Matrix ι ι ℂ}
    (hinv : wᴴ * F.map (algebraMap ℂ A) * w = F.map (algebraMap ℂ A)) :
    w * F⁻¹.map (algebraMap ℂ A) * wᴴ = F⁻¹.map (algebraMap ℂ A) := by
  set f := algebraMap ℂ A
  by_cases hdet : IsUnit F.det
  · set FA := F.map f
    set FiA := F⁻¹.map f
    have hFFi : FA * FiA = 1 := by
      rw [← Matrix.map_mul, mul_nonsing_inv F hdet, Matrix.map_one _ (map_zero f) (map_one f)]
    have hFiF : FiA * FA = 1 := by
      rw [← Matrix.map_mul, nonsing_inv_mul F hdet, Matrix.map_one _ (map_zero f) (map_one f)]
    have hwFA : wᴴ * FA = FA * w_inv := by
      calc
        wᴴ * FA = wᴴ * FA * (w * w_inv) := by rw [hw1, Matrix.mul_one]
        _ = (wᴴ * FA * w) * w_inv := by simp only [Matrix.mul_assoc]
        _ = FA * w_inv := by rw [hinv]
    have hFiw : FiA * wᴴ = w_inv * FiA := by
      calc
        FiA * wᴴ = FiA * (wᴴ * (FA * FiA)) := by rw [hFFi, Matrix.mul_one]
        _ = (FiA * FA) * w_inv * FiA := by
          rw [← Matrix.mul_assoc wᴴ FA FiA, hwFA]; simp only [Matrix.mul_assoc]
        _ = w_inv * FiA := by rw [hFiF, Matrix.one_mul]
    calc
      w * FiA * wᴴ = w * (FiA * wᴴ) := by rw [Matrix.mul_assoc]
      _ = (w * w_inv) * FiA := by rw [hFiw, Matrix.mul_assoc]
      _ = FiA := by rw [hw1, Matrix.one_mul]
  · rw [nonsing_inv_apply_not_isUnit _ hdet, Matrix.map_zero _ (map_zero f),
      Matrix.mul_zero, Matrix.zero_mul]

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
  set G := haarGramMatrix h b.dualBasis
  set r := Real.sqrt ((G⁻¹.trace).re / (G.trace).re)
  have hmap : (unitarizingMatrix h b).map (algebraMap ℂ A) =
      (r : ℂ) • G.map (algebraMap ℂ A) := by
    ext j l
    rw [Matrix.map_apply, show unitarizingMatrix h b = r • G from rfl, Matrix.smul_apply,
      Complex.real_smul, map_mul, Matrix.smul_apply, Matrix.map_apply, Algebra.smul_def]
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
  exact mul_inv_map_mul_conjTranspose
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
`w = coefficientMatrix b.dualBasis` is a complex scalar multiple of `haarGramMatrix h b.dualBasis`.
-/
private theorem exists_eq_smul_haarGramMatrix [Module.Finite ℂ M]
    [IsSimpleOrder (Subcomodule ℂ A M)]
    (hh : h.IsRightInvariantIntegral) (hpos : ∀ a, a ≠ 0 → 0 < h (star a * a))
    (b : Basis ι ℂ M) {F : Matrix ι ι ℂ}
    (hinv :
      letI := dual (R := ℂ) (H := A) (M := M)
      (coefficientMatrix (C := A) b.dualBasis)ᴴ * F.map (algebraMap ℂ A) *
          coefficientMatrix (C := A) b.dualBasis =
        F.map (algebraMap ℂ A)) :
    letI := dual (R := ℂ) (H := A) (M := M)
    ∃ c : ℂ, F = c • haarGramMatrix h b.dualBasis := by
  let _ := dual (R := ℂ) (H := A) (M := M)
  let _ := convolutionModule (R := ℂ) (C := A) (M := Module.Dual ℂ M)
  have : IsSimpleOrder (Subcomodule ℂ A (Module.Dual ℂ M)) :=
    Subcomodule.isSimpleOrder_dual_iff_of_starCoalgebra.mpr inferInstance
  have : IsSimpleModule (WithConv (A →ₗ[ℂ] ℂ)) (Module.Dual ℂ M) :=
    isSimpleModule_convolution_iff.mpr inferInstance
  set G := haarGramMatrix h b.dualBasis
  have hG : G.PosDef := posDef_haarGramMatrix hpos b.dualBasis
  have hGdet : IsUnit G.det := (isUnit_iff_isUnit_det G).mp hG.isUnit
  set w := coefficientMatrix (C := A) b.dualBasis
  set f := algebraMap ℂ A
  have hinter : w * (G⁻¹ * F).map f = (G⁻¹ * F).map f * w := by
    have hwG := mul_inv_map_mul_conjTranspose
      (coefficientMatrix_mul_map_antipode b.dualBasis)
      (conjTranspose_coefficientMatrix_mul_haarGramMatrix_mul hh b.dualBasis)
    calc
      w * (G⁻¹ * F).map f = w * (G⁻¹.map f * (wᴴ * F.map f * w)) := by rw [hinv, Matrix.map_mul]
      _ = (w * G⁻¹.map f * wᴴ) * F.map f * w := by simp only [Matrix.mul_assoc]
      _ = (G⁻¹ * F).map f * w := by rw [hwG, ← Matrix.map_mul]
  let T : Hom ℂ A (Module.Dual ℂ M) (Module.Dual ℂ M) :=
    { toLinearMap := Matrix.toLin b.dualBasis b.dualBasis (G⁻¹ * F)
      map_coact := (b.dualBasis.map_coact_iff_coefficientMatrix b.dualBasis _).mpr
        (by rw [LinearMap.toMatrix_toLin]; exact hinter) }
  set c : ℂ := endAlgEquivSelfOfIsSimpleModule (k := ℂ) T.toConvolutionLinearMap
  have hGF : G⁻¹ * F = c • 1 := by
    have hT : Matrix.toLin b.dualBasis b.dualBasis (G⁻¹ * F) = c • LinearMap.id :=
      LinearMap.ext fun φ ↦ by
        change T φ = c • φ
        rw [← Hom.toConvolutionLinearMap_apply, ← endAlgEquivSelfOfIsSimpleModule_smul (k := ℂ)]
    rw [← LinearMap.toMatrix_toLin b.dualBasis b.dualBasis (G⁻¹ * F), hT, map_smul,
      LinearMap.toMatrix_id]
  refine ⟨c, ?_⟩
  calc
    F = G * (G⁻¹ * F) := by rw [← Matrix.mul_assoc, mul_nonsing_inv G hGdet, Matrix.one_mul]
    _ = c • G := by rw [hGF, Matrix.mul_smul, Matrix.mul_one]

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
  let _ := dual (R := ℂ) (H := A) (M := M)
  have : Nontrivial M := by
    let _ := convolutionModule (R := ℂ) (C := A) (M := M)
    have := isSimpleModule_convolution_iff.mpr (inferInstance : IsSimpleOrder (Subcomodule ℂ A M))
    exact IsSimpleModule.nontrivial (WithConv (A →ₗ[ℂ] ℂ)) M
  have : Nonempty ι := b.index_nonempty
  set G := haarGramMatrix h b.dualBasis
  have hG : G.PosDef := posDef_haarGramMatrix hpos b.dualBasis
  obtain ⟨c, hFc⟩ := exists_eq_smul_haarGramMatrix hh hpos b hinv
  -- Positivity of `Tr F` and `Tr G` forces `c` to be a positive real `r` with `r² = Tr G⁻¹ / Tr G`.
  obtain ⟨hGre, hGeq⟩ := pos_re_and_eq_ofReal hG.trace_pos
  obtain ⟨hFre, hFeq⟩ := pos_re_and_eq_ofReal hF.trace_pos
  obtain ⟨_, hGinvEq⟩ := pos_re_and_eq_ofReal hG.inv.trace_pos
  set r : ℝ := (F.trace).re / (G.trace).re
  have hr : 0 < r := div_pos hFre hGre
  have hcr : c = (r : ℂ) := by
    have htrc : F.trace = c * G.trace := by rw [hFc, trace_smul, smul_eq_mul]
    apply mul_right_cancel₀ (by rw [← hGeq]; exact_mod_cast hGre.ne' : G.trace ≠ 0)
    rw [← htrc, ← hFeq, ← hGeq]
    exact_mod_cast (div_mul_cancel₀ (F.trace).re hGre.ne').symm
  have hFr : F = r • G := by
    ext i j
    simp [hFc, hcr, G, Complex.real_smul]
  have hrsq : r ^ 2 = (G⁻¹.trace).re / (G.trace).re := by
    have htr' := htr
    rw [hFr, inv_real_smul hr.ne', trace_smul, trace_smul, ← hGeq, ← hGinvEq,
      Complex.real_smul, Complex.real_smul] at htr'
    have hre : r * (G.trace).re = r⁻¹ * (G⁻¹.trace).re := by exact_mod_cast htr'
    rw [eq_div_iff hGre.ne']
    calc
      r ^ 2 * (G.trace).re = r * (r * (G.trace).re) := by ring
      _ = r * (r⁻¹ * (G⁻¹.trace).re) := by rw [hre]
      _ = (G⁻¹.trace).re := by rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  rw [show unitarizingMatrix h b = Real.sqrt ((G⁻¹.trace).re / (G.trace).re) • G from rfl,
    hFr, ← hrsq, Real.sqrt_sq hr.le]

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
