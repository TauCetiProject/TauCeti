/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Conjugate
public import TauCeti.Algebra.Coalgebra.Comodule.Schur
public import TauCeti.QuantumGroups.CompactType.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Weighted Schur orthogonality for complex Hopf star algebras

Let `A` be a complex Hopf star algebra and `h : A → ℂ` a normalized two-sided invariant integral.
Right invariance averages `star (u i j) * v k l` into an intertwiner between the comodules of `u`
and `v`; left invariance averages `u i j * star (v k l)` similarly. Consequently, coefficients of
non-isomorphic simple comodules with unitary coefficient matrices are orthogonal under `h`.

For a single simple comodule with unitary coefficient matrix `u`, any positive definite matrix
`Ft` intertwining the conjugate corepresentation `u.map star` (`(u.map star)ᴴ * Ft * (u.map star)
= Ft`) determines both orthogonality relations:
* `h (star (u i j) * u k l) = δ j l * Ft⁻¹ i k / trace Ft⁻¹`,
* `h (u i j * star (u k l)) = δ i k * Ft j l / trace Ft`,
and implements the squared antipode via its transpose `F = Ftᵀ`: `S²(u) = F * u * F⁻¹`.
Rescaling `Ft` so that `trace Ft = trace Ft⁻¹` makes `Ft` unique. When `h` is an
`AlgebraicHaar`, the Haar Gram matrix of the conjugate comodule `u.map star` provides such a
positive definite intertwiner, yielding weighted Schur orthogonality.

## Main declarations

* `TauCeti.apply_star_mul_eq_zero_of_isRightInvariantIntegral` and
  `TauCeti.apply_mul_star_eq_zero_of_isLeftInvariantIntegral`: orthogonality of non-isomorphic
  simple comodules under one-sided invariant integrals.
* `TauCeti.map_antipode_antipode_coefficientMatrix_eq`: `S²(u) = Ftᵀ * u * (Ftᵀ)⁻¹` from any
  positive definite unitarizer `Ft` of `u.map star`.
* `TauCeti.apply_star_mul_eq_of_posDef_unitarizer` and
  `TauCeti.apply_mul_star_eq_of_posDef_unitarizer`: weighted Schur orthogonality from a normalized
  two-sided invariant integral and any positive definite unitarizer of `u.map star` (without
  assuming positivity of `h`).
* `TauCeti.AlgebraicHaar.schurWeight`: the unique normalized positive definite weight matrix `Ft`
  for a simple unitary basis.
* `TauCeti.schur_orthogonality` and `TauCeti.Comodule.IsUnitary.schur_orthogonality`: weighted
  Schur orthogonality with uniqueness of the normalized weight matrix.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Section 3.2.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*,
  SMF, 2013, Theorem 1.4.2 and Section 1.7.
-/

public noncomputable section

open Module Matrix
open scoped ComplexOrder

namespace TauCeti

section Helpers

private theorem transpose_map_algebraMap_mul {R A ι : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] [Fintype ι] (P : Matrix ι ι R) (X : Matrix ι ι A) :
    (P.map (algebraMap R A) * X)ᵀ = Xᵀ * Pᵀ.map (algebraMap R A) := by
  ext i j
  simp only [transpose_apply, Matrix.mul_apply, Matrix.map_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  exact Algebra.commutes (P j k) (X k i)

private theorem transpose_mul_map_algebraMap {R A ι : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] [Fintype ι] (X : Matrix ι ι A) (P : Matrix ι ι R) :
    (X * P.map (algebraMap R A))ᵀ = Pᵀ.map (algebraMap R A) * Xᵀ := by
  ext i j
  simp only [transpose_apply, Matrix.mul_apply, Matrix.map_apply]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  exact (Algebra.commutes (P k i) (X j k)).symm

private theorem complex_eq_ofReal_of_pos {z : ℂ} (hz : 0 < z) :
    z = (z.re : ℂ) ∧ 0 < z.re := by
  rw [Complex.lt_def] at hz
  refine ⟨Complex.ext rfl ?_, hz.1⟩
  simpa using hz.2.symm

end Helpers

section PosDefTrace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Rescale a positive definite matrix `G` by a positive real scalar so that
`trace G = trace G⁻¹`. -/
def normalizePosDefTrace (G : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ((Real.sqrt (G⁻¹.trace.re / G.trace.re) : ℝ) : ℂ) • G

/-- Trace-normalizing a positive definite matrix preserves positive definiteness. -/
theorem posDef_normalizePosDefTrace [Nonempty ι] {G : Matrix ι ι ℂ} (hG : G.PosDef) :
    (normalizePosDefTrace G).PosDef := by
  have htr : 0 < G.trace.re := (complex_eq_ofReal_of_pos hG.trace_pos).2
  have htrInv : 0 < G⁻¹.trace.re := (complex_eq_ofReal_of_pos hG.inv.trace_pos).2
  have ht : (0 : ℂ) < ((Real.sqrt (G⁻¹.trace.re / G.trace.re) : ℝ) : ℂ) := by
    rw [Complex.lt_def]
    exact ⟨Real.sqrt_pos.mpr (div_pos htrInv htr), rfl⟩
  exact hG.smul ht

/-- The trace-normalized matrix satisfies `trace (normalizePosDefTrace G) =
trace (normalizePosDefTrace G)⁻¹`. -/
theorem trace_normalizePosDefTrace_eq_trace_inv [Nonempty ι] {G : Matrix ι ι ℂ} (hG : G.PosDef) :
    (normalizePosDefTrace G).trace = (normalizePosDefTrace G)⁻¹.trace := by
  obtain ⟨hGeq, hGpos⟩ := complex_eq_ofReal_of_pos hG.trace_pos
  obtain ⟨hIeq, hIpos⟩ := complex_eq_ofReal_of_pos hG.inv.trace_pos
  set t : ℝ := Real.sqrt (G⁻¹.trace.re / G.trace.re)
  have htpos : 0 < t := Real.sqrt_pos.mpr (div_pos hIpos hGpos)
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr htpos.ne'
  have hdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
  have hdef : normalizePosDefTrace G = (t : ℂ) • G := rfl
  have hinv : (normalizePosDefTrace G)⁻¹ = (t : ℂ)⁻¹ • G⁻¹ := by
    rw [hdef]
    simpa [Units.smul_def] using Matrix.inv_smul' G (Units.mk0 (t : ℂ) htc) hdet
  rw [hinv, hdef, Matrix.trace_smul, Matrix.trace_smul,
    smul_eq_mul, smul_eq_mul, hGeq, hIeq, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul]
  congr 1
  have hsq : t ^ 2 = G⁻¹.trace.re / G.trace.re := Real.sq_sqrt (div_pos hIpos hGpos).le
  field_simp [htpos.ne']
  rw [hsq, div_mul_cancel₀ _ hGpos.ne']

/-- Two positive definite complex matrices satisfying `trace M = trace M⁻¹` that are scalar
multiples of each other are equal. -/
theorem eq_of_smul_posDef_trace_eq [Nonempty ι] {Ft₁ Ft₂ : Matrix ι ι ℂ}
    (h₁ : Ft₁.PosDef) (h₂ : Ft₂.PosDef)
    (htr₁ : Ft₁.trace = Ft₁⁻¹.trace) (htr₂ : Ft₂.trace = Ft₂⁻¹.trace)
    {c : ℂ} (hsmul : Ft₁ = c • Ft₂) : Ft₁ = Ft₂ := by
  obtain ⟨h1eq, h1pos⟩ := complex_eq_ofReal_of_pos h₁.trace_pos
  obtain ⟨h2eq, h2pos⟩ := complex_eq_ofReal_of_pos h₂.trace_pos
  have htr : Ft₁.trace = c * Ft₂.trace := by
    rw [hsmul, Matrix.trace_smul, smul_eq_mul]
  have h2ne : Ft₂.trace ≠ 0 := by rw [h2eq]; exact Complex.ofReal_ne_zero.mpr h2pos.ne'
  have hc_eq : c = ((Ft₁.trace.re / Ft₂.trace.re : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, ← h1eq, ← h2eq]
    exact eq_div_of_mul_eq h2ne htr.symm
  have hcre : 0 < c.re := by rw [hc_eq, Complex.ofReal_re]; exact div_pos h1pos h2pos
  have hcim : c.im = 0 := by rw [hc_eq, Complex.ofReal_im]
  have hcne : c ≠ 0 := fun h ↦ by simp [h] at hcre
  have hdet₂ : IsUnit Ft₂.det := (Matrix.isUnit_iff_isUnit_det Ft₂).mp h₂.isUnit
  have hinv : Ft₁⁻¹ = c⁻¹ • Ft₂⁻¹ := by
    rw [hsmul]
    simpa [Units.smul_def] using Matrix.inv_smul' Ft₂ (Units.mk0 c hcne) hdet₂
  have hcc : c * Ft₂.trace = c⁻¹ * Ft₂.trace := by
    calc c * Ft₂.trace = Ft₁.trace := htr.symm
      _ = Ft₁⁻¹.trace := htr₁
      _ = c⁻¹ * Ft₂⁻¹.trace := by rw [hinv, Matrix.trace_smul, smul_eq_mul]
      _ = c⁻¹ * Ft₂.trace := by rw [← htr₂]
  have hcinv : c = c⁻¹ := mul_right_cancel₀ h2ne hcc
  have hcsq : c * c = 1 := by
    calc c * c = c * c⁻¹ := by nth_rw 2 [hcinv]
      _ = 1 := mul_inv_cancel₀ hcne
  have hre_sq : c.re * c.re = 1 := by
    have := congrArg Complex.re hcsq
    simpa [Complex.mul_re, hcim] using this
  have hcre1 : c.re = 1 := by nlinarith
  have hc1 : c = 1 := Complex.ext hcre1 hcim
  rw [hsmul, hc1, one_smul]

end PosDefTrace

section InvariantAveraging

variable {A M N ι κ : Type*} [Ring A] [Bialgebra ℂ A] [StarRing A] [StarModule ℂ A]
  [StarCoalgebra ℂ A] [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
  [AddCommGroup N] [Module ℂ N] [Comodule ℂ A N]

/-- Right invariance averages `star (u i p) * v k q` into a matrix invariant under
`E ↦ uᴴ * E * v`. -/
private theorem conjTranspose_mul_rightAvg_mul [Fintype ι] [Fintype κ] {h : A →ₗ[ℂ] ℂ}
    (hh : h.IsRightInvariantIntegral) (b : Basis ι ℂ M) (c : Basis κ ℂ N) (i : ι) (k : κ) :
    let u := Comodule.coefficientMatrix (C := A) b
    let v := Comodule.coefficientMatrix (C := A) c
    let E : Matrix ι κ ℂ := Matrix.of fun p q ↦ h (star (u i p) * v k q)
    uᴴ * E.map (algebraMap ℂ A) * v = E.map (algebraMap ℂ A) := by
  intro u v E
  let ru (p q : ι) : Coalgebra.Repr ℂ (u p q) ι :=
    ⟨Finset.univ, fun r ↦ u p r, fun r ↦ u r q,
      (Comodule.comul_coefficientMatrix_eq_sum b p q).symm⟩
  let rv (p q : κ) : Coalgebra.Repr ℂ (v p q) κ :=
    ⟨Finset.univ, fun r ↦ v p r, fun r ↦ v r q,
      (Comodule.comul_coefficientMatrix_eq_sum c p q).symm⟩
  ext j l
  calc (uᴴ * E.map (algebraMap ℂ A) * v) j l
      = ∑ p, ∑ q, h (star (u i p) * v k q) • (star (u p j) * v q l) := by
        simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply, E, Matrix.of_apply,
          Finset.sum_mul, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one]
        rw [Finset.sum_comm]
    _ = h (star (u i j) * v k l) • (1 : A) := by
        simpa [ru, rv] using hh.sum_sum_mul (ru i j).star (rv k l)
    _ = (E.map (algebraMap ℂ A)) j l := by
        simp [E, Algebra.algebraMap_eq_smul_one]

/-- Left invariance averages `u p j * star (v q l)` into a matrix invariant under
`E ↦ u * E * vᴴ`. -/
private theorem mul_leftAvg_mul_conjTranspose [Fintype ι] [Fintype κ] {h : A →ₗ[ℂ] ℂ}
    (hh : h.IsLeftInvariantIntegral) (b : Basis ι ℂ M) (c : Basis κ ℂ N) (j : ι) (l : κ) :
    let u := Comodule.coefficientMatrix (C := A) b
    let v := Comodule.coefficientMatrix (C := A) c
    let E : Matrix ι κ ℂ := Matrix.of fun p q ↦ h (u p j * star (v q l))
    u * E.map (algebraMap ℂ A) * vᴴ = E.map (algebraMap ℂ A) := by
  intro u v E
  let ru (p q : ι) : Coalgebra.Repr ℂ (u p q) ι :=
    ⟨Finset.univ, fun r ↦ u p r, fun r ↦ u r q,
      (Comodule.comul_coefficientMatrix_eq_sum b p q).symm⟩
  let rv (p q : κ) : Coalgebra.Repr ℂ (v p q) κ :=
    ⟨Finset.univ, fun r ↦ v p r, fun r ↦ v r q,
      (Comodule.comul_coefficientMatrix_eq_sum c p q).symm⟩
  ext i k
  calc (u * E.map (algebraMap ℂ A) * vᴴ) i k
      = ∑ p, ∑ q, h (u p j * star (v q l)) • (u i p * star (v k q)) := by
        simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply, E, Matrix.of_apply,
          Finset.sum_mul, Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one]
        rw [Finset.sum_comm]
    _ = h (u i j * star (v k l)) • (1 : A) := by
        simpa [ru, rv] using hh.sum_sum_mul (ru i j) (rv k l).star
    _ = (E.map (algebraMap ℂ A)) i k := by
        simp [E, Algebra.algebraMap_eq_smul_one]

/-- **Schur orthogonality between non-isomorphic simple comodules (right invariant form).**
If `h` is right invariant and `u` is unitary, then `h (star (u i j) * v k l) = 0` whenever `M`
and `N` are simple comodules with distinct coefficient spaces. -/
theorem apply_star_mul_eq_zero_of_isRightInvariantIntegral [Fintype ι] [DecidableEq ι] [Finite κ]
    [IsSimpleOrder (Subcomodule ℂ A M)] [IsSimpleOrder (Subcomodule ℂ A N)]
    (hne : Comodule.matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M) ≠
      Comodule.matrixCoefficientSubmodule (R := ℂ) (C := A) (M := N))
    {h : A →ₗ[ℂ] ℂ} (hh : h.IsRightInvariantIntegral)
    (b : Basis ι ℂ M) (c : Basis κ ℂ N)
    (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    (i j : ι) (k l : κ) :
    h (star (Comodule.coefficientMatrix (C := A) b i j) *
      Comodule.coefficientMatrix (C := A) c k l) = 0 := by
  have : Fintype κ := Fintype.ofFinite κ
  set u := Comodule.coefficientMatrix (C := A) b
  set v := Comodule.coefficientMatrix (C := A) c
  let E : Matrix ι κ ℂ := Matrix.of fun p q ↦ h (star (u i p) * v k q)
  have havg := conjTranspose_mul_rightAvg_mul hh b c i k
  have hu2 : u * uᴴ = 1 := by simpa [Matrix.star_eq_conjTranspose] using hu.2
  have hinter : u * E.map (algebraMap ℂ A) = E.map (algebraMap ℂ A) * v := by
    calc u * E.map (algebraMap ℂ A)
        = u * (uᴴ * E.map (algebraMap ℂ A) * v) := by rw [havg]
      _ = (u * uᴴ) * E.map (algebraMap ℂ A) * v := by simp only [Matrix.mul_assoc]
      _ = E.map (algebraMap ℂ A) * v := by rw [hu2, Matrix.one_mul]
  have hE0 : E = 0 := c.eq_zero_of_coefficientMatrix_mul_eq b
    (Comodule.Hom.eq_zero_of_matrixCoefficientSubmodule_ne hne.symm) hinter
  exact congrFun (congrFun hE0 j) l

/-- **Schur orthogonality between non-isomorphic simple comodules (left invariant form).**
If `h` is left invariant and `v` is unitary, then `h (u i j * star (v k l)) = 0` whenever `M`
and `N` are simple comodules with distinct coefficient spaces. -/
theorem apply_mul_star_eq_zero_of_isLeftInvariantIntegral [Finite ι] [Fintype κ] [DecidableEq κ]
    [IsSimpleOrder (Subcomodule ℂ A M)] [IsSimpleOrder (Subcomodule ℂ A N)]
    (hne : Comodule.matrixCoefficientSubmodule (R := ℂ) (C := A) (M := M) ≠
      Comodule.matrixCoefficientSubmodule (R := ℂ) (C := A) (M := N))
    {h : A →ₗ[ℂ] ℂ} (hh : h.IsLeftInvariantIntegral)
    (b : Basis ι ℂ M) (c : Basis κ ℂ N)
    (hv : Comodule.coefficientMatrix (C := A) c ∈ unitary (Matrix κ κ A))
    (i j : ι) (k l : κ) :
    h (Comodule.coefficientMatrix (C := A) b i j *
      star (Comodule.coefficientMatrix (C := A) c k l)) = 0 := by
  have : Fintype ι := Fintype.ofFinite ι
  set u := Comodule.coefficientMatrix (C := A) b
  set v := Comodule.coefficientMatrix (C := A) c
  let E : Matrix ι κ ℂ := Matrix.of fun p q ↦ h (u p j * star (v q l))
  have havg := mul_leftAvg_mul_conjTranspose hh b c j l
  have hv1 : vᴴ * v = 1 := by simpa [Matrix.star_eq_conjTranspose] using hv.1
  have hinter : u * E.map (algebraMap ℂ A) = E.map (algebraMap ℂ A) * v := by
    calc u * E.map (algebraMap ℂ A)
        = u * E.map (algebraMap ℂ A) * (vᴴ * v) := by rw [hv1, Matrix.mul_one]
      _ = (u * E.map (algebraMap ℂ A) * vᴴ) * v := by simp only [Matrix.mul_assoc]
      _ = E.map (algebraMap ℂ A) * v := by rw [havg]
  have hE0 : E = 0 := c.eq_zero_of_coefficientMatrix_mul_eq b
    (Comodule.Hom.eq_zero_of_matrixCoefficientSubmodule_ne hne.symm) hinter
  exact congrFun (congrFun hE0 i) k

end InvariantAveraging

section UnifiedOrthogonality

variable {A M ι : Type*} [Ring A] [HopfAlgebra ℂ A] [StarRing A] [StarModule ℂ A]
  [StarCoalgebra ℂ A] [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
  [Fintype ι] [DecidableEq ι]

/-- A positive definite unitarizer `Ft` of `u.map star` satisfies
`Ft⁻¹ * (u.map star)ᴴ * Ft = (S² u)ᵀ`. -/
private theorem inv_mul_conjTranspose_map_star_mul (b : Basis ι ℂ M)
    (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {Ft : Matrix ι ι ℂ} (hFt : Ft.PosDef)
    (hinv : ((Comodule.coefficientMatrix (C := A) b).map star)ᴴ *
      Ft.map (algebraMap ℂ A) * (Comodule.coefficientMatrix (C := A) b).map star =
      Ft.map (algebraMap ℂ A)) :
    Ft⁻¹.map (algebraMap ℂ A) * ((Comodule.coefficientMatrix (C := A) b).map star)ᴴ *
      Ft.map (algebraMap ℂ A) =
      ((Comodule.coefficientMatrix (C := A) b).map
        (fun a ↦ HopfAlgebra.antipode ℂ (HopfAlgebra.antipode ℂ a)))ᵀ := by
  set f := algebraMap ℂ A
  set u := Comodule.coefficientMatrix (C := A) b
  set ubar := u.map star
  set w := (u.map (fun a ↦ HopfAlgebra.antipode ℂ (HopfAlgebra.antipode ℂ a)))ᵀ
  have hdet : IsUnit Ft.det := (Matrix.isUnit_iff_isUnit_det Ft).mp hFt.isUnit
  have hFInvF : Ft⁻¹.map f * Ft.map f = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul Ft hdet, Matrix.map_one _ (map_zero f) (map_one f)]
  have huw : ubar * w = 1 :=
    Comodule.map_star_coefficientMatrix_mul_transpose_antipode_antipode b hu
  calc Ft⁻¹.map f * ubarᴴ * Ft.map f
      = Ft⁻¹.map f * ubarᴴ * Ft.map f * (ubar * w) := by rw [huw, Matrix.mul_one]
    _ = Ft⁻¹.map f * (ubarᴴ * Ft.map f * ubar) * w := by simp only [Matrix.mul_assoc]
    _ = (Ft⁻¹.map f * Ft.map f) * w := by rw [hinv, Matrix.mul_assoc]
    _ = w := by rw [hFInvF, Matrix.one_mul]

/-- Any positive definite unitarizer `Ft` of the conjugate corepresentation `u.map star`
implements the squared antipode on `u` via its transpose `Ftᵀ`:
`S²(u) = Ftᵀ * u * (Ftᵀ)⁻¹`. -/
theorem map_antipode_antipode_coefficientMatrix_eq (b : Basis ι ℂ M)
    (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {Ft : Matrix ι ι ℂ} (hFt : Ft.PosDef)
    (hinv : ((Comodule.coefficientMatrix (C := A) b).map star)ᴴ *
      Ft.map (algebraMap ℂ A) * (Comodule.coefficientMatrix (C := A) b).map star =
      Ft.map (algebraMap ℂ A)) :
    (Comodule.coefficientMatrix (C := A) b).map
      (fun a ↦ HopfAlgebra.antipode ℂ (HopfAlgebra.antipode ℂ a)) =
      Ftᵀ.map (algebraMap ℂ A) * Comodule.coefficientMatrix (C := A) b *
        (Ftᵀ)⁻¹.map (algebraMap ℂ A) := by
  have hw := inv_mul_conjTranspose_map_star_mul b hu hFt hinv
  have hubarT : ((Comodule.coefficientMatrix (C := A) b).map star)ᴴᵀ =
      Comodule.coefficientMatrix (C := A) b := by
    ext i j
    simp [conjTranspose_apply]
  have htrans := congrArg Matrix.transpose hw
  rw [transpose_mul_map_algebraMap, transpose_map_algebraMap_mul, hubarT,
    Matrix.transpose_nonsing_inv, ← Matrix.mul_assoc] at htrans
  simpa using htrans.symm

variable [IsSimpleOrder (Subcomodule ℂ A M)]

/-- Right and left invariance factor `h (star (u i j) * u k l)` into `δ j l * C i k`, where `C`
has trace `1` and satisfies `ubar * C * ubarᴴ = C`. -/
private theorem exists_star_mul_factor {h : A →ₗ[ℂ] ℂ}
    (h1 : h 1 = 1) (hL : h.IsLeftInvariantIntegral) (hR : h.IsRightInvariantIntegral)
    (b : Basis ι ℂ M) (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ∃ C : Matrix ι ι ℂ, C.trace = 1 ∧
      (Comodule.coefficientMatrix (C := A) b).map star * C.map (algebraMap ℂ A) *
        ((Comodule.coefficientMatrix (C := A) b).map star)ᴴ = C.map (algebraMap ℂ A) ∧
      ∀ i j k l, h (star (Comodule.coefficientMatrix (C := A) b i j) *
        Comodule.coefficientMatrix (C := A) b k l) = if j = l then C i k else 0 := by
  set f := algebraMap ℂ A
  set u := Comodule.coefficientMatrix (C := A) b
  set ubar := u.map star
  have : Nontrivial M := Comodule.nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
  obtain ⟨j₀⟩ := b.index_nonempty
  have hfactor (p r : ι) : ∃ c : ℂ, ∀ q s, h (star (u p q) * u r s) = if q = s then c else 0 := by
    let E : Matrix ι ι ℂ := Matrix.of fun q s ↦ h (star (u p q) * u r s)
    have havg := conjTranspose_mul_rightAvg_mul hR b b p r
    have hu2 : u * uᴴ = 1 := by simpa [Matrix.star_eq_conjTranspose] using hu.2
    have hcomm : u * E.map f = E.map f * u := by
      calc u * E.map f = u * (uᴴ * E.map f * u) := by rw [havg]
        _ = (u * uᴴ) * E.map f * u := by simp only [Matrix.mul_assoc]
        _ = E.map f * u := by rw [hu2, Matrix.one_mul]
    obtain ⟨c, hc⟩ := b.exists_eq_smul_one_of_coefficientMatrix_mul_eq hcomm
    exact ⟨c, fun q s ↦ by simpa [E, Matrix.one_apply] using congrFun (congrFun hc q) s⟩
  let C : Matrix ι ι ℂ := Matrix.of fun p r ↦ h (star (u p j₀) * u r j₀)
  refine ⟨C, ?_, ?_, fun p q r s ↦ ?_⟩
  · have hu1 : (uᴴ * u) j₀ j₀ = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using congrFun (congrFun hu.1 j₀) j₀
    calc C.trace = ∑ p, h (star (u p j₀) * u p j₀) := rfl
      _ = h (∑ p, star (u p j₀) * u p j₀) := (map_sum h _ _).symm
      _ = h ((uᴴ * u) j₀ j₀) := by simp [Matrix.mul_apply, conjTranspose_apply]
      _ = 1 := by rw [hu1, h1]
  · let ru (p q : ι) : Coalgebra.Repr ℂ (u p q) ι :=
      ⟨Finset.univ, fun r ↦ u p r, fun r ↦ u r q,
        (Comodule.comul_coefficientMatrix_eq_sum b p q).symm⟩
    ext p r
    calc (ubar * C.map f * ubarᴴ) p r
        = ∑ a, ∑ d, C a d • (star (u p a) * u r d) := by
          simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply, ubar, f,
            star_star, Finset.sum_mul, Algebra.algebraMap_eq_smul_one, mul_smul_comm,
            smul_mul_assoc, mul_one]
          rw [Finset.sum_comm]
      _ = h (star (u p j₀) * u r j₀) • (1 : A) := by
          simpa [ru, C] using hL.sum_sum_mul (ru p j₀).star (ru r j₀)
      _ = (C.map f) p r := by simp [C, f, Algebra.algebraMap_eq_smul_one]
  · obtain ⟨c, hc⟩ := hfactor p r
    have hcj : C p r = c := by simpa [C] using hc j₀ j₀
    rw [hcj]
    exact hc q s

/-- Left and right invariance factor `h (u i j * star (u k l))` into `δ i k * D j l`, where `D`
has trace `1` and satisfies `ubarᴴ * D * ubar = D`. -/
private theorem exists_mul_star_factor {h : A →ₗ[ℂ] ℂ}
    (h1 : h 1 = 1) (hL : h.IsLeftInvariantIntegral) (hR : h.IsRightInvariantIntegral)
    (b : Basis ι ℂ M) (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ∃ D : Matrix ι ι ℂ, D.trace = 1 ∧
      ((Comodule.coefficientMatrix (C := A) b).map star)ᴴ * D.map (algebraMap ℂ A) *
        (Comodule.coefficientMatrix (C := A) b).map star = D.map (algebraMap ℂ A) ∧
      ∀ i j k l, h (Comodule.coefficientMatrix (C := A) b i j *
        star (Comodule.coefficientMatrix (C := A) b k l)) = if i = k then D j l else 0 := by
  set f := algebraMap ℂ A
  set u := Comodule.coefficientMatrix (C := A) b
  set ubar := u.map star
  have : Nontrivial M := Comodule.nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
  obtain ⟨i₀⟩ := b.index_nonempty
  have hfactor (q s : ι) : ∃ d : ℂ, ∀ p r, h (u p q * star (u r s)) = if p = r then d else 0 := by
    let E : Matrix ι ι ℂ := Matrix.of fun p r ↦ h (u p q * star (u r s))
    have havg := mul_leftAvg_mul_conjTranspose hL b b q s
    have hu1 : uᴴ * u = 1 := by simpa [Matrix.star_eq_conjTranspose] using hu.1
    have hcomm : u * E.map f = E.map f * u := by
      calc u * E.map f = u * E.map f * (uᴴ * u) := by rw [hu1, Matrix.mul_one]
        _ = (u * E.map f * uᴴ) * u := by simp only [Matrix.mul_assoc]
        _ = E.map f * u := by rw [havg]
    obtain ⟨d, hd⟩ := b.exists_eq_smul_one_of_coefficientMatrix_mul_eq hcomm
    exact ⟨d, fun p r ↦ by simpa [E, Matrix.one_apply] using congrFun (congrFun hd p) r⟩
  let D : Matrix ι ι ℂ := Matrix.of fun q s ↦ h (u i₀ q * star (u i₀ s))
  refine ⟨D, ?_, ?_, fun p q r s ↦ ?_⟩
  · have hu2 : (u * uᴴ) i₀ i₀ = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using congrFun (congrFun hu.2 i₀) i₀
    calc D.trace = ∑ q, h (u i₀ q * star (u i₀ q)) := rfl
      _ = h (∑ q, u i₀ q * star (u i₀ q)) := (map_sum h _ _).symm
      _ = h ((u * uᴴ) i₀ i₀) := by simp [Matrix.mul_apply, conjTranspose_apply]
      _ = 1 := by rw [hu2, h1]
  · let ru (p q : ι) : Coalgebra.Repr ℂ (u p q) ι :=
      ⟨Finset.univ, fun r ↦ u p r, fun r ↦ u r q,
        (Comodule.comul_coefficientMatrix_eq_sum b p q).symm⟩
    ext q s
    calc (ubarᴴ * D.map f * ubar) q s
        = ∑ a, ∑ d, D a d • (u a q * star (u d s)) := by
          simp only [Matrix.mul_apply, Matrix.map_apply, conjTranspose_apply, ubar, f,
            star_star, Finset.sum_mul, Algebra.algebraMap_eq_smul_one, mul_smul_comm,
            smul_mul_assoc, mul_one]
          rw [Finset.sum_comm]
      _ = h (u i₀ q * star (u i₀ s)) • (1 : A) := by
          simpa [ru, D] using hR.sum_sum_mul (ru i₀ q) (ru i₀ s).star
      _ = (D.map f) q s := by simp [D, f, Algebra.algebraMap_eq_smul_one]
  · obtain ⟨d, hd⟩ := hfactor q s
    have hdi : D q s = d := by simpa [D] using hd i₀ i₀
    rw [hdi]
    exact hd p r

/-- **First weighted Schur orthogonality relation** for a normalized two-sided invariant integral
and any positive definite unitarizer `Ft` of the conjugate corepresentation `u.map star`. No
positivity hypothesis on `h` is required. -/
theorem apply_star_mul_eq_of_posDef_unitarizer {h : A →ₗ[ℂ] ℂ}
    (h1 : h 1 = 1) (hL : h.IsLeftInvariantIntegral) (hR : h.IsRightInvariantIntegral)
    (b : Basis ι ℂ M) (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {Ft : Matrix ι ι ℂ} (hFt : Ft.PosDef)
    (hinv : ((Comodule.coefficientMatrix (C := A) b).map star)ᴴ *
      Ft.map (algebraMap ℂ A) * (Comodule.coefficientMatrix (C := A) b).map star =
      Ft.map (algebraMap ℂ A)) (i j k l : ι) :
    h (star (Comodule.coefficientMatrix (C := A) b i j) *
      Comodule.coefficientMatrix (C := A) b k l) =
      if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0 := by
  set f := algebraMap ℂ A
  set u := Comodule.coefficientMatrix (C := A) b
  set ubar := u.map star
  obtain ⟨C, hCtr, hC_inv, hC_eq⟩ := exists_star_mul_factor h1 hL hR b hu
  have hcomm_ubar : ubar * (C * Ft).map f = (C * Ft).map f * ubar := by
    rw [Matrix.map_mul]
    calc ubar * (C.map f * Ft.map f)
        = ubar * C.map f * (ubarᴴ * Ft.map f * ubar) := by rw [hinv, Matrix.mul_assoc]
      _ = (ubar * C.map f * ubarᴴ) * Ft.map f * ubar := by simp only [Matrix.mul_assoc]
      _ = C.map f * Ft.map f * ubar := by rw [hC_inv]
  let _ : Comodule ℂ A (ι → ℂ) :=
    Comodule.matrixComodule ℂ ubar
      (Comodule.map_comul_map_star u (Comodule.coefficientMatrix_map_comul b))
      (Comodule.counit_basisFun_map_star u (Comodule.coefficientMatrix_counit_basisFun b))
  have : IsSimpleOrder (Subcomodule ℂ A (ι → ℂ)) :=
    Comodule.isSimpleOrder_matrixComodule_coefficientMatrix_map_star b
  have hcomm_basis : Comodule.coefficientMatrix (C := A) (Pi.basisFun ℂ ι) * (C * Ft).map f =
      (C * Ft).map f * Comodule.coefficientMatrix (C := A) (Pi.basisFun ℂ ι) := by
    simpa only [Comodule.coefficientMatrix_matrixComodule] using hcomm_ubar
  obtain ⟨c, hc⟩ :=
    (Pi.basisFun ℂ ι).exists_eq_smul_one_of_coefficientMatrix_mul_eq hcomm_basis
  have hdet : IsUnit Ft.det := (Matrix.isUnit_iff_isUnit_det Ft).mp hFt.isUnit
  have hC_smul : C = c • Ft⁻¹ := by
    calc C = (C * Ft) * Ft⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv Ft hdet, Matrix.mul_one]
      _ = (c • (1 : Matrix ι ι ℂ)) * Ft⁻¹ := by rw [hc]
      _ = c • Ft⁻¹ := by rw [Matrix.smul_mul, Matrix.one_mul]
  have hc_val : c = (Ft⁻¹.trace)⁻¹ := by
    have htr : c * Ft⁻¹.trace = 1 := by
      rw [← smul_eq_mul, ← Matrix.trace_smul, ← hC_smul, hCtr]
    exact eq_inv_of_mul_eq_one_left htr
  rw [hC_eq i j k l, hC_smul, hc_val]
  simp [Matrix.smul_apply, div_eq_inv_mul]

/-- **Second weighted Schur orthogonality relation** for a normalized two-sided invariant integral
and any positive definite unitarizer `Ft` of the conjugate corepresentation `u.map star`. No
positivity hypothesis on `h` is required. -/
theorem apply_mul_star_eq_of_posDef_unitarizer {h : A →ₗ[ℂ] ℂ}
    (h1 : h 1 = 1) (hL : h.IsLeftInvariantIntegral) (hR : h.IsRightInvariantIntegral)
    (b : Basis ι ℂ M) (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A))
    {Ft : Matrix ι ι ℂ} (hFt : Ft.PosDef)
    (hinv : ((Comodule.coefficientMatrix (C := A) b).map star)ᴴ *
      Ft.map (algebraMap ℂ A) * (Comodule.coefficientMatrix (C := A) b).map star =
      Ft.map (algebraMap ℂ A)) (i j k l : ι) :
    h (Comodule.coefficientMatrix (C := A) b i j *
      star (Comodule.coefficientMatrix (C := A) b k l)) =
      if i = k then Ft j l / Ft.trace else 0 := by
  set f := algebraMap ℂ A
  set u := Comodule.coefficientMatrix (C := A) b
  set ubar := u.map star
  obtain ⟨D, hDtr, hD_inv, hD_eq⟩ := exists_mul_star_factor h1 hL hR b hu
  have hdet : IsUnit Ft.det := (Matrix.isUnit_iff_isUnit_det Ft).mp hFt.isUnit
  have hFFInv : Ft.map f * Ft⁻¹.map f = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv Ft hdet, Matrix.map_one _ (map_zero f) (map_one f)]
  have hw := inv_mul_conjTranspose_map_star_mul b hu hFt hinv
  have huw := Comodule.map_star_coefficientMatrix_mul_transpose_antipode_antipode b hu
  have hcomm_ubar : ubar * (Ft⁻¹ * D).map f = (Ft⁻¹ * D).map f * ubar := by
    rw [Matrix.map_mul]
    calc ubar * (Ft⁻¹.map f * D.map f)
        = ubar * (Ft⁻¹.map f * (ubarᴴ * D.map f * ubar)) := by rw [hD_inv]
      _ = ubar * (Ft⁻¹.map f * ubarᴴ * (Ft.map f * Ft⁻¹.map f) * D.map f * ubar) := by
          rw [hFFInv, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = (ubar * (Ft⁻¹.map f * ubarᴴ * Ft.map f)) * (Ft⁻¹.map f * D.map f) * ubar := by
          simp only [Matrix.mul_assoc]
      _ = Ft⁻¹.map f * D.map f * ubar := by rw [hw, huw, Matrix.one_mul]
  let _ : Comodule ℂ A (ι → ℂ) :=
    Comodule.matrixComodule ℂ ubar
      (Comodule.map_comul_map_star u (Comodule.coefficientMatrix_map_comul b))
      (Comodule.counit_basisFun_map_star u (Comodule.coefficientMatrix_counit_basisFun b))
  have : IsSimpleOrder (Subcomodule ℂ A (ι → ℂ)) :=
    Comodule.isSimpleOrder_matrixComodule_coefficientMatrix_map_star b
  have hcomm_basis : Comodule.coefficientMatrix (C := A) (Pi.basisFun ℂ ι) * (Ft⁻¹ * D).map f =
      (Ft⁻¹ * D).map f * Comodule.coefficientMatrix (C := A) (Pi.basisFun ℂ ι) := by
    simpa only [Comodule.coefficientMatrix_matrixComodule] using hcomm_ubar
  obtain ⟨d, hd⟩ :=
    (Pi.basisFun ℂ ι).exists_eq_smul_one_of_coefficientMatrix_mul_eq hcomm_basis
  have hD_smul : D = d • Ft := by
    calc D = Ft * (Ft⁻¹ * D) := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv Ft hdet, Matrix.one_mul]
      _ = Ft * (d • (1 : Matrix ι ι ℂ)) := by rw [hd]
      _ = d • Ft := by rw [Matrix.mul_smul, Matrix.mul_one]
  have hd_val : d = (Ft.trace)⁻¹ := by
    have htr : d * Ft.trace = 1 := by
      rw [← smul_eq_mul, ← Matrix.trace_smul, ← hD_smul, hDtr]
    exact eq_inv_of_mul_eq_one_left htr
  rw [hD_eq i j k l, hD_smul, hd_val]
  simp [Matrix.smul_apply, div_eq_inv_mul]

end UnifiedOrthogonality

section WeightUniqueness

/-- The second Schur orthogonality relation together with positive definiteness and
`trace Ft = trace Ft⁻¹` uniquely determines `Ft`. -/
theorem schurWeight_unique_of_apply_mul_star {A M ι : Type*} [Semiring A] [Algebra ℂ A]
    [Coalgebra ℂ A] [Star A] [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
    [IsSimpleOrder (Subcomodule ℂ A M)] [Fintype ι] [DecidableEq ι]
    {h : A →ₗ[ℂ] ℂ} (b : Basis ι ℂ M)
    {Ft₁ Ft₂ : Matrix ι ι ℂ} (h₁ : Ft₁.PosDef) (h₂ : Ft₂.PosDef)
    (htr₁ : Ft₁.trace = Ft₁⁻¹.trace) (htr₂ : Ft₂.trace = Ft₂⁻¹.trace)
    (heq₁ : ∀ i j k l,
      h (Comodule.coefficientMatrix (C := A) b i j *
        star (Comodule.coefficientMatrix (C := A) b k l)) =
        if i = k then Ft₁ j l / Ft₁.trace else 0)
    (heq₂ : ∀ i j k l,
      h (Comodule.coefficientMatrix (C := A) b i j *
        star (Comodule.coefficientMatrix (C := A) b k l)) =
        if i = k then Ft₂ j l / Ft₂.trace else 0) :
    Ft₁ = Ft₂ := by
  have : Nontrivial M := Comodule.nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
  have : Nonempty ι := b.index_nonempty
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have h1ne : Ft₁.trace ≠ 0 := h₁.trace_pos.ne'
  have hsmul : Ft₁ = (Ft₁.trace / Ft₂.trace) • Ft₂ := by
    ext j l
    have hjl := (heq₁ i₀ j i₀ l).symm.trans (heq₂ i₀ j i₀ l)
    simp only [↓reduceIte] at hjl
    simp only [Matrix.smul_apply, smul_eq_mul]
    calc Ft₁ j l = (Ft₁ j l / Ft₁.trace) * Ft₁.trace := (div_mul_cancel₀ _ h1ne).symm
      _ = (Ft₂ j l / Ft₂.trace) * Ft₁.trace := by rw [hjl]
      _ = (Ft₁.trace / Ft₂.trace) * Ft₂ j l := by ring
  exact eq_of_smul_posDef_trace_eq h₁ h₂ htr₁ htr₂ hsmul

end WeightUniqueness

section AlgebraicHaarOrthogonality

variable {A : Type*} [Ring A] [HopfAlgebra ℂ A] [StarRing A] [StarModule ℂ A]
  [StarCoalgebra ℂ A]

/-- The canonical normalized positive definite Schur weight matrix `Ft` (whose transpose `F = Ftᵀ`
implements `S²`) associated with a simple comodule and a finite basis whose coefficient matrix is
unitary. It is obtained by trace-normalizing the Haar Gram matrix of the conjugate comodule
`u.map star`. -/
def AlgebraicHaar.schurWeight {M ι : Type*} [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
    [Fintype ι] [DecidableEq ι] (h : AlgebraicHaar A) (b : Basis ι ℂ M) : Matrix ι ι ℂ :=
  let _ : Comodule ℂ A (ι → ℂ) :=
    Comodule.matrixComodule ℂ ((Comodule.coefficientMatrix (C := A) b).map star)
      (Comodule.map_comul_map_star _ (Comodule.coefficientMatrix_map_comul b))
      (Comodule.counit_basisFun_map_star _ (Comodule.coefficientMatrix_counit_basisFun b))
  normalizePosDefTrace (Comodule.haarGramMatrix h.toLinearMap (Pi.basisFun ℂ ι))

/-- The Schur weight matrix is a positive definite unitarizer of the conjugate corepresentation
`u.map star`. -/
theorem AlgebraicHaar.conjTranspose_map_star_mul_schurWeight_mul {M ι : Type*}
    [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M] [Fintype ι] [DecidableEq ι]
    (h : AlgebraicHaar A) (b : Basis ι ℂ M) :
    ((Comodule.coefficientMatrix (C := A) b).map star)ᴴ *
      (h.schurWeight b).map (algebraMap ℂ A) * (Comodule.coefficientMatrix (C := A) b).map star =
      (h.schurWeight b).map (algebraMap ℂ A) := by
  let _ : Comodule ℂ A (ι → ℂ) :=
    Comodule.matrixComodule ℂ ((Comodule.coefficientMatrix (C := A) b).map star)
      (Comodule.map_comul_map_star _ (Comodule.coefficientMatrix_map_comul b))
      (Comodule.counit_basisFun_map_star _ (Comodule.coefficientMatrix_counit_basisFun b))
  set G := Comodule.haarGramMatrix h.toLinearMap (Pi.basisFun ℂ ι)
  have hG : ((Comodule.coefficientMatrix (C := A) b).map star)ᴴ * G.map (algebraMap ℂ A) *
      (Comodule.coefficientMatrix (C := A) b).map star = G.map (algebraMap ℂ A) := by
    simpa only [Comodule.coefficientMatrix_matrixComodule] using
      Comodule.conjTranspose_coefficientMatrix_mul_haarGramMatrix_mul
        h.isRightInvariantIntegral (Pi.basisFun ℂ ι)
  have hmap : (h.schurWeight b).map (algebraMap ℂ A) =
      ((Real.sqrt (G⁻¹.trace.re / G.trace.re) : ℝ) : ℂ) • G.map (algebraMap ℂ A) := by
    ext i j
    rw [Matrix.map_apply, AlgebraicHaar.schurWeight, normalizePosDefTrace,
      Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.smul_apply, Matrix.map_apply,
      Algebra.smul_def]
  rw [hmap, Matrix.mul_smul, Matrix.smul_mul, hG]

variable {M ι : Type*} [AddCommGroup M] [Module ℂ M] [Comodule ℂ A M]
  [IsSimpleOrder (Subcomodule ℂ A M)] [Fintype ι] [DecidableEq ι]

/-- The Schur weight matrix of a simple comodule is positive definite. -/
theorem AlgebraicHaar.posDef_schurWeight (h : AlgebraicHaar A) (b : Basis ι ℂ M) :
    (h.schurWeight b).PosDef := by
  have : Nontrivial M := Comodule.nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
  have : Nonempty ι := b.index_nonempty
  let _ : Comodule ℂ A (ι → ℂ) :=
    Comodule.matrixComodule ℂ ((Comodule.coefficientMatrix (C := A) b).map star)
      (Comodule.map_comul_map_star _ (Comodule.coefficientMatrix_map_comul b))
      (Comodule.counit_basisFun_map_star _ (Comodule.coefficientMatrix_counit_basisFun b))
  exact posDef_normalizePosDefTrace
    (Comodule.posDef_haarGramMatrix (fun _ ha ↦ h.apply_star_mul_self_pos ha) (Pi.basisFun ℂ ι))

/-- The Schur weight matrix is normalized so that `trace Ft = trace Ft⁻¹`. -/
theorem AlgebraicHaar.trace_schurWeight_eq_trace_inv (h : AlgebraicHaar A) (b : Basis ι ℂ M) :
    (h.schurWeight b).trace = (h.schurWeight b)⁻¹.trace := by
  have : Nontrivial M := Comodule.nontrivial_of_isSimpleOrder (R := ℂ) (C := A)
  have : Nonempty ι := b.index_nonempty
  let _ : Comodule ℂ A (ι → ℂ) :=
    Comodule.matrixComodule ℂ ((Comodule.coefficientMatrix (C := A) b).map star)
      (Comodule.map_comul_map_star _ (Comodule.coefficientMatrix_map_comul b))
      (Comodule.counit_basisFun_map_star _ (Comodule.coefficientMatrix_counit_basisFun b))
  exact trace_normalizePosDefTrace_eq_trace_inv
    (Comodule.posDef_haarGramMatrix (fun _ ha ↦ h.apply_star_mul_self_pos ha) (Pi.basisFun ℂ ι))

/-- First weighted Schur orthogonality identity in terms of `AlgebraicHaar.schurWeight`. -/
theorem AlgebraicHaar.apply_star_mul_coefficientMatrix (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) (i j k l : ι) :
    h (star (Comodule.coefficientMatrix (C := A) b i j) *
      Comodule.coefficientMatrix (C := A) b k l) =
      if j = l then (h.schurWeight b)⁻¹ i k / (h.schurWeight b)⁻¹.trace else 0 :=
  apply_star_mul_eq_of_posDef_unitarizer h.map_one' h.isLeftInvariantIntegral
    h.isRightInvariantIntegral b hu (h.posDef_schurWeight b)
    (h.conjTranspose_map_star_mul_schurWeight_mul b) i j k l

/-- Second weighted Schur orthogonality identity in terms of `AlgebraicHaar.schurWeight`. -/
theorem AlgebraicHaar.apply_coefficientMatrix_mul_star (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) (i j k l : ι) :
    h (Comodule.coefficientMatrix (C := A) b i j *
      star (Comodule.coefficientMatrix (C := A) b k l)) =
      if i = k then h.schurWeight b j l / (h.schurWeight b).trace else 0 :=
  apply_mul_star_eq_of_posDef_unitarizer h.map_one' h.isLeftInvariantIntegral
    h.isRightInvariantIntegral b hu (h.posDef_schurWeight b)
    (h.conjTranspose_map_star_mul_schurWeight_mul b) i j k l

/-- The transpose of `h.schurWeight b` implements `S²` on a simple unitary coefficient matrix:
`S²(u) = F * u * F⁻¹` where `F = (h.schurWeight b)ᵀ`. -/
theorem AlgebraicHaar.map_antipode_antipode_coefficientMatrix (h : AlgebraicHaar A)
    (b : Basis ι ℂ M) (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    (Comodule.coefficientMatrix (C := A) b).map
      (fun a ↦ HopfAlgebra.antipode ℂ (HopfAlgebra.antipode ℂ a)) =
      (h.schurWeight b)ᵀ.map (algebraMap ℂ A) * Comodule.coefficientMatrix (C := A) b *
        ((h.schurWeight b)ᵀ)⁻¹.map (algebraMap ℂ A) :=
  map_antipode_antipode_coefficientMatrix_eq b hu (h.posDef_schurWeight b)
    (h.conjTranspose_map_star_mul_schurWeight_mul b)

/-- **Weighted Schur orthogonality.** For a simple finite comodule over a complex Hopf star
algebra with an algebraic Haar integral `h` and a basis `b` whose coefficient matrix `u` is
unitary, there is a unique positive definite matrix `Ft` with `trace Ft = trace Ft⁻¹` such that
`h (star (u i j) * u k l) = δ j l * Ft⁻¹ i k / trace Ft⁻¹` and
`h (u i j * star (u k l)) = δ i k * Ft j l / trace Ft`. -/
theorem schur_orthogonality (h : AlgebraicHaar A) (b : Basis ι ℂ M)
    (hu : Comodule.coefficientMatrix (C := A) b ∈ unitary (Matrix ι ι A)) :
    ∃! Ft : Matrix ι ι ℂ, Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
      (∀ i j k l,
        h (star (Comodule.coefficientMatrix (C := A) b i j) *
          Comodule.coefficientMatrix (C := A) b k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (Comodule.coefficientMatrix (C := A) b i j *
          star (Comodule.coefficientMatrix (C := A) b k l)) =
          if i = k then Ft j l / Ft.trace else 0) :=
  ⟨h.schurWeight b,
    ⟨h.posDef_schurWeight b, h.trace_schurWeight_eq_trace_inv b,
      h.apply_star_mul_coefficientMatrix b hu, h.apply_coefficientMatrix_mul_star b hu⟩,
    fun _ hFt ↦ schurWeight_unique_of_apply_mul_star b hFt.1 (h.posDef_schurWeight b)
      hFt.2.1 (h.trace_schurWeight_eq_trace_inv b) hFt.2.2.2
      (h.apply_coefficientMatrix_mul_star b hu)⟩

/-- **Weighted Schur orthogonality for a unitary Hilbert comodule.** Specialization of
`TauCeti.schur_orthogonality` to an orthonormal basis of a simple finite-dimensional unitary
comodule. -/
theorem Comodule.IsUnitary.schur_orthogonality {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [Comodule ℂ A H]
    [IsSimpleOrder (Subcomodule ℂ A H)] (hH : Comodule.IsUnitary ℂ A H)
    (h : AlgebraicHaar A) (b : OrthonormalBasis ι ℂ H) :
    ∃! Ft : Matrix ι ι ℂ, Ft.PosDef ∧ Ft.trace = Ft⁻¹.trace ∧
      (∀ i j k l,
        h (star (Comodule.coefficientMatrix (C := A) b.toBasis i j) *
          Comodule.coefficientMatrix (C := A) b.toBasis k l) =
          if j = l then Ft⁻¹ i k / Ft⁻¹.trace else 0) ∧
      (∀ i j k l,
        h (Comodule.coefficientMatrix (C := A) b.toBasis i j *
          star (Comodule.coefficientMatrix (C := A) b.toBasis k l)) =
          if i = k then Ft j l / Ft.trace else 0) :=
  TauCeti.schur_orthogonality h b.toBasis (b.isUnitary_comodule_iff.mp hH)

end AlgebraicHaarOrthogonality

end TauCeti
