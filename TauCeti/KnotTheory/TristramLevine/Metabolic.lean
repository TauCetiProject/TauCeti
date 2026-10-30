/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.HermitianSignature.Metabolic
public import TauCeti.KnotTheory.TristramLevine.Alexander

/-!
# The signature obstruction for metabolic Seifert matrices

A Seifert matrix with a half-size zero block has zero Tristram--Levine signature whenever
its Hermitian form is nonsingular. The same conclusion holds after a change of basis.
On the unit circle, the exceptional parameters are precisely the Alexander roots and `1`;
the signature at `1` always vanishes.

The zero block records vanishing of the Seifert pairing on the first half of a basis,
the matrix normal form of a metabolizer. This is an algebraic result about a chosen matrix:
constructing Seifert forms of geometric knots and obtaining metabolizers from slice discs
are separate geometric results. In particular, no claim is made about the unaveraged
signature at Alexander roots.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, GTM 175 (1997), Chapter 8,
  Theorem 8.19 (vanishing of the signature of a slice knot away from Alexander roots).
* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory*
  (2005), Section 3.1 (metabolic forms and signature obstructions).

The proof combines `Matrix.IsHermitian.signature_eq_zero_of_fromBlocks_zero₁₁` with
`tristramLevineForm_congr` and `det_tristramLevineForm_ne_zero_iff`.
-/

public section

open TauCeti.KnotTheory LaurentPolynomial

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Seifert matrix with a half-size zero block has vanishing Tristram--Levine signature
at every parameter for which its Hermitian form is nonsingular. -/
theorem tristramLevineSignature_eq_zero_of_zero_block
    (V : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (hzero : V.toBlocks₁₁ = 0) (ω : ℂ)
    (hdet : (tristramLevineForm V ω).det ≠ 0) :
    tristramLevineSignature V ω = 0 := by
  let H := tristramLevineForm V ω
  have hH : H.IsHermitian := isHermitian_tristramLevineForm V ω
  have h₀ : H.toBlocks₁₁ = 0 := by
    calc
      H.toBlocks₁₁ = tristramLevineForm V.toBlocks₁₁ ω :=
        (tristramLevineForm_submatrix Sum.inl V ω).symm
      _ = 0 := by rw [hzero]; ext i j; simp
  have hparts := isHermitian_fromBlocks_iff.mp (H.fromBlocks_toBlocks.symm ▸ hH)
  have heq : H = Matrix.fromBlocks 0 H.toBlocks₁₂ H.toBlocks₁₂ᴴ H.toBlocks₂₂ := by
    rw [hparts.2.1, ← h₀, fromBlocks_toBlocks]
  have hs := Matrix.IsHermitian.signature_eq_zero_of_fromBlocks_zero₁₁ hparts.2.2.2
    (isUnit_iff_ne_zero.mpr (by rw [← heq]; exact hdet))
  rw [tristramLevineSignature_def]
  convert hs using 2

/-- If a change of basis puts the Seifert pairing in metabolic block form, its
Tristram--Levine signature vanishes away from the Alexander roots, including at `1`. -/
theorem tristramLevineSignature_eq_zero_of_congr_zero_block
    (V P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (hP : IsUnit P.det)
    (hzero : (P * V * Pᵀ).toBlocks₁₁ = 0) (ω : Circle)
    (hΔ : eval₂ Complex.ofRealHom (Circle.toUnits ω) (alexander V) ≠ 0) :
    tristramLevineSignature V ω = 0 := by
  by_cases hω : ω = 1
  · subst ω
    exact tristramLevineSignature_one V
  have hdet := (det_tristramLevineForm_ne_zero_iff V ω hω).mpr hΔ
  have hPC : IsUnit (P.map ((↑) : ℝ → ℂ)).det :=
    RingHom.map_det Complex.ofRealHom P ▸ hP.map Complex.ofRealHom
  have hdet' : (tristramLevineForm (P * V * Pᵀ) ω).det ≠ 0 := by
    rw [tristramLevineForm_congr, det_mul, det_mul, det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero (isUnit_iff_ne_zero.mp hPC) hdet)
      (by simpa only [star_ne_zero] using isUnit_iff_ne_zero.mp hPC)
  rw [← tristramLevineSignature_congr hP V ω]
  exact tristramLevineSignature_eq_zero_of_zero_block _ hzero ω hdet'

end Matrix
