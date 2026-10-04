/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.TristramLevine.Basic
public import TauCeti.LinearAlgebra.Matrix.Metabolic

/-!
# The Tristram--Levine signature of a metabolic Seifert matrix

A Seifert matrix of a slice knot is metabolic (`Matrix.IsMetabolic`): after a change of basis it
vanishes on a block of half its size. This file proves the algebraic half of the signature
obstruction to sliceness. If `V` is metabolic and the Tristram--Levine form
`(1 - ω) V + (1 - conj ω) Vᵀ` is nonsingular, then `σ_ω(V) = 0`. For a unit-circle parameter
`ω ≠ 1` the form is a nonzero multiple of `Vᵀ - ω V`, so it is nonsingular exactly when `ω` is
not a root of `det (Vᵀ - t V)`, the Alexander polynomial up to a unit. This is the hypothesis of
Lickorish's Theorem 8.19.

Two Seifert matrices `V` and `W` are algebraically concordant when the block sum `V ⊕ -W` is
metabolic. Classically this holds for Seifert matrices of concordant knots: `-W` is a Seifert
matrix of the reversed mirror image, and the connected sum of a knot with the reversed mirror
image of a concordant knot is slice. Combined with additivity of the signature along block sums, the
vanishing theorem shows that algebraically concordant Seifert matrices have the same
Tristram--Levine signature wherever both forms are nonsingular. This is the matrix-level form of
the concordance invariance of the signature.

Neither the passage from a knot to its Seifert matrix nor the geometric theorem that a slice knot
has a metabolic Seifert matrix is treated here.

## Main results

* `Matrix.IsMetabolic.tristramLevineSignature_eq_zero`: a metabolic matrix has vanishing
  Tristram--Levine signature wherever its form is nonsingular.
* `TauCeti.KnotTheory.tristramLevineSignature_eq_of_isMetabolic`: algebraically concordant
  matrices have the same Tristram--Levine signature wherever both forms are nonsingular.

## References

* A. G. Tristram, *Some cobordism invariants for links*, Proc. Cambridge Philos. Soc. 66
  (1969), 251--264.
* J. Levine, *Knot cobordism groups in codimension two*, Comment. Math. Helv. 44 (1969),
  229--244.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 8,
  Theorem 8.19.
* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005).
-/

public section

open Matrix
open scoped ComplexConjugate

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open TauCeti.KnotTheory in
/-- **The Tristram--Levine signature of a metabolic matrix vanishes** at every parameter `ω`
where the Tristram--Levine form is nonsingular. -/
theorem IsMetabolic.tristramLevineSignature_eq_zero {V : Matrix ι ι ℝ} (hV : V.IsMetabolic)
    {ω : ℂ} (hω : (tristramLevineForm V ω).det ≠ 0) : tristramLevineSignature V ω = 0 := by
  obtain ⟨P, hP, s, hs, h⟩ := isMetabolic_def.1 hV
  rw [← tristramLevineSignature_congr hP, tristramLevineSignature_def]
  refine (isHermitian_tristramLevineForm _ ω).signature_eq_zero_of_forall_mem_eq_zero ?_ hs.le
    fun i hi j hj => by simp [h i hi j hj, h j hj i hi]
  -- The form of `P * V * Pᵀ` is the `*`-congruence of the form of `V` by the complexification of
  -- `P`, whose determinant is the image of `det P`.
  have hP' : IsUnit (P.map ((↑) : ℝ → ℂ)).det :=
    RingHom.map_det Complex.ofRealHom P ▸ hP.map Complex.ofRealHom
  rw [tristramLevineForm_congr, det_mul, det_mul, det_conjTranspose]
  exact (hP'.mul (isUnit_iff_ne_zero.2 hω)).mul hP'.star

end Matrix

namespace TauCeti.KnotTheory

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- **Algebraically concordant matrices have the same Tristram--Levine signature.** If the block
sum `V ⊕ -W` is metabolic, then `σ_ω(V) = σ_ω(W)` at every parameter `ω` where the
Tristram--Levine forms of `V` and `W` are both nonsingular. -/
theorem tristramLevineSignature_eq_of_isMetabolic {V : Matrix ι ι ℝ} {W : Matrix κ κ ℝ}
    (h : (fromBlocks V 0 0 (-W)).IsMetabolic) {ω : ℂ}
    (hV : (tristramLevineForm V ω).det ≠ 0) (hW : (tristramLevineForm W ω).det ≠ 0) :
    tristramLevineSignature V ω = tristramLevineSignature W ω := by
  have hneg : tristramLevineForm (-W) ω = -tristramLevineForm W ω := by
    ext i j
    simp only [tristramLevineForm_apply, Matrix.neg_apply, Complex.ofReal_neg]
    ring
  have hdet : (tristramLevineForm (fromBlocks V 0 0 (-W)) ω).det ≠ 0 := by
    rw [tristramLevineForm_fromBlocks_zero, det_fromBlocks_zero₂₁, hneg, det_neg]
    exact mul_ne_zero hV (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hW)
  have h0 := h.tristramLevineSignature_eq_zero hdet
  rw [tristramLevineSignature_fromBlocks_zero, ← transpose_transpose W, ← transpose_neg,
    tristramLevineSignature_transpose, tristramLevineSignature_neg_transpose] at h0
  omega

end TauCeti.KnotTheory
