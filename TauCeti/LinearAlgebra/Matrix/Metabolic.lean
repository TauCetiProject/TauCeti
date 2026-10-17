/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Signature

/-!
# Metabolic matrices

A square matrix `V` of size `2g` is *metabolic* when it is congruent, by a matrix with unit
determinant, to a block matrix `!![0, A; B, C]` whose upper left `g × g` block vanishes. Read as a
bilinear form, `V` then vanishes on a direct summand of half the rank. This is Levine's condition
on Seifert matrices: the Seifert matrix of a slice knot is metabolic, so metabolic matrices are the
algebraic shadow of slice knots, and two Seifert matrices `V`, `W` are algebraically concordant
when the block sum `V ⊕ -W` is metabolic.

The definition allows the vanishing block to sit on any set of half of the coordinates, which is the
same condition up to reordering the basis and avoids fixing a block decomposition of the index
type. It is stated over an arbitrary commutative ring, so that an integral Seifert matrix and its
rational or real images (`Matrix.IsMetabolic.map`) are covered alike.

The signature obstruction is proved here over a linearly ordered field: a metabolic matrix `V`
whose symmetrisation `V + Vᵀ` is invertible has signature zero. For an integral Seifert matrix of
a knot, `det (V + Vᵀ)` is odd, so in particular nonzero, and this is the algebraic content of the
classical theorem that a slice knot has signature zero.

## Main definitions

* `Matrix.IsMetabolic`: congruence to a matrix vanishing on half of the coordinates.

## Main results

* `Matrix.isMetabolic_congr`: being metabolic is invariant under unimodular congruence.
* `Matrix.isMetabolic_submatrix_equiv_iff`: being metabolic is invariant under reindexing.
* `Matrix.isMetabolic_neg_iff` and `Matrix.isMetabolic_transpose_iff`: being metabolic is invariant
  under negation and under transposition.
* `Matrix.IsMetabolic.map`: ring homomorphisms preserve metabolic matrices.
* `Matrix.IsMetabolic.fromBlocks`: the block sum of metabolic matrices is metabolic.
* `Matrix.isMetabolic_fromBlocks_neg`: the block sum `V ⊕ -V` is metabolic, for every `V`.
* `Matrix.IsMetabolic.signature_eq_zero`: a metabolic matrix `V` with `V + Vᵀ` invertible has
  signature zero.

## References

* J. Levine, *Knot cobordism groups in codimension two*, Comment. Math. Helv. 44 (1969),
  229--244.
* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  for the terminology.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 8.
-/

public section

namespace Matrix

variable {R S : Type*} [CommRing R] [CommRing S] {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

/-- A square matrix `V` is *metabolic* when some congruence `V ↦ P * V * Pᵀ` by a matrix with unit
determinant makes it vanish on `s × s` for a set `s` of exactly half of the coordinates. -/
def IsMetabolic (V : Matrix ι ι R) : Prop :=
  ∃ P : Matrix ι ι R, IsUnit P.det ∧ ∃ s : Finset ι, Fintype.card ι = 2 * s.card ∧
    ∀ i ∈ s, ∀ j ∈ s, (P * V * Pᵀ) i j = 0

/-- Unfold `Matrix.IsMetabolic`: a unimodular congruence makes `V` vanish on half of the
coordinates. -/
theorem isMetabolic_def {V : Matrix ι ι R} :
    V.IsMetabolic ↔ ∃ P : Matrix ι ι R, IsUnit P.det ∧ ∃ s : Finset ι,
      Fintype.card ι = 2 * s.card ∧ ∀ i ∈ s, ∀ j ∈ s, (P * V * Pᵀ) i j = 0 :=
  Iff.rfl

/-- A matrix vanishing on half of the coordinates is metabolic. -/
theorem isMetabolic_of_forall_mem_eq_zero {V : Matrix ι ι R} {s : Finset ι}
    (hs : Fintype.card ι = 2 * s.card) (h : ∀ i ∈ s, ∀ j ∈ s, V i j = 0) : V.IsMetabolic :=
  ⟨1, by simp, s, hs, by simpa using h⟩

/-- A unimodular congruence of a metabolic matrix is metabolic. -/
theorem IsMetabolic.congr {V : Matrix ι ι R} (hV : V.IsMetabolic) {P : Matrix ι ι R}
    (hP : IsUnit P.det) : (P * V * Pᵀ).IsMetabolic := by
  obtain ⟨Q, hQ, s, hs, h⟩ := hV
  refine ⟨Q * P⁻¹, ?_, s, hs, fun i hi j hj => ?_⟩
  · rw [det_mul]
    exact hQ.mul (isUnit_nonsing_inv_det P hP)
  · have hcongr : Q * P⁻¹ * (P * V * Pᵀ) * (Q * P⁻¹)ᵀ = Q * V * Qᵀ := by
      rw [transpose_mul, transpose_nonsing_inv]
      simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hP]
      rw [← Matrix.mul_assoc Pᵀ, mul_nonsing_inv _ (isUnit_det_transpose _ hP), Matrix.one_mul]
    rw [hcongr]
    exact h i hi j hj

/-- **Being metabolic is invariant under unimodular congruence.** -/
theorem isMetabolic_congr {V P : Matrix ι ι R} (hP : IsUnit P.det) :
    (P * V * Pᵀ).IsMetabolic ↔ V.IsMetabolic := by
  refine ⟨fun h => ?_, fun h => h.congr hP⟩
  convert h.congr (isUnit_nonsing_inv_det P hP) using 1
  rw [transpose_nonsing_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hP,
    Matrix.one_mul, Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_det_transpose _ hP),
    Matrix.mul_one]

/-- Reindexing a metabolic matrix along an equivalence of index types keeps it metabolic. -/
theorem IsMetabolic.submatrix_equiv {V : Matrix ι ι R} (hV : V.IsMetabolic) (e : ι ≃ κ) :
    (V.submatrix e.symm e.symm).IsMetabolic := by
  obtain ⟨P, hP, s, hs, h⟩ := hV
  refine ⟨P.submatrix e.symm e.symm, by rwa [det_submatrix_equiv_self], s.map e.toEmbedding,
    by rw [Finset.card_map, ← hs, Fintype.card_congr e], fun i hi j hj => ?_⟩
  have hsub : P.submatrix e.symm e.symm * V.submatrix e.symm e.symm *
      (P.submatrix e.symm e.symm)ᵀ = (P * V * Pᵀ).submatrix e.symm e.symm := by
    rw [transpose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]
  rw [hsub, submatrix_apply]
  exact h _ (by simpa [Finset.mem_map_equiv] using hi) _ (by simpa [Finset.mem_map_equiv] using hj)

/-- **Being metabolic is invariant under reindexing.** -/
theorem isMetabolic_submatrix_equiv_iff {V : Matrix ι ι R} (e : ι ≃ κ) :
    (V.submatrix e.symm e.symm).IsMetabolic ↔ V.IsMetabolic := by
  refine ⟨fun h => ?_, fun h => h.submatrix_equiv e⟩
  simpa using h.submatrix_equiv e.symm

/-- The negation of a metabolic matrix is metabolic. -/
theorem IsMetabolic.neg {V : Matrix ι ι R} (hV : V.IsMetabolic) : (-V).IsMetabolic := by
  obtain ⟨P, hP, s, hs, h⟩ := hV
  refine ⟨P, hP, s, hs, fun i hi j hj => ?_⟩
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_apply, h i hi j hj, neg_zero]

/-- **Being metabolic is invariant under negation.** -/
@[simp]
theorem isMetabolic_neg_iff {V : Matrix ι ι R} : (-V).IsMetabolic ↔ V.IsMetabolic :=
  ⟨fun h => neg_neg V ▸ h.neg, IsMetabolic.neg⟩

/-- The transpose of a metabolic matrix is metabolic. -/
theorem IsMetabolic.transpose {V : Matrix ι ι R} (hV : V.IsMetabolic) : Vᵀ.IsMetabolic := by
  obtain ⟨P, hP, s, hs, h⟩ := hV
  refine ⟨P, hP, s, hs, fun i hi j hj => ?_⟩
  have hT : P * Vᵀ * Pᵀ = (P * V * Pᵀ)ᵀ := by
    rw [transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  rw [hT, transpose_apply, h j hj i hi]

/-- **Being metabolic is invariant under transposition.** -/
@[simp]
theorem isMetabolic_transpose_iff {V : Matrix ι ι R} : Vᵀ.IsMetabolic ↔ V.IsMetabolic :=
  ⟨fun h => transpose_transpose V ▸ h.transpose, IsMetabolic.transpose⟩

/-- The image of a metabolic matrix under a ring homomorphism is metabolic. In particular an
integral metabolic matrix stays metabolic over `ℚ` and over `ℝ`. -/
theorem IsMetabolic.map {V : Matrix ι ι R} (hV : V.IsMetabolic) (f : R →+* S) :
    (V.map f).IsMetabolic := by
  obtain ⟨P, hP, s, hs, h⟩ := hV
  refine ⟨P.map f, RingHom.map_det f P ▸ hP.map f, s, hs, fun i hi j hj => ?_⟩
  rw [← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, map_apply, h i hi j hj, map_zero]

/-- **The block sum of metabolic matrices is metabolic.** For Seifert matrices this is the
connected sum of two algebraically slice knots. -/
theorem IsMetabolic.fromBlocks {V : Matrix ι ι R} {W : Matrix κ κ R} (hV : V.IsMetabolic)
    (hW : W.IsMetabolic) : (Matrix.fromBlocks V 0 0 W).IsMetabolic := by
  obtain ⟨P, hP, s, hs, h⟩ := hV
  obtain ⟨Q, hQ, t, ht, h'⟩ := hW
  refine ⟨Matrix.fromBlocks P 0 0 Q, ?_, s.disjSum t, ?_, ?_⟩
  · rw [det_fromBlocks_zero₂₁]
    exact hP.mul hQ
  · rw [Fintype.card_sum, hs, ht, Finset.card_disjSum]
    ring
  · rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
    rintro (i | i) hi (j | j) hj <;> simp_all

/-- **The block sum `V ⊕ -V` is metabolic**: it vanishes on the diagonal copy of the coordinates
of `V`. For a Seifert matrix `V` of a knot `K`, the matrix `-V` is a Seifert matrix of the
reversed mirror image, and this is the algebraic form of the sliceness of `K # -K`. -/
theorem isMetabolic_fromBlocks_neg (V : Matrix ι ι R) :
    (Matrix.fromBlocks V 0 0 (-V)).IsMetabolic := by
  refine ⟨Matrix.fromBlocks 1 1 0 1, by simp, Finset.univ.map .inl, by simp [two_mul], ?_⟩
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  rintro (i | i) hi (j | j) hj <;> simp_all

section Signature

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- **A metabolic matrix has signature zero** as soon as its symmetrisation `V + Vᵀ` is
invertible. The image of an integral Seifert matrix of a knot satisfies this, so the signature of
an algebraically slice knot vanishes. -/
theorem IsMetabolic.signature_eq_zero {V : Matrix ι ι 𝕜} (hV : V.IsMetabolic)
    (hdet : IsUnit (V + Vᵀ).det) : signature V = 0 := by
  obtain ⟨P, hP, s, hs, h⟩ := hV
  rw [← signature_congr hP]
  refine signature_eq_zero_of_forall_mem_eq_zero ?_ hs.le h
  have hsymm : P * V * Pᵀ + (P * V * Pᵀ)ᵀ = P * (V + Vᵀ) * Pᵀ := by
    simp only [transpose_mul, transpose_transpose, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_assoc]
  rw [hsymm, det_mul, det_mul, det_transpose]
  exact (hP.mul hdet).mul hP

end Signature

end Matrix
