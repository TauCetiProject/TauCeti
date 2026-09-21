/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Complex
public import TauCeti.LinearAlgebra.QuadraticForm.Real
public import TauCeti.NumberTheory.HilbertSymbol.Archimedean
public import TauCeti.NumberTheory.QuadraticForm.Global.Signature

/-!
# Classification of quadratic forms at the archimedean places of a number field

A regular quadratic form over a number field has a complete system of invariants at each
archimedean place: the signature at a real place, and the rank alone at a complex one.  This file
states those two classifications for the localizations `QuadraticForm.atRealPlace` and
`QuadraticForm.atComplexEmbedding`, together with the archimedean normal forms they single out.

At a real place the invariants are the positive and negative indices, and the normal form is
`QuadraticForm.realSignatureForm p q`, the orthogonal sum of `p` copies of `⟨1⟩` and `q` copies of
`⟨-1⟩`.  Since the two indices of a regular form add to the global rank, forms of equal rank are
separated by the positive index alone, which is the invariant recorded once per real place in the
local-global theory.

Alongside the classification, the archimedean Hasse sign of a global diagonalization is computed:
the product of the real Hilbert symbols `(a_i, a_j)` over the ordered pairs of coefficients of a
diagonalization of a form is `(-1)^(q(q-1)/2)` for its negative index `q` at that place.  It is
the archimedean factor of the product over all places of the Hasse signs of a global form.

Through a complex embedding the only invariant is the rank, and the normal form is the standard
sum of squares.  For regular forms this is what makes the complex clause of the local-global
predicates automatic; the degenerate cases need the finite-place clauses instead, as
`TauCeti/NumberTheory/QuadraticForm/Global/ComplexPlaces.lean` shows.

## Main results

* `QuadraticForm.equivalent_atRealPlace_iff_realSignature_eq`: at a real place regular forms are
  classified by their signature.
* `QuadraticForm.equivalent_atRealPlace_iff_realPositiveIndex_eq`: at a fixed global rank the
  positive index alone classifies them.
* `QuadraticForm.equivalent_atRealPlace_realSignatureForm_iff`: the localization is the normal
  form `p⟨1⟩ ⊥ q⟨-1⟩` exactly when `(p, q)` is its signature.
* `TauCeti.prod_hilbertSymbol_atRealPlace`: the archimedean Hasse sign of a diagonalization.
* `QuadraticForm.equivalent_atComplexEmbedding_iff_finrank_eq`: through a complex embedding
  regular forms are classified by their rank.
* `QuadraticForm.equivalent_atComplexEmbedding_weightedSumSquares_one`: through a complex
  embedding the normal form is the standard sum of squares.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), §61 for the archimedean
  classification and 71:18 for the real Hilbert symbol.
-/

public section
noncomputable section

open Finset NumberField NumberField.InfinitePlace QuadraticMap

universe u v v'

namespace QuadraticForm

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type v'} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {Q : _root_.QuadraticForm K V} {R : _root_.QuadraticForm K W}

section RealPlace

/-- **Sylvester's law of inertia at a real place.** Two regular quadratic forms become isometric
at a real place exactly when their signatures there agree. -/
theorem equivalent_atRealPlace_iff_realSignature_eq (hQ : Q.Nondegenerate) (hR : R.Nondegenerate)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (Q.atRealPlace w).Equivalent (R.atRealPlace w) ↔ Q.realSignature w = R.realSignature w := by
  rw [equivalent_iff_sigPos_eq_and_sigNeg_eq (Nondegenerate.atRealPlace hQ w)
    (Nondegenerate.atRealPlace hR w)]
  simp only [Prod.ext_iff, realSignature_fst, realSignature_snd, realPositiveIndex_eq_sigPos,
    realNegativeIndex_eq_sigNeg]

/-- At a real place the positive index is already a complete invariant of regular forms of equal
global rank, because the negative index is the rank minus the positive index. -/
theorem equivalent_atRealPlace_iff_realPositiveIndex_eq (hQ : Q.Nondegenerate)
    (hR : R.Nondegenerate) (hrank : Module.finrank K V = Module.finrank K W)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (Q.atRealPlace w).Equivalent (R.atRealPlace w) ↔
      Q.realPositiveIndex w = R.realPositiveIndex w := by
  have hQsum := realPositiveIndex_add_realNegativeIndex_eq_finrank hQ w
  have hRsum := realPositiveIndex_add_realNegativeIndex_eq_finrank hR w
  rw [equivalent_atRealPlace_iff_realSignature_eq hQ hR w]
  simp only [Prod.ext_iff, realSignature_fst, realSignature_snd]
  omega

/-- A regular quadratic form is isometric at a real place to the normal form `p⟨1⟩ ⊥ q⟨-1⟩`
exactly when `(p, q)` is its signature there. -/
theorem equivalent_atRealPlace_realSignatureForm_iff (hQ : Q.Nondegenerate)
    (w : {w : InfinitePlace K // w.IsReal}) (p q : ℕ) :
    (Q.atRealPlace w).Equivalent (realSignatureForm p q) ↔ Q.realSignature w = (p, q) := by
  rw [equivalent_iff_sigPos_eq_and_sigNeg_eq (Nondegenerate.atRealPlace hQ w)
      (nondegenerate_realSignatureForm p q), sigPos_realSignatureForm, sigNeg_realSignatureForm,
    Prod.ext_iff, realSignature_fst, realSignature_snd, realPositiveIndex_eq_sigPos,
    realNegativeIndex_eq_sigNeg]

omit [FiniteDimensional K V] in
/-- **The archimedean Hasse sign.** For a diagonalization `Q ≃ ⟨a₁, …, aₙ⟩` by global units, the
product of the real Hilbert symbols of the localized coefficients over the ordered pairs `i < j`
is `(-1)^(q(q-1)/2)`, where `q` is the negative index of `Q` at the real place.  In particular
the product depends on `Q` and the place alone, not on the chosen diagonalization. -/
theorem _root_.TauCeti.prod_hilbertSymbol_atRealPlace {ι : Type*} [Fintype ι] [LinearOrder ι]
    {a : ι → Kˣ} (h : Q.Equivalent (weightedSumSquares K fun i ↦ (a i : K)))
    (w : {w : InfinitePlace K // w.IsReal}) :
    ∏ ij ∈ univ.filter (fun ij : ι × ι => ij.1 < ij.2),
        TauCeti.hilbertSymbol (TauCeti.unitAtRealPlace w (a ij.1))
          (TauCeti.unitAtRealPlace w (a ij.2)) =
      (-1) ^ (Q.realNegativeIndex w).choose 2 := by
  have hcoe : (fun i ↦ ((TauCeti.unitAtRealPlace w (a i) : ℝˣ) : ℝ)) =
      fun i ↦ embedding_of_isReal w.2 (a i : K) := by
    funext i
    simp
  have hloc : (Q.atRealPlace w).Equivalent
      (weightedSumSquares ℝ fun i ↦ ((TauCeti.unitAtRealPlace w (a i) : ℝˣ) : ℝ)) := by
    rw [hcoe]
    exact (h.atRealPlace w).trans ⟨atRealPlaceWeightedSumSquares w fun i ↦ (a i : K)⟩
  rw [TauCeti.prod_hilbertSymbol_real_of_equiv_weightedSumSquares hloc,
    realNegativeIndex_eq_sigNeg]

end RealPlace

section ComplexEmbedding

/-- Through a complex embedding regular quadratic forms are classified by their rank alone. -/
theorem equivalent_atComplexEmbedding_iff_finrank_eq (hQ : Q.Nondegenerate)
    (hR : R.Nondegenerate) (w : InfinitePlace K) :
    (Q.atComplexEmbedding w).Equivalent (R.atComplexEmbedding w) ↔
      Module.finrank K V = Module.finrank K W := by
  let _ : CharZero K := RingHom.charZero w.embedding
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let _ : Algebra K ℂ := w.embedding.toAlgebra
  rw [equivalent_iff_finrank_eq_of_isAlgClosed _ _ (Nondegenerate.atComplexEmbedding hQ w)
      (Nondegenerate.atComplexEmbedding hR w), Module.finrank_baseChange,
    Module.finrank_baseChange]

/-- Through a complex embedding a regular quadratic form is isometric to the standard sum of
squares of its global rank. -/
theorem equivalent_atComplexEmbedding_weightedSumSquares_one (hQ : Q.Nondegenerate)
    (w : InfinitePlace K) :
    (Q.atComplexEmbedding w).Equivalent
      (weightedSumSquares ℂ (1 : Fin (Module.finrank K V) → ℂ)) := by
  let _ : CharZero K := RingHom.charZero w.embedding
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let _ : Algebra K ℂ := w.embedding.toAlgebra
  have hrank : Module.finrank ℂ (w.ComplexScalarExtension (V := V)) = Module.finrank K V :=
    Module.finrank_baseChange
  have hsep : (associated (Q.atComplexEmbedding w)).SeparatingLeft :=
    (nondegenerate_associated_iff.mpr (Nondegenerate.atComplexEmbedding hQ w)).1
  rw [← hrank]
  exact equivalent_weightedSumSquares_of_isAlgClosed (Q.atComplexEmbedding w) hsep

end ComplexEmbedding

end QuadraticForm
