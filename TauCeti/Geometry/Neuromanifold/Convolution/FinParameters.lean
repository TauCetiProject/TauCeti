/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Neuromanifold.Convolution.Polynomial

/-!
# Numbered parameters for convolutional chains

List the filter entries layer by layer, in filter order within a layer. For an affine chain,
put the one shared bias immediately after its layer's filter. This gives a computable numbering
by `Fin p` and equivalences from vectors of that length to the original parameter products.
The bias-free numbering omits the biases entirely. Renaming the parameter variables of the
joint polynomials by these numberings lets them be evaluated directly on the numbered vectors.

The shared-bias convention is that of Shahverdi, *Algebraic Complexity and Neurovariety of
Linear Convolutional Networks*, [arXiv:2401.16613v1](https://arxiv.org/abs/2401.16613v1), §2.1.
The numbering uses Mathlib's `finSumFinEquiv` within a layer and `finSigmaFinEquiv` across layers.
-/

public section

open MvPolynomial

namespace TauCeti.Neuromanifold.ConvolutionSpec

variable {K : Type*} {L : ℕ}

/-- Enumerate the affine coordinates in layer order, with each shared bias last in its layer. -/
def parameterIndexEquivFin (A : ConvolutionSpec K L) :
    A.ParameterIndex ≃ Fin (∑ i, (A.filterLength i + 1)) :=
  (Equiv.sigmaCongrRight fun _ =>
    (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv).trans finSigmaFinEquiv

/-- The index is the total size of the preceding layers plus the position within this layer.
The shared bias has position `A.filterLength i`. -/
theorem val_parameterIndexEquivFin (A : ConvolutionSpec K L) (i : Fin L)
    (j : Fin (A.filterLength i) ⊕ Unit) :
    (A.parameterIndexEquivFin ⟨i, j⟩).val =
      (∑ t : Fin i, (A.filterLength (Fin.castLE i.isLt.le t) + 1)) +
        j.elim Fin.val (fun _ => A.filterLength i) := by
  cases j with
  | inl j => simp [parameterIndexEquivFin, finSigmaFinEquiv_apply]
  | inr u => simp [parameterIndexEquivFin, finSigmaFinEquiv_apply, finSumFinEquiv_apply_right]

/-- Reconstruct the affine parameter product from a vector in layer order. -/
def finParameterEquiv (A : ConvolutionSpec K L) :
    (Fin (∑ i, (A.filterLength i + 1)) → K) ≃ A.Parameters :=
  (Equiv.arrowCongr A.parameterIndexEquivFin.symm (Equiv.refl K)).trans A.parameterEquiv

/-- Recover a filter entry from its numbered affine coordinate. -/
@[simp] theorem finParameterEquiv_apply_fst (A : ConvolutionSpec K L)
    (v : Fin (∑ i, (A.filterLength i + 1)) → K) (i : Fin L) (j : Fin (A.filterLength i)) :
    (A.finParameterEquiv v i).1 j = v (A.parameterIndexEquivFin ⟨i, .inl j⟩) := by
  exact A.parameterEquiv_apply_fst (v ∘ A.parameterIndexEquivFin) i j

/-- Recover the shared bias from its numbered affine coordinate. -/
@[simp] theorem finParameterEquiv_apply_snd (A : ConvolutionSpec K L)
    (v : Fin (∑ i, (A.filterLength i + 1)) → K) (i : Fin L) :
    (A.finParameterEquiv v i).2 = v (A.parameterIndexEquivFin ⟨i, .inr ()⟩) := by
  exact A.parameterEquiv_apply_snd (v ∘ A.parameterIndexEquivFin) i

/-- Flattening an affine parameter product puts each filter entry at its numbered coordinate. -/
@[simp] theorem finParameterEquiv_symm_apply_inl (A : ConvolutionSpec K L) (p : A.Parameters)
    (i : Fin L) (j : Fin (A.filterLength i)) :
    A.finParameterEquiv.symm p (A.parameterIndexEquivFin ⟨i, .inl j⟩) = (p i).1 j := by
  simpa only [finParameterEquiv_apply_fst] using
    congrArg (fun q : A.Parameters => (q i).1 j) (A.finParameterEquiv.apply_symm_apply p)

/-- Flattening an affine parameter product puts each shared bias at its numbered coordinate. -/
@[simp] theorem finParameterEquiv_symm_apply_inr (A : ConvolutionSpec K L) (p : A.Parameters)
    (i : Fin L) : A.finParameterEquiv.symm p (A.parameterIndexEquivFin ⟨i, .inr ()⟩) = (p i).2 := by
  simpa only [finParameterEquiv_apply_snd] using
    congrArg (fun q : A.Parameters => (q i).2) (A.finParameterEquiv.apply_symm_apply p)

/-- Reconstruct the bias-free filter product from a vector in layer order. -/
def finWeightEquiv (A : ConvolutionSpec K L) :
    (Fin (∑ i, A.filterLength i) → K) ≃ A.Weights :=
  (Equiv.arrowCongr finSigmaFinEquiv.symm (Equiv.refl K)).trans A.weightEquiv

/-- Recover a filter entry from its numbered bias-free coordinate. -/
@[simp] theorem finWeightEquiv_apply (A : ConvolutionSpec K L)
    (v : Fin (∑ i, A.filterLength i) → K) (i : Fin L) (j : Fin (A.filterLength i)) :
    A.finWeightEquiv v i j = v (finSigmaFinEquiv ⟨i, j⟩) := by
  exact A.weightEquiv_apply (v ∘ finSigmaFinEquiv) i j

/-- Flattening a filter product puts each entry at its numbered bias-free coordinate. -/
@[simp] theorem finWeightEquiv_symm_apply (A : ConvolutionSpec K L) (w : A.Weights)
    (i : Fin L) (j : Fin (A.filterLength i)) :
    A.finWeightEquiv.symm w (finSigmaFinEquiv ⟨i, j⟩) = w i j := by
  simpa only [finWeightEquiv_apply] using
    congrArg (fun u : A.Weights => u i j) (A.finWeightEquiv.apply_symm_apply w)

section Polynomial

variable [CommSemiring K]

/-- The jointly polynomial affine model in numbered parameter coordinates. -/
noncomputable def polynomialRealizeFin (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K) :
    Fin (A.width (Fin.last L)) →
      MvPolynomial (Fin (∑ i, (A.filterLength i + 1)) ⊕ Fin (A.width 0)) K :=
  fun j => rename (Sum.map A.parameterIndexEquivFin id) (A.polynomialRealize q j)

/-- The affine model renames parameter variables and leaves input variables unchanged. -/
theorem polynomialRealizeFin_def (A : ConvolutionSpec K L) (q : Fin (L - 1) → Polynomial K) :
    A.polynomialRealizeFin q =
      fun j => rename (Sum.map A.parameterIndexEquivFin id) (A.polynomialRealize q j) := (rfl)

/-- Evaluation on numbered affine coordinates agrees with realization on the reconstructed
parameters, at every input. -/
theorem polynomialRealization_polynomialRealizeFin (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K) (hq : ∀ j t, A.activation j t = (q j).eval t) :
    polynomialRealization (A.polynomialRealizeFin q) = A.realize ∘ A.finParameterEquiv := by
  rw [polynomialRealizeFin_def, polynomialRealization_rename_parameters,
    A.polynomialRealization_polynomialRealize q hq]
  rfl

/-- The jointly polynomial bias-free model in numbered filter coordinates. -/
noncomputable def polynomialRealizeWeightsFin (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K) :
    Fin (A.width (Fin.last L)) → MvPolynomial (Fin (∑ i, A.filterLength i) ⊕ Fin (A.width 0)) K :=
  fun j => rename (Sum.map finSigmaFinEquiv id) (A.polynomialRealizeWeights q j)

/-- The bias-free model renames the filter variables and leaves input variables unchanged. -/
theorem polynomialRealizeWeightsFin_def (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K) :
    A.polynomialRealizeWeightsFin q =
      fun j => rename (Sum.map finSigmaFinEquiv id) (A.polynomialRealizeWeights q j) := (rfl)

/-- Evaluation on numbered bias-free coordinates agrees with realization on the reconstructed
filters, at every input. -/
theorem polynomialRealization_polynomialRealizeWeightsFin (A : ConvolutionSpec K L)
    (q : Fin (L - 1) → Polynomial K) (hq : ∀ j t, A.activation j t = (q j).eval t) :
    polynomialRealization (A.polynomialRealizeWeightsFin q) =
      A.realizeWeights ∘ A.finWeightEquiv := by
  rw [polynomialRealizeWeightsFin_def, polynomialRealization_rename_parameters,
    A.polynomialRealization_polynomialRealizeWeights q hq]
  rfl

end Polynomial

end TauCeti.Neuromanifold.ConvolutionSpec
