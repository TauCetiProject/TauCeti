/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Real
public import TauCeti.LinearAlgebra.QuadraticForm.Isometry
public import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# Classification of real quadratic forms by their signature

Mathlib proves the two halves of Sylvester's law of inertia separately: every real quadratic form
on a finite-dimensional space is equivalent to a weighted sum of squares with weights `1`, `0`
and `-1`, and the numbers of positive and of negative weights are the invariants `sigPos` and
`sigNeg`.  This file combines them into the classification itself: two real quadratic forms are
isometric exactly when their dimensions and their two indices of inertia agree.  For a
nondegenerate form the two indices already determine the dimension, so a regular real form is
classified by its signature alone.

The file also supplies the normal form realizing a prescribed signature, the orthogonal sum of
`p` copies of `⟨1⟩` and `q` copies of `⟨-1⟩`, and shows that every regular real form is isometric
to the normal form of its own signature.

## Main results

* `QuadraticForm.equivalent_iff_finrank_eq_and_sigPos_eq_and_sigNeg_eq`: two real quadratic forms
  on finite-dimensional spaces are isometric exactly when their dimensions and both indices of
  inertia agree.
* `QuadraticForm.equivalent_iff_sigPos_eq_and_sigNeg_eq`: two nondegenerate real quadratic forms
  are isometric exactly when their signatures agree.
* `QuadraticForm.realSignatureForm`: the normal form of signature `(p, q)`.
* `QuadraticForm.sigPos_realSignatureForm`, `QuadraticForm.sigNeg_realSignatureForm` and
  `QuadraticForm.nondegenerate_realSignatureForm`: every signature is realized by a regular form.
* `QuadraticForm.equivalent_realSignatureForm`: a regular real quadratic form is isometric to the
  normal form of its signature.
* `QuadraticForm.equivalent_realSignatureForm_iff`: distinct signatures give non-isometric normal
  forms.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section
noncomputable section

open Finset QuadraticMap

namespace QuadraticForm

section Fibres

/-- A fibre counted as a set of indices and as a subtype gives the same number; this is
`Nat.card_coe_set_eq` in the subtype presentation that `Equiv.ofFiberEquiv` expects. -/
private theorem ncard_fibre_eq_card {ι : Type*} (u : ι → SignType) (s : SignType) :
    {i | u i = s}.ncard = Nat.card {i // u i = s} :=
  (Nat.card_coe_set_eq _).symm

/-- The three fibres of a sign-valued family exhaust the index type. -/
private theorem ncard_fibre_zero_add_ncard_fibre_neg_add_ncard_fibre_pos {ι : Type*} [Finite ι]
    (u : ι → SignType) :
    {i | u i = 0}.ncard + {i | u i = -1}.ncard + {i | u i = 1}.ncard = Nat.card ι := by
  have : Fintype ι := Fintype.ofFinite ι
  simp only [ncard_fibre_eq_card, Nat.card_eq_fintype_card]
  have hsigma : Fintype.card ι = ∑ s : SignType, Fintype.card {i // u i = s} := by
    rw [← Fintype.card_sigma]
    exact (Fintype.card_congr (Equiv.sigmaFiberEquiv u)).symm
  rw [hsigma, SignType.univ_eq, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, add_assoc]

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- The positive index of inertia of a sign-weighted sum of squares counts the weights `1`. -/
private theorem ncard_fibre_pos (u : ι → SignType) :
    {i | u i = 1}.ncard = sigPos (weightedSumSquares ℝ fun i ↦ ((u i : ℝ))) := by
  rw [sigPos_weightedSumSquares]
  congr 1
  ext i
  cases h : u i <;> simp [h]

/-- The negative index of inertia of a sign-weighted sum of squares counts the weights `-1`. -/
private theorem ncard_fibre_neg (u : ι → SignType) :
    {i | u i = -1}.ncard = sigNeg (weightedSumSquares ℝ fun i ↦ ((u i : ℝ))) := by
  rw [sigNeg_weightedSumSquares]
  congr 1
  ext i
  cases h : u i <;> simp [h]

/-- Two sign-weighted sums of squares are isometric as soon as each of the three weights occurs
the same number of times in both. -/
private theorem equivalent_weightedSumSquares_of_ncard_fibre_eq (u : ι → SignType)
    (u' : ι' → SignType) (h : ∀ s : SignType, {i | u i = s}.ncard = {i' | u' i' = s}.ncard) :
    Equivalent (weightedSumSquares ℝ fun i ↦ ((u i : ℝ)))
      (weightedSumSquares ℝ fun i' ↦ ((u' i' : ℝ))) := by
  have hfibre : ∀ s : SignType, {i // u i = s} ≃ {i' // u' i' = s} := fun s ↦ by
    refine (Fintype.card_eq.mp ?_).some
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact h s
  let σ : ι ≃ ι' := Equiv.ofFiberEquiv hfibre
  have hσ : ∀ i, u' (σ i) = u i := fun i ↦ Equiv.ofFiberEquiv_map hfibre i
  have hcomp : (fun i' ↦ ((u' i' : ℝ))) ∘ σ = fun i ↦ ((u i : ℝ)) := by
    funext i
    exact congrArg (fun s : SignType ↦ ((s : ℝ))) (hσ i)
  exact ⟨((weightedSumSquaresCongrEquiv (R := ℝ) (fun i' ↦ ((u' i' : ℝ))) σ).trans
    (weightedSumSquaresCongr hcomp)).symm⟩

end Fibres

variable {M M' : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup M'] [Module ℝ M']
  [FiniteDimensional ℝ M] [FiniteDimensional ℝ M']

/-- **Sylvester's law of inertia**, classification form: two real quadratic forms on
finite-dimensional spaces are isometric exactly when their dimensions agree and both indices of
inertia agree.  The dimension is a genuine third condition: it records the number of zero weights
in a diagonalization, which the two indices do not see. -/
theorem equivalent_iff_finrank_eq_and_sigPos_eq_and_sigNeg_eq (Q : _root_.QuadraticForm ℝ M)
    (Q' : _root_.QuadraticForm ℝ M') :
    Q.Equivalent Q' ↔ Module.finrank ℝ M = Module.finrank ℝ M' ∧
      sigPos Q = sigPos Q' ∧ sigNeg Q = sigNeg Q' := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.toLinearEquiv.finrank_eq, Equivalent.sigPos_eq ⟨e⟩, Equivalent.sigNeg_eq ⟨e⟩⟩
  · rintro ⟨hrank, hpos, hneg⟩
    obtain ⟨u, hu⟩ := Q.equivalent_signType_weighted_sum_squared
    obtain ⟨u', hu'⟩ := Q'.equivalent_signType_weighted_sum_squared
    refine hu.trans ((equivalent_weightedSumSquares_of_ncard_fibre_eq u u' ?_).trans hu'.symm)
    have hposFibre : {i | u i = 1}.ncard = {i' | u' i' = 1}.ncard := by
      rw [ncard_fibre_pos, ncard_fibre_pos, ← hu.sigPos_eq, ← hu'.sigPos_eq, hpos]
    have hnegFibre : {i | u i = -1}.ncard = {i' | u' i' = -1}.ncard := by
      rw [ncard_fibre_neg, ncard_fibre_neg, ← hu.sigNeg_eq, ← hu'.sigNeg_eq, hneg]
    have hsum := ncard_fibre_zero_add_ncard_fibre_neg_add_ncard_fibre_pos u
    have hsum' := ncard_fibre_zero_add_ncard_fibre_neg_add_ncard_fibre_pos u'
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hsum hsum'
    have hzeroFibre : {i | u i = 0}.ncard = {i' | u' i' = 0}.ncard := by omega
    intro s
    cases s
    · exact hzeroFibre
    · exact hnegFibre
    · exact hposFibre

/-- **Sylvester's law of inertia** for regular forms: two nondegenerate real quadratic forms are
isometric exactly when their signatures agree. -/
theorem equivalent_iff_sigPos_eq_and_sigNeg_eq {Q : _root_.QuadraticForm ℝ M}
    {Q' : _root_.QuadraticForm ℝ M'} (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate) :
    Q.Equivalent Q' ↔ sigPos Q = sigPos Q' ∧ sigNeg Q = sigNeg Q' := by
  rw [equivalent_iff_finrank_eq_and_sigPos_eq_and_sigNeg_eq]
  refine ⟨fun h ↦ ⟨h.2.1, h.2.2⟩, fun h ↦ ⟨?_, h.1, h.2⟩⟩
  rw [← sigPos_add_sigNeg_of_nondegenerate Q hQ, ← sigPos_add_sigNeg_of_nondegenerate Q' hQ',
    h.1, h.2]

/-- The normal form of signature `(p, q)`: the orthogonal sum of `p` copies of `⟨1⟩` and `q`
copies of `⟨-1⟩`. -/
def realSignatureForm (p q : ℕ) : _root_.QuadraticForm ℝ (Fin p ⊕ Fin q → ℝ) :=
  weightedSumSquares ℝ (Sum.elim (fun _ ↦ (1 : ℝ)) fun _ ↦ -1)

@[simp]
theorem realSignatureForm_apply (p q : ℕ) (x : Fin p ⊕ Fin q → ℝ) :
    realSignatureForm p q x =
      (∑ i : Fin p, x (Sum.inl i) ^ 2) - ∑ j : Fin q, x (Sum.inr j) ^ 2 := by
  simp [realSignatureForm, weightedSumSquares_apply, Fintype.sum_sum_type, _root_.sq,
    sub_eq_add_neg]

/-- The positive index of inertia of the normal form `realSignatureForm p q` is `p`. -/
@[simp]
theorem sigPos_realSignatureForm (p q : ℕ) : sigPos (realSignatureForm p q) = p := by
  have hset : {x : Fin p ⊕ Fin q | 0 < Sum.elim (fun _ ↦ (1 : ℝ)) (fun _ ↦ -1) x} =
      Sum.inl '' Set.univ := by
    ext x
    cases x <;> simp
  rw [realSignatureForm, sigPos_weightedSumSquares, hset,
    Set.ncard_image_of_injective _ Sum.inl_injective, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- The negative index of inertia of the normal form `realSignatureForm p q` is `q`. -/
@[simp]
theorem sigNeg_realSignatureForm (p q : ℕ) : sigNeg (realSignatureForm p q) = q := by
  have hset : {x : Fin p ⊕ Fin q | Sum.elim (fun _ ↦ (1 : ℝ)) (fun _ ↦ -1) x < 0} =
      Sum.inr '' Set.univ := by
    ext x
    cases x <;> simp
  rw [realSignatureForm, sigNeg_weightedSumSquares, hset,
    Set.ncard_image_of_injective _ Sum.inr_injective, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- The normal form of signature `(p, q)` is regular, so every signature is realized by a regular
real quadratic form. -/
@[simp]
theorem nondegenerate_realSignatureForm (p q : ℕ) : (realSignatureForm p q).Nondegenerate := by
  let _ : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  rw [nondegenerate_iff_radical_eq_bot, ← Submodule.finrank_eq_zero]
  have hsum := sigPos_add_sigNeg_add_radical (Q := realSignatureForm p q)
  rw [sigPos_realSignatureForm, sigNeg_realSignatureForm] at hsum
  have hdim : Module.finrank ℝ (Fin p ⊕ Fin q → ℝ) = p + q := by simp
  omega

/-- Two normal forms are isometric exactly when their signatures coincide, so the signature is a
complete and independent system of invariants for regular real quadratic forms. -/
@[simp]
theorem equivalent_realSignatureForm_iff (p q p' q' : ℕ) :
    (realSignatureForm p q).Equivalent (realSignatureForm p' q') ↔ p = p' ∧ q = q' := by
  rw [equivalent_iff_sigPos_eq_and_sigNeg_eq (nondegenerate_realSignatureForm p q)
    (nondegenerate_realSignatureForm p' q')]
  simp

/-- Every regular real quadratic form is isometric to the normal form of its signature. -/
theorem equivalent_realSignatureForm (Q : _root_.QuadraticForm ℝ M) (hQ : Q.Nondegenerate) :
    Q.Equivalent (realSignatureForm (sigPos Q) (sigNeg Q)) :=
  (equivalent_iff_sigPos_eq_and_sigNeg_eq hQ (nondegenerate_realSignatureForm _ _)).mpr
    ⟨(sigPos_realSignatureForm _ _).symm, (sigNeg_realSignatureForm _ _).symm⟩

end QuadraticForm
