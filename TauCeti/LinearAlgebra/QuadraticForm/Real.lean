/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Analysis.Real.Sqrt
import TauCeti.LinearAlgebra.QuadraticForm.Standard
public import TauCeti.Data.SignType.Cardinality
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

Without any finite-dimensionality assumption, a real quadratic form is anisotropic exactly when
it is positive or negative definite. This identifies the algebraic condition used in compactness
criteria for real orthogonal groups with the usual order-theoretic notion of definiteness.

## Main results

* `QuadraticForm.anisotropic_iff_posDef_or_negDef`: real anisotropic forms are exactly the
  positive and negative definite forms, including forms on the zero space.
* `QuadraticMap.map_inv_sqrt_smul_eq_one`: a vector of positive quadratic value can be
  normalized to value one by inverse-square-root scaling. This normalization feeds the
  reflection-pair construction for compact real Clifford forms.
* `QuadraticForm.sigPos_weightedSumSquares_signType` and
  `QuadraticForm.sigNeg_weightedSumSquares_signType`: the two indices of inertia of a
  sign-weighted sum of squares count the weights `1` and the weights `-1`.
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
* `QuadraticForm.exists_nondegenerate_and_sigPos_eq_and_sigNeg_eq`: every signature `(p, n - p)` is
  realized by a regular form on the coordinate space `ℝⁿ`.
* `QuadraticForm.equivalent_realSignatureForm_iff_sigPos_eq_and_sigNeg_eq`: a regular real form is
  isometric to a prescribed normal form exactly when it has the prescribed signature.
* `QuadraticForm.equivalent_realSignatureForm_iff`: distinct signatures give non-isometric normal
  forms.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section
noncomputable section

open Finset QuadraticMap

namespace QuadraticMap

variable {M : Type*} [AddCommMonoid M] [Module ℝ M]

/-- Scaling a vector by the inverse square root of its positive quadratic value gives value one. -/
@[simp]
theorem map_inv_sqrt_smul_eq_one {Q : QuadraticForm ℝ M} {v : M} (hpos : 0 < Q v) :
    Q ((Real.sqrt (Q v))⁻¹ • v) = 1 := by
  have hsquare : (Real.sqrt (Q v))⁻¹ ^ 2 = (Q v)⁻¹ := by
    simpa only [mul_one, one_pow, one_div] using Real.inv_sqrt_mul_sq hpos.le 1
  calc
    Q ((Real.sqrt (Q v))⁻¹ • v) = (Real.sqrt (Q v))⁻¹ ^ 2 * Q v := by
      simp only [QuadraticMap.map_smul, smul_eq_mul, pow_two]
    _ = (Q v)⁻¹ * Q v := by rw [hsquare]
    _ = 1 := inv_mul_cancel₀ hpos.ne'

end QuadraticMap

namespace QuadraticForm

section Definiteness

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

/-- A real quadratic form is anisotropic if and only if it is positive or negative definite.
No finite-dimensionality assumption is needed; on the zero space both alternatives hold. -/
theorem anisotropic_iff_posDef_or_negDef (Q : _root_.QuadraticForm ℝ M) :
    Q.Anisotropic ↔ Q.PosDef ∨ (-Q).PosDef := by
  constructor
  · intro hQ
    have hsign (x y : M) (hx : 0 < Q x) (hy : Q y < 0) : False := by
      let f : ℝ → ℝ := fun t ↦
        (1 - t) ^ 2 * Q x + t ^ 2 * Q y + (1 - t) * t * polar Q x y
      have hf (t : ℝ) : Q ((1 - t) • x + t • y) = f t := by
        simp only [QuadraticMap.map_add, QuadraticMap.map_smul, polar_smul_left,
          polar_smul_right, smul_eq_mul, f, pow_two]
        ring
      have hcont : Continuous f := by fun_prop
      have hinterval : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := by
        simpa [f] using And.intro hy.le hx.le
      obtain ⟨t, -, ht⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
        hcont.continuousOn hinterval
      have ht1 : t ≠ 1 := by
        intro h
        have : Q y = 0 := by simpa [f, h] using ht
        exact hy.ne this
      have hz := hQ _ ((hf t).trans ht)
      have heq := congrArg Q (eq_neg_of_add_eq_zero_left hz)
      simp only [QuadraticMap.map_smul, QuadraticMap.map_neg, smul_eq_mul] at heq
      have hpos := mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm ht1))) hx
      have hneg := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) hy.le
      nlinarith
    by_cases hn : ∀ x, 0 ≤ Q x
    · exact Or.inl (posDef_of_nonneg hn hQ)
    · push Not at hn
      obtain ⟨y, hy⟩ := hn
      refine Or.inr (posDef_of_nonneg (fun x ↦ ?_) (fun x hx ↦ hQ x ?_))
      · simp only [neg_apply, neg_nonneg]
        exact le_of_not_gt fun hx ↦ hsign x y hx hy
      · simpa using hx
  · rintro (hQ | hQ)
    · exact hQ.anisotropic
    · exact fun x hx ↦ hQ.anisotropic x (by simpa using hx)

end Definiteness

section Fibers

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- The positive index of inertia of a sign-weighted sum of squares counts the weights `1`. -/
theorem sigPos_weightedSumSquares_signType (u : ι → SignType) :
    sigPos (weightedSumSquares ℝ fun i ↦ ((u i : ℝ))) = {i | u i = 1}.ncard := by
  rw [sigPos_weightedSumSquares]
  congr 1
  ext i
  cases h : u i <;> simp [h]

/-- The negative index of inertia of a sign-weighted sum of squares counts the weights `-1`. -/
theorem sigNeg_weightedSumSquares_signType (u : ι → SignType) :
    sigNeg (weightedSumSquares ℝ fun i ↦ ((u i : ℝ))) = {i | u i = -1}.ncard := by
  rw [sigNeg_weightedSumSquares]
  congr 1
  ext i
  cases h : u i <;> simp [h]

/-- Two sign-weighted sums of squares are isometric as soon as each of the three weights occurs
the same number of times in both. -/
private theorem equivalent_weightedSumSquares_of_ncard_fiber_eq (u : ι → SignType)
    (u' : ι' → SignType) (h : ∀ s : SignType, {i | u i = s}.ncard = {i' | u' i' = s}.ncard) :
    Equivalent (weightedSumSquares ℝ fun i ↦ ((u i : ℝ)))
      (weightedSumSquares ℝ fun i' ↦ ((u' i' : ℝ))) := by
  have hfiber : ∀ s : SignType, {i // u i = s} ≃ {i' // u' i' = s} := fun s ↦ by
    refine (Fintype.card_eq.mp ?_).some
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact h s
  let σ : ι ≃ ι' := Equiv.ofFiberEquiv hfiber
  have hσ : ∀ i, u' (σ i) = u i := fun i ↦ Equiv.ofFiberEquiv_map hfiber i
  have hcomp : (fun i' ↦ ((u' i' : ℝ))) ∘ σ = fun i ↦ ((u i : ℝ)) := by
    funext i
    exact congrArg (fun s : SignType ↦ ((s : ℝ))) (hσ i)
  exact equivalent_weightedSumSquares_of_comp_eq σ hcomp

end Fibers

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
    refine hu.trans ((equivalent_weightedSumSquares_of_ncard_fiber_eq u u' ?_).trans hu'.symm)
    have hposFiber : {i | u i = 1}.ncard = {i' | u' i' = 1}.ncard := by
      rw [← sigPos_weightedSumSquares_signType, ← sigPos_weightedSumSquares_signType,
        ← hu.sigPos_eq, ← hu'.sigPos_eq, hpos]
    have hnegFiber : {i | u i = -1}.ncard = {i' | u' i' = -1}.ncard := by
      rw [← sigNeg_weightedSumSquares_signType, ← sigNeg_weightedSumSquares_signType,
        ← hu.sigNeg_eq, ← hu'.sigNeg_eq, hneg]
    have hsum := SignType.ncard_fiber_zero_add_ncard_fiber_neg_add_ncard_fiber_pos u
    have hsum' := SignType.ncard_fiber_zero_add_ncard_fiber_neg_add_ncard_fiber_pos u'
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hsum hsum'
    have hzeroFiber : {i | u i = 0}.ncard = {i' | u' i' = 0}.ncard := by omega
    intro s
    cases s
    · exact hzeroFiber
    · exact hnegFiber
    · exact hposFiber

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

/-- The normal form is the weighted sum of squares with `p` positive and `q` negative weights. -/
theorem realSignatureForm_def (p q : ℕ) :
    realSignatureForm p q =
      weightedSumSquares ℝ (Sum.elim (fun _ ↦ (1 : ℝ)) fun _ ↦ -1) := (rfl)

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

/-- A regular real quadratic form is isometric to the normal form of signature `(p, q)` exactly
when its positive and negative indices are `p` and `q`. -/
@[simp]
theorem equivalent_realSignatureForm_iff_sigPos_eq_and_sigNeg_eq
    {Q : _root_.QuadraticForm ℝ M} (hQ : Q.Nondegenerate) (p q : ℕ) :
    Q.Equivalent (realSignatureForm p q) ↔ sigPos Q = p ∧ sigNeg Q = q := by
  rw [equivalent_iff_sigPos_eq_and_sigNeg_eq hQ (nondegenerate_realSignatureForm p q)]
  simp

/-- Two normal forms are isometric exactly when their signatures coincide, so the signature is a
complete and independent system of invariants for regular real quadratic forms. -/
theorem equivalent_realSignatureForm_iff (p q p' q' : ℕ) :
    (realSignatureForm p q).Equivalent (realSignatureForm p' q') ↔ p = p' ∧ q = q' := by
  rw [equivalent_realSignatureForm_iff_sigPos_eq_and_sigNeg_eq
    (nondegenerate_realSignatureForm p q)]
  simp

/-- Every regular real quadratic form is isometric to the normal form of its signature. -/
theorem equivalent_realSignatureForm (Q : _root_.QuadraticForm ℝ M) (hQ : Q.Nondegenerate) :
    Q.Equivalent (realSignatureForm (sigPos Q) (sigNeg Q)) :=
  (equivalent_realSignatureForm_iff_sigPos_eq_and_sigNeg_eq hQ _ _).mpr ⟨rfl, rfl⟩

/-- Every signature `(p, n - p)` with `p ≤ n` is the signature of a regular quadratic form on the
coordinate space `ℝⁿ`: the normal form `realSignatureForm p (n - p)` transported along a bijection
of its index type with `Fin n`. -/
theorem exists_nondegenerate_and_sigPos_eq_and_sigNeg_eq {n p : ℕ} (h : p ≤ n) :
    ∃ Q : _root_.QuadraticForm ℝ (Fin n → ℝ),
      Q.Nondegenerate ∧ sigPos Q = p ∧ sigNeg Q = n - p := by
  let e : Fin n ≃ Fin p ⊕ Fin (n - p) :=
    (finCongr (Nat.add_sub_cancel' h)).symm.trans finSumFinEquiv.symm
  obtain ⟨f⟩ : (weightedSumSquares ℝ ((Sum.elim (fun _ ↦ (1 : ℝ)) fun _ ↦ -1) ∘ e)).Equivalent
      (realSignatureForm p (n - p)) := by
    rw [realSignatureForm_def]
    exact equivalent_weightedSumSquares_of_comp_eq e rfl
  exact ⟨_, f.nondegenerate_iff.mpr (nondegenerate_realSignatureForm p (n - p)),
    by rw [Equivalent.sigPos_eq ⟨f⟩, sigPos_realSignatureForm],
    by rw [Equivalent.sigNeg_eq ⟨f⟩, sigNeg_realSignatureForm]⟩

end QuadraticForm

namespace TauCeti

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {Q : _root_.QuadraticForm ℝ V}

/-- A positive definite real quadratic form is isometric to the standard sum-of-squares form
in its dimension. -/
theorem nonempty_isometryEquiv_toQuadraticForm'_one_of_posDef (hQ : Q.PosDef) :
    Nonempty (Q.IsometryEquiv
      (Matrix.toQuadraticForm' (1 : Matrix (Fin (Module.finrank ℝ V))
        (Fin (Module.finrank ℝ V)) ℝ))) := by
  obtain ⟨w, hw, ⟨e⟩⟩ := Q.equivalent_one_zero_neg_one_weighted_sum_squared
  have hwpos (i : Fin (Module.finrank ℝ V)) : 0 < w i := by
    have h := hQ (e.symm (Pi.single i 1)) (by simp)
    rw [← e.map_app] at h
    simpa [QuadraticMap.weightedSumSquares_apply, Pi.single_apply,
      Finset.sum_ite_eq'] using h
  have hwone : w = 1 := funext fun i ↦ by
    rcases hw i with h | h | h
    · exfalso
      have hp := hwpos i
      norm_num [h] at hp
    · exact False.elim (by simpa [h] using hwpos i)
    · exact h
  have hstandard : QuadraticMap.weightedSumSquares ℝ w =
      Matrix.toQuadraticForm' (1 : Matrix (Fin (Module.finrank ℝ V))
        (Fin (Module.finrank ℝ V)) ℝ) := by
    rw [hwone, weightedSumSquares_eq_toQuadraticForm_diagonal, Matrix.diagonal_one']
  rw [hstandard] at e
  exact ⟨e⟩

end TauCeti
