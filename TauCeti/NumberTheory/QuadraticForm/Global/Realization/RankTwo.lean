/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Classification
import TauCeti.NumberTheory.QuadraticForm.Global.SignPrescription
import TauCeti.NumberTheory.QuadraticForm.Global.ProductFormula

/-!
# Global realization of binary invariants

Every admissible rank-two system over a number field is realized by a regular binary form.
If `δ` represents its plain discriminant, the form is `⟨a, aδ⟩`. Its finite Hasse signs are
`(a, -δ)`, and the same formula holds for its real Hasse signs. Hilbert sign prescription
therefore supplies `a`: the small-rank admissibility condition excludes a negative sign wherever
`-δ` is a square, and the product condition makes the prescribed support even.

At a real place the discriminant and Hasse sign together distinguish the three binary
signatures. Thus the construction realizes the positive indices as well as the finite signs,
and gives the prescribed local isometry classes, without using a local-global isometry or
representation theorem.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 71:19a and 72:1.
* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §§2–3.
-/

public section
noncomputable section

open Finset IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap

namespace TauCeti.NumberField.QuadraticForm.GlobalFormInvariants

variable {K : Type} [Field K] [NumberField K] {I : GlobalFormInvariants K}

/-- An admissible binary system prescribes the Hilbert symbols of a single global pair with
second argument the negative of a representative of its discriminant. -/
private theorem exists_hilbertSymbol_eq_of_rank_eq_two (hI : I.IsAdmissible)
    (hn : I.rank = 2) (δ : Kˣ) (hδ : squareClass δ = I.discr) :
    ∃ a : Kˣ,
      (∀ v : HeightOneSpectrum (𝓞 K),
        hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace (-δ)) = I.finiteHasse v) ∧
      ∀ w : {w : InfinitePlace K // w.IsReal},
        hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w (-δ)) = I.realHasse w := by
  classical
  let S := hI.hasFiniteMulSupport_finiteHasse.toFinset
  let T := univ.filter fun w => I.realHasse w ≠ 1
  have hS (v) : v ∈ S ↔ I.finiteHasse v ≠ 1 := by simp [S, Function.mulSupport]
  have hT (w) : w ∈ T ↔ I.realHasse w ≠ 1 := by simp [T]
  have hs (v) : I.finiteHasse v = if v ∈ S then -1 else 1 := by
    rcases Int.units_eq_one_or (I.finiteHasse v) with h | h <;> simp [hS, h]
  have ht (w) : I.realHasse w = if w ∈ T then -1 else 1 := by
    simp only [hT]
    rcases Int.units_eq_one_or (I.realHasse w) with h | h <;> simp only [h] <;> norm_num
  -- The product relation is exactly the parity condition for sign prescription.
  have heven : Even (S.card + T.card) := by
    have hp := hI.prod_finiteHasse_mul_prod_realHasse_eq_one (S := S)
      (by intro v hv; exact (hS v).mpr hv)
    simp_rw [hs, ht] at hp
    have hp' : (-1 : ℤˣ) ^ (S.card + T.card) = 1 := by
      simpa [prod_ite, pow_add] using hp
    exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).mp hp'
  obtain ⟨a, ha, har⟩ := exists_hilbertSymbol_eq_ite (-δ) S T (fun v hv hsq => by
    apply (hS v).mp hv
    apply hI.finiteHasse_eq_one_of_rank_eq_two hn v
    rw [discrAtFinitePlace_def, ← hδ, RingHom.squareClassMap_apply,
      squareClass_eq_iff_isSquare_mul]
    convert hsq using 1
    apply Units.ext
    simp) (fun w hw => by
    have hh := (hT w).mp hw
    have hd := hI.discrAtRealPlace_eq w
    rw [discrAtRealPlace_def, ← hδ, RingHom.squareClassMap_apply] at hd
    have hneg : I.realNegativeIndex w = 2 := by
      have hle : I.realNegativeIndex w ≤ 2 := by simp [hn]
      by_contra hne
      have hz : (I.realNegativeIndex w).choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
      exact hh (by rw [realHasse_def, hz, pow_zero])
    have hdpos : 0 < embedding_of_isReal w.2 (δ : K) := by
      rw [hneg] at hd
      have heq : Units.map (embedding_of_isReal w.2).toMonoidHom δ =
          unitAtRealPlace w δ := Units.ext (by simp)
      have hz : squareClass (unitAtRealPlace w δ) = 0 := by
        simpa only [heq, ← squareClass_pow, neg_one_sq, squareClass_one] using hd
      simpa only [unitAtRealPlace_apply] using (Units.squareClass_eq_zero_iff_pos _).mp hz
    simpa using neg_neg_of_pos hdpos) heven
  exact ⟨a, fun v => (ha v).trans (hs v).symm, fun w => (har w).trans (ht w).symm⟩

end TauCeti.NumberField.QuadraticForm.GlobalFormInvariants

namespace QuadraticForm

open TauCeti TauCeti.NumberField.QuadraticForm
  TauCeti.NumberField.QuadraticForm.GlobalFormInvariants

variable {K : Type} [Field K] [NumberField K] {I : GlobalFormInvariants K}

/-- The discriminant and real Hasse sign determine the positive index of a regular binary form
at a real place. -/
private theorem realPositiveIndex_eq_of_rank_eq_two (Q : QuadraticForm K (Fin 2 → K))
    (hI : I.IsAdmissible) (hn : I.rank = 2) (hQ : Q.Nondegenerate)
    (hd : RegularFormClass.discr (formClass Q hQ) = I.discr)
    (w : {w : InfinitePlace K // w.IsReal})
    (hh : (Q.globalInvariants hQ).realHasse w = I.realHasse w) :
    Q.realPositiveIndex w = I.realPositiveIndex w := by
  have hsum := _root_.QuadraticForm.realPositiveIndex_add_realNegativeIndex_eq_finrank hQ w
  have hbound := hI.realPositiveIndex_le_rank w
  have hdreal := _root_.QuadraticForm.squareClassMap_discr_formClass_eq_realNegativeIndex_nsmul
    Q hQ w
  rw [hd, ← discrAtRealPlace_def, hI.discrAtRealPlace_eq] at hdreal
  rw [realHasse_def, _root_.QuadraticForm.globalInvariants_realNegativeIndex, realHasse_def,
    realNegativeIndex_def, hn] at hh
  simp only [Module.finrank_fin_fun] at hsum
  rw [hn] at hbound
  have hqbound : Q.realNegativeIndex w ≤ 2 := by omega
  simp only [realNegativeIndex_def, hn] at hdreal
  have hne : squareClass (-1 : ℝˣ) ≠ 0 := by norm_num [Units.isSquare_iff_pos]
  -- Discriminant parity separates the indefinite signature; the Hasse sign separates
  -- the two definite signatures. Close each of the nine cases independently.
  interval_cases Q.realNegativeIndex w <;> interval_cases I.realPositiveIndex w
  · norm_num at hh
  · exact (hne (by simpa [← squareClass_pow] using hdreal)).elim
  · omega
  · exact (hne (by simpa [← squareClass_pow] using hdreal.symm)).elim
  · omega
  · exact (hne (by simpa [← squareClass_pow] using hdreal.symm)).elim
  · omega
  · exact (hne (by simpa [← squareClass_pow] using hdreal)).elim
  · norm_num at hh

end QuadraticForm

namespace TauCeti.NumberField.QuadraticForm.GlobalFormInvariants

variable {K : Type} [Field K] [NumberField K] {I : GlobalFormInvariants K}

/-- Every admissible rank-two system over a number field is the invariant system of a regular
binary form. -/
theorem IsAdmissible.exists_globalForm_of_rank_eq_two (hI : I.IsAdmissible) (hn : I.rank = 2) :
    ∃ (Q : _root_.QuadraticForm K (Fin 2 → K)) (hQ : Q.Nondegenerate),
      Q.globalInvariants hQ = I := by
  classical
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨δ, hδ⟩ : ∃ δ : Kˣ, squareClass δ = I.discr := ⟨_, squareClass_toMul_out _⟩
  obtain ⟨a, ha, har⟩ := exists_hilbertSymbol_eq_of_rank_eq_two hI hn δ hδ
  -- Scaling the norm plane changes its Hasse signs without changing its discriminant.
  let c : Fin 2 → Kˣ := ![a, a * δ]
  let Q : _root_.QuadraticForm K (Fin 2 → K) := weightedSumSquares K fun i => (c i : K)
  have hQ : Q.Nondegenerate := nondegenerate_weightedSumSquares fun i =>
    isRegular_iff_ne_zero.mpr (c i).ne_zero
  have hd : RegularFormClass.discr (formClass Q hQ) = I.discr := by
    rw [discr_formClass_weightedSumSquares c hQ, ← hδ,
      squareClass_eq_iff_isSquare_mul]
    exact ⟨a * δ, by simp [c]; ac_rfl⟩
  have hfinite (v : HeightOneSpectrum (𝓞 K)) : Q.finiteHasse hQ v = I.finiteHasse v := by
    let _ : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    have hc : (fun i => (c i : K)) = ![(a : K), (a * δ : K)] := by
      ext i; fin_cases i <;> simp [c]
    have hh := _root_.QuadraticForm.finiteHasse_weightedSumSquares_binary a (a * δ)
      (by simpa only [Q, hc] using hQ) v
    rw [map_mul, hilbertSymbol_self_mul two_ne_zero] at hh
    have hneg : v.unitAtFinitePlace (-δ) = -(v.unitAtFinitePlace δ) := Units.ext (by simp)
    simpa only [Q, hc, Units.val_mul] using hh.trans (by simpa only [hneg] using ha v)
  have hreal (w : {w : InfinitePlace K // w.IsReal}) :
      (Q.globalInvariants hQ).realHasse w = I.realHasse w := by
    have h0 : Ioi (0 : Fin 2) = {1} := by decide
    have h1 : Ioi (1 : Fin 2) = ∅ := by decide
    rw [_root_.QuadraticForm.globalInvariants_realHasse_eq_prod_hilbertSymbol Q hQ
      (a := c) (.refl _) w, Fin.prod_univ_two, h0, h1]
    simp only [prod_singleton, prod_empty, mul_one, c, Matrix.cons_val_zero,
      Matrix.cons_val_one, map_mul]
    have hs := hilbertSymbol_real_mul_right (unitAtRealPlace w a)
      (-(unitAtRealPlace w a)) (-(unitAtRealPlace w δ))
    simp only [neg_mul_neg, hilbertSymbol_neg_self, one_mul] at hs
    rw [hs]
    have hneg : unitAtRealPlace w (-δ) = -(unitAtRealPlace w δ) := Units.ext (by simp)
    simpa only [hneg] using har w
  refine ⟨Q, hQ, GlobalFormInvariants.ext (by simp [hn]) (by simpa using hd)
    (by simpa using funext hfinite) ?_⟩
  funext w
  rw [_root_.QuadraticForm.globalInvariants_realPositiveIndex]
  exact _root_.QuadraticForm.realPositiveIndex_eq_of_rank_eq_two Q hI hn hQ hd w (hreal w)

/-- For a rank-two system, admissibility is equivalent to realization by a regular global
binary form, including all real positive indices and finite Hasse signs. -/
theorem isAdmissible_iff_exists_globalForm_of_rank_eq_two (hn : I.rank = 2) :
    I.IsAdmissible ↔ ∃ (Q : _root_.QuadraticForm K (Fin 2 → K)) (hQ : Q.Nondegenerate),
      Q.globalInvariants hQ = I := by
  refine ⟨fun hI => hI.exists_globalForm_of_rank_eq_two hn, ?_⟩
  rintro ⟨Q, hQ, rfl⟩
  exact _root_.QuadraticForm.isAdmissible_globalInvariants Q hQ (by simp)

/-- An admissible rank-two system has a global realization with the prescribed local
isometry classes, for any family realizing the system locally. -/
theorem IsAdmissible.exists_equivalent_at_places_of_rank_eq_two (hI : I.IsAdmissible)
    (hn : I.rank = 2)
    {U : ∀ v : HeightOneSpectrum (𝓞 K),
      _root_.QuadraticForm (v.adicCompletion K) (Fin I.rank → v.adicCompletion K)}
    {R : {w : InfinitePlace K // w.IsReal} → _root_.QuadraticForm ℝ (Fin I.rank → ℝ)}
    (hL : I.IsLocalRealization U R) :
    ∃ (Q : _root_.QuadraticForm K (Fin 2 → K)) (hQ : Q.Nondegenerate),
      Q.globalInvariants hQ = I ∧
      (∀ v, (Q.atFinitePlace v).Equivalent (U v)) ∧
      ∀ w, (Q.atRealPlace w).Equivalent (R w) := by
  obtain ⟨Q, hQ, hQI⟩ := hI.exists_globalForm_of_rank_eq_two hn
  exact ⟨Q, hQ, hQI, hL.equivalent_atFinitePlace hQI, hL.equivalent_atRealPlace hQI⟩

end TauCeti.NumberField.QuadraticForm.GlobalFormInvariants
