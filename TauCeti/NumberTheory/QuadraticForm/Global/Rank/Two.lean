/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Classification
import TauCeti.NumberTheory.QuadraticForm.Global.CorrectionPlanes
import TauCeti.NumberTheory.QuadraticForm.Global.ProductFormula
import TauCeti.NumberTheory.QuadraticForm.Global.SignPrescription

/-!
# Realization of binary global invariant systems

Every admissible rank-two system over a number field is realized by a regular binary form.
For a representative `d` of its plain discriminant, Hilbert sign prescription supplies `a`
and the form is `⟨a, ad⟩`, written as the scaled norm plane `⟨a, -ab⟩` with `b = -d`.
The binary local realization exception ensures that `b` is nonsquare at each finite place
where a negative Hasse sign is prescribed. At real places the discriminant and the Hasse
sign distinguish the three possible signatures.

This construction does not use a local-global theorem for isotropy or representation.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 71:19a and 72:1.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap TauCeti

namespace TauCeti.NumberField.QuadraticForm.GlobalFormInvariants

variable {K : Type} [Field K] [NumberField K] {I : GlobalFormInvariants K}

/-- An admissible binary system prescribes the Hilbert symbols of one scaled norm plane.
The second argument is the negative of a representative of the plain discriminant. -/
theorem IsAdmissible.exists_hilbertSymbol_eq_of_rank_eq_two
    (hI : I.IsAdmissible) (hn : I.rank = 2) (d : Kˣ) (hd : squareClass d = I.discr) :
    ∃ a : Kˣ,
      (∀ v, hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace (-d)) = I.finiteHasse v) ∧
      ∀ w, hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w (-d)) = I.realHasse w := by
  classical
  let S := hI.hasFiniteMulSupport_finiteHasse.toFinset
  let T := Finset.univ.filter fun w => I.realHasse w ≠ 1
  have hS (v) : v ∈ S ↔ I.finiteHasse v ≠ 1 := Set.Finite.mem_toFinset _
  have hT (w) : w ∈ T ↔ I.realHasse w ≠ 1 := by simp [T]
  have hs (v) : I.finiteHasse v = if v ∈ S then -1 else 1 := by
    rcases Int.units_eq_one_or (I.finiteHasse v) with h | h <;> simp [hS, h]
  have ht (w) : I.realHasse w = if w ∈ T then -1 else 1 := by
    rcases Int.units_eq_one_or (I.realHasse w) with h | h <;>
      simp only [hT, h] <;> norm_num
  have heven : Even (S.card + T.card) := by
    have hp := hI.prod_finiteHasse_mul_prod_realHasse_eq_one
      (S := S) (fun v hv => (hS v).mpr hv)
    have hpS : (∏ v ∈ S, I.finiteHasse v) = (-1 : ℤˣ) ^ S.card := by
      simp_rw [hs]
      simp
    have hpT : (∏ w, I.realHasse w) = (-1 : ℤˣ) ^ T.card := by
      simp_rw [ht]
      simp
    rw [hpS, hpT, ← pow_add] at hp
    exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).mp hp
  have hfinite (v) (hv : v ∈ S) : ¬IsSquare (v.unitAtFinitePlace (-d)) := by
    intro hsq
    have heq : I.discrAtFinitePlace v = squareClass (-1) := by
      rw [discrAtFinitePlace_def, ← hd, RingHom.squareClassMap_apply,
        squareClass_eq_iff_isSquare_mul]
      have he : Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom d * (-1) =
          v.unitAtFinitePlace (-d) := Units.ext (by simp)
      rwa [he]
    exact (hS v).mp hv (hI.finiteHasse_eq_one_of_rank_eq_two hn v heq)
  have hreal (w) (hw : w ∈ T) : embedding_of_isReal w.2 (-d : Kˣ) < 0 := by
    have hzero := (I.realHasse_ne_one_iff_realPositiveIndex_eq_zero_of_rank_eq_two hn w).mp
      ((hT w).mp hw)
    have hdisc := hI.discrAtRealPlace_eq w
    have hdpos : squareClass (Units.map (embedding_of_isReal w.2).toMonoidHom d) = 0 := by
      simpa [discrAtRealPlace_def, ← hd, realNegativeIndex_def, hn, hzero,
        ← squareClass_pow] using hdisc
    have hpos := (Units.squareClass_eq_zero_iff_pos _).mp hdpos
    simpa using neg_neg_of_pos hpos
  obtain ⟨a, haS, haT⟩ := exists_hilbertSymbol_eq_ite (-d) S T hfinite hreal heven
  exact ⟨a, fun v => (haS v).trans (hs v).symm, fun w => (haT w).trans (ht w).symm⟩

/-- Every admissible system of rank two is the invariant system of a regular binary form. -/
theorem IsAdmissible.exists_form_globalInvariants_eq_of_rank_eq_two
    (hI : I.IsAdmissible) (hn : I.rank = 2) :
    ∃ (Q : _root_.QuadraticForm K (Fin 2 → K)) (hQ : Q.Nondegenerate),
      Q.globalInvariants hQ = I := by
  classical
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let d : Kˣ := Additive.toMul (Quotient.out I.discr)
  have hd : squareClass d = I.discr := squareClass_toMul_out _
  obtain ⟨a, haS, haT⟩ := hI.exists_hilbertSymbol_eq_of_rank_eq_two hn d hd
  let Q : _root_.QuadraticForm K (Fin 2 → K) :=
    weightedSumSquares K ![(a : K), -(a * (-d) : K)]
  have hQ : Q.Nondegenerate :=
    _root_.QuadraticForm.nondegenerate_weightedSumSquares_neg_self_mul a (-d)
  -- The scaled norm plane has the prescribed discriminant and finite Hasse signs.
  have hdiscr : (Q.globalInvariants hQ).discr = I.discr := by
    rw [_root_.QuadraticForm.globalInvariants_discr]
    simpa only [Units.val_neg, neg_neg, hd] using
      (_root_.QuadraticForm.discr_formClass_weightedSumSquares_neg_self_mul a (-d)).trans
        (_root_.QuadraticForm.discr_formClass_weightedSumSquares_one_neg (-d))
  refine ⟨Q, hQ, GlobalFormInvariants.ext (by simp [hn]) hdiscr (funext fun v => ?_)
    (funext fun w => ?_)⟩
  · rw [_root_.QuadraticForm.globalInvariants_finiteHasse]
    exact (_root_.QuadraticForm.finiteHasse_weightedSumSquares_neg_self_mul a (-d) hQ v).trans
      (haS v)
  · have hhasse : (Q.globalInvariants hQ).realHasse w = I.realHasse w := by
      simpa only [Units.val_neg] using
        (_root_.QuadraticForm.globalInvariants_realHasse_weightedSumSquares_neg_self_mul
          a (-d) hQ w).trans (haT w)
    have hJ := Q.isAdmissible_globalInvariants hQ (by simp)
    have hdisc := hJ.discrAtRealPlace_eq w
    rw [discrAtRealPlace_def, hdiscr, ← discrAtRealPlace_def,
      hI.discrAtRealPlace_eq w] at hdisc
    have hp : I.realPositiveIndex w ≤ 2 := hn ▸ hI.realPositiveIndex_le_rank w
    have hq : (Q.globalInvariants hQ).realPositiveIndex w ≤ 2 := by
      simpa using hJ.realPositiveIndex_le_rank w
    have hnr : (Q.globalInvariants hQ).rank = 2 := by simp
    have hzero : (Q.globalInvariants hQ).realPositiveIndex w = 0 ↔
        I.realPositiveIndex w = 0 := by
      rw [← realHasse_ne_one_iff_realPositiveIndex_eq_zero_of_rank_eq_two _ hnr w,
        ← realHasse_ne_one_iff_realPositiveIndex_eq_zero_of_rank_eq_two _ hn w, hhasse]
    simp only [realNegativeIndex_def, hn, hnr] at hdisc
    -- In rank two the Hasse sign separates index zero, and the discriminant separates one and two.
    interval_cases I.realPositiveIndex w <;>
      interval_cases (Q.globalInvariants hQ).realPositiveIndex w <;> solve
      | rfl
      | norm_num at hzero
      | norm_num [← squareClass_pow, eq_comm] at hdisc

/-- In rank two, admissibility is equivalent to global realization with the prescribed local
isometries. The local forms may be any realization of the given invariant system. -/
theorem isAdmissible_iff_exists_form_globalInvariants_eq_equivalent_at_places_of_rank_eq_two
    (hn : I.rank = 2)
    {U : ∀ v : HeightOneSpectrum (𝓞 K),
      _root_.QuadraticForm (v.adicCompletion K) (Fin I.rank → v.adicCompletion K)}
    {R : {w : InfinitePlace K // w.IsReal} → _root_.QuadraticForm ℝ (Fin I.rank → ℝ)}
    (hL : I.IsLocalRealization U R) :
    I.IsAdmissible ↔ ∃ (Q : _root_.QuadraticForm K (Fin 2 → K)) (hQ : Q.Nondegenerate),
      Q.globalInvariants hQ = I ∧
      (∀ v, (Q.atFinitePlace v).Equivalent (U v)) ∧
      ∀ w, (Q.atRealPlace w).Equivalent (R w) := by
  constructor
  · intro hI
    obtain ⟨Q, hQ, hQI⟩ := hI.exists_form_globalInvariants_eq_of_rank_eq_two hn
    exact ⟨Q, hQ, hQI, hL.equivalent_atFinitePlace hQI, hL.equivalent_atRealPlace hQI⟩
  · rintro ⟨Q, hQ, hQI, -, -⟩
    rw [← hQI]
    exact Q.isAdmissible_globalInvariants hQ (by simp)

end TauCeti.NumberField.QuadraticForm.GlobalFormInvariants
