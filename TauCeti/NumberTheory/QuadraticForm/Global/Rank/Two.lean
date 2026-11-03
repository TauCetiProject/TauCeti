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
    have hp := hI.hasseProduct_eq_one
    rw [I.hasseProduct_eq_prod_of_mulSupport_subset
      (S := S) (fun v hv => (hS v).mpr hv)] at hp
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
    have hp : I.realPositiveIndex w ≤ 2 := hn ▸ hI.realPositiveIndex_le_rank w
    have hne := (hT w).mp hw
    have hzero : I.realPositiveIndex w = 0 := by
      interval_cases h : I.realPositiveIndex w
      · rfl
      · norm_num [realHasse_def, realNegativeIndex_def, hn, h] at hne
      · norm_num [realHasse_def, realNegativeIndex_def, hn, h] at hne
    have hdisc := hI.discrAtRealPlace_eq w
    have hdpos : squareClass (unitAtRealPlace w d) = 0 := by
      simpa [discrAtRealPlace_def, ← hd, realNegativeIndex_def, hn, hzero,
        ← squareClass_pow] using hdisc
    have hpos := (Units.squareClass_eq_zero_iff_pos _).mp hdpos
    simpa using neg_neg_of_pos hpos
  obtain ⟨a, haS, haT⟩ := exists_hilbertSymbol_eq_ite (-d) S T hfinite hreal heven
  exact ⟨a, fun v => (haS v).trans (hs v).symm, fun w => (haT w).trans (ht w).symm⟩

-- This calculation identifies the signature of the plane used in the construction below.
private theorem realPositiveIndex_plane_eq (hI : I.IsAdmissible) (hn : I.rank = 2)
    (a d : Kˣ) (hd : squareClass d = I.discr) (w : {w : InfinitePlace K // w.IsReal})
    (hsign : hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w (-d)) = I.realHasse w) :
    _root_.QuadraticForm.realPositiveIndex
      (weightedSumSquares K ![(a : K), -(a * (-d) : K)]) w =
      I.realPositiveIndex w := by
    classical
    rw [_root_.QuadraticForm.realPositiveIndex_weightedSumSquares]
    have hp : I.realPositiveIndex w ≤ 2 := hn ▸ hI.realPositiveIndex_le_rank w
    have hdisc := hI.discrAtRealPlace_eq w
    have hdpos (heven : Even (I.realNegativeIndex w)) :
        0 < embedding_of_isReal w.2 (d : K) := by
      have heq : squareClass (Units.map (embedding_of_isReal w.2).toMonoidHom d) =
          I.realNegativeIndex w • squareClass (-1) := by
        simpa only [discrAtRealPlace_def, ← hd, RingHom.squareClassMap_apply] using hdisc
      have hzero : squareClass (Units.map (embedding_of_isReal w.2).toMonoidHom d) = 0 := by
        rw [heq, ← squareClass_pow, heven.neg_one_pow, squareClass_one]
      exact (Units.squareClass_eq_zero_iff_pos _).mp hzero
    have ha0 : embedding_of_isReal w.2 (a : K) ≠ 0 :=
      (map_ne_zero _).mpr a.ne_zero
    -- The three allowed positive indices are separated by discriminant sign and Hasse sign.
    interval_cases h : I.realPositiveIndex w
    · have hdp := hdpos (by simp [realNegativeIndex_def, hn, h])
      have han : embedding_of_isReal w.2 (a : K) < 0 := by
        have hh : hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w (-d)) = -1 := by
          simpa [realHasse_def, realNegativeIndex_def, hn, h] using hsign
        exact ((hilbertSymbol_unitAtRealPlace_eq_neg_one_iff _ _ _).mp hh).1
      have hprod : embedding_of_isReal w.2 (a : K) * embedding_of_isReal w.2 (d : K) < 0 :=
        mul_neg_of_neg_of_pos han hdp
      have hset : {i | 0 < embedding_of_isReal w.2
          (![(a : K), -(a * (-d) : K)] i)} = ∅ := by
        ext i
        fin_cases i <;> simp [han.not_gt, hprod.not_gt]
      rw [hset, Set.ncard_empty]
    · have hdn : embedding_of_isReal w.2 (d : K) < 0 := by
        have heq : squareClass (Units.map (embedding_of_isReal w.2).toMonoidHom d) =
            squareClass (-1) := by
          simpa only [discrAtRealPlace_def, ← hd, RingHom.squareClassMap_apply,
            realNegativeIndex_def, hn, h, Nat.reduceSub, one_nsmul] using hdisc
        exact (Units.squareClass_eq_squareClass_neg_one_iff_neg _).mp heq
      rcases ha0.lt_or_gt with han | hap
      · have hprod := mul_pos_of_neg_of_neg han hdn
        have hset : {i | 0 < embedding_of_isReal w.2
            (![(a : K), -(a * (-d) : K)] i)} = {1} := by
          ext i
          fin_cases i <;> simp [han.not_gt, hprod]
        rw [hset, Set.ncard_singleton]
      · have hprod := mul_neg_of_pos_of_neg hap hdn
        have hset : {i | 0 < embedding_of_isReal w.2
            (![(a : K), -(a * (-d) : K)] i)} = {0} := by
          ext i
          fin_cases i <;> simp [hap, hprod.not_gt]
        rw [hset, Set.ncard_singleton]
    · have hdp := hdpos (by simp [realNegativeIndex_def, hn, h])
      have hap : 0 < embedding_of_isReal w.2 (a : K) := by
        have hh : hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w (-d)) = 1 := by
          simpa [realHasse_def, realNegativeIndex_def, hn, h] using hsign
        rcases (hilbertSymbol_unitAtRealPlace_eq_one_iff _ _ _).mp hh with ha | hb
        · exact ha
        · simp only [Units.val_neg, map_neg] at hb
          linarith
      have hprod := mul_pos hap hdp
      have hset : {i | 0 < embedding_of_isReal w.2
          (![(a : K), -(a * (-d) : K)] i)} = Set.univ := by
        ext i
        fin_cases i <;> simp [hap, hprod]
      rw [hset, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Every admissible system of rank two is the invariant system of a regular binary form.
No local-global principle for isotropy or representation is needed. -/
theorem IsAdmissible.exists_globalForm_of_rank_eq_two
    (hI : I.IsAdmissible) (hn : I.rank = 2) :
    ∃ (Q : _root_.QuadraticForm K (Fin 2 → K)) (hQ : Q.Nondegenerate),
      Q.globalInvariants hQ = I := by
  classical
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let d : Kˣ := Additive.toMul (Quotient.out I.discr)
  have hd : squareClass d = I.discr := squareClass_toMul_out _
  obtain ⟨a, haS, haT⟩ := hI.exists_hilbertSymbol_eq_of_rank_eq_two hn d hd
  let Q := weightedSumSquares K ![(a : K), -(a * (-d) : K)]
  have hQ : Q.Nondegenerate :=
    _root_.QuadraticForm.nondegenerate_weightedSumSquares_neg_self_mul a (-d)
  refine ⟨Q, hQ, GlobalFormInvariants.ext (by simp [hn]) ?_ (funext fun v => ?_)
    (funext fun w => ?_)⟩
  · have hplane := _root_.QuadraticForm.discr_formClass_weightedSumSquares_neg_self_mul a (-d)
    simp only [Units.val_neg] at hplane
    rw [_root_.QuadraticForm.globalInvariants_discr, hplane]
    have hc : ![1, -((-d : Kˣ) : K)] = fun i => ((![1, d] : Fin 2 → Kˣ) i : K) := by
      ext i
      fin_cases i <;> simp
    have hequiv : (weightedSumSquares K ![1, -((-d : Kˣ) : K)]).Equivalent
        (presentedForm ⟨2, ![1, d]⟩) := by
      rw [presentedForm_eq_weightedSumSquares_coe, ← hc]
    simp only [Units.val_neg] at hequiv
    rw [discr_formClass _ _ ⟨2, ![1, d]⟩ hequiv, Fin.prod_univ_two]
    simpa using hd
  · rw [_root_.QuadraticForm.globalInvariants_finiteHasse]
    exact (_root_.QuadraticForm.finiteHasse_weightedSumSquares_neg_self_mul a (-d) hQ v).trans
      (haS v)
  · rw [_root_.QuadraticForm.globalInvariants_realPositiveIndex]
    exact realPositiveIndex_plane_eq hI hn a d hd w (haT w)

/-- In rank two, admissibility is equivalent to global realization with the prescribed local
isometries. The local forms may be any realization of the given invariant system. -/
theorem isAdmissible_iff_exists_globalForm_equivalent_at_places_of_rank_eq_two
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
    obtain ⟨Q, hQ, hQI⟩ := hI.exists_globalForm_of_rank_eq_two hn
    exact ⟨Q, hQ, hQI, hL.equivalent_atFinitePlace hQI, hL.equivalent_atRealPlace hQI⟩
  · rintro ⟨Q, hQ, hQI, -, -⟩
    rw [← hQI]
    exact Q.isAdmissible_globalInvariants hQ (by simp)

end TauCeti.NumberField.QuadraticForm.GlobalFormInvariants
