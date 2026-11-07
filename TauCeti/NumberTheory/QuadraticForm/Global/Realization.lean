/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Classification
import TauCeti.FieldTheory.SquareClassGroup.Real
import TauCeti.NumberTheory.NumberField.SignApproximation
import TauCeti.NumberTheory.QuadraticForm.Global.ArchimedeanSymbol
import TauCeti.NumberTheory.QuadraticForm.Global.ProductFormula
import TauCeti.NumberTheory.QuadraticForm.Global.Rank.One
import TauCeti.NumberTheory.QuadraticForm.Global.Rank.Two
import TauCeti.NumberTheory.QuadraticForm.Global.Rank.Three

/-!
# Realization of admissible global invariant systems

Every admissible system of local invariants over a number field `K` is the system of a regular
global quadratic form: a rank `n ≥ 1`, a global discriminant, finite Hasse signs and real
positive indices satisfying the admissibility conditions are realized by a regular form on
`Kⁿ`. Conversely the system of a regular form of positive rank is admissible, so admissibility
characterizes the systems that arise from forms. Such a form is isometric, at every finite and
real place, to any prescribed family of local forms realizing the system.

Ranks one, two and three are realized directly. In rank `n + 1 ≥ 4`, let `d` represent the
discriminant and choose `c ∈ Kˣ` negative exactly at the real places of positive index zero. If
`Q'` has rank `n`, discriminant `c d`, finite Hasse signs `s_v · (c, c d)_v` and positive index
`p_w` lowered by one at the real places where `c` is positive, then `⟨c⟩ ⊥ Q'` has the system
`I`, by the orthogonal-sum formula for Hasse signs. This complementary system
satisfies the real conditions by the choice of signs of `c`, the small-rank conditions because
`n ≥ 3`, and the product relation by the product formula for `(c, c d)`. So it is admissible and,
by induction, realized by a form `Q'`. The construction uses neither a local-global principle for
isotropy or representation nor O'Meara's correction planes.

## Main results

* `GlobalFormInvariants.IsAdmissible.exists_globalForm`: every admissible system is the system of
  a regular form on `Fin I.rank → K`.
* `GlobalFormInvariants.isAdmissible_iff_exists_globalForm`: a system is admissible exactly when
  its rank is positive and it is the system of a regular form.
* `GlobalFormInvariants.IsAdmissible.exists_globalForm_equivalent_at_places`: the realizing form
  can be taken isometric at every finite and real place to any prescribed local realization of
  the system.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 72:1.
* J.-P. Serre, *A Course in Arithmetic*, Springer (1973), Chapter IV, §3.3, the same existence
  theorem over `ℚ`, proved by induction on the rank.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap TauCeti

namespace TauCeti.NumberField.QuadraticForm.GlobalFormInvariants

variable {K : Type} [Field K] [NumberField K]

/-- The system complementary to the line `⟨c⟩` in a system `I` whose discriminant is the class
of `d`: rank `n - 1`, discriminant the class of `c d`, finite Hasse signs `s_v · (c, c d)_v`, and
positive indices lowered by one at the real places where `c` is positive. -/
private noncomputable def complementLine (I : GlobalFormInvariants K) (c d : Kˣ) :
    GlobalFormInvariants K where
  rank := I.rank - 1
  discr := squareClass (c * d)
  finiteHasse v :=
    I.finiteHasse v * hilbertSymbol (v.unitAtFinitePlace c) (v.unitAtFinitePlace (c * d))
  realPositiveIndex w := by
    classical
    exact if 0 < embedding_of_isReal w.2 (c : K) then I.realPositiveIndex w - 1
      else I.realPositiveIndex w

variable {I : GlobalFormInvariants K} {c d : Kˣ}

section complementLine

variable (hc : ∀ w : {w : InfinitePlace K // w.IsReal},
    embedding_of_isReal w.2 (c : K) < 0 ↔ I.realPositiveIndex w = 0)
include hc

/-- Where `c` is positive the positive index of `I` is nonzero. -/
private theorem realPositiveIndex_ne_zero_of_pos {w : {w : InfinitePlace K // w.IsReal}}
    (hw : 0 < embedding_of_isReal w.2 (c : K)) : I.realPositiveIndex w ≠ 0 :=
  fun h => hw.not_gt ((hc w).mpr h)

/-- Where `c` is not positive the positive index of `I` is zero. -/
private theorem realPositiveIndex_eq_zero_of_not_pos {w : {w : InfinitePlace K // w.IsReal}}
    (hw : ¬0 < embedding_of_isReal w.2 (c : K)) : I.realPositiveIndex w = 0 := by
  refine (hc w).mp (lt_of_le_of_ne (not_lt.mp hw) ?_)
  rw [← unitAtRealPlace_apply]
  exact (unitAtRealPlace w c).ne_zero

/-- Where `c` is not positive the negative index of `I` is its rank, which is a successor. -/
private theorem exists_realNegativeIndex_eq_add_one_of_not_pos (hI : I.IsAdmissible)
    {w : {w : InfinitePlace K // w.IsReal}} (hw : ¬0 < embedding_of_isReal w.2 (c : K)) :
    ∃ m, I.realNegativeIndex w = m + 1 := by
  refine ⟨I.rank - 1, ?_⟩
  have := hI.one_le_rank
  simp only [realNegativeIndex_def, realPositiveIndex_eq_zero_of_not_pos hc hw]
  omega

/-- The negative index of the complementary system is that of `I` where `c` is positive, and
one less where `c` is negative. -/
private theorem realNegativeIndex_complementLine (hI : I.IsAdmissible)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (complementLine I c d).realNegativeIndex w =
      if 0 < embedding_of_isReal w.2 (c : K) then I.realNegativeIndex w
        else I.realNegativeIndex w - 1 := by
  have hp := hI.realPositiveIndex_le_rank w
  simp only [realNegativeIndex_def, complementLine]
  split_ifs with hw
  · have := realPositiveIndex_ne_zero_of_pos hc hw
    omega
  · omega

/-- The real Hasse sign of the complementary system is `h_w(I) · (c, c d)_w`. -/
private theorem realHasse_complementLine (hI : I.IsAdmissible) (hd : squareClass d = I.discr)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (complementLine I c d).realHasse w =
      I.realHasse w * hilbertSymbol (unitAtRealPlace w c) (unitAtRealPlace w (c * d)) := by
  rw [realHasse_def, realHasse_def, realNegativeIndex_complementLine hc hI]
  split_ifs with hw
  · rw [(hilbertSymbol_unitAtRealPlace_eq_one_iff w c (c * d)).mpr (Or.inl hw), mul_one]
  · -- Here `p_w = 0`, so the negative index of `I` is the rank `m + 1`, and `(c, c d)_w` is
    -- `-1` exactly when `d` is positive, that is, when `m` is odd.
    have hp := realPositiveIndex_eq_zero_of_not_pos hc hw
    have hcn : embedding_of_isReal w.2 (c : K) < 0 := (hc w).mpr hp
    obtain ⟨m, hm⟩ := exists_realNegativeIndex_eq_add_one_of_not_pos hc hI hw
    have hdn : embedding_of_isReal w.2 (d : K) < 0 ↔ Even m := by
      rw [hI.embedding_of_isReal_neg_iff_odd hd w, hm, Nat.odd_add_one, Nat.not_odd_iff_even]
    have hd0 : embedding_of_isReal w.2 (d : K) ≠ 0 := by
      rw [← unitAtRealPlace_apply]
      exact (unitAtRealPlace w d).ne_zero
    have hsymb : hilbertSymbol (unitAtRealPlace w c) (unitAtRealPlace w (c * d)) = (-1) ^ m := by
      rcases Nat.even_or_odd m with he | ho
      · rw [he.neg_one_pow, hilbertSymbol_unitAtRealPlace_eq_one_iff]
        simpa using Or.inr (mul_pos_of_neg_of_neg hcn (hdn.mpr he))
      · rw [ho.neg_one_pow, hilbertSymbol_unitAtRealPlace_eq_neg_one_iff]
        have hdp : 0 < embedding_of_isReal w.2 (d : K) :=
          lt_of_le_of_ne (not_lt.mp (hdn.not.mpr (Nat.not_even_iff_odd.mpr ho))) hd0.symm
        simpa using ⟨hcn, mul_neg_of_neg_of_pos hcn hdp⟩
    have hch : (m + 1).choose 2 = m.choose 2 + m := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    have hsq : (-1 : ℤˣ) ^ m * (-1) ^ m = 1 := by rw [← mul_pow, Int.units_mul_self, one_pow]
    rw [hm, Nat.add_sub_cancel, hsymb, hch, pow_add, mul_assoc, hsq, mul_one]

/-- The real discriminant condition holds for the complementary system. -/
private theorem discrAtRealPlace_complementLine (hI : I.IsAdmissible)
    (hd : squareClass d = I.discr) (w : {w : InfinitePlace K // w.IsReal}) :
    (complementLine I c d).discrAtRealPlace w =
      (complementLine I c d).realNegativeIndex w • squareClass (-1 : ℝˣ) := by
  have h := hI.discrAtRealPlace_eq w
  rw [discrAtRealPlace_def, ← hd, squareClassMap_embedding_of_isReal_squareClass] at h
  rw [realNegativeIndex_complementLine hc hI, discrAtRealPlace_def]
  simp only [complementLine]
  rw [squareClassMap_embedding_of_isReal_squareClass, map_mul, squareClass_mul, h]
  split_ifs with hw
  · rw [(Units.squareClass_eq_zero_iff_pos _).mpr (by simpa using hw)]
    exact zero_add (I.realNegativeIndex w • squareClass (-1 : ℝˣ))
  · have hcn : embedding_of_isReal w.2 (c : K) < 0 :=
      (hc w).mpr (realPositiveIndex_eq_zero_of_not_pos hc hw)
    obtain ⟨m, hm⟩ := exists_realNegativeIndex_eq_add_one_of_not_pos hc hI hw
    have hc1 : squareClass (unitAtRealPlace w c) = squareClass (-1 : ℝˣ) :=
      (Units.squareClass_eq_squareClass_neg_one_iff_neg _).mpr (by simpa using hcn)
    have h2 : squareClass (-1 : ℝˣ) + (m + 1) • squareClass (-1 : ℝˣ) =
        m • squareClass (-1 : ℝˣ) := by
      rw [← squareClass_pow, ← squareClass_pow, ← squareClass_mul, squareClass_eq_iff_isSquare_mul]
      exact ⟨(-1) ^ (m + 1), Units.ext (by push_cast; ring)⟩
    rw [hc1, hm, Nat.add_sub_cancel, h2]

/-- **The complementary system is admissible.** -/
private theorem isAdmissible_complementLine (hI : I.IsAdmissible) (hd : squareClass d = I.discr)
    (hn : 4 ≤ I.rank) : (complementLine I c d).IsAdmissible := by
  classical
  have h3 : 3 ≤ (complementLine I c d).rank := by
    simp only [complementLine]
    omega
  refine ⟨by omega, fun w => ?_, fun w => ?_, ?_, fun h => by omega, fun h => by omega, ?_⟩
  · have hp := hI.realPositiveIndex_le_rank w
    simp only [complementLine]
    split_ifs with hw
    · omega
    · rw [realPositiveIndex_eq_zero_of_not_pos hc hw]
      exact Nat.zero_le _
  · exact discrAtRealPlace_complementLine hc hI hd w
  · exact hI.hasFiniteMulSupport_finiteHasse.mul
      (hasFiniteMulSupport_hilbertSymbol_unitAtFinitePlace c (c * d))
  · rw [hasseProduct_def, Finset.prod_congr rfl fun w _ => realHasse_complementLine hc hI hd w,
      Finset.prod_mul_distrib]
    simp only [complementLine]
    rw [finprod_mul_distrib hI.hasFiniteMulSupport_finiteHasse
      (hasFiniteMulSupport_hilbertSymbol_unitAtFinitePlace c (c * d))]
    calc
      _ = I.hasseProduct *
          ((∏ᶠ v : HeightOneSpectrum (𝓞 K),
            hilbertSymbol (v.unitAtFinitePlace c) (v.unitAtFinitePlace (c * d))) *
            ∏ w, hilbertSymbol (unitAtRealPlace w c) (unitAtRealPlace w (c * d))) := by
        rw [hasseProduct_def]
        ac_rfl
      _ = 1 := by rw [hI.hasseProduct_eq_one, hilbertSymbol_productFormula, one_mul]

end complementLine

/-- **Splitting off a line.** If `Q'` realizes the system complementary to `⟨c⟩` in `I`, then
`⟨c⟩ ⊥ Q'` realizes `I`. -/
private theorem globalInvariants_prod_complementLine (hd : squareClass d = I.discr)
    (hn : 1 ≤ I.rank) (hc : ∀ w : {w : InfinitePlace K // w.IsReal},
      embedding_of_isReal w.2 (c : K) < 0 ↔ I.realPositiveIndex w = 0)
    {Q' : _root_.QuadraticForm K (Fin (complementLine I c d).rank → K)} (hQ' : Q'.Nondegenerate)
    (hQI : Q'.globalInvariants hQ' = complementLine I c d) :
    letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    _root_.QuadraticForm.globalInvariants ((presentedForm ⟨1, fun _ => c⟩).prod Q')
        ((nondegenerate_presentedForm _).prod hQ') = I := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  have hL1 : Module.finrank K (Fin 1 → K) ≤ 1 := by simp
  have hLd : RegularFormClass.discr (formClass _ (nondegenerate_presentedForm ⟨1, fun _ => c⟩)) =
      squareClass c := by
    rw [formClass_presentedForm, RegularFormClass.discr_mk, Fin.prod_univ_one]
  have hQd : RegularFormClass.discr (formClass Q' hQ') = squareClass (c * d) := by
    rw [← _root_.QuadraticForm.globalInvariants_discr, hQI]
    simp only [complementLine]
  have hcd : squareClass c + squareClass (c * d) = I.discr := by
    rw [← hd, ← squareClass_mul, squareClass_eq_iff_isSquare_mul]
    exact ⟨c * d, Units.ext (by push_cast; ring)⟩
  refine GlobalFormInvariants.ext ?_ ?_ (funext fun v => ?_) (funext fun w => ?_)
  · rw [_root_.QuadraticForm.globalInvariants_rank, Module.finrank_prod, Module.finrank_fin_fun,
      Module.finrank_fin_fun]
    simp only [complementLine]
    omega
  · rw [_root_.QuadraticForm.globalInvariants_discr,
      formClass_prod _ (nondegenerate_presentedForm _) Q' hQ', RegularFormClass.discr_add,
      hLd, hQd, hcd]
  · have hv := congrFun (congrArg GlobalFormInvariants.finiteHasse hQI) v
    rw [_root_.QuadraticForm.globalInvariants_finiteHasse] at hv ⊢
    -- The local image of a global square class is the class of the localized unit.
    have hloc (x : Kˣ) : (algebraMap K (v.adicCompletion K)).squareClassMap (squareClass x) =
        squareClass (v.unitAtFinitePlace x) :=
      (RingHom.squareClassMap_apply _ x).trans (congrArg squareClass (Units.ext (by simp)))
    rw [_root_.QuadraticForm.finiteHasse_prod _ (nondegenerate_presentedForm _) Q' hQ', hv, hLd,
      hQd, _root_.QuadraticForm.finiteHasse_eq_one_of_finrank_le_one _ _ hL1, one_mul, hloc,
      hloc, hilbertSymbolOnSquareClasses_squareClass]
    -- The symbol `(c, c d)_v` is a sign, so it cancels against itself.
    simp only [complementLine, mul_assoc, Int.units_mul_self, mul_one]
  · have hw := congrFun (congrArg GlobalFormInvariants.realPositiveIndex hQI) w
    rw [_root_.QuadraticForm.globalInvariants_realPositiveIndex] at hw ⊢
    rw [_root_.QuadraticForm.realPositiveIndex_prod, hw, presentedForm_eq_weightedSumSquares_coe,
      _root_.QuadraticForm.realPositiveIndex_weightedSumSquares]
    simp only [complementLine]
    split_ifs with hpos
    · have := realPositiveIndex_ne_zero_of_pos hc hpos
      simp only [hpos, Set.ofPred_true, Set.ncard_univ, Nat.card_eq_fintype_card,
        Fintype.card_unique]
      omega
    · simp only [hpos, Set.ofPred_false, Set.ncard_empty, zero_add]

/-- Admissible systems of rank `n + 3` are realized, by induction on `n`: the rank-three case
is the ternary construction, and a system of higher rank is `⟨c⟩` plus its complementary
system. -/
private theorem exists_globalForm_of_rank_eq_add_three :
    ∀ (n : ℕ) {I : GlobalFormInvariants K}, I.IsAdmissible → I.rank = n + 3 →
      ∃ (Q : _root_.QuadraticForm K (Fin I.rank → K)) (hQ : Q.Nondegenerate),
        Q.globalInvariants hQ = I
  | 0, I, hI, hn => by
    obtain ⟨Q, hQ, hQI⟩ := hI.exists_globalForm_of_rank_eq_three hn
    exact exists_globalForm_of_globalInvariants_eq hQ hQI
  | n + 1, I, hI, hn => by
    obtain ⟨d, hd⟩ : ∃ d : Kˣ, squareClass d = I.discr :=
      ⟨Additive.toMul (Quotient.out I.discr), squareClass_toMul_out _⟩
    obtain ⟨x, hx0, hx⟩ :=
      _root_.NumberField.exists_ne_zero_neg_iff_mem {w | I.realPositiveIndex w = 0}
    have hc : ∀ w : {w : InfinitePlace K // w.IsReal},
        embedding_of_isReal w.2 ((Units.mk0 x hx0 : Kˣ) : K) < 0 ↔ I.realPositiveIndex w = 0 :=
      fun w => by rw [Units.val_mk0]; exact hx w
    have hI' := isAdmissible_complementLine hc hI hd (by omega)
    obtain ⟨Q', hQ', hQI'⟩ := exists_globalForm_of_rank_eq_add_three n hI'
      (by simp only [complementLine]; omega)
    exact exists_globalForm_of_globalInvariants_eq ((nondegenerate_presentedForm _).prod hQ')
      (globalInvariants_prod_complementLine hd (by omega) hc hQ' hQI')

/-- **Realization of admissible systems.** Every admissible system of local invariants over a
number field is the system of a regular global form on `Fin I.rank → K`. -/
theorem IsAdmissible.exists_globalForm (hI : I.IsAdmissible) :
    ∃ (Q : _root_.QuadraticForm K (Fin I.rank → K)) (hQ : Q.Nondegenerate),
      Q.globalInvariants hQ = I := by
  have h1 := hI.one_le_rank
  obtain h | h | ⟨n, h⟩ : I.rank = 1 ∨ I.rank = 2 ∨ ∃ n, I.rank = n + 3 := by
    rcases Nat.lt_or_ge I.rank 3 with h | h
    · omega
    · exact Or.inr (Or.inr ⟨I.rank - 3, by omega⟩)
  · obtain ⟨Q, hQ, hQI⟩ := hI.exists_globalForm_of_rank_eq_one h
    exact exists_globalForm_of_globalInvariants_eq hQ hQI
  · obtain ⟨Q, hQ, hQI⟩ := hI.exists_form_globalInvariants_eq_of_rank_eq_two h
    exact exists_globalForm_of_globalInvariants_eq hQ hQI
  · exact exists_globalForm_of_rank_eq_add_three n hI h

/-- **Admissibility characterizes the systems of regular forms.** A system of local invariants
over a number field is admissible exactly when its rank is positive and it is the system of a
regular global form on `Fin I.rank → K`. -/
theorem isAdmissible_iff_exists_globalForm (I : GlobalFormInvariants K) :
    I.IsAdmissible ↔ 1 ≤ I.rank ∧
      ∃ (Q : _root_.QuadraticForm K (Fin I.rank → K)) (hQ : Q.Nondegenerate),
        Q.globalInvariants hQ = I := by
  refine ⟨fun hI => ⟨hI.one_le_rank, hI.exists_globalForm⟩, ?_⟩
  rintro ⟨hn, Q, hQ, hQI⟩
  rw [← hQI]
  exact Q.isAdmissible_globalInvariants hQ (by simpa using hn)

/-- **Existence with prescribed local behavior for admissible systems.** An admissible system
has a regular global realization on `Fin I.rank → K` that is isometric at every finite and real
place to any prescribed local realization of the system. -/
theorem IsAdmissible.exists_globalForm_equivalent_at_places (hI : I.IsAdmissible)
    {U : ∀ v : HeightOneSpectrum (𝓞 K),
      _root_.QuadraticForm (v.adicCompletion K) (Fin I.rank → v.adicCompletion K)}
    {R : {w : InfinitePlace K // w.IsReal} → _root_.QuadraticForm ℝ (Fin I.rank → ℝ)}
    (hL : I.IsLocalRealization U R) :
    ∃ (Q : _root_.QuadraticForm K (Fin I.rank → K)) (hQ : Q.Nondegenerate),
      Q.globalInvariants hQ = I ∧
      (∀ v, (Q.atFinitePlace v).Equivalent (U v)) ∧
      ∀ w, (Q.atRealPlace w).Equivalent (R w) := by
  obtain ⟨Q, hQ, hQI⟩ := hI.exists_globalForm
  exact ⟨Q, hQ, hQI, hL.equivalent_atFinitePlace hQI, hL.equivalent_atRealPlace hQI⟩

end TauCeti.NumberField.QuadraticForm.GlobalFormInvariants
