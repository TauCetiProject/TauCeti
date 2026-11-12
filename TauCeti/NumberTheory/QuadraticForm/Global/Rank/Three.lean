/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Classification
import TauCeti.NumberTheory.LocalField.QuadraticForm.Brauer
import TauCeti.NumberTheory.QuadraticForm.Global.SignPrescription
import TauCeti.NumberTheory.QuadraticForm.Global.ProductFormula

/-!
# Realizing ternary global invariants

Every admissible rank-three invariant system over a number field is realized by a regular
ternary form. The construction is a scaled pure quaternion norm form
`d⟨-a, -b, ab⟩`, where `d` represents the prescribed plain discriminant. Its finite Hasse sign is
`(a,b) · (-1,-d)`. Hilbert sign prescription supplies `a,b`; at real places the discriminant
and Hasse sign distinguish the four possible signatures of a ternary form.

This gives existence, including local isometries to any family realizing the system, without a
local-global isotropy or representation theorem.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, 71:19 and 72:1.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter V, §3, for pure quaternion
  norm forms and their Hasse invariants.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap TauCeti

namespace TauCeti.NumberField.QuadraticForm.GlobalFormInvariants

variable {K : Type} [Field K] [NumberField K]

private abbrev ternaryPresentation (d a b : Kˣ) : RegularFormPresentation K :=
  ⟨3, fun i => d * ![-a, -b, a * b] i⟩

omit [NumberField K] in
private theorem discr_ternaryPresentation (d a b : Kˣ) [Invertible (2 : K)] :
    RegularFormClass.discr (Quotient.mk (regularFormSetoid K) (ternaryPresentation d a b)) =
      squareClass d := by
  rw [RegularFormClass.discr_mk]
  have hp : (∏ i, (ternaryPresentation d a b).2 i) = d * (d * a * b) ^ 2 := by
    dsimp only [ternaryPresentation]
    rw [Fin.prod_univ_three]
    apply Units.ext
    simp
    ring
  rw [hp, squareClass_mul, squareClass_pow,
    ZModModule.char_nsmul_eq_zero 2 (squareClass (d * a * b))]
  exact add_zero (squareClass d)

private theorem finiteHasse_ternaryPresentation (d a b : Kˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    (presentedForm (ternaryPresentation d a b)).finiteHasse
        (nondegenerate_presentedForm _) v =
      hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) *
        hilbertSymbol (v.unitAtFinitePlace (-1)) (v.unitAtFinitePlace (-d)) := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let _ : Invertible (2 : v.adicCompletion K) := invertibleOfNonzero two_ne_zero
  have hneg (x : Kˣ) : v.unitAtFinitePlace (-x) = -v.unitAtFinitePlace x :=
    Units.ext (by simp)
  have hp : (ternaryPresentation d a b).baseChange (v.adicCompletion K) =
      ⟨3, fun i => v.unitAtFinitePlace d *
        ![-v.unitAtFinitePlace a, -v.unitAtFinitePlace b,
          v.unitAtFinitePlace a * v.unitAtFinitePlace b] i⟩ := by
    rw [RegularFormPresentation.baseChange_def]
    dsimp only [ternaryPresentation]
    congr 1
    funext i
    fin_cases i <;> apply Units.ext <;> simp
  rw [_root_.QuadraticForm.finiteHasse_eq_localHasse_baseChange, formClass_presentedForm,
    RegularFormClass.baseChange_mk, hp,
    RegularFormClass.localHasse_mk_scale _
      ⟨3, ![-v.unitAtFinitePlace a, -v.unitAtFinitePlace b,
        v.unitAtFinitePlace a * v.unitAtFinitePlace b]⟩,
    RegularFormClass.localHasse_mk_neg_neg_mul]
  have h2 : (2 : v.adicCompletion K) ≠ 0 := two_ne_zero
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Nat.choose, Nat.reduceAdd, Nat.reduceSub,
    Int.units_sq, mul_one, hneg, map_one]
  rw [pow_succ, Int.units_sq, one_mul, neg_eq_neg_one_mul (v.unitAtFinitePlace d),
    hilbertSymbol_mul_right h2, hilbertSymbol_comm (v.unitAtFinitePlace d) (-1)]
  ac_rfl

private theorem exists_ternary_symbols (I : GlobalFormInvariants K) (hI : I.IsAdmissible)
    (d : Kˣ) :
    ∃ a b : Kˣ,
      (∀ v : HeightOneSpectrum (𝓞 K),
        hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) =
          I.finiteHasse v *
            hilbertSymbol (v.unitAtFinitePlace (-1)) (v.unitAtFinitePlace (-d))) ∧
      ∀ w : {w : InfinitePlace K // w.IsReal},
        hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) =
          I.realHasse w * hilbertSymbol (unitAtRealPlace w (-1)) (unitAtRealPlace w (-d)) := by
  classical
  let f := fun v : HeightOneSpectrum (𝓞 K) => I.finiteHasse v *
    hilbertSymbol (v.unitAtFinitePlace (-1)) (v.unitAtFinitePlace (-d))
  let g := fun w : {w : InfinitePlace K // w.IsReal} => I.realHasse w *
    hilbertSymbol (unitAtRealPlace w (-1)) (unitAtRealPlace w (-d))
  have hf : Function.HasFiniteMulSupport f :=
    hI.hasFiniteMulSupport_finiteHasse.mul (hasFiniteMulSupport_hilbertSymbol_unitAtFinitePlace _ _)
  let S := hf.toFinset
  let T := Finset.univ.filter fun w => g w ≠ 1
  have hS (v) : f v = if v ∈ S then -1 else 1 := by
    rcases Int.units_eq_one_or (f v) with h | h <;> simp [S, Function.mulSupport, h]
  have hT (w) : g w = if w ∈ T then -1 else 1 := by
    rcases Int.units_eq_one_or (g w) with h | h <;> simp [T, h]
  have hp : (∏ᶠ v, f v) * ∏ w, g w = 1 := by
    rw [finprod_mul_distrib hI.hasFiniteMulSupport_finiteHasse
      (hasFiniteMulSupport_hilbertSymbol_unitAtFinitePlace (-1) (-d)), Finset.prod_mul_distrib]
    calc
      _ = I.hasseProduct *
          ((∏ᶠ v : HeightOneSpectrum (𝓞 K),
            hilbertSymbol (v.unitAtFinitePlace (-1)) (v.unitAtFinitePlace (-d))) *
            ∏ w, hilbertSymbol (unitAtRealPlace w (-1)) (unitAtRealPlace w (-d))) := by
        rw [hasseProduct_def]
        ac_rfl
      _ = 1 := by rw [hI.hasseProduct_eq_one, hilbertSymbol_productFormula]; simp
  have heven : Even (S.card + T.card) := by
    apply (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).mp
    rw [pow_add]
    rw [finprod_eq_prod f hf] at hp
    have hpS : (∏ v ∈ S, f v) = (-1 : ℤˣ) ^ S.card := by
      rw [Finset.prod_congr rfl (fun v hv => (hS v).trans (ite_eq_left hv)), Finset.prod_const]
    have hpT : (∏ w, g w) = (-1 : ℤˣ) ^ T.card := by
      simp_rw [hT]
      rw [Fintype.prod_ite_mem, Finset.prod_const]
    rwa [hpS, hpT] at hp
  obtain ⟨a, b, ha, hb⟩ := exists_pair_hilbertSymbol_eq_ite S T heven
  exact ⟨a, b, fun v => (ha v).trans (hS v).symm, fun w => (hb w).trans (hT w).symm⟩

private theorem realPositiveIndex_ternaryPresentation (I : GlobalFormInvariants K)
    (hI : I.IsAdmissible) (hn : I.rank = 3) (d a b : Kˣ) (hd : squareClass d = I.discr)
    (w : {w : InfinitePlace K // w.IsReal})
    (hab : hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) =
      I.realHasse w * hilbertSymbol (unitAtRealPlace w (-1)) (unitAtRealPlace w (-d))) :
    (presentedForm (ternaryPresentation d a b)).realPositiveIndex w = I.realPositiveIndex w := by
  classical
  have hp := hI.realPositiveIndex_le_rank w
  rw [hn] at hp
  have hdisc := hI.discrAtRealPlace_eq w
  rw [discrAtRealPlace_def, ← hd, realNegativeIndex_def, hn] at hdisc
  have hdisc' : squareClass (unitAtRealPlace w d) =
      (3 - I.realPositiveIndex w) • squareClass (-1 : ℝˣ) := by
    rw [RingHom.squareClassMap_apply] at hdisc
    have hm : Units.map (embedding_of_isReal w.2).toMonoidHom d = unitAtRealPlace w d :=
      Units.ext (by simp)
    rwa [hm] at hdisc
  have hda : embedding_of_isReal w.2 (d : K) ≠ 0 :=
    (unitAtRealPlace_apply w d) ▸ (unitAtRealPlace w d).ne_zero
  have haa : embedding_of_isReal w.2 (a : K) ≠ 0 :=
    (unitAtRealPlace_apply w a) ▸ (unitAtRealPlace w a).ne_zero
  have hba : embedding_of_isReal w.2 (b : K) ≠ 0 :=
    (unitAtRealPlace_apply w b) ▸ (unitAtRealPlace w b).ne_zero
  rw [presentedForm_eq_weightedSumSquares_coe,
    _root_.QuadraticForm.realPositiveIndex_weightedSumSquares, Set.ncard_eq_toFinset_card']
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  simp only [realHasse_def, realNegativeIndex_def, hn, hilbertSymbol_real,
    unitAtRealPlace_apply, Units.val_neg, Units.val_one, map_neg, map_one] at hab
  rw [Set.toFinset_ofPred, huniv, Finset.filter_insert, Finset.filter_insert,
    Finset.filter_singleton]
  have htwo : (2 : ℕ) • squareClass (-1 : ℝˣ) = 0 :=
    ZModModule.char_nsmul_eq_zero 2 (squareClass (-1 : ℝˣ))
  have hthree : (3 : ℕ) • squareClass (-1 : ℝˣ) = squareClass (-1 : ℝˣ) := by
    rw [succ_nsmul, htwo]
    exact zero_add (squareClass (-1 : ℝˣ))
  have hcube : (-1 : ℤˣ) ^ 3 = -1 := by decide
  -- In rank three the determinant sign and Hasse sign distinguish all four signatures.
  interval_cases I.realPositiveIndex w <;>
    rcases lt_or_gt_of_ne hda with hdsgn | hdsgn <;>
    rcases lt_or_gt_of_ne haa with hasgn | hasgn <;>
    rcases lt_or_gt_of_ne hba with hbsgn | hbsgn <;>
    simp [htwo, hthree, hcube, one_nsmul (squareClass (-1 : ℝˣ)), unitAtRealPlace_apply,
      hdsgn, not_lt_of_ge hdsgn.le, hasgn, not_lt_of_ge hasgn.le,
      hbsgn, not_lt_of_ge hbsgn.le, mul_pos_iff, mul_neg_iff] at hdisc' hab ⊢

/-- Every admissible rank-three system is the system of a regular global ternary form. -/
theorem IsAdmissible.exists_globalForm_of_rank_eq_three {I : GlobalFormInvariants K}
    (hI : I.IsAdmissible) (hn : I.rank = 3) :
    ∃ (Q : _root_.QuadraticForm K (Fin 3 → K)) (hQ : Q.Nondegenerate),
      Q.globalInvariants hQ = I := by
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  obtain ⟨d, hd⟩ : ∃ d : Kˣ, squareClass d = I.discr :=
    ⟨Additive.toMul (Quotient.out I.discr), squareClass_toMul_out _⟩
  obtain ⟨a, b, hfin, hreal⟩ := exists_ternary_symbols I hI d
  let p := ternaryPresentation d a b
  refine ⟨presentedForm p, nondegenerate_presentedForm p, ?_⟩
  refine GlobalFormInvariants.ext ?_ ?_ (funext fun v => ?_) (funext fun w => ?_)
  · simpa [p] using hn.symm
  · rw [_root_.QuadraticForm.globalInvariants_discr, formClass_presentedForm,
      discr_ternaryPresentation, hd]
  · rw [_root_.QuadraticForm.globalInvariants_finiteHasse, finiteHasse_ternaryPresentation,
      hfin, mul_assoc, Int.units_mul_self, mul_one]
  · rw [_root_.QuadraticForm.globalInvariants_realPositiveIndex]
    exact realPositiveIndex_ternaryPresentation I hI hn d a b hd w (hreal w)

/-- In rank three, admissibility is equivalent to realization by a regular global form. -/
theorem isAdmissible_iff_exists_globalForm_of_rank_eq_three (I : GlobalFormInvariants K)
    (hn : I.rank = 3) :
    I.IsAdmissible ↔ ∃ (Q : _root_.QuadraticForm K (Fin 3 → K)) (hQ : Q.Nondegenerate),
      Q.globalInvariants hQ = I := by
  refine ⟨fun hI => hI.exists_globalForm_of_rank_eq_three hn, ?_⟩
  rintro ⟨Q, hQ, rfl⟩
  exact Q.isAdmissible_globalInvariants hQ (by simp)

/-- A rank-three admissible system has a regular global realization isometric at every finite
and real place to any prescribed local realization of the system. -/
theorem IsAdmissible.exists_globalForm_equivalent_at_places_of_rank_eq_three
    {I : GlobalFormInvariants K} (hI : I.IsAdmissible) (hn : I.rank = 3)
    {U : ∀ v : HeightOneSpectrum (𝓞 K),
      _root_.QuadraticForm (v.adicCompletion K) (Fin I.rank → v.adicCompletion K)}
    {R : {w : InfinitePlace K // w.IsReal} → _root_.QuadraticForm ℝ (Fin I.rank → ℝ)}
    (hL : I.IsLocalRealization U R) :
    ∃ (Q : _root_.QuadraticForm K (Fin 3 → K)) (hQ : Q.Nondegenerate),
      Q.globalInvariants hQ = I ∧
      (∀ v, (Q.atFinitePlace v).Equivalent (U v)) ∧
      ∀ w, (Q.atRealPlace w).Equivalent (R w) := by
  obtain ⟨Q, hQ, hQI⟩ := hI.exists_globalForm_of_rank_eq_three hn
  exact ⟨Q, hQ, hQI, hL.equivalent_atFinitePlace hQI, hL.equivalent_atRealPlace hQI⟩

end TauCeti.NumberField.QuadraticForm.GlobalFormInvariants
