/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Classification
public import TauCeti.NumberTheory.QuadraticForm.Global.ProductFormula
import TauCeti.NumberTheory.QuadraticForm.Global.SignPrescription
import TauCeti.NumberTheory.LocalField.QuadraticForm.Brauer

/-!
# Realizing ternary global invariant systems

Every admissible rank-three system over a number field is realized by a regular ternary form.
The construction uses scalar multiples of pure quaternion norm forms and Hilbert sign
prescription. It does not use a local-global principle for isotropy or representation.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 71:19 and 72:1.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter V, §3, for pure quaternion
  norm forms and their Hasse invariants.
-/

public section

open Finset IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap TauCeti

namespace TauCeti.NumberField.QuadraticForm

variable {K : Type} [Field K] [NumberField K]

private theorem finiteHasse_scaled_pure (d a b : Kˣ)
    (h : (weightedSumSquares K
      (fun i : Fin 3 ↦ ((d * ![-a, -b, a * b] i : Kˣ) : K))).Nondegenerate)
    (v : HeightOneSpectrum (𝓞 K)) :
    _root_.QuadraticForm.finiteHasse _ h v =
      hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) *
        hilbertSymbol (-1 : (v.adicCompletion K)ˣ) (-1) *
        hilbertSymbol (v.unitAtFinitePlace d) (-1) := by
  let : Invertible (2 : v.adicCompletion K) := invertibleOfNonzero two_ne_zero
  let : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  rw [_root_.QuadraticForm.finiteHasse_eq_prod_hilbertSymbol _ h (.refl _) v]
  have hmap : (fun i : Fin 3 ↦ v.unitAtFinitePlace (d * ![-a, -b, a * b] i)) =
      fun i ↦ v.unitAtFinitePlace d *
        ![-v.unitAtFinitePlace a, -v.unitAtFinitePlace b,
          v.unitAtFinitePlace a * v.unitAtFinitePlace b] i := by
    funext i
    fin_cases i <;> apply Units.ext <;> simp
  simp_rw [congrFun hmap]
  rw [← RegularFormClass.localHasse_mk ⟨3, fun i ↦ v.unitAtFinitePlace d *
    ![-v.unitAtFinitePlace a, -v.unitAtFinitePlace b,
      v.unitAtFinitePlace a * v.unitAtFinitePlace b] i⟩,
    RegularFormClass.localHasse_mk_scale _ ⟨3, ![-v.unitAtFinitePlace a,
      -v.unitAtFinitePlace b, v.unitAtFinitePlace a * v.unitAtFinitePlace b]⟩,
    RegularFormClass.localHasse_mk_neg_neg_mul]
  simp [pow_succ]

private theorem realHasse_scaled_pure (d a b : Kˣ)
    (h : (weightedSumSquares K
      (fun i : Fin 3 ↦ ((d * ![-a, -b, a * b] i : Kˣ) : K))).Nondegenerate)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (_root_.QuadraticForm.globalInvariants _ h).realHasse w =
      hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) *
        hilbertSymbol (-1 : ℝˣ) (-1) * hilbertSymbol (unitAtRealPlace w d) (-1) := by
  rw [_root_.QuadraticForm.globalInvariants_realHasse_eq_prod_hilbertSymbol _ h (.refl _) w,
    prod_prod_Ioi_three]
  simp only [map_mul]
  -- The signs of the three nonzero parameters determine every coefficient sign.
  -- In particular, the pure norm form is definite exactly when both quaternion parameters
  -- are negative; the formula also records the effect of the scalar `d`.
  rcases (map_ne_zero (embedding_of_isReal w.2)).mpr d.ne_zero |>.lt_or_gt with hd | hd <;>
    rcases (map_ne_zero (embedding_of_isReal w.2)).mpr a.ne_zero |>.lt_or_gt with ha | ha <;>
    rcases (map_ne_zero (embedding_of_isReal w.2)).mpr b.ne_zero |>.lt_or_gt with hb | hb <;>
    simp [hilbertSymbol_real, unitAtRealPlace_apply, mul_neg_iff, mul_pos_iff,
      hd, ha, hb, hd.not_gt, ha.not_gt, hb.not_gt]

private theorem exists_pair_relative_hasse (I J : GlobalFormInvariants K)
    (hI : I.IsAdmissible) (hJ : J.IsAdmissible) :
    ∃ a b : Kˣ,
      (∀ v, hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) =
        I.finiteHasse v * J.finiteHasse v) ∧
      ∀ w, hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) =
        I.realHasse w * J.realHasse w := by
  classical
  let f := fun v ↦ I.finiteHasse v * J.finiteHasse v
  let g := fun w ↦ I.realHasse w * J.realHasse w
  have hf : Function.HasFiniteMulSupport f :=
    hI.hasFiniteMulSupport_finiteHasse.mul hJ.hasFiniteMulSupport_finiteHasse
  let S := hf.toFinset
  let T := univ.filter fun w ↦ g w ≠ 1
  have hs (v) : f v = if v ∈ S then -1 else 1 := by
    have hmem : v ∈ S ↔ f v ≠ 1 := Set.Finite.mem_toFinset hf
    simp only [hmem]
    rcases Int.units_eq_one_or (f v) with h | h <;> simp [h]
  have ht (w) : g w = if w ∈ T then -1 else 1 := by
    simp only [T, mem_filter, mem_univ, true_and]
    rcases Int.units_eq_one_or (g w) with h | h <;> simp [h]
  have hprod : (∏ᶠ v, f v) * ∏ w, g w = 1 := by
    rw [finprod_mul_distrib hI.hasFiniteMulSupport_finiteHasse
      hJ.hasFiniteMulSupport_finiteHasse, Finset.prod_mul_distrib]
    calc
      _ = I.hasseProduct * J.hasseProduct := by
        rw [I.hasseProduct_def, J.hasseProduct_def]
        ac_rfl
      _ = 1 := by rw [hI.hasseProduct_eq_one, hJ.hasseProduct_eq_one, one_mul]
  have hparity : Even (S.card + T.card) := by
    rw [finprod_eq_prod f hf] at hprod
    rw [← neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)]
    have hpS : (∏ v ∈ hf.toFinset, f v) = (-1 : ℤˣ) ^ S.card := by simp [hs, S]
    have hpT : (∏ w, g w) = (-1 : ℤˣ) ^ T.card := by simp [ht]
    simpa only [hpS, hpT, pow_add] using hprod
  obtain ⟨a, b, ha, hb⟩ := exists_pair_hilbertSymbol_eq_ite S T hparity
  exact ⟨a, b, fun v ↦ (ha v).trans (hs v).symm, fun w ↦ (hb w).trans (ht w).symm⟩

private theorem realPositiveIndex_eq_of_ternary (I J : GlobalFormInvariants K)
    (hI : I.IsAdmissible) (hJ : J.IsAdmissible) (hi : I.rank = 3) (hj : J.rank = 3)
    (hd : I.discr = J.discr) (w : {w : InfinitePlace K // w.IsReal})
    (hs : I.realHasse w = J.realHasse w) : I.realPositiveIndex w = J.realPositiveIndex w := by
  have hdisc : I.realNegativeIndex w • squareClass (-1 : ℝˣ) =
      J.realNegativeIndex w • squareClass (-1 : ℝˣ) := by
    rw [← hI.discrAtRealPlace_eq, ← hJ.discrAtRealPlace_eq,
      GlobalFormInvariants.discrAtRealPlace_def, GlobalFormInvariants.discrAtRealPlace_def, hd]
  rw [← squareClass_pow, ← squareClass_pow, squareClass_eq_iff_isSquare_mul,
    ← Units.isSquare_coe_iff, Real.isSquare_iff] at hdisc
  have hp := hI.realPositiveIndex_le_rank w
  have hq := hJ.realPositiveIndex_le_rank w
  simp only [hi, hj] at hp hq
  simp only [GlobalFormInvariants.realHasse_def, GlobalFormInvariants.realNegativeIndex_def,
    hi, hj] at hs hdisc
  generalize I.realPositiveIndex w = p at *
  generalize J.realPositiveIndex w = q at *
  -- For negative indices 0, 1, 2, 3, the determinant and Hasse signs are respectively
  -- (+,+), (-,+), (+,-), (-,-), so together they distinguish the four signatures.
  interval_cases p <;> interval_cases q <;> norm_num [pow_succ] at *

/-- Every admissible rank-three system of global invariants is realized by a regular ternary
form over the number field. -/
theorem GlobalFormInvariants.IsAdmissible.exists_globalForm_rank_three
    {I : GlobalFormInvariants K} (hI : I.IsAdmissible) (hn : I.rank = 3) :
    ∃ (Q : _root_.QuadraticForm K (Fin 3 → K)) (hQ : Q.Nondegenerate),
      Q.globalInvariants hQ = I := by
  classical
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  let d := Additive.toMul (Quotient.out I.discr)
  have hd : squareClass d = I.discr := squareClass_toMul_out _
  -- Compare with one global form of the prescribed discriminant. Its Hasse product is one.
  let Q₀ : _root_.QuadraticForm K (Fin 3 → K) :=
    weightedSumSquares K fun i : Fin 3 ↦ ((d * ![-(1 : Kˣ), -1, 1 * 1] i : Kˣ) : K)
  have hQ₀ : Q₀.Nondegenerate := nondegenerate_weightedSumSquares fun i ↦
    (d * ![-(1 : Kˣ), -1, 1 * 1] i).isUnit.isRegular
  let J := Q₀.globalInvariants hQ₀
  have hJ : J.IsAdmissible := Q₀.isAdmissible_globalInvariants hQ₀ (by simp)
  -- Prescribe the relative Hasse signs, including the real places. Multiplying the pure
  -- quaternion norm form by `d` restores the desired discriminant.
  obtain ⟨a, b, ha, hb⟩ := exists_pair_relative_hasse I J hI hJ
  let Q : _root_.QuadraticForm K (Fin 3 → K) :=
    weightedSumSquares K fun i : Fin 3 ↦ ((d * ![-a, -b, a * b] i : Kˣ) : K)
  have hQ : Q.Nondegenerate := nondegenerate_weightedSumSquares fun i ↦
    (d * ![-a, -b, a * b] i).isUnit.isRegular
  let L := Q.globalInvariants hQ
  have hL : L.IsAdmissible := Q.isAdmissible_globalInvariants hQ (by simp)
  have hLd : L.discr = I.discr := by
    rw [_root_.QuadraticForm.globalInvariants_discr, ← hd,
      discr_formClass_weightedSumSquares, Fin.prod_univ_three, squareClass_eq_iff_isSquare_mul]
    -- The product of the three coefficients times `d` is `(d²ab)²`.
    refine ⟨d ^ 2 * a * b, ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      mul_neg, neg_mul, neg_neg, pow_two]
    ac_rfl
  -- At each place, the Hasse sign of the reference form cancels the relative correction.
  have hfinite (v) : L.finiteHasse v = I.finiteHasse v := by
    have hbase : J.finiteHasse v =
        hilbertSymbol (-1 : (v.adicCompletion K)ˣ) (-1) *
          hilbertSymbol (v.unitAtFinitePlace d) (-1) := by
      rw [_root_.QuadraticForm.globalInvariants_finiteHasse]
      exact (finiteHasse_scaled_pure d 1 1 hQ₀ v).trans (by
        rw [map_one, hilbertSymbol_one_left, one_mul])
    have hnew := finiteHasse_scaled_pure d a b hQ v
    rw [ha] at hnew
    simp only [mul_assoc] at hnew
    rw [← hbase] at hnew
    simpa only [L, _root_.QuadraticForm.globalInvariants_finiteHasse,
      mul_assoc, Int.units_mul_self, mul_one] using hnew
  have hreal (w) : L.realHasse w = I.realHasse w := by
    have hbase : J.realHasse w = hilbertSymbol (-1 : ℝˣ) (-1) *
        hilbertSymbol (unitAtRealPlace w d) (-1) :=
      (realHasse_scaled_pure d 1 1 hQ₀ w).trans (by
        rw [map_one, hilbertSymbol_one_left, one_mul])
    have hnew := realHasse_scaled_pure d a b hQ w
    rw [hb] at hnew
    simp only [mul_assoc] at hnew
    rw [← hbase] at hnew
    simpa only [L, mul_assoc, Int.units_mul_self, mul_one] using hnew
  refine ⟨Q, hQ, GlobalFormInvariants.ext (by simpa [L] using hn.symm) hLd
    (funext hfinite) (funext fun w ↦ ?_)⟩
  exact realPositiveIndex_eq_of_ternary L I hL hI (by simp [L]) hn hLd w (hreal w)

/-- A rank-three system is admissible exactly when it is the invariant system of a regular
ternary form over the number field. -/
theorem GlobalFormInvariants.isAdmissible_iff_exists_globalForm_rank_three
    {I : GlobalFormInvariants K} (hn : I.rank = 3) :
    I.IsAdmissible ↔ ∃ (Q : _root_.QuadraticForm K (Fin 3 → K)) (hQ : Q.Nondegenerate),
      Q.globalInvariants hQ = I := by
  refine ⟨fun hI ↦ hI.exists_globalForm_rank_three hn, ?_⟩
  rintro ⟨Q, hQ, hQI⟩
  rw [← hQI]
  exact Q.isAdmissible_globalInvariants hQ (by simp)

/-- An admissible rank-three system has a regular global realization isometric to every
member of any prescribed family of regular finite and real local realizations. -/
theorem GlobalFormInvariants.IsAdmissible.exists_globalForm_rank_three_equivalent_at_places
    {I : GlobalFormInvariants K} (hI : I.IsAdmissible) (hn : I.rank = 3)
    {U : ∀ v : HeightOneSpectrum (𝓞 K),
      _root_.QuadraticForm (v.adicCompletion K) (Fin I.rank → v.adicCompletion K)}
    {R : {w : InfinitePlace K // w.IsReal} → _root_.QuadraticForm ℝ (Fin I.rank → ℝ)}
    (hL : I.IsLocalRealization U R) :
    ∃ (Q : _root_.QuadraticForm K (Fin 3 → K)) (hQ : Q.Nondegenerate),
      Q.globalInvariants hQ = I ∧
      (∀ v, (Q.atFinitePlace v).Equivalent (U v)) ∧
      ∀ w, (Q.atRealPlace w).Equivalent (R w) := by
  obtain ⟨Q, hQ, hQI⟩ := hI.exists_globalForm_rank_three hn
  exact ⟨Q, hQ, hQI, hL.equivalent_atFinitePlace hQI, hL.equivalent_atRealPlace hQI⟩

end TauCeti.NumberField.QuadraticForm
