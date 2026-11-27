/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import TauCeti.Probability.RandomMatrix.LeastSingularValue.Basic
public import TauCeti.Probability.RandomMatrix.RandomSubspace
import TauCeti.Probability.Independence.LeastCommonDenominator
import TauCeti.Probability.Moments.SubGaussian.AntiConcentration
import TauCeti.Probability.Moments.SubGaussian.Basic
import TauCeti.Probability.RandomMatrix.ColumnDistance
import TauCeti.Probability.RandomMatrix.LeastSingularValue.SmallDimensions
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# The least singular value of a square sub-Gaussian matrix

Arithmetic anti-concentration for a unit normal to the other columns bounds the probability
that a column is close to their span. Averaging these bounds in the least-singular-value
reduction gives the lower tail on the scale `1 / √n`.

## References

* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, Advances in Mathematics 218 (2008), Theorem 1.2 and §5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Metric Set Real Module TauCeti.Probability
open scoped ENNReal NNReal InnerProductSpace

namespace ProbabilityTheory.iIndepFun

variable {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
  {P : Measure Ω} {A : Ω → Matrix n n ℝ} {K : ℝ≥0}
  {ν : n → Measure ℝ}

/-- A fixed span with a unit normal of least common denominator at least `L` gives a
small-ball bound for the distance of a column from that span. -/
private theorem measureReal_infDist_lt_le_of_largeLCD
    {i : n} (hcol : iIndepFun (fun r ω ↦ A ω r i) P)
    (hν : ∀ r, HasLaw (fun ω ↦ A ω r i) (ν i) P)
    {b : ℝ} (hb : ∀ v, ((ν i).map (2 * ·)).real (ball v 1) ≤ 1 - b)
    {U : Submodule ℝ (EuclideanSpace ℝ n)} {x : EuclideanSpace ℝ n}
    (hx : x ∈ Uᗮ) (hx1 : ‖x‖ = 1) {α : ℝ≥0} {γ L : ℝ} (hγ : 0 < γ) (hL : 0 < L)
    (hLCD : ENNReal.ofReal L ≤ TauCeti.leastCommonDenominator α γ x)
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | infDist (WithLp.toLp 2 fun r ↦ A ω r i) (U : Set _) < t} ≤
      16 * π * (2 * t + L⁻¹) / (γ * √b) + 4 * exp (1 - α ^ 2 * b / 2) := by
  have := hcol.isProbabilityMeasure
  have hscaled := hcol.comp (fun _ ↦ (2 * ·)) (fun _ ↦ measurable_const.mul measurable_id)
  have hscaledLaw (r : n) : HasLaw (fun ω ↦ 2 * A ω r i) ((ν i).map (2 * ·)) P :=
    (hasLaw_map (measurable_const.mul measurable_id).aemeasurable).fun_comp (hν r)
  have hx0 : x ≠ 0 := by aesop
  refine (measureReal_mono (s₂ := {ω | |(∑ r, x r * (2 * A ω r i)) - 0| ≤ 2 * t}) ?_
    (measure_ne_top _ _)).trans ?_
  · intro ω hω
    let y : EuclideanSpace ℝ n := WithLp.toLp 2 fun r ↦ A ω r i
    have hinner : |⟪x, y⟫_ℝ| ≤ infDist y (U : Set _) := by
      refine (le_infDist ⟨0, U.zero_mem⟩).2 fun z hz ↦ ?_
      have hz0 : ⟪x, z⟫_ℝ = 0 := (Submodule.mem_orthogonal' _ _).1 hx z hz
      simpa only [inner_sub_right, hz0, sub_zero, hx1, one_mul, dist_eq_norm] using
        abs_real_inner_le_norm x (y - z)
    have hsum : (∑ r, x r * (2 * A ω r i)) = 2 * ⟪x, y⟫_ℝ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ ↦ by simp [y]; ring
    rw [mem_ofPred_eq, hsum, sub_zero, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (hinner.trans (mem_ofPred.mp hω).le) (by norm_num)
  · simpa only [hx1, mul_one, Function.comp_apply, sub_zero] using
      hscaled.measureReal_abs_sum_mul_sub_le_le_of_ofReal_le_leastCommonDenominator
        hscaledLaw hb hx0 hγ hL hLCD 0 (by positivity : 0 ≤ 2 * t)

/-- For a square real matrix, the probability that a column has distance
less than `t` from the span of the others is at most `B t + D exp (-a n)`. Entries are independent,
sub-Gaussian with a common upper variance proxy, have second moments at least one and have a
common law within each column. -/
theorem exists_measureReal_infDist_col_span_lt_le (K : ℝ≥0) :
    ∃ B D a : ℝ, 0 < B ∧ 0 < D ∧ 0 < a ∧
      ∀ {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] {P : Measure Ω}
        {A : Ω → Matrix n n ℝ} {ν : n → Measure ℝ},
        iIndepFun (fun ij : n × n ↦ fun ω ↦ A ω ij.1 ij.2) P →
        (∀ i j, HasSubgaussianMGF (fun ω ↦ A ω i j) K P) →
        (∀ i j, 1 ≤ ∫ ω, (A ω i j) ^ 2 ∂P) →
        (∀ i j, HasLaw (fun ω ↦ A ω i j) (ν j) P) →
        ∀ (i : n) {t : ℝ}, 0 ≤ t →
        P.real {ω | infDist (WithLp.toLp 2 fun r ↦ A ω r i)
          (Submodule.span ℝ (range fun j : {j // j ≠ i} ↦
            WithLp.toLp 2 fun r ↦ A ω r j) : Set (EuclideanSpace ℝ n)) < t} ≤
          B * t + D * exp (-a * Fintype.card n) := by
  classical
  obtain ⟨c, C, hc, hC, hstruct⟩ :=
    exists_measureReal_exists_mem_orthogonal_span_ne_leastCommonDenominator_lt_le K
  let b := 9 / (4096 * √2 * ((K : ℝ) + 1) ^ 2)
  let M := 16 * π / (c * √b)
  let a := min c (c ^ 2 * b / 2)
  have hb : 0 < b := by dsimp [b]; positivity
  have hM : 0 < M := div_pos (by positivity) (mul_pos hc (sqrt_pos.2 hb))
  have ha : 0 < a := lt_min hc (by positivity)
  refine ⟨2 * M, M / c + 4 * exp 1 + C + exp a, a, by positivity, by positivity, ha, ?_⟩
  intro Ω n _ _ P A ν hind hA hvar hlaw i t ht
  have := hind.isProbabilityMeasure
  by_cases hdim : 2 ≤ Fintype.card n
  swap
  · have hd : (Fintype.card n : ℝ) ≤ 1 := by
      exact_mod_cast (show Fintype.card n ≤ 1 by omega)
    refine measureReal_le_one.trans ((one_le_exp (x := a + -a * Fintype.card n)
      (by nlinarith)).trans ?_)
    rw [exp_add]
    exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left
      (by positivity : 0 ≤ M / c + 4 * exp 1 + C)) (exp_pos _).le).trans
      (le_add_of_nonneg_left (by positivity))
  have hmeas : AEMeasurable A P := .of_eval fun r ↦ .of_eval fun j ↦ (hA r j).aemeasurable
  have hbball (v : ℝ) : ((ν i).map (2 * ·)).real (ball v 1) ≤ 1 - b := by
    have hscaled : HasLaw (fun ω ↦ 2 * A ω i i) ((ν i).map (2 * ·)) P :=
      (hasLaw_map (measurable_id.const_mul 2).aemeasurable).fun_comp (hlaw i i)
    rw [← hscaled.map_eq]
    have hsub := (hA i i).mono (le_add_of_nonneg_right zero_le_one)
    simpa [b] using hsub.measureReal_map_two_mul_ball_le (hvar i i) v
  let V (ω : Ω) := Submodule.span ℝ (range fun j : {j // j ≠ i} ↦
    (WithLp.toLp 2 fun r ↦ A ω r j : EuclideanSpace ℝ n))
  let d := Fintype.card n
  let α : ℝ≥0 := ⟨c * √d, by positivity⟩
  have hα : (α : ℝ) = c * √d := rfl
  let L := c * √d * exp (c * d)
  have hL : 0 < L := by dsimp [L, d]; positivity
  let bad := {ω | ∃ x ∈ (V ω)ᗮ, ‖x‖ = 1 ∧
    TauCeti.leastCommonDenominator α c x < ENNReal.ofReal L}
  have hbad : P.real bad ≤ C * exp (-c * d) := by
    have hcodim : Fintype.card n - (Fintype.card n - 1) = 1 := by omega
    simpa only [bad, V, hα, L, d, hcodim, Nat.cast_one, div_one] using
      hstruct hind hA hvar hlaw (by omega) i
  have hcol : iIndepFun (fun r ω ↦ A ω r i) P :=
    hind.precomp (g := fun r ↦ (r, i)) (fun _ _ h ↦ congrArg Prod.fst h)
  refine (hind.measureReal_infDist_col_span_lt_le_add hmeas i
    (b := M * (2 * t + L⁻¹) + 4 * exp (1 - α ^ 2 * b / 2))
    (bad := bad) (by positivity) ?_).trans ?_
  · intro ω hω
    let v (j : {j // j ≠ i}) : EuclideanSpace ℝ n := WithLp.toLp 2 fun r ↦ A ω r j
    have hcard : Fintype.card {j : n // j ≠ i} = d - 1 := by simp [d]
    have hdimV : finrank ℝ (V ω) ≤ d - 1 := (finrank_range_le_card (R := ℝ) v).trans_eq hcard
    have hdimO := (V ω).finrank_add_finrank_orthogonal
    rw [finrank_euclideanSpace] at hdimO
    have hpos : 0 < finrank ℝ (V ω)ᗮ := by dsimp [d] at *; omega
    let : Nontrivial ((V ω)ᗮ) := nontrivial_of_finrank_pos hpos
    obtain ⟨x, hx⟩ := exists_norm_eq ((V ω)ᗮ) zero_le_one
    have hx1 : ‖(x : EuclideanSpace ℝ n)‖ = 1 := hx
    have hLCD := le_of_not_gt (fun hlt ↦ hω ⟨x, x.property, hx1, hlt⟩)
    simpa only [M, div_mul_eq_mul_div] using
      measureReal_infDist_lt_le_of_largeLCD hcol (fun r ↦ hlaw r i) hbball
        x.property hx1 hc hL hLCD ht
  · have hs : 1 ≤ √(d : ℝ) := by
      rw [← sqrt_one]; exact sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ d by omega))
    have hinv : L⁻¹ ≤ c⁻¹ * exp (-a * d) := by
      rw [show L⁻¹ = (c * √d)⁻¹ * exp (-(c * d)) by simp [L, exp_neg, mul_comm]]
      gcongr
      · exact le_mul_of_one_le_right hc.le hs
      · rw [← neg_mul]; gcongr; exact min_le_left _ _
    have hexp : exp (1 - α ^ 2 * b / 2) ≤ exp 1 * exp (-a * d) := by
      rw [← exp_add]
      apply exp_le_exp.mpr
      have hsq : (α : ℝ) ^ 2 = c ^ 2 * d := by
        rw [hα, mul_pow, sq_sqrt (by positivity)]
      rw [hsq]
      have hle := mul_le_mul_of_nonneg_right (min_le_right c (c ^ 2 * b / 2))
        (Nat.cast_nonneg d)
      linarith
    have hc_exp : exp (-c * d) ≤ exp (-a * d) := by
      gcongr
      exact min_le_left _ _
    calc
      _ ≤ M * (2 * t + c⁻¹ * exp (-a * d)) + 4 * (exp 1 * exp (-a * d)) +
          C * exp (-a * d) :=
        add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left (add_le_add le_rfl hinv) hM.le)
          (mul_le_mul_of_nonneg_left hexp (by norm_num)))
          (hbad.trans (mul_le_mul_of_nonneg_left hc_exp hC.le))
      _ = 2 * M * t + (M / c + 4 * exp 1 + C) * exp (-a * d) := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ _ := add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (exp_pos _).le) (exp_pos _).le)

private theorem exists_measureReal_singularValues_card_sub_one_lt_le_mul_exp (K : ℝ≥0) :
    ∃ B D a : ℝ, 0 < B ∧ 0 < D ∧ 0 < a ∧
      ∀ {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n] {P : Measure Ω}
        {A : Ω → Matrix n n ℝ} {ν : n → Measure ℝ},
        iIndepFun (fun ij : n × n ↦ fun ω ↦ A ω ij.1 ij.2) P →
        (∀ i j, HasSubgaussianMGF (fun ω ↦ A ω i j) K P) →
        (∀ i j, 1 ≤ ∫ ω, (A ω i j) ^ 2 ∂P) →
        (∀ i j, HasLaw (fun ω ↦ A ω i j) (ν j) P) →
        2 ≤ Fintype.card n → ∀ {t : ℝ}, 0 ≤ t →
        P.real {ω | (toEuclideanLin (A ω)).singularValues (Fintype.card n - 1) <
          t / √(Fintype.card n)} ≤ B * t + D * exp (-a * Fintype.card n) := by
  obtain ⟨B, D, a, _, hD, ha, hcol⟩ := exists_measureReal_infDist_col_span_lt_le K
  obtain ⟨ρ, hρ, _, a', C, ha', hC, hreduce⟩ :=
    TauCeti.Probability.exists_measureReal_singularValues_card_sub_one_lt_le K
  let b := min a a'
  refine ⟨max 4 (C * B / ρ), 4 + C * D, b, by positivity, by positivity, lt_min ha ha', ?_⟩
  intro Ω n _ _ _ P A ν hind hA hvar hlaw hn t ht
  have := hind.isProbabilityMeasure
  have hρ' : (0 : ℝ) < ρ := NNReal.coe_pos.2 hρ
  have hdim : (0 : ℝ) < Fintype.card n := by exact_mod_cast (show 0 < Fintype.card n by omega)
  have hs := sqrt_pos.2 hdim
  by_cases hcut : t / √(Fintype.card n) ≤ √(Fintype.card n) / 4
  · have hscale : (ρ : ℝ) / √(Fintype.card n) * (t / ρ) = t / √(Fintype.card n) := by
      field_simp
    have h := hreduce hind hA hvar le_rfl (ε := t / ρ) (hscale.symm ▸ hcut)
    rw [hscale] at h
    refine h.trans ?_
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦
      hcol hind hA hvar hlaw i (div_nonneg ht hρ'.le))
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    have havg := (div_le_div_of_nonneg_right hsum hdim.le).trans_eq
      (mul_div_cancel_left₀ _ hdim.ne')
    have hexp (x : ℝ) (hx : b ≤ x) : exp (-x * Fintype.card n) ≤
        exp (-b * Fintype.card n) := by gcongr
    calc
      _ ≤ 4 * exp (-b * Fintype.card n) +
          C * (B * (t / ρ) + D * exp (-b * Fintype.card n)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left (hexp a' (min_le_right _ _)) (by norm_num))
          (mul_le_mul_of_nonneg_left (havg.trans (add_le_add le_rfl
            (mul_le_mul_of_nonneg_left (hexp a (min_le_left _ _)) hD.le))) hC.le)
      _ = (C * B / ρ) * t + (4 + C * D) * exp (-b * Fintype.card n) := by ring
      _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_right (le_max_right _ _) ht) _
  · have hlarge := (lt_div_iff₀ hs).1 (lt_of_not_ge hcut)
    have hsq := sq_sqrt hdim.le
    have hdim' : (1 : ℝ) ≤ Fintype.card n :=
      by exact_mod_cast (show 1 ≤ Fintype.card n by omega)
    have ht' : 1 ≤ 4 * t := by nlinarith
    exact measureReal_le_one.trans (ht'.trans ((mul_le_mul_of_nonneg_right
      (le_max_left _ _) ht).trans (le_add_of_nonneg_right (by positivity))))

private theorem measureReal_singularValues_card_sub_one_le_le_of_measureReal_ge
    [DecidableEq n] [IsProbabilityMeasure P] (hA : AEMeasurable A P)
    {u p t : ℝ} (hn : 0 < Fintype.card n) (ht : 0 ≤ t) (htu : t < u)
    (hgood : p ≤ P.real {ω | u ≤ (toEuclideanLin (A ω)).singularValues (Fintype.card n - 1)}) :
    P.real {ω | (toEuclideanLin (A ω)).singularValues (Fintype.card n - 1) ≤
      t / √(Fintype.card n)} ≤ 1 - p := by
  let s (ω : Ω) := (toEuclideanLin (A ω)).singularValues (Fintype.card n - 1)
  have hs : AEMeasurable s P := by
    have hm := (LinearMap.continuous_minimalStretch.comp
      Matrix.continuous_toEuclideanCLM).measurable.comp_aemeasurable hA
    simpa only [s, Function.comp_def, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
      LinearMap.minimalStretch_def, finrank_euclideanSpace] using hm
  have hm : NullMeasurableSet {ω | u ≤ s ω} P := nullMeasurableSet_le aemeasurable_const hs
  have hcompl := measureReal_compl₀ hm
  rw [probReal_univ] at hcompl
  have hrest : P.real {ω | u ≤ s ω}ᶜ ≤ 1 - p := by
    rw [hcompl]
    exact sub_le_sub_left hgood _
  have hone : 1 ≤ √(Fintype.card n : ℝ) := by
    rw [← sqrt_one]
    exact sqrt_le_sqrt (by exact_mod_cast hn)
  refine (measureReal_mono (s₂ := {ω | u ≤ s ω}ᶜ) fun ω hω ↦ ?_).trans hrest
  exact not_le.mpr ((mem_ofPred.mp hω).trans_lt ((div_le_self ht hone).trans_lt htu))

/-- **Rudelson–Vershynin least-singular-value bound.** For independent real sub-Gaussian
entries with common upper variance proxy and second moments at least one, assume the entries
within each column have a common law. The probability that the least singular value of the
unnormalized square matrix is at most `t / √n` is bounded by `C * t + c ^ n`, where
`C > 0` and `0 < c < 1` depend only on the proxy. -/
theorem exists_measureReal_singularValues_card_sub_one_le_le (K : ℝ≥0) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c < 1 ∧
      ∀ {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n] {P : Measure Ω}
        {A : Ω → Matrix n n ℝ} {ν : n → Measure ℝ},
        iIndepFun (fun ij : n × n ↦ fun ω ↦ A ω ij.1 ij.2) P →
        (∀ i j, HasSubgaussianMGF (fun ω ↦ A ω i j) K P) →
        (∀ i j, 1 ≤ ∫ ω, (A ω i j) ^ 2 ∂P) →
        (∀ i j, HasLaw (fun ω ↦ A ω i j) (ν j) P) →
        ∀ {t : ℝ}, 0 ≤ t →
        P.real {ω | (toEuclideanLin (A ω)).singularValues (Fintype.card n - 1) ≤
          t / √(Fintype.card n)} ≤ C * t + c ^ Fintype.card n := by
  obtain ⟨B, D, a, hB, hD, ha, hlarge⟩ :=
    exists_measureReal_singularValues_card_sub_one_lt_le_mul_exp K
  let N := ⌈2 * log D / a⌉₊ + 2
  have hN : 2 ≤ N := by dsimp [N]; omega
  obtain ⟨u, p, hu, hp, hp₁, hsmall⟩ :=
    exists_le_measureReal_singularValues_card_sub_one_ge_of_card_le K N
  let C := max B u⁻¹
  let c := max (exp (-(a / 2))) (1 - p / (N + 1))
  have hC : 0 < C := hB.trans_le (le_max_left _ _)
  have hc : 0 < c := (exp_pos _).trans_le (le_max_left _ _)
  refine ⟨C, c, hC, hc, max_lt (exp_lt_one_iff.mpr (by linarith))
    (sub_lt_self _ (div_pos hp (by positivity))), ?_⟩
  intro Ω n _ _ _ P A ν hind hA hvar hlaw t ht
  have := hind.isProbabilityMeasure
  let d := Fintype.card n
  by_cases hd : d = 0
  · exact measureReal_le_one.trans (by
      rw [show Fintype.card n = 0 from hd, pow_zero]
      exact le_add_of_nonneg_left (mul_nonneg hC.le ht))
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  have hs : 0 < √(d : ℝ) := sqrt_pos.2 (by positivity)
  by_cases hcut : N ≤ d
  · have hlog : 2 * log D / a ≤ (d : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈2 * log D / a⌉₊ ≤ d by omega))
    have hdecay : D * exp (-a * d) ≤ c ^ d := by
      calc
        _ = exp (log D + -a * d) := by rw [exp_add, exp_log hD]
        _ ≤ exp (d * (-(a / 2))) := exp_le_exp.mpr (by
          have hlog' := (div_le_iff₀ ha).1 hlog
          nlinarith)
        _ = exp (-(a / 2)) ^ d := exp_natCast_mul _ _
        _ ≤ c ^ d := pow_le_pow_left₀ (exp_pos _).le (le_max_left _ _) _
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have hshift : t < t + ε / C := lt_add_of_pos_right _ (div_pos hε hC)
    refine (measureReal_mono (fun ω hω ↦ (mem_ofPred.mp hω).trans_lt
      ((div_lt_div_iff_of_pos_right hs).2 hshift))).trans
      ((hlarge hind hA hvar hlaw (hN.trans hcut) (ht.trans hshift.le)).trans ?_)
    have hcoef := mul_le_mul_of_nonneg_right (le_max_left B u⁻¹) (ht.trans hshift.le)
    have hlinear : C * (t + ε / C) = C * t + ε := by field_simp
    have hsum := add_le_add hcoef hdecay
    rw [hlinear] at hsum
    linarith
  · by_cases htu : u ≤ t
    · have hCu := mul_le_mul_of_nonneg_right (le_max_right B u⁻¹) ht
      have hunit : 1 ≤ u⁻¹ * t := by rwa [inv_mul_eq_div, le_div_iff₀ hu, one_mul]
      exact measureReal_le_one.trans (hunit.trans
        (hCu.trans (le_add_of_nonneg_right (pow_nonneg hc.le _))))
    have hdN : d ≤ N := (le_of_not_ge hcut)
    have hmeas : AEMeasurable A P := .of_eval fun i ↦ .of_eval fun j ↦ (hA i j).aemeasurable
    have hrest := measureReal_singularValues_card_sub_one_le_le_of_measureReal_ge hmeas hd' ht
      (lt_of_not_ge htu) (hsmall hind hA hvar hd' hdN)
    have hpower : 1 - p ≤ c ^ d := by
      have hbase : 0 ≤ 1 - p / ((N : ℝ) + 1) :=
        sub_nonneg.mpr ((div_le_iff₀ (by positivity)).2 (by linarith))
      have hdiv : (d : ℝ) * (p / (N + 1)) ≤ p := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        have : (d : ℝ) ≤ N := by exact_mod_cast hdN
        nlinarith
      exact (by linarith : 1 - p ≤ 1 + d * ((1 - p / (N + 1)) - 1)).trans
        ((one_add_mul_sub_le_pow (by linarith : -1 ≤ 1 - p / ((N : ℝ) + 1)) d).trans
          (pow_le_pow_left₀ hbase (le_max_right _ _) _))
    exact hrest.trans (hpower.trans (le_add_of_nonneg_left (mul_nonneg hC.le ht)))

end ProbabilityTheory.iIndepFun
