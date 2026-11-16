/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
public import TauCeti.Probability.Process.TimeMeasure
public import TauCeti.Probability.Process.Indistinguishable
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.Normed.Group.Real
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Elementary predictable integrands and the Brownian Itô integral predicate

An elementary predictable integrand (`TauCeti.ElementaryIntegrand`) consists of a finite
nondecreasing grid `s 0 ≤ s 1 ≤ ⋯ ≤ s n` together with uniformly bounded `ℱ (s i)`-measurable
heights `ξ i` held on each left-open interval `(s i, s (i + 1)]`. Its associated predictable
process is `∑ i, ξ i · 1_{(s i, s (i + 1)]}` (`ElementaryIntegrand.toProcess`), and its elementary
stochastic integral against a process `W` is
`∑ i, ξ i · (W (min t (s (i + 1))) - W (min t (s i)))` (`ElementaryIntegrand.integral`).

`TauCeti.IsItoIntegral ℱ P W H I` characterizes a continuous stochastic integral process `I` of a
strongly predictable integrand `H` against `W`: at each time `t`, some sequence of elementary
integrands approximates `H` in pathwise square energy in probability on `(0, t]` (measured by the
nonnegative lower Lebesgue integral, so infinite energy is never masked by a default Bochner value),
while the corresponding elementary integrals at `t` converge in probability to `I t`.

Against a filtered pre-Brownian motion `W`, any two Itô integrals of the same integrand are
indistinguishable (`IsFilteredPreBrownianReal.isItoIntegral_unique`), and predictable integrands
that agree `(timeMeasure T).prod P`-almost everywhere on every finite horizon have indistinguishable
Itô integrals (`IsFilteredPreBrownianReal.itoIntegral_local_congr`). Neither uniqueness nor
integrand congruence requires Brownian path continuity or usual filtration conditions.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}

/-- An elementary predictable integrand: a finite nondecreasing grid `s 0 ≤ s 1 ≤ ⋯ ≤ s n` with
uniformly bounded `ℱ (s i)`-measurable heights `ξ i` held on `(s i, s (i + 1)]`. -/
structure ElementaryIntegrand (ℱ : Filtration ℝ≥0 mΩ) where
  /-- The number of intervals in the grid. -/
  n : ℕ
  /-- The nondecreasing grid of dates `s 0 ≤ s 1 ≤ ⋯ ≤ s n`. -/
  s : Fin (n + 1) → ℝ≥0
  /-- The grid dates are nondecreasing. -/
  mono : Monotone s
  /-- The random height held on `(s i, s (i + 1)]`. -/
  ξ : Fin n → Ω → ℝ
  /-- Each height is strongly measurable at the left endpoint of its interval. -/
  stronglyMeasurable : ∀ i : Fin n, StronglyMeasurable[ℱ (s i.castSucc)] (ξ i)
  /-- Each height is uniformly bounded. -/
  bounded : ∀ i : Fin n, ∃ C : ℝ, ∀ ω, |ξ i ω| ≤ C

namespace ElementaryIntegrand

/-- Two elementary integrands with the same grid length, dates, and heights are equal. -/
theorem ext {K L : ElementaryIntegrand ℱ} (hn : K.n = L.n)
    (hs : ∀ i : Fin (K.n + 1), K.s i = L.s (i.cast (by rw [hn])))
    (hξ : ∀ i : Fin K.n, K.ξ i = L.ξ (i.cast hn)) : K = L := by
  cases K; cases L; simp only at hn; subst hn
  congr <;> funext i <;> [exact hs i; exact hξ i]

/-- The predictable step process `t ↦ ∑ i, ξ i · 1_{(s i, s (i + 1)]}(t)` of an elementary
integrand. -/
def toProcess (K : ElementaryIntegrand ℱ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i : Fin K.n, (Ioc (K.s i.castSucc) (K.s i.succ)).indicator (fun _ ↦ K.ξ i ω) t

/-- Unfolding lemma for `ElementaryIntegrand.toProcess`. -/
theorem toProcess_def (K : ElementaryIntegrand ℱ) (t : ℝ≥0) (ω : Ω) :
    K.toProcess t ω =
      ∑ i : Fin K.n, (Ioc (K.s i.castSucc) (K.s i.succ)).indicator (fun _ ↦ K.ξ i ω) t := (rfl)

/-- The elementary stochastic integral `t ↦ ∑ i, ξ i · (W (min t (s (i + 1))) - W (min t (s i)))`
of an elementary integrand against a process `W`. -/
def integral (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i : Fin K.n, K.ξ i ω * (W (min t (K.s i.succ)) ω - W (min t (K.s i.castSucc)) ω)

/-- Unfolding lemma for `ElementaryIntegrand.integral`. -/
theorem integral_def (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    K.integral W t ω =
      ∑ i : Fin K.n, K.ξ i ω * (W (min t (K.s i.succ)) ω - W (min t (K.s i.castSucc)) ω) := (rfl)

/-- The empty-grid elementary integrand, whose process and integral are identically zero. -/
def zero (ℱ : Filtration ℝ≥0 mΩ) : ElementaryIntegrand ℱ where
  n := 0
  s := fun _ ↦ 0
  mono := fun _ _ _ ↦ le_rfl
  ξ := Fin.elim0
  stronglyMeasurable := fun i ↦ i.elim0
  bounded := fun i ↦ i.elim0

@[simp]
theorem toProcess_zero (t : ℝ≥0) (ω : Ω) : (zero ℱ).toProcess t ω = 0 := by
  simp [toProcess_def, zero]

@[simp]
theorem integral_zero (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : (zero ℱ).integral W t ω = 0 := by
  simp [integral_def, zero]

/-- A one-step elementary integrand holding a bounded `ℱ s`-measurable height `ξ` on `(s, t]`. -/
def single {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) (hb : ∃ C : ℝ, ∀ ω, |ξ ω| ≤ C) :
    ElementaryIntegrand ℱ where
  n := 1
  s := ![s, t]
  mono := fun i j hij ↦ by fin_cases i <;> fin_cases j <;> simp_all
  ξ := ![ξ]
  stronglyMeasurable := fun i ↦ by fin_cases i; exact hξ
  bounded := fun i ↦ by fin_cases i; simpa using hb

@[simp]
theorem toProcess_single {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) (hb : ∃ C : ℝ, ∀ ω, |ξ ω| ≤ C) (u : ℝ≥0) (ω : Ω) :
    (single hst hξ hb).toProcess u ω = (Ioc s t).indicator (fun _ ↦ ξ ω) u := by
  simp [toProcess_def, single]

@[simp]
theorem integral_single {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) (hb : ∃ C : ℝ, ∀ ω, |ξ ω| ≤ C)
    (W : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) :
    (single hst hξ hb).integral W u ω = ξ ω * (W (min u t) ω - W (min u s) ω) := by
  simp [integral_def, single]

/-- Package a bounded `ℕ`-indexed simple holding on a monotone finite grid as an
`ElementaryIntegrand`. -/
def ofSimple (n : ℕ) (τ : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ)
    (hτ : MonotoneOn τ (Set.Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (hb : ∀ i < n, ∃ C : ℝ, ∀ ω, |a i ω| ≤ C) : ElementaryIntegrand ℱ where
  n := n
  s := fun i ↦ τ i
  mono := fun i j hij ↦ hτ (Nat.lt_succ_iff.mp i.isLt) (Nat.lt_succ_iff.mp j.isLt) hij
  ξ := fun i ↦ a i
  stronglyMeasurable := fun i ↦ ha i i.isLt
  bounded := fun i ↦ hb i i.isLt

@[simp]
theorem toProcess_ofSimple {n : ℕ} {τ : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Set.Iic n)) (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (hb : ∀ i < n, ∃ C : ℝ, ∀ ω, |a i ω| ≤ C) (t : ℝ≥0) (ω : Ω) :
    (ofSimple n τ a hτ ha hb).toProcess t ω = Finance.simpleHolding τ n a t ω := by
  rw [toProcess_def, Finance.simpleHolding_def,
    ← Fin.sum_univ_eq_sum_range (fun i ↦ (Ioc (τ i) (τ (i + 1))).indicator (fun _ ↦ a i ω) t) n]
  rfl

@[simp]
theorem integral_ofSimple {n : ℕ} {τ : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ}
    (hτ : MonotoneOn τ (Set.Iic n)) (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (hb : ∀ i < n, ∃ C : ℝ, ∀ ω, |a i ω| ≤ C) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    (ofSimple n τ a hτ ha hb).integral W t ω = Finance.simpleGains τ n a W t ω := by
  rw [integral_def, Finance.simpleGains_def, ← Fin.sum_univ_eq_sum_range
    (fun i ↦ a i ω * (W (min (τ (i + 1)) t) ω - W (min (τ i) t) ω)) n]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [ofSimple, min_comm]; rfl

/-- Scale every height of an elementary integrand by a real constant, keeping the same grid. -/
def smul (c : ℝ) (K : ElementaryIntegrand ℱ) : ElementaryIntegrand ℱ where
  n := K.n
  s := K.s
  mono := K.mono
  ξ := fun i ω ↦ c * K.ξ i ω
  stronglyMeasurable := fun i ↦ (K.stronglyMeasurable i).const_mul c
  bounded := fun i ↦ let ⟨C, hC⟩ := K.bounded i
    ⟨|c| * C, fun ω ↦ by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC ω) (abs_nonneg c)⟩

@[simp]
theorem toProcess_smul (c : ℝ) (K : ElementaryIntegrand ℱ) (t : ℝ≥0) (ω : Ω) :
    (K.smul c).toProcess t ω = c * K.toProcess t ω := by
  simp only [toProcess_def, smul, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  by_cases ht : t ∈ Ioc (K.s i.castSucc) (K.s i.succ) <;> simp [ht]

@[simp]
theorem integral_smul (c : ℝ) (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    (K.smul c).integral W t ω = c * K.integral W t ω := by
  simp only [integral_def, smul, mul_sum, mul_assoc]

/-- Negate every height of an elementary integrand, keeping the same grid. -/
def neg (K : ElementaryIntegrand ℱ) : ElementaryIntegrand ℱ := K.smul (-1)

@[simp]
theorem toProcess_neg (K : ElementaryIntegrand ℱ) (t : ℝ≥0) (ω : Ω) :
    K.neg.toProcess t ω = -K.toProcess t ω := by
  simp [neg]

@[simp]
theorem integral_neg (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    K.neg.integral W t ω = -K.integral W t ω := by
  simp [neg]

/-- Every elementary integrand vanishes at time zero because `(s i, s (i + 1)]` is left-open. -/
@[simp]
theorem toProcess_eval_zero (K : ElementaryIntegrand ℱ) (ω : Ω) : K.toProcess 0 ω = 0 :=
  sum_eq_zero fun _ _ ↦ indicator_of_notMem (by simp) _

/-- Every elementary stochastic integral vanishes at time zero. -/
@[simp]
theorem integral_eval_zero (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    K.integral W 0 ω = 0 := by
  simp [integral_def]

/-- Two elementary integrands can be added on a common finite grid, preserving both their
processes and their elementary integrals against every process `W`. -/
theorem exists_add (K L : ElementaryIntegrand ℱ) :
    ∃ M : ElementaryIntegrand ℱ,
      (∀ t ω, M.toProcess t ω = K.toProcess t ω + L.toProcess t ω) ∧
      ∀ W t ω, M.integral W t ω = K.integral W t ω + L.integral W t ω := by
  classical
  let l : Fin K.n ⊕ Fin L.n → ℝ≥0 := Sum.elim (fun i ↦ K.s i.castSucc) (fun j ↦ L.s j.castSucc)
  let u : Fin K.n ⊕ Fin L.n → ℝ≥0 := Sum.elim (fun i ↦ K.s i.succ) (fun j ↦ L.s j.succ)
  let a : Fin K.n ⊕ Fin L.n → Ω → ℝ := Sum.elim K.ξ L.ξ
  have ha : ∀ x ∈ (Finset.univ : Finset (Fin K.n ⊕ Fin L.n)),
      StronglyMeasurable[ℱ (l x)] (a x) := fun x _ ↦
    Sum.casesOn x K.stronglyMeasurable L.stronglyMeasurable
  have hlu : ∀ x, l x ≤ u x := fun x ↦
    Sum.casesOn x (fun i ↦ K.mono i.castSucc_le_succ) (fun j ↦ L.mono j.castSucc_le_succ)
  have hb : ∀ x, ∃ C : ℝ, ∀ ω, ‖a x ω‖ ≤ C := fun x ↦ by
    cases x <;> simpa only [a, Sum.elim_inl, Sum.elim_inr, Real.norm_eq_abs] using
      by first | exact K.bounded _ | exact L.bounded _
  choose C hC using hb
  obtain ⟨n, τ, b, -, hτ, hb_meas, hb_bound, hhold, hgain⟩ :=
    Finance.exists_simpleHolding_simpleGains_eq_sum ℱ Finset.univ l u a ha
  refine ⟨ofSimple n τ b hτ.monotoneOn hb_meas (fun j hj ↦ ⟨∑ x, C x, fun ω ↦ by
    simpa only [Real.norm_eq_abs] using (hb_bound j hj ω).trans (sum_le_sum fun x _ ↦ hC x ω)⟩),
    fun t ω ↦ by rw [toProcess_ofSimple, hhold, Fintype.sum_sum_type]; rfl,
    fun W t ω ↦ by
      rw [integral_ofSimple, hgain]
      simp only [hlu, ite_true, Fintype.sum_sum_type, l, u, a, Sum.elim_inl, Sum.elim_inr,
        integral_def, min_comm]⟩

/-- The difference of two elementary integrands can be represented on a common finite grid,
preserving both their processes and their elementary integrals against every process `W`. -/
theorem exists_sub (K L : ElementaryIntegrand ℱ) :
    ∃ M : ElementaryIntegrand ℱ,
      (∀ t ω, M.toProcess t ω = K.toProcess t ω - L.toProcess t ω) ∧
      ∀ W t ω, M.integral W t ω = K.integral W t ω - L.integral W t ω := by
  obtain ⟨M, hP, hI⟩ := K.exists_add L.neg
  exact ⟨M, fun t ω ↦ by simpa only [toProcess_neg, sub_eq_add_neg] using hP t ω,
    fun W t ω ↦ by simpa only [integral_neg, sub_eq_add_neg] using hI W t ω⟩

/-- Extend the finite grid `K.s` constantly past `K.n` to interface with `ℕ`-indexed helpers. -/
private def sExt (K : ElementaryIntegrand ℱ) (i : ℕ) : ℝ≥0 :=
  K.s ⟨min i K.n, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- Extend the finite heights `K.ξ` by zero past `K.n` to interface with `ℕ`-indexed helpers. -/
private def ξExt (K : ElementaryIntegrand ℱ) (i : ℕ) : Ω → ℝ :=
  if hi : i < K.n then K.ξ ⟨i, hi⟩ else 0

private theorem sExt_of_le (K : ElementaryIntegrand ℱ) {i : ℕ} (hi : i ≤ K.n) :
    K.sExt i = K.s ⟨i, Nat.lt_succ_of_le hi⟩ := by
  simp only [sExt]; congr 1; ext; exact min_eq_left hi

private theorem monotone_sExt (K : ElementaryIntegrand ℱ) : Monotone K.sExt :=
  fun _ _ hij ↦ K.mono (Fin.mk_le_mk.mpr (min_le_min_right K.n hij))

private theorem stronglyMeasurable_ξExt (K : ElementaryIntegrand ℱ) {i : ℕ} (hi : i < K.n) :
    StronglyMeasurable[ℱ (K.sExt i)] (K.ξExt i) := by
  rw [K.sExt_of_le hi.le]
  simpa only [ξExt, hi, dite_true] using K.stronglyMeasurable ⟨i, hi⟩

private theorem bounded_ξExt (K : ElementaryIntegrand ℱ) {i : ℕ} (hi : i < K.n) :
    ∃ C : ℝ, ∀ ω, |K.ξExt i ω| ≤ C := by
  simpa only [ξExt, hi, dite_true] using K.bounded ⟨i, hi⟩

private theorem memLp_ξExt (K : ElementaryIntegrand ℱ) {P : Measure Ω} [IsFiniteMeasure P]
    {i : ℕ} (hi : i < K.n) : MemLp (K.ξExt i) 2 P := by
  obtain ⟨C, hC⟩ := K.bounded_ξExt hi
  exact MemLp.of_bound ((K.stronglyMeasurable_ξExt hi).mono (ℱ.le _)).aestronglyMeasurable
    C (.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hC ω)

private theorem toProcess_eq_simpleHolding (K : ElementaryIntegrand ℱ) :
    K.toProcess = Finance.simpleHolding K.sExt K.n K.ξExt := by
  ext t ω
  rw [toProcess_def, Finance.simpleHolding_def, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [K.sExt_of_le i.isLt.le, K.sExt_of_le i.isLt, ξExt, i.isLt, dite_true]; rfl

private theorem integral_eq_simpleGains (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) :
    K.integral W = Finance.simpleGains K.sExt K.n K.ξExt W := by
  ext t ω
  rw [integral_def, Finance.simpleGains_def, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [K.sExt_of_le i.isLt.le, K.sExt_of_le i.isLt, ξExt, i.isLt, dite_true, min_comm]; rfl

/-- The process of an elementary integrand is strongly predictable. -/
theorem isStronglyPredictable_toProcess (K : ElementaryIntegrand ℱ) :
    IsStronglyPredictable ℱ K.toProcess :=
  K.toProcess_eq_simpleHolding ▸
    Finance.isStronglyPredictable_simpleHolding fun _ hi ↦ K.stronglyMeasurable_ξExt hi

/-- Under any finite measure, an elementary integrand is Brownian integrable. -/
theorem brownianIntegrable_toProcess {P : Measure Ω} [IsFiniteMeasure P]
    (K : ElementaryIntegrand ℱ) : BrownianIntegrable ℱ P K.toProcess := by
  refine ⟨K.isStronglyPredictable_toProcess, fun T ↦ ?_⟩
  rw [K.toProcess_eq_simpleHolding, NNReal.comap_volume_restrict_Ioc, ← Probability.timeMeasure_def]
  exact (ℱ.memLp_predictableMeasure_iff P
    (Finance.isStronglyPredictable_simpleHolding fun _ hi ↦ K.stronglyMeasurable_ξExt hi) T 2).mp
    (Finance.memLp_simpleHolding_predictableMeasure (fun _ hi ↦ K.stronglyMeasurable_ξExt hi)
      (fun _ hi ↦ K.memLp_ξExt hi) T)

/-- The elementary integral of an adapted process is adapted. -/
theorem stronglyAdapted_integral (K : ElementaryIntegrand ℱ) {W : ℝ≥0 → Ω → ℝ}
    (hW : StronglyAdapted ℱ W) : StronglyAdapted ℱ (K.integral W) :=
  K.integral_eq_simpleGains W ▸ Finance.stronglyAdapted_simpleGains (K.monotone_sExt.monotoneOn _)
    (fun _ hi ↦ K.stronglyMeasurable_ξExt hi) hW

/-- Path continuity of the integrator passes pathwise to every elementary integral. -/
theorem continuous_integral (K : ElementaryIntegrand ℱ) {W : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hW : Continuous (W · ω)) : Continuous (K.integral W · ω) := by
  simp only [integral_def]
  exact continuous_finsetSum _ fun _ _ ↦ continuous_const.mul
    ((hW.comp (continuous_id.min continuous_const)).sub
      (hW.comp (continuous_id.min continuous_const)))

/-- Almost-sure path continuity of the integrator passes to every elementary integral. -/
theorem ae_continuous_integral (K : ElementaryIntegrand ℱ) {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω)) : ∀ᵐ ω ∂P, Continuous (K.integral W · ω) :=
  hW.mono fun _ hω ↦ K.continuous_integral hω

/-- The elementary integral against a martingale is a martingale. -/
theorem martingale_integral (K : ElementaryIntegrand ℱ) {P : Measure Ω} [SigmaFiniteFiltration P ℱ]
    {W : ℝ≥0 → Ω → ℝ} (hW : Martingale W ℱ P) : Martingale (K.integral W) ℱ P :=
  K.integral_eq_simpleGains W ▸ hW.simpleGains_of_bdd (K.monotone_sExt.monotoneOn _)
    (fun _ hi ↦ K.stronglyMeasurable_ξExt hi)
    (fun _ hi ↦ let ⟨C, hC⟩ := K.bounded_ξExt hi; ⟨C, .of_forall hC⟩)

/-- Every elementary integral against a filtered pre-Brownian motion lies in `L²` at every time. -/
theorem memLp_integral (K : ElementaryIntegrand ℱ) {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P) (t : ℝ≥0) :
    MemLp (K.integral W t) 2 P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hfun : K.integral W t = fun ω ↦ ∑ i ∈ range K.n,
      K.ξExt i ω * (W (min (K.sExt (i + 1)) t) ω - W (min (K.sExt i) t) ω) :=
    funext fun ω ↦ by rw [K.integral_eq_simpleGains W, Finance.simpleGains_def]
  rw [hfun]
  exact hW.memLp_sum_mul_sub_min (range K.n) (fun i _ ↦ K.monotone_sExt (Nat.le_succ i))
    (fun _ hi ↦ K.stronglyMeasurable_ξExt (mem_range.mp hi))
    (fun _ hi ↦ K.memLp_ξExt (mem_range.mp hi)) t

end ElementaryIntegrand

/-- `IsItoIntegral ℱ P W H I` asserts that `I` is a continuous Brownian Itô integral process of
the strongly predictable integrand `H` against `W`: at every time `t`, some sequence of elementary
integrands approximates `H` on `(0, t]` in pathwise square energy in probability (as a nonnegative
lower Lebesgue integral) while its elementary integrals at `t` converge in probability to `I t`. -/
structure IsItoIntegral (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (W H I : ℝ≥0 → Ω → ℝ) : Prop where
  /-- The integrand is predictable for the declared filtration. -/
  isStronglyPredictable : IsStronglyPredictable ℱ H
  /-- The integral process has almost surely continuous paths. -/
  ae_continuous : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)
  /-- At every time `t`, some elementary integrands approximate `H` in square energy in
  probability while their elementary integrals at `t` converge in probability to `I t`. -/
  exists_approx : ∀ t : ℝ≥0, ∃ K : ℕ → ElementaryIntegrand ℱ,
    (∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖(K m).toProcess s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) atTop (𝓝 0)) ∧
    TendstoInMeasure P (fun m ↦ (K m).integral W t) atTop (I t)

/-- The elementary integral of an elementary integrand against an almost surely continuous process
satisfies `IsItoIntegral`. -/
theorem ElementaryIntegrand.isItoIntegral (K : ElementaryIntegrand ℱ) {P : Measure Ω}
    {W : ℝ≥0 → Ω → ℝ} (hW : ∀ᵐ ω ∂P, Continuous (W · ω)) :
    IsItoIntegral ℱ P W K.toProcess (K.integral W) where
  isStronglyPredictable := K.isStronglyPredictable_toProcess
  ae_continuous := K.ae_continuous_integral hW
  exists_approx _ := ⟨fun _ ↦ K, fun _ hε ↦ by simp [hε.not_ge], fun _ hε ↦ by simp [hε.not_ge]⟩

namespace IsItoIntegral

variable {P : Measure Ω} {W B H H₁ H₂ K I I₁ I₂ J : ℝ≥0 → Ω → ℝ}

/-- The zero process is an Itô integral of the zero integrand. -/
theorem zero (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) :
    IsItoIntegral ℱ P W 0 0 where
  isStronglyPredictable := stronglyMeasurable_zero
  ae_continuous := .of_forall fun _ ↦ continuous_const
  exists_approx _ := ⟨fun _ ↦ ElementaryIntegrand.zero ℱ,
    fun _ hε ↦ by simp [hε.not_ge], fun _ hε ↦ by simp [hε.not_ge]⟩

/-- For an almost surely continuous process starting at zero almost surely, `W` itself is an Itô
integral of the constant integrand `1`. -/
theorem const_one (hcont : ∀ᵐ ω ∂P, Continuous (W · ω)) (h0 : ∀ᵐ ω ∂P, W 0 ω = 0) :
    IsItoIntegral ℱ P W (fun _ _ ↦ 1) W where
  isStronglyPredictable := stronglyMeasurable_const
  ae_continuous := hcont
  exists_approx t := by
    let E : ElementaryIntegrand ℱ := ElementaryIntegrand.single (s := 0) (t := t)
      (ξ := fun _ ↦ (1 : ℝ)) bot_le stronglyMeasurable_const ⟨1, fun _ ↦ by norm_num⟩
    refine ⟨fun _ ↦ E, fun ε hε ↦ ?_,
      TendstoInMeasure.congr_left (f := fun _ ↦ W t)
        (fun _ ↦ h0.mono fun ω hω ↦ by simp [E, hω]) (fun _ hε ↦ by simp [hε.not_ge])⟩
    have hzero (ω : Ω) : ∫⁻ s, ‖E.toProcess s ω - 1‖ₑ ^ 2 ∂Probability.timeMeasure t = 0 :=
      (lintegral_eq_zero_iff' ((E.isStronglyPredictable_toProcess.sub stronglyMeasurable_const).mono
        ℱ.predictable_le_prod |>.comp_measurable (measurable_id.prodMk measurable_const)
        |>.measurable.eNorm.pow_const 2).aemeasurable).2
        ((Probability.ae_mem_Ioc_timeMeasure t).mono fun s hs ↦ by simp [E, hs])
    simp [hzero, hε.not_ge]

/-- Indistinguishable processes have the same Itô integral predicate. -/
theorem congr_indist (hI : IsItoIntegral ℱ P W H I) (heq : I ≡ᵐ[P] J) :
    IsItoIntegral ℱ P W H J where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := heq.ae_continuous hI.ae_continuous
  exists_approx t :=
    let ⟨L, hE, hM⟩ := hI.exists_approx t; ⟨L, hE, hM.congr_right (heq.ae_eq_eval t)⟩

/-- Replacing the integrand by a predictable process agreeing `(timeMeasure T).prod P`-almost
everywhere on every finite horizon preserves `IsItoIntegral`. -/
theorem congr_integrand_ae [SFinite P] (hI : IsItoIntegral ℱ P W H I)
    (hK : IsStronglyPredictable ℱ K)
    (hHK : ∀ T : ℝ≥0, Function.uncurry H =ᵐ[(Probability.timeMeasure T).prod P]
      Function.uncurry K) :
    IsItoIntegral ℱ P W K I where
  isStronglyPredictable := hK
  ae_continuous := hI.ae_continuous
  exists_approx t := by
    obtain ⟨L, hE, hM⟩ := hI.exists_approx t
    have hsec : ∀ᵐ ω ∂P, (fun s ↦ H s ω) =ᵐ[Probability.timeMeasure t] (fun s ↦ K s ω) :=
      Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae (hHK t))
    refine ⟨L, fun ε hε ↦ (hE ε hε).congr fun m ↦ measure_congr ?_, hM⟩
    filter_upwards [hsec] with ω hω
    exact Iff.of_eq (congrArg (ε ≤ ·) (lintegral_congr_ae
      (hω.mono fun s hs ↦ congrArg (fun x ↦ ‖(L m).toProcess s ω - x‖ₑ ^ 2) hs)))

/-- Replacing the integrator by a process equal almost surely at each fixed time preserves
`IsItoIntegral`. -/
theorem congr_integrator_ae (hI : IsItoIntegral ℱ P W H I) (hWB : ∀ t : ℝ≥0, W t =ᵐ[P] B t) :
    IsItoIntegral ℱ P B H I where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := hI.ae_continuous
  exists_approx t := by
    obtain ⟨L, hE, hM⟩ := hI.exists_approx t
    refine ⟨L, hE, hM.congr_left fun m ↦ ?_⟩
    filter_upwards [ae_all_iff.mpr fun i : Fin (L m).n ↦ (hWB (min t ((L m).s i.succ))).and
      (hWB (min t ((L m).s i.castSucc)))] with ω hω
    exact sum_congr rfl fun i _ ↦ by rw [(hω i).1, (hω i).2]

/-- Every Itô integral vanishes almost surely at time zero. -/
theorem eval_zero_ae_eq_zero (hI : IsItoIntegral ℱ P W H I) : I 0 =ᵐ[P] 0 :=
  let ⟨_, _, hM⟩ := hI.exists_approx 0
  tendstoInMeasure_ae_unique hM fun _ hε ↦ by
    simp [ElementaryIntegrand.integral_eval_zero, hε.not_ge]

/-- Scaling both the integrand and the integral by a real constant preserves `IsItoIntegral`. -/
theorem const_mul (hI : IsItoIntegral ℱ P W H I) (c : ℝ) :
    IsItoIntegral ℱ P W (fun t ω ↦ c * H t ω) (fun t ω ↦ c * I t ω) where
  isStronglyPredictable := hI.isStronglyPredictable.const_mul c
  ae_continuous := hI.ae_continuous.mono fun _ hω ↦ continuous_const.mul hω
  exists_approx t := by
    rcases eq_or_ne c 0 with rfl | hc
    · exact ⟨fun _ ↦ ElementaryIntegrand.zero ℱ,
        fun _ hε ↦ by simp [hε.not_ge], fun _ hε ↦ by simp [hε.not_ge]⟩
    · obtain ⟨L, hE, hM⟩ := hI.exists_approx t
      refine ⟨fun m ↦ (L m).smul c, fun ε hε ↦ ?_, tendstoInMeasure_iff_norm.2 fun ε hε ↦ ?_⟩
      · have hc₂_pos : 0 < ‖c‖ₑ ^ 2 :=
          pos_iff_ne_zero.mpr (pow_ne_zero 2 (eNorm_pos.mpr hc).ne')
        have hc₂_ne_top : ‖c‖ₑ ^ 2 ≠ ∞ := by finiteness
        refine (hE (ε / ‖c‖ₑ ^ 2) (ENNReal.div_pos hε.ne' hc₂_ne_top)).congr fun m ↦ congrArg P ?_
        ext ω
        have hlint :
            (∫⁻ s, ‖((L m).smul c).toProcess s ω - c * H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t) =
              ‖c‖ₑ ^ 2 * ∫⁻ s, ‖(L m).toProcess s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t := by
          rw [← lintegral_const_mul' _ _ hc₂_ne_top]
          exact lintegral_congr fun s ↦ by
            rw [ElementaryIntegrand.toProcess_smul, ← mul_sub, eNorm_mul, mul_pow]
        simp only [mem_ofPred_eq, hlint, ENNReal.div_le_iff_le_mul (.inl hc₂_pos.ne')
          (.inl hc₂_ne_top), mul_comm]
      · refine (tendstoInMeasure_iff_norm.1 hM (ε / |c|) (div_pos hε (abs_pos.mpr hc))).congr
          fun m ↦ congrArg P ?_
        ext ω
        simp only [mem_ofPred_eq, ElementaryIntegrand.integral_smul, ← mul_sub, norm_mul,
          Real.norm_eq_abs, div_le_iff₀ (abs_pos.mpr hc), mul_comm]

/-- Negating both the integrand and the integral preserves `IsItoIntegral`. -/
theorem neg (hI : IsItoIntegral ℱ P W H I) :
    IsItoIntegral ℱ P W (fun t ω ↦ -H t ω) (fun t ω ↦ -I t ω) := by
  simpa only [neg_one_mul] using hI.const_mul (-1)

private theorem enorm_add_sq_le (x y : ℝ) :
    ‖x + y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
  have h := ENNReal.ofReal_le_ofReal (norm_sub_sq_le_two_mul x (-y) 0)
  simp only [sub_neg_eq_add, sub_zero, norm_neg, mul_add,
    ENNReal.ofReal_add (mul_nonneg zero_le_two (sq_nonneg _))
      (mul_nonneg zero_le_two (sq_nonneg _)),
    ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
    ENNReal.ofReal_ofNat] at h
  exact h

private theorem le_two_mul_add_two_mul_imp {ε a b : ℝ≥0∞} (h : ε ≤ 2 * a + 2 * b) :
    ε / 4 ≤ a ∨ ε / 4 ≤ b := by
  by_contra hnot; push Not at hnot; rcases hnot with ⟨ha, hb⟩
  by_cases htop : ε = ∞
  · subst htop
    simp only [ENNReal.top_div_of_ne_top (by norm_num : (4 : ℝ≥0∞) ≠ ∞)] at ha hb
    exact (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) ha,
      ENNReal.mul_lt_top (by norm_num) hb⟩).not_ge h
  · have hlt := ENNReal.add_lt_add
      (ENNReal.mul_lt_mul_right (a := 2) (by norm_num) (by norm_num) ha)
      (ENNReal.mul_lt_mul_right (a := 2) (by norm_num) (by norm_num) hb)
    have hsum : 2 * (ε / 4) + 2 * (ε / 4) = ε := by
      rw [← mul_add, ← two_mul, ← mul_assoc]; norm_num
      exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
    exact (hlt.trans_eq hsum).not_ge h

private theorem tendsto_lintegral_enorm_sq_of_enorm_le {t : ℝ≥0} {F F₁ F₂ : ℕ → ℝ≥0 → Ω → ℝ}
    (hm₁ : ∀ m ω, Measurable (fun s ↦ ‖F₁ m s ω‖ₑ ^ 2))
    (hbound : ∀ m s ω, ‖F m s ω‖ₑ ^ 2 ≤ 2 * ‖F₁ m s ω‖ₑ ^ 2 + 2 * ‖F₂ m s ω‖ₑ ^ 2)
    (h₁ : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖F₁ m s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) atTop (𝓝 0))
    (h₂ : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖F₂ m s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun m ↦ P {ω | ε ≤ ∫⁻ s, ‖F m s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) atTop (𝓝 0) := by
  have hε4 : 0 < ε / 4 := ENNReal.div_pos hε.ne' (by norm_num)
  have hlim : Tendsto (fun m ↦ P {ω | ε / 4 ≤ ∫⁻ s, ‖F₁ m s ω‖ₑ ^ 2 ∂Probability.timeMeasure t} +
      P {ω | ε / 4 ≤ ∫⁻ s, ‖F₂ m s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) atTop (𝓝 0) := by
    simpa only [zero_add] using (h₁ (ε / 4) hε4).add (h₂ (ε / 4) hε4)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ zero_le) fun m ↦ (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
  have hle : (∫⁻ s, ‖F m s ω‖ₑ ^ 2 ∂Probability.timeMeasure t) ≤
      2 * (∫⁻ s, ‖F₁ m s ω‖ₑ ^ 2 ∂Probability.timeMeasure t) +
      2 * (∫⁻ s, ‖F₂ m s ω‖ₑ ^ 2 ∂Probability.timeMeasure t) := by
    refine (lintegral_mono (hbound m · ω)).trans_eq ?_
    rw [lintegral_add_left ((hm₁ m ω).const_mul 2), lintegral_const_mul' _ _ (by norm_num),
      lintegral_const_mul' _ _ (by norm_num)]
  exact le_two_mul_add_two_mul_imp (hω.trans hle)

/-- Adding two integrands and their Itô integrals preserves `IsItoIntegral`. -/
theorem add (h₁ : IsItoIntegral ℱ P W H₁ I₁) (h₂ : IsItoIntegral ℱ P W H₂ I₂) :
    IsItoIntegral ℱ P W (fun t ω ↦ H₁ t ω + H₂ t ω) (fun t ω ↦ I₁ t ω + I₂ t ω) where
  isStronglyPredictable := h₁.isStronglyPredictable.add h₂.isStronglyPredictable
  ae_continuous := h₁.ae_continuous.mp (h₂.ae_continuous.mono fun _ hω₂ hω₁ ↦ hω₁.add hω₂)
  exists_approx t := by
    obtain ⟨K₁, hE₁, hM₁⟩ := h₁.exists_approx t
    obtain ⟨K₂, hE₂, hM₂⟩ := h₂.exists_approx t
    choose M hMP hMI using fun m ↦ (K₁ m).exists_add (K₂ m)
    refine ⟨M, fun _ hε ↦ tendsto_lintegral_enorm_sq_of_enorm_le
        (fun m ω ↦ (((K₁ m).isStronglyPredictable_toProcess.sub h₁.isStronglyPredictable).mono
          ℱ.predictable_le_prod |>.comp_measurable (measurable_id.prodMk measurable_const)
          |>.measurable.eNorm.pow_const 2))
        (fun m s ω ↦ by
          have : (M m).toProcess s ω - (H₁ s ω + H₂ s ω) =
              ((K₁ m).toProcess s ω - H₁ s ω) + ((K₂ m).toProcess s ω - H₂ s ω) := by
            rw [hMP m s ω]; ring
          exact this ▸ enorm_add_sq_le _ _) hE₁ hE₂ hε,
      tendstoInMeasure_iff_norm.2 fun ε hε ↦ ?_⟩
    have hlim : Tendsto (fun m ↦ P {ω | ε / 2 ≤ ‖(K₁ m).integral W t ω - I₁ t ω‖} +
        P {ω | ε / 2 ≤ ‖(K₂ m).integral W t ω - I₂ t ω‖}) atTop (𝓝 0) := by
      simpa only [zero_add] using (tendstoInMeasure_iff_norm.1 hM₁ (ε / 2) (half_pos hε)).add
        (tendstoInMeasure_iff_norm.1 hM₂ (ε / 2) (half_pos hε))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ ↦ zero_le) fun m ↦ (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
    simp only [mem_ofPred_eq, hMI m] at hω
    have htri : ‖(K₁ m).integral W t ω + (K₂ m).integral W t ω - (I₁ t ω + I₂ t ω)‖ ≤
        ‖(K₁ m).integral W t ω - I₁ t ω‖ + ‖(K₂ m).integral W t ω - I₂ t ω‖ := by
      simpa only [add_sub_add_comm] using
        norm_add_le ((K₁ m).integral W t ω - I₁ t ω) ((K₂ m).integral W t ω - I₂ t ω)
    by_contra hnot; simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hnot; linarith

/-- Subtracting two integrands and their Itô integrals preserves `IsItoIntegral`. -/
theorem sub (h₁ : IsItoIntegral ℱ P W H₁ I₁) (h₂ : IsItoIntegral ℱ P W H₂ I₂) :
    IsItoIntegral ℱ P W (fun t ω ↦ H₁ t ω - H₂ t ω) (fun t ω ↦ I₁ t ω - I₂ t ω) := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg

end IsItoIntegral

end TauCeti

namespace TauCeti.Probability.IsFilteredPreBrownianReal

open TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- Clipped grid dates `min (sExt i) t` for evaluating elementary integrals up to horizon `t`. -/
private def clipGrid (K : ElementaryIntegrand ℱ) (t : ℝ≥0) (i : ℕ) : ℝ≥0 := min (K.sExt i) t

/-- Clipped heights vanishing on intervals that have not yet started at time `t`. -/
private def clipHeight (K : ElementaryIntegrand ℱ) (t : ℝ≥0) (i : ℕ) : Ω → ℝ :=
  if K.sExt i < t then K.ξExt i else 0

private theorem clipGrid_monotoneOn (K : ElementaryIntegrand ℱ) (t : ℝ≥0) :
    MonotoneOn (clipGrid K t) (Set.Iic K.n) :=
  fun _ _ _ _ hij ↦ min_le_min_right t (K.monotone_sExt hij)

private theorem clipHeight_stronglyMeasurable (K : ElementaryIntegrand ℱ) (t : ℝ≥0)
    {i : ℕ} (hi : i < K.n) : StronglyMeasurable[ℱ (clipGrid K t i)] (clipHeight K t i) := by
  by_cases hlt : K.sExt i < t
  · rw [clipGrid, min_eq_left hlt.le]
    simpa only [clipHeight, hlt, ite_true] using K.stronglyMeasurable_ξExt hi
  · simpa only [clipHeight, hlt, ite_false] using
      (stronglyMeasurable_zero : StronglyMeasurable[ℱ (clipGrid K t i)] (fun _ : Ω ↦ (0 : ℝ)))

private theorem sum_clipHeight_eq_integral (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    (∑ i ∈ range K.n, clipHeight K t i ω *
      (W (clipGrid K t (i + 1)) ω - W (clipGrid K t i) ω)) = K.integral W t ω := by
  rw [K.integral_eq_simpleGains W, Finance.simpleGains_def]
  refine sum_congr rfl fun i _ ↦ ?_
  by_cases hlt : K.sExt i < t
  · simp [clipHeight, clipGrid, hlt]
  · have hge : t ≤ K.sExt i := le_of_not_gt hlt
    simp [clipHeight, clipGrid, hlt, min_eq_right hge,
      min_eq_right (hge.trans (K.monotone_sExt (Nat.le_succ i)))]

private theorem ofReal_elementaryEnergy_clip_eq (K : ElementaryIntegrand ℱ) (t : ℝ≥0) (ω : Ω) :
    ENNReal.ofReal (elementaryEnergy (clipGrid K t) (clipHeight K t) K.n ω) =
      ∫⁻ s, ‖K.toProcess s ω‖ₑ ^ 2 ∂timeMeasure t := by
  rw [K.toProcess_eq_simpleHolding,
    Finance.lintegral_enorm_sq_simpleHolding_timeMeasure (K.monotone_sExt.monotoneOn _),
    elementaryEnergy_def, ENNReal.ofReal_sum_of_nonneg]
  · refine sum_congr rfl fun i _ ↦ ?_
    by_cases hlt : K.sExt i < t
    · simp only [clipHeight, clipGrid, hlt, ite_true, min_eq_left hlt.le,
        ENNReal.ofReal_mul (sq_nonneg _), Real.enorm_sq_eq_ofReal_sq]
    · simp [clipHeight, hlt, le_of_not_gt hlt]
  · exact fun i _ ↦ mul_nonneg (sq_nonneg _) (sub_nonneg.mpr
      (NNReal.coe_le_coe.mpr (min_le_min_right t (K.monotone_sExt (Nat.le_succ i)))))

/-- Vanishing pathwise square energy in probability on `(0, t]` implies convergence to zero in
probability of the elementary Brownian integrals at time `t`. No path continuity of `W` or moment
bounds on the elementary integrands are required. -/
theorem tendstoInMeasure_integral_of_lintegral_enorm_sq
    (hW : IsFilteredPreBrownianReal ℱ W P) {ι : Type*} {l : Filter ι}
    {K : ι → ElementaryIntegrand ℱ} {t : ℝ≥0}
    (henergy : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖(K m).toProcess s ω‖ₑ ^ 2 ∂timeMeasure t}) l (𝓝 0)) :
    TendstoInMeasure P (fun m ↦ (K m).integral W t) l (fun _ ↦ 0) := by
  have he : TendstoInMeasure P
      (fun m ↦ elementaryEnergy (clipGrid (K m) t) (clipHeight (K m) t) (K m).n) l (fun _ ↦ 0) := by
    refine tendstoInMeasure_iff_norm.2 fun ε hε ↦
      (henergy (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)).congr fun m ↦ congrArg P ?_
    ext ω
    have hnn := elementaryEnergy_nonneg (a := clipHeight (K m) t) (clipGrid_monotoneOn (K m) t) ω
    simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs, abs_of_nonneg hnn,
      ← ofReal_elementaryEnergy_clip_eq (K m) t ω, ENNReal.ofReal_le_ofReal_iff hnn]
  exact (hW.tendstoInMeasure_sum_mul_sub_of_energy (fun m ↦ clipGrid_monotoneOn (K m) t)
    (fun m _ hi ↦ clipHeight_stronglyMeasurable (K m) t hi) he).congr_left
    fun m ↦ EventuallyEq.of_eq (funext (sum_clipHeight_eq_integral (K m) W t))

/-- Two limits in probability of elementary Brownian integrals whose elementary integrands
approximate the same predictable process in square energy in probability at time `t` are equal
almost surely. -/
theorem ae_eq_of_tendsto_lintegral_enorm_sq
    (hW : IsFilteredPreBrownianReal ℱ W P) {t : ℝ≥0} {H : ℝ≥0 → Ω → ℝ}
    (hH : IsStronglyPredictable ℱ H)
    {K L : ℕ → ElementaryIntegrand ℱ} {X Y : Ω → ℝ}
    (hKE : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖(K m).toProcess s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0))
    (hLE : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖(L m).toProcess s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0))
    (hKX : TendstoInMeasure P (fun m ↦ (K m).integral W t) atTop X)
    (hLY : TendstoInMeasure P (fun m ↦ (L m).integral W t) atTop Y) :
    X =ᵐ[P] Y := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  choose M hMP hMI using fun m ↦ (K m).exists_sub (L m)
  have hME : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖(M m).toProcess s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0) :=
    fun _ hε ↦ IsItoIntegral.tendsto_lintegral_enorm_sq_of_enorm_le
      (F₁ := fun m s ω ↦ (K m).toProcess s ω - H s ω)
      (fun m ω ↦ (((K m).isStronglyPredictable_toProcess.sub hH).mono
        ℱ.predictable_le_prod |>.comp_measurable (measurable_id.prodMk measurable_const)
        |>.measurable.eNorm.pow_const 2))
      (fun m s ω ↦ by
        have hEq : (M m).toProcess s ω =
            ((K m).toProcess s ω - H s ω) + (H s ω - (L m).toProcess s ω) := by
          rw [hMP m s ω]; ring
        simpa only [hEq, eNorm_sub_rev (H s ω)] using
          IsItoIntegral.enorm_add_sq_le ((K m).toProcess s ω - H s ω) (H s ω - (L m).toProcess s ω))
      hKE hLE hε
  have hdiff0 : TendstoInMeasure P
      (fun m ω ↦ (K m).integral W t ω - (L m).integral W t ω) atTop (fun _ ↦ 0) :=
    (hW.tendstoInMeasure_integral_of_lintegral_enorm_sq hME).congr_left
      fun m ↦ EventuallyEq.of_eq (funext (hMI m W t))
  have hdiffXY : TendstoInMeasure P
      (fun m ω ↦ (K m).integral W t ω - (L m).integral W t ω) atTop (fun ω ↦ X ω - Y ω) :=
    hKX.continuous_comp₂ hLY continuous_sub (.of_forall fun m ↦
      ((((K m).stronglyAdapted_integral hW.adapted.stronglyAdapted t).mono (ℱ.le t)).sub
        (((L m).stronglyAdapted_integral hW.adapted.stronglyAdapted t).mono (ℱ.le t)))
      |>.aestronglyMeasurable)
  exact (tendstoInMeasure_ae_unique hdiffXY hdiff0).mono fun _ hω ↦ sub_eq_zero.mp hω

/-- **Uniqueness of the Brownian Itô integral.** Against a filtered pre-Brownian motion, any two
Itô integrals of the same integrand are indistinguishable. Neither path continuity of `W` nor
usual filtration conditions are required. -/
theorem isItoIntegral_unique (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I J : ℝ≥0 → Ω → ℝ} (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W H J) :
    I ≡ᵐ[P] J :=
  indist_of_ae_eq_of_ae_continuous hI.ae_continuous hJ.ae_continuous fun t ↦
    let ⟨_, hKE, hKI⟩ := hI.exists_approx t
    let ⟨_, hLE, hLJ⟩ := hJ.exists_approx t
    hW.ae_eq_of_tendsto_lintegral_enorm_sq hI.isStronglyPredictable hKE hLE hKI hLJ

/-- **Representative independence of the Brownian Itô integral.** Itô integrals of predictable
integrands that agree `(timeMeasure T).prod P`-almost everywhere on every finite horizon are
indistinguishable. Neither local square integrability nor Brownian path continuity is required. -/
theorem itoIntegral_local_congr (hW : IsFilteredPreBrownianReal ℱ W P)
    {H K I J : ℝ≥0 → Ω → ℝ}
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J)
    (hHK : ∀ T : ℝ≥0, Function.uncurry H =ᵐ[(timeMeasure T).prod P] Function.uncurry K) :
    I ≡ᵐ[P] J := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact hW.isItoIntegral_unique (hI.congr_integrand_ae hJ.isStronglyPredictable hHK) hJ

end TauCeti.Probability.IsFilteredPreBrownianReal
