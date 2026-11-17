/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
public import TauCeti.Probability.Finance.SimpleStrategy.Basic
public import TauCeti.Probability.Process.TimeMeasure
public import TauCeti.Probability.Process.Indistinguishable
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.Normed.Group.Real
import TauCeti.Data.ENNReal.Inv
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Elementary predictable integrands and the Brownian Itô integral predicate

An elementary predictable integrand (`TauCeti.ElementaryIntegrand`) consists of a finite
nondecreasing `ℕ`-indexed grid `τ 0 ≤ τ 1 ≤ ⋯ ≤ τ n` together with uniformly bounded
`ℱ (τ i)`-measurable heights `a i` held on each left-open interval `(τ i, τ (i + 1)]`. Its
associated predictable process is `Finance.simpleHolding τ n a`
(`ElementaryIntegrand.toProcess`), and its elementary stochastic integral against a process `W`
is `Finance.simpleGains τ n a W` (`ElementaryIntegrand.integral`). Elementary integrands carry
`Zero`, `Add`, `Neg`, `Sub`, and `SMul ℝ` instances (`0`, `+`, `-`, `•`) preserving both
processes and elementary integrals on a refined common grid.

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

/-- An elementary predictable integrand: a finite nondecreasing `ℕ`-indexed grid
`τ 0 ≤ τ 1 ≤ ⋯ ≤ τ n` with uniformly bounded `ℱ (τ i)`-measurable heights `a i` held on
`(τ i, τ (i + 1)]`. -/
structure ElementaryIntegrand (ℱ : Filtration ℝ≥0 mΩ) where
  /-- The number of intervals in the grid. -/
  n : ℕ
  /-- The nondecreasing grid of dates `τ 0 ≤ τ 1 ≤ ⋯ ≤ τ n`. -/
  τ : ℕ → ℝ≥0
  /-- The grid dates are nondecreasing on `Iic n`. -/
  mono : MonotoneOn τ (Set.Iic n)
  /-- The random height held on `(τ i, τ (i + 1)]`. -/
  a : ℕ → Ω → ℝ
  /-- Each height is strongly measurable at the left endpoint of its interval. -/
  stronglyMeasurable : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i)
  /-- Each height is uniformly bounded. -/
  bounded : ∀ i < n, ∃ C : ℝ, ∀ ω, |a i ω| ≤ C

namespace ElementaryIntegrand

/-- Two elementary integrands with the same grid length, dates, and heights are equal. -/
theorem ext {K L : ElementaryIntegrand ℱ} (hn : K.n = L.n) (hτ : K.τ = L.τ) (ha : K.a = L.a) :
    K = L := by cases K; cases L; congr

/-- The predictable step process `t ↦ ∑ i ∈ range n, a i · 1_{(τ i, τ (i + 1)]}(t)` of an
elementary integrand. -/
def toProcess (K : ElementaryIntegrand ℱ) : ℝ≥0 → Ω → ℝ := Finance.simpleHolding K.τ K.n K.a

/-- Defining equation relating `ElementaryIntegrand.toProcess` to `Finance.simpleHolding`. -/
theorem toProcess_eq_simpleHolding (K : ElementaryIntegrand ℱ) :
    K.toProcess = Finance.simpleHolding K.τ K.n K.a := (rfl)

/-- Unfolding lemma for `ElementaryIntegrand.toProcess`. -/
theorem toProcess_def (K : ElementaryIntegrand ℱ) (t : ℝ≥0) (ω : Ω) :
    K.toProcess t ω =
      ∑ i ∈ range K.n, (Ioc (K.τ i) (K.τ (i + 1))).indicator (fun _ ↦ K.a i ω) t :=
  Finance.simpleHolding_def K.τ K.n K.a t ω

/-- The elementary stochastic integral
`t ↦ ∑ i ∈ range n, a i · (W (min (τ (i + 1)) t) - W (min (τ i) t))`
of an elementary integrand against a process `W`. -/
def integral (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  Finance.simpleGains K.τ K.n K.a W

/-- Defining equation relating `ElementaryIntegrand.integral` to `Finance.simpleGains`. -/
theorem integral_eq_simpleGains (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) :
    K.integral W = Finance.simpleGains K.τ K.n K.a W := (rfl)

/-- Unfolding lemma for `ElementaryIntegrand.integral`. -/
theorem integral_def (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    K.integral W t ω =
      ∑ i ∈ range K.n, K.a i ω * (W (min (K.τ (i + 1)) t) ω - W (min (K.τ i) t) ω) :=
  Finance.simpleGains_def K.τ K.n K.a W t ω

/-- The empty-grid elementary integrand, whose process and integral are identically zero. -/
protected def zero : ElementaryIntegrand ℱ where
  n := 0; τ := fun _ ↦ 0; mono := fun _ _ _ _ _ ↦ le_rfl; a := fun _ _ ↦ 0
  stronglyMeasurable := fun _ hi ↦ (Nat.not_lt_zero _ hi).elim
  bounded := fun _ hi ↦ (Nat.not_lt_zero _ hi).elim

instance : Zero (ElementaryIntegrand ℱ) := ⟨ElementaryIntegrand.zero⟩

private theorem zero_n : (0 : ElementaryIntegrand ℱ).n = 0 := rfl

@[simp] theorem toProcess_zero (t : ℝ≥0) (ω : Ω) : (0 : ElementaryIntegrand ℱ).toProcess t ω = 0 :=
  by simp only [toProcess_def, zero_n, range_zero, sum_empty]

@[simp] theorem integral_zero (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    (0 : ElementaryIntegrand ℱ).integral W t ω = 0 := by
  simp only [integral_def, zero_n, range_zero, sum_empty]

/-- A one-step elementary integrand holding a bounded `ℱ s`-measurable height `ξ` on `(s, t]`. -/
def single {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) (hb : ∃ C : ℝ, ∀ ω, |ξ ω| ≤ C) :
    ElementaryIntegrand ℱ where
  n := 1; τ := fun i ↦ if i = 0 then s else t; a := fun _ ↦ ξ; bounded := fun _ _ ↦ hb
  mono := fun i hi j hj hij ↦ by
    have : (i = 0 ∨ i = 1) ∧ (j = 0 ∨ j = 1) := by simp only [Set.mem_Iic] at hi hj; omega
    rcases this with ⟨rfl | rfl, rfl | rfl⟩ <;> simp [hst] at hij ⊢
  stronglyMeasurable := fun i hi ↦ by rcases Nat.lt_one_iff.mp hi with rfl; simpa using hξ

@[simp] theorem toProcess_single {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) (hb : ∃ C : ℝ, ∀ ω, |ξ ω| ≤ C) (u : ℝ≥0) (ω : Ω) :
    (single hst hξ hb).toProcess u ω = (Ioc s t).indicator (fun _ ↦ ξ ω) u := by
  simp [toProcess_def, single]

@[simp] theorem integral_single {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ s] ξ) (hb : ∃ C : ℝ, ∀ ω, |ξ ω| ≤ C)
    (W : ℝ≥0 → Ω → ℝ) (u : ℝ≥0) (ω : Ω) :
    (single hst hξ hb).integral W u ω = ξ ω * (W (min t u) ω - W (min s u) ω) := by
  simp [integral_def, single]

/-- Scale every height of an elementary integrand by a real constant, keeping the same grid. -/
protected def smul (c : ℝ) (K : ElementaryIntegrand ℱ) : ElementaryIntegrand ℱ where
  n := K.n; τ := K.τ; mono := K.mono; a := c • K.a
  stronglyMeasurable := fun i hi ↦ (K.stronglyMeasurable i hi).const_smul c
  bounded := fun i hi ↦ let ⟨C, hC⟩ := K.bounded i hi; ⟨|c| * C, fun ω ↦ by
    simpa only [Pi.smul_apply, smul_eq_mul, abs_mul] using
      mul_le_mul_of_nonneg_left (hC ω) (abs_nonneg c)⟩

instance : SMul ℝ (ElementaryIntegrand ℱ) := ⟨ElementaryIntegrand.smul⟩

@[simp] theorem toProcess_smul (c : ℝ) (K : ElementaryIntegrand ℱ) (t : ℝ≥0) (ω : Ω) :
    (c • K).toProcess t ω = c * K.toProcess t ω := Finance.simpleHolding_smul K.τ K.n c K.a t ω

@[simp] theorem integral_smul (c : ℝ) (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : (c • K).integral W t ω = c * K.integral W t ω :=
  Finance.simpleGains_smul K.τ K.n c K.a W t ω

/-- Negate every height of an elementary integrand, keeping the same grid. -/
protected def neg (K : ElementaryIntegrand ℱ) : ElementaryIntegrand ℱ := (-1 : ℝ) • K

instance : Neg (ElementaryIntegrand ℱ) := ⟨ElementaryIntegrand.neg⟩

private theorem neg_eq_smul (K : ElementaryIntegrand ℱ) : -K = (-1 : ℝ) • K := rfl

@[simp] theorem toProcess_neg (K : ElementaryIntegrand ℱ) (t : ℝ≥0) (ω : Ω) :
    (-K).toProcess t ω = -K.toProcess t ω := by rw [neg_eq_smul, toProcess_smul, neg_one_mul]

@[simp] theorem integral_neg (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    (-K).integral W t ω = -K.integral W t ω := by rw [neg_eq_smul, integral_smul, neg_one_mul]

/-- Every elementary integrand vanishes at time zero because `(τ i, τ (i + 1)]` is left-open. -/
@[simp] theorem toProcess_eval_zero (K : ElementaryIntegrand ℱ) (ω : Ω) : K.toProcess 0 ω = 0 := by
  rw [toProcess_def]; exact sum_eq_zero fun _ _ ↦ indicator_of_notMem (by simp) _

/-- Every elementary stochastic integral vanishes at time zero. -/
@[simp] theorem integral_eval_zero (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    K.integral W 0 ω = 0 := by simp [integral_def]

/-- Refine two elementary integrands onto a common strictly increasing grid, preserving both
their processes and their elementary integrals against every process `W`. -/
private theorem exists_add (K L : ElementaryIntegrand ℱ) :
    ∃ M : ElementaryIntegrand ℱ,
      (∀ t ω, M.toProcess t ω = K.toProcess t ω + L.toProcess t ω) ∧
      ∀ W t ω, M.integral W t ω = K.integral W t ω + L.integral W t ω := by
  classical
  let s : Finset (ℕ ⊕ ℕ) := (range K.n).disjSum (range L.n)
  let l := Sum.elim K.τ L.τ; let a := Sum.elim K.a L.a
  let u := Sum.elim (fun i ↦ K.τ (i + 1)) (fun j ↦ L.τ (j + 1))
  have ha : ∀ x ∈ s, StronglyMeasurable[ℱ (l x)] (a x) := by
    rintro (i | j) hx
    · exact K.stronglyMeasurable i (Finset.mem_range.mp (inl_mem_disjSum.mp hx))
    · exact L.stronglyMeasurable j (Finset.mem_range.mp (inr_mem_disjSum.mp hx))
  have hlu : ∀ x ∈ s, l x ≤ u x := by
    rintro (i | j) hx
    · have hi := Finset.mem_range.mp (inl_mem_disjSum.mp hx); exact K.mono hi.le hi (Nat.le_succ i)
    · have hj := Finset.mem_range.mp (inr_mem_disjSum.mp hx); exact L.mono hj.le hj (Nat.le_succ j)
  let C : ℕ ⊕ ℕ → ℝ := Sum.elim (fun i ↦ if hi : i < K.n then (K.bounded i hi).choose else 0)
    (fun j ↦ if hj : j < L.n then (L.bounded j hj).choose else 0)
  have hC : ∀ x ∈ s, ∀ ω, ‖a x ω‖ ≤ C x := by
    rintro (i | j) hx ω
    · have hi := Finset.mem_range.mp (inl_mem_disjSum.mp hx)
      simpa only [a, C, Sum.elim_inl, hi, dite_true, Real.norm_eq_abs] using
        (K.bounded i hi).choose_spec ω
    · have hj := Finset.mem_range.mp (inr_mem_disjSum.mp hx)
      simpa only [a, C, Sum.elim_inr, hj, dite_true, Real.norm_eq_abs] using
        (L.bounded j hj).choose_spec ω
  obtain ⟨n, τ, b, -, hτ, hb_meas, hb_bound, hhold, hgain⟩ :=
    Finance.exists_simpleHolding_simpleGains_eq_sum ℱ s l u a ha
  refine ⟨⟨n, τ, hτ.monotoneOn, b, hb_meas, fun j hj ↦ ⟨∑ x ∈ s, C x, fun ω ↦ by
      simpa only [Real.norm_eq_abs] using
        (hb_bound j hj ω).trans (sum_le_sum fun x hx ↦ hC x hx ω)⟩⟩,
    fun t ω ↦ by
      rw [K.toProcess_def, L.toProcess_def]
      exact (hhold t ω).trans (by simp [s, sum_disjSum, l, u, a]),
    fun W t ω ↦ by
      rw [K.integral_def, L.integral_def]
      refine (hgain W t ω).trans ?_
      rw [sum_congr rfl fun x hx ↦ ite_eq_left (hlu x hx)]; simp [s, sum_disjSum, l, u, a]⟩

/-- Sum of two elementary integrands on a common finite grid, preserving both processes and
elementary integrals against every process `W`. -/
protected def add (K L : ElementaryIntegrand ℱ) : ElementaryIntegrand ℱ := (exists_add K L).choose

instance : Add (ElementaryIntegrand ℱ) := ⟨ElementaryIntegrand.add⟩

private theorem add_def (K L : ElementaryIntegrand ℱ) : K + L = (exists_add K L).choose := rfl

@[simp] theorem toProcess_add (K L : ElementaryIntegrand ℱ) (t : ℝ≥0) (ω : Ω) :
    (K + L).toProcess t ω = K.toProcess t ω + L.toProcess t ω :=
  add_def K L ▸ (exists_add K L).choose_spec.1 t ω

@[simp] theorem integral_add (K L : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    (K + L).integral W t ω = K.integral W t ω + L.integral W t ω :=
  add_def K L ▸ (exists_add K L).choose_spec.2 W t ω

/-- Difference of two elementary integrands on a common finite grid, preserving both processes and
elementary integrals against every process `W`. -/
protected def sub (K L : ElementaryIntegrand ℱ) : ElementaryIntegrand ℱ := K + (-L)

instance : Sub (ElementaryIntegrand ℱ) := ⟨ElementaryIntegrand.sub⟩

private theorem sub_def (K L : ElementaryIntegrand ℱ) : K - L = K + (-L) := rfl

@[simp] theorem toProcess_sub (K L : ElementaryIntegrand ℱ) (t : ℝ≥0) (ω : Ω) :
    (K - L).toProcess t ω = K.toProcess t ω - L.toProcess t ω := by
  rw [sub_def, toProcess_add, toProcess_neg, ← sub_eq_add_neg]

@[simp] theorem integral_sub (K L : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    (K - L).integral W t ω = K.integral W t ω - L.integral W t ω := by
  rw [sub_def, integral_add, integral_neg, ← sub_eq_add_neg]

/-- Under any finite measure, each height of an elementary integrand belongs to `Lᵖ`. -/
theorem memLp_a (K : ElementaryIntegrand ℱ) {P : Measure Ω} [IsFiniteMeasure P] {p : ℝ≥0∞}
    {i : ℕ} (hi : i < K.n) : MemLp (K.a i) p P :=
  let ⟨C, hC⟩ := K.bounded i hi
  MemLp.of_bound ((K.stronglyMeasurable i hi).mono (ℱ.le _)).aestronglyMeasurable
    C (.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hC ω)

/-- The process of an elementary integrand is strongly predictable. -/
theorem isStronglyPredictable_toProcess (K : ElementaryIntegrand ℱ) :
    IsStronglyPredictable ℱ K.toProcess :=
  Finance.isStronglyPredictable_simpleHolding K.stronglyMeasurable

/-- Under any finite measure, an elementary integrand is Brownian integrable. -/
theorem brownianIntegrable_toProcess {P : Measure Ω} [IsFiniteMeasure P]
    (K : ElementaryIntegrand ℱ) : BrownianIntegrable ℱ P K.toProcess :=
  brownianIntegrable_iff_memLp_predictableMeasure.mpr ⟨K.isStronglyPredictable_toProcess,
    fun T ↦ Finance.memLp_simpleHolding_predictableMeasure K.stronglyMeasurable
      (fun _ hi ↦ K.memLp_a hi) T⟩

/-- The elementary integral of an adapted process is adapted. -/
theorem stronglyAdapted_integral (K : ElementaryIntegrand ℱ) {W : ℝ≥0 → Ω → ℝ}
    (hW : StronglyAdapted ℱ W) : StronglyAdapted ℱ (K.integral W) :=
  Finance.stronglyAdapted_simpleGains K.mono K.stronglyMeasurable hW

/-- Path continuity of the integrator passes pathwise to every elementary integral. -/
theorem continuous_integral (K : ElementaryIntegrand ℱ) {W : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hW : Continuous (W · ω)) : Continuous (K.integral W · ω) := by
  simp only [integral_def]
  exact continuous_finsetSum _ fun _ _ ↦ continuous_const.mul
    ((hW.comp (continuous_const.min continuous_id)).sub
      (hW.comp (continuous_const.min continuous_id)))

/-- Almost-sure path continuity of the integrator passes to every elementary integral. -/
theorem ae_continuous_integral (K : ElementaryIntegrand ℱ) {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
    (hW : ∀ᵐ ω ∂P, Continuous (W · ω)) : ∀ᵐ ω ∂P, Continuous (K.integral W · ω) :=
  hW.mono fun _ hω ↦ K.continuous_integral hω

/-- The elementary integral against a martingale is a martingale. -/
theorem martingale_integral (K : ElementaryIntegrand ℱ) {P : Measure Ω} [SigmaFiniteFiltration P ℱ]
    {W : ℝ≥0 → Ω → ℝ} (hW : Martingale W ℱ P) : Martingale (K.integral W) ℱ P :=
  hW.simpleGains_of_bdd K.mono K.stronglyMeasurable
    fun i hi ↦ let ⟨C, hC⟩ := K.bounded i hi; ⟨C, .of_forall hC⟩

/-- Every elementary integral against a filtered pre-Brownian motion lies in `L²` at every time. -/
theorem memLp_integral (K : ElementaryIntegrand ℱ) {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P) (t : ℝ≥0) : MemLp (K.integral W t) 2 P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  rw [show K.integral W t = _ from funext (K.integral_def W t)]
  exact hW.memLp_sum_mul_sub_min (range K.n)
    (fun i hi ↦ K.mono (Finset.mem_range.mp hi).le (Finset.mem_range.mp hi) (Nat.le_succ i))
    (fun i hi ↦ K.stronglyMeasurable i (Finset.mem_range.mp hi))
    (fun i hi ↦ K.memLp_a (Finset.mem_range.mp hi)) t

end ElementaryIntegrand

/-- `IsItoIntegral ℱ P W H I` asserts that `I` is a continuous Brownian Itô integral process of
the strongly predictable integrand `H` against `W`: at each time `t`, some sequence of elementary
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
  exists_approx _ := ⟨fun _ ↦ (0 : ElementaryIntegrand ℱ),
    fun _ hε ↦ by simp [hε.not_ge], fun _ hε ↦ by simp [hε.not_ge]⟩

/-- For an almost surely continuous process starting at zero almost surely, `W` itself is an Itô
integral of the constant integrand `1`. -/
theorem const_one (hcont : ∀ᵐ ω ∂P, Continuous (W · ω)) (h0 : ∀ᵐ ω ∂P, W 0 ω = 0) :
    IsItoIntegral ℱ P W (fun _ _ ↦ 1) W where
  isStronglyPredictable := stronglyMeasurable_const
  ae_continuous := hcont
  exists_approx t := by
    let E := ElementaryIntegrand.single (ℱ := ℱ) (s := 0) (t := t) (ξ := fun _ ↦ (1 : ℝ))
      bot_le stronglyMeasurable_const ⟨1, fun _ ↦ by norm_num⟩
    refine ⟨fun _ ↦ E, fun ε hε ↦ ?_, TendstoInMeasure.congr_left (f := fun _ ↦ W t)
      (fun _ ↦ h0.mono fun ω hω ↦ by simp [E, hω]) (fun _ hε ↦ by simp [hε.not_ge])⟩
    have hzero (ω : Ω) : ∫⁻ s, ‖E.toProcess s ω - 1‖ₑ ^ 2 ∂Probability.timeMeasure t = 0 :=
      (lintegral_eq_zero_iff' (IsStronglyPredictable.measurable_eNorm_pow
        (H := fun s ω ↦ E.toProcess s ω - 1)
        (E.isStronglyPredictable_toProcess.sub stronglyMeasurable_const) ω 2).aemeasurable).2
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
    exact hsec.mono fun ω hω ↦ Iff.of_eq (congrArg (ε ≤ ·) (lintegral_congr_ae
      (hω.mono fun s hs ↦ congrArg (fun x ↦ ‖(L m).toProcess s ω - x‖ₑ ^ 2) hs)))

/-- Replacing the integrator by a process equal almost surely at each fixed time preserves
`IsItoIntegral`. -/
theorem congr_integrator_ae (hI : IsItoIntegral ℱ P W H I) (hWB : ∀ t : ℝ≥0, W t =ᵐ[P] B t) :
    IsItoIntegral ℱ P B H I where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := hI.ae_continuous
  exists_approx t :=
    let ⟨L, hE, hM⟩ := hI.exists_approx t
    ⟨L, hE, hM.congr_left fun m ↦ (ae_all_iff.mpr fun i : ℕ ↦ hWB (min ((L m).τ i) t)).mono
      fun ω hω ↦ Finance.simpleGains_congr_price ω fun i _ ↦ hω i⟩

/-- Every Itô integral vanishes almost surely at time zero. -/
theorem eval_zero_ae_eq_zero (hI : IsItoIntegral ℱ P W H I) : I 0 =ᵐ[P] 0 :=
  let ⟨K, _, hM⟩ := hI.exists_approx 0
  tendstoInMeasure_ae_unique hM fun _ hε ↦ by simp [(K _).integral_eval_zero, hε.not_ge]

/-- Scaling both the integrand and the integral by a real constant preserves `IsItoIntegral`. -/
theorem const_mul (hI : IsItoIntegral ℱ P W H I) (c : ℝ) :
    IsItoIntegral ℱ P W (fun t ω ↦ c * H t ω) (fun t ω ↦ c * I t ω) where
  isStronglyPredictable := hI.isStronglyPredictable.const_mul c
  ae_continuous := hI.ae_continuous.mono fun _ hω ↦ continuous_const.mul hω
  exists_approx t := by
    rcases eq_or_ne c 0 with rfl | hc
    · exact ⟨fun _ ↦ 0, fun _ hε ↦ by simp [hε.not_ge], fun _ hε ↦ by simp [hε.not_ge]⟩
    · obtain ⟨L, hE, hM⟩ := hI.exists_approx t
      refine ⟨fun m ↦ c • L m, fun ε hε ↦ ?_, tendstoInMeasure_iff_norm.2 fun ε hε ↦ ?_⟩
      · have hc₂_pos : 0 < ‖c‖ₑ ^ 2 := pos_iff_ne_zero.mpr (pow_ne_zero 2 (eNorm_pos.mpr hc).ne')
        have hc₂_ne_top : ‖c‖ₑ ^ 2 ≠ ∞ := by finiteness
        refine (hE (ε / ‖c‖ₑ ^ 2) (ENNReal.div_pos hε.ne' hc₂_ne_top)).congr fun m ↦ congrArg P ?_
        ext ω
        have hlint : (∫⁻ s, ‖(c • L m).toProcess s ω - c * H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t) =
            ‖c‖ₑ ^ 2 * ∫⁻ s, ‖(L m).toProcess s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure t := by
          rw [← lintegral_const_mul' _ _ hc₂_ne_top]
          exact lintegral_congr fun s ↦ by
            rw [ElementaryIntegrand.toProcess_smul, ← mul_sub, eNorm_mul, mul_pow]
        simp only [mem_ofPred_eq, hlint, ENNReal.div_le_iff_le_mul (.inl hc₂_pos.ne')
          (.inl hc₂_ne_top), mul_comm]
      · refine (tendstoInMeasure_iff_norm.1 hM (ε / |c|) (div_pos hε (abs_pos.mpr hc))).congr
          fun m ↦ congrArg P ?_
        ext ω; simp only [mem_ofPred_eq, ElementaryIntegrand.integral_smul, ← mul_sub, norm_mul,
          Real.norm_eq_abs, div_le_iff₀ (abs_pos.mpr hc), mul_comm]

/-- Negating both the integrand and the integral preserves `IsItoIntegral`. -/
theorem neg (hI : IsItoIntegral ℱ P W H I) :
    IsItoIntegral ℱ P W (fun t ω ↦ -H t ω) (fun t ω ↦ -I t ω) := by
  simpa only [neg_one_mul] using hI.const_mul (-1)

private theorem tendsto_lintegral_enorm_sq_of_enorm_le {t : ℝ≥0} {F F₁ F₂ : ℕ → ℝ≥0 → Ω → ℝ}
    (hm₁ : ∀ m ω, Measurable (fun s ↦ ‖F₁ m s ω‖ₑ ^ 2))
    (hbound : ∀ m s ω, ‖F m s ω‖ₑ ^ 2 ≤ 2 * (‖F₁ m s ω‖ₑ ^ 2 + ‖F₂ m s ω‖ₑ ^ 2))
    (h₁ : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖F₁ m s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) atTop (𝓝 0))
    (h₂ : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖F₂ m s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) atTop (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun m ↦ P {ω | ε ≤ ∫⁻ s, ‖F m s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) atTop (𝓝 0) := by
  have hε4 : 0 < ε / (2 * 2) := ENNReal.div_pos hε.ne' (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using (h₁ (ε / (2 * 2)) hε4).add (h₂ (ε / (2 * 2)) hε4))
    (fun _ ↦ zero_le) fun m ↦ (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
  refine ENNReal.div_two_mul_le_or_div_two_mul_le_of_le_mul_add (hω.trans <|
    (lintegral_mono (hbound m · ω)).trans_eq ?_)
  rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left (hm₁ m ω)]

/-- Adding two integrands and their Itô integrals preserves `IsItoIntegral`. -/
theorem add (h₁ : IsItoIntegral ℱ P W H₁ I₁) (h₂ : IsItoIntegral ℱ P W H₂ I₂) :
    IsItoIntegral ℱ P W (fun t ω ↦ H₁ t ω + H₂ t ω) (fun t ω ↦ I₁ t ω + I₂ t ω) where
  isStronglyPredictable := h₁.isStronglyPredictable.add h₂.isStronglyPredictable
  ae_continuous := h₁.ae_continuous.mp (h₂.ae_continuous.mono fun _ hω₂ hω₁ ↦ hω₁.add hω₂)
  exists_approx t := by
    obtain ⟨K₁, hE₁, hM₁⟩ := h₁.exists_approx t; obtain ⟨K₂, hE₂, hM₂⟩ := h₂.exists_approx t
    refine ⟨fun m ↦ K₁ m + K₂ m, fun _ hε ↦ tendsto_lintegral_enorm_sq_of_enorm_le
        (fun m ω ↦ IsStronglyPredictable.measurable_eNorm_pow
          (H := fun s ω ↦ (K₁ m).toProcess s ω - H₁ s ω)
          ((K₁ m).isStronglyPredictable_toProcess.sub h₁.isStronglyPredictable) ω 2)
        (fun m s ω ↦ by
          have : (K₁ m + K₂ m).toProcess s ω - (H₁ s ω + H₂ s ω) =
              ((K₁ m).toProcess s ω - H₁ s ω) + ((K₂ m).toProcess s ω - H₂ s ω) := by
            rw [ElementaryIntegrand.toProcess_add]; ring
          exact this ▸ TauCeti.eNorm_add_sq_le _ _) hE₁ hE₂ hε,
      tendstoInMeasure_iff_norm.2 fun ε hε ↦ ?_⟩
    have hsum := (tendstoInMeasure_iff_norm.1 hM₁ (ε / 2) (half_pos hε)).add
      (tendstoInMeasure_iff_norm.1 hM₂ (ε / 2) (half_pos hε))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [zero_add] using hsum) (fun _ ↦ zero_le) fun m ↦
      (measure_mono fun ω hω ↦ ?_).trans (measure_union_le _ _)
    simp only [mem_ofPred_eq, ElementaryIntegrand.integral_add] at hω
    have htri : ‖(K₁ m).integral W t ω + (K₂ m).integral W t ω - (I₁ t ω + I₂ t ω)‖ ≤
        ‖(K₁ m).integral W t ω - I₁ t ω‖ + ‖(K₂ m).integral W t ω - I₂ t ω‖ := by
      simpa only [add_sub_add_comm] using
        norm_add_le ((K₁ m).integral W t ω - I₁ t ω) ((K₂ m).integral W t ω - I₂ t ω)
    by_contra hnot; simp only [Set.mem_union, mem_ofPred_eq, not_or, not_le] at hnot; linarith

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

private def clipGrid (K : ElementaryIntegrand ℱ) (t : ℝ≥0) (i : ℕ) : ℝ≥0 := min (K.τ i) t

private def clipHeight (K : ElementaryIntegrand ℱ) (t : ℝ≥0) (i : ℕ) : Ω → ℝ :=
  if K.τ i < t then K.a i else 0

private theorem clipGrid_monotoneOn (K : ElementaryIntegrand ℱ) (t : ℝ≥0) :
    MonotoneOn (clipGrid K t) (Set.Iic K.n) :=
  fun _ ha _ hb hab ↦ min_le_min_right t (K.mono ha hb hab)

private theorem clipHeight_stronglyMeasurable (K : ElementaryIntegrand ℱ) (t : ℝ≥0)
    {i : ℕ} (hi : i < K.n) : StronglyMeasurable[ℱ (clipGrid K t i)] (clipHeight K t i) := by
  by_cases hlt : K.τ i < t
  · rw [clipGrid, min_eq_left hlt.le]
    simpa only [clipHeight, hlt, ite_true] using K.stronglyMeasurable i hi
  · simpa only [clipHeight, hlt, ite_false] using
      (stronglyMeasurable_zero : StronglyMeasurable[ℱ (clipGrid K t i)] (fun _ : Ω ↦ (0 : ℝ)))

private theorem sum_clipHeight_eq_integral (K : ElementaryIntegrand ℱ) (W : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    (∑ i ∈ range K.n, clipHeight K t i ω *
      (W (clipGrid K t (i + 1)) ω - W (clipGrid K t i) ω)) = K.integral W t ω := by
  rw [K.integral_def]; refine sum_congr rfl fun i hi ↦ ?_
  by_cases hlt : K.τ i < t
  · simp [clipHeight, clipGrid, hlt]
  · have hi' := mem_range.mp hi; have hge := le_of_not_gt hlt
    simp [clipHeight, clipGrid, hlt, min_eq_right hge,
      min_eq_right (hge.trans (K.mono hi'.le hi' (Nat.le_succ i)))]

private theorem ofReal_elementaryEnergy_clip_eq (K : ElementaryIntegrand ℱ) (t : ℝ≥0) (ω : Ω) :
    ENNReal.ofReal (elementaryEnergy (clipGrid K t) (clipHeight K t) K.n ω) =
      ∫⁻ s, ‖K.toProcess s ω‖ₑ ^ 2 ∂timeMeasure t := by
  rw [ElementaryIntegrand.toProcess, Finance.lintegral_enorm_sq_simpleHolding_timeMeasure K.mono,
    elementaryEnergy_def, ENNReal.ofReal_sum_of_nonneg]
  · refine sum_congr rfl fun i _ ↦ ?_
    by_cases hlt : K.τ i < t
    · simp only [clipHeight, clipGrid, hlt, ite_true, min_eq_left hlt.le,
        ENNReal.ofReal_mul (sq_nonneg _), Real.enorm_sq_eq_ofReal_sq]
    · simp [clipHeight, hlt, le_of_not_gt hlt]
  · exact fun i hi ↦ mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (NNReal.coe_le_coe.mpr
      (min_le_min_right t (K.mono (mem_range.mp hi).le (mem_range.mp hi) (Nat.le_succ i)))))

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
    ext ω; have hnn := elementaryEnergy_nonneg (a := clipHeight (K m) t)
      (clipGrid_monotoneOn (K m) t) ω
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
    (hH : IsStronglyPredictable ℱ H) {K L : ℕ → ElementaryIntegrand ℱ} {X Y : Ω → ℝ}
    (hKE : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖(K m).toProcess s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0))
    (hLE : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖(L m).toProcess s ω - H s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0))
    (hKX : TendstoInMeasure P (fun m ↦ (K m).integral W t) atTop X)
    (hLY : TendstoInMeasure P (fun m ↦ (L m).integral W t) atTop Y) : X =ᵐ[P] Y := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hME : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖(K m - L m).toProcess s ω‖ₑ ^ 2 ∂timeMeasure t}) atTop (𝓝 0) :=
    fun _ hε ↦ IsItoIntegral.tendsto_lintegral_enorm_sq_of_enorm_le
      (F₁ := fun m s ω ↦ (K m).toProcess s ω - H s ω)
      (fun m ω ↦ IsStronglyPredictable.measurable_eNorm_pow
        (H := fun s ω ↦ (K m).toProcess s ω - H s ω)
        ((K m).isStronglyPredictable_toProcess.sub hH) ω 2)
      (fun m s ω ↦ by
        have hEq : (K m - L m).toProcess s ω =
            ((K m).toProcess s ω - H s ω) + (H s ω - (L m).toProcess s ω) := by
          rw [ElementaryIntegrand.toProcess_sub]; ring
        simpa only [hEq, eNorm_sub_rev (H s ω)] using
          TauCeti.eNorm_add_sq_le ((K m).toProcess s ω - H s ω) (H s ω - (L m).toProcess s ω))
      hKE hLE hε
  have hdiff0 : TendstoInMeasure P
      (fun m ω ↦ (K m).integral W t ω - (L m).integral W t ω) atTop (fun _ ↦ 0) :=
    (hW.tendstoInMeasure_integral_of_lintegral_enorm_sq hME).congr_left
      fun m ↦ EventuallyEq.of_eq (funext fun ω ↦ ElementaryIntegrand.integral_sub _ _ W t ω)
  have hdiffXY := hKX.continuous_comp₂ hLY continuous_sub (.of_forall fun m ↦
    (((K m).stronglyAdapted_integral hW.adapted.stronglyAdapted t).mono (ℱ.le t)
      |>.sub (((L m).stronglyAdapted_integral hW.adapted.stronglyAdapted t).mono (ℱ.le t)))
    |>.aestronglyMeasurable)
  exact (tendstoInMeasure_ae_unique hdiffXY hdiff0).mono fun _ hω ↦ sub_eq_zero.mp hω

/-- **Uniqueness of the Brownian Itô integral.** Against a filtered pre-Brownian motion, any two
Itô integrals of the same integrand are indistinguishable. Neither path continuity of `W` nor
usual filtration conditions are required. -/
theorem isItoIntegral_unique (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I J : ℝ≥0 → Ω → ℝ} (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W H J) :
    I ≡ᵐ[P] J :=
  indist_of_ae_eq_of_ae_continuous hI.ae_continuous hJ.ae_continuous fun t ↦
    let ⟨_, hKE, hKI⟩ := hI.exists_approx t; let ⟨_, hLE, hLJ⟩ := hJ.exists_approx t
    hW.ae_eq_of_tendsto_lintegral_enorm_sq hI.isStronglyPredictable hKE hLE hKI hLJ

/-- **Representative independence of the Brownian Itô integral.** Itô integrals of predictable
integrands that agree `(timeMeasure T).prod P`-almost everywhere on every finite horizon are
indistinguishable. Neither local square integrability nor Brownian path continuity is required. -/
theorem itoIntegral_local_congr (hW : IsFilteredPreBrownianReal ℱ W P)
    {H K I J : ℝ≥0 → Ω → ℝ} (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J)
    (hHK : ∀ T : ℝ≥0, Function.uncurry H =ᵐ[(timeMeasure T).prod P] Function.uncurry K) :
    I ≡ᵐ[P] J := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact hW.isItoIntegral_unique (hI.congr_integrand_ae hJ.isStronglyPredictable hHK) hJ

end TauCeti.Probability.IsFilteredPreBrownianReal
