/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.StdSimplex
public import TauCeti.MeasureTheory.OptimalTransport.MultiMarginal.Finite.Basic
public import TauCeti.Topology.Sion
import TauCeti.Algebra.BigOperators.Finset.Fiber

/-!
# Finite multi-marginal duality and complementary slackness

For finitely many finite spaces, the multi-marginal dual problem has one real-valued potential
per marginal, constrained so that their pointwise sum never exceeds the cost.

The basic identity in this file is the multi-marginal analogue of the transportation-matrix gap
formula: the difference between the cost of a plan and the value of a family of potentials is the
expectation of the pointwise dual gap. It gives weak duality and complementary slackness. A
finite-dimensional minimax argument then proves strong duality and attainment of both problems.
In particular, a feasible plan and feasible potentials are simultaneously optimal exactly when
every configuration carrying mass saturates the dual constraint.

The finite coupling model and its bridge to the measure-theoretic `TauCeti.MultiCoupling` API live
in `TauCeti.MeasureTheory.OptimalTransport.MultiMarginal.Finite.Basic`.

This completes the finite linear-programming part of multi-marginal duality. The index type is
assumed nonempty for strong duality: with no marginals the dual has no variables and cannot
represent an arbitrary cost on the one-point empty product.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer, 2009, Chapter 1, for the
  multi-marginal Kantorovich problem and its marginal-potential dual.
* M. Sion, *On general minimax theorems*, Pacific J. Math. 8 (1958), 171--176, through
  `Mathlib.Topology.Sion`.
* `TauCeti.MeasureTheory.OptimalTransport.Finite.Duality`, for the two-marginal gap and
  minimax and complementary-slackness arguments generalized here to a finite family.
-/

public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace TauCeti

universe u v

variable {ι : Type u} {X : ι → Type v} {μ : ∀ i, PMF (X i)}

section DualValue

variable [Fintype ι] [∀ i, Fintype (X i)]

/-- The value of a finite family of multi-marginal potentials: the sum of their expectations
against the prescribed marginals. -/
def finiteMultiDualValue (μ : ∀ i, PMF (X i)) (φ : ∀ i, X i → ℝ) : ℝ :=
  ∑ i, ∑ x, ((μ i) x).toReal * φ i x

/-- The defining finite-sum formula for the value of multi-marginal potentials. -/
theorem finiteMultiDualValue_def (μ : ∀ i, PMF (X i)) (φ : ∀ i, X i → ℝ) :
    finiteMultiDualValue μ φ = ∑ i, ∑ x, ((μ i) x).toReal * φ i x := (rfl)

/-- Adding a coordinatewise constant to the potentials adds the sum of those constants to the
dual value. -/
theorem finiteMultiDualValue_add_const (μ : ∀ i, PMF (X i)) (φ : ∀ i, X i → ℝ)
    (a : ι → ℝ) :
    finiteMultiDualValue μ (fun i x ↦ φ i x + a i) =
      finiteMultiDualValue μ φ + ∑ i, a i := by
  simp only [finiteMultiDualValue_def, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    PMF.sum_toReal_eq_one, one_mul, Finset.sum_add_distrib]

/-- The finite multi-marginal dual value is monotone in every potential. -/
theorem finiteMultiDualValue_mono {φ ψ : ∀ i, X i → ℝ} (h : ∀ i x, φ i x ≤ ψ i x) :
    finiteMultiDualValue μ φ ≤ finiteMultiDualValue μ ψ := by
  refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun x _ ↦ ?_
  exact mul_le_mul_of_nonneg_left (h i x) ENNReal.toReal_nonneg

end DualValue

section DualFeasible

variable [Fintype ι]

/-- A family of potentials is feasible for the finite multi-marginal dual problem when their
pointwise sum never exceeds the cost. -/
def FiniteMultiDualFeasible (c : (∀ i, X i) → ℝ) (φ : ∀ i, X i → ℝ) : Prop :=
  ∀ x, ∑ i, φ i (x i) ≤ c x

/-- The pointwise inequality defining finite multi-marginal dual feasibility. -/
@[simp]
theorem finiteMultiDualFeasible_iff {c : (∀ i, X i) → ℝ} {φ : ∀ i, X i → ℝ} :
    FiniteMultiDualFeasible c φ ↔ ∀ x, ∑ i, φ i (x i) ≤ c x := Iff.rfl

namespace FiniteMultiDualFeasible

/-- Apply a feasible family of potentials to one configuration. -/
theorem sum_le {c : (∀ i, X i) → ℝ} {φ : ∀ i, X i → ℝ}
    (h : FiniteMultiDualFeasible c φ) (x : ∀ i, X i) : ∑ i, φ i (x i) ≤ c x :=
  h x

/-- Lowering every potential preserves dual feasibility. -/
theorem mono {c : (∀ i, X i) → ℝ} {φ ψ : ∀ i, X i → ℝ}
    (h : FiniteMultiDualFeasible c φ) (hψ : ∀ i x, ψ i x ≤ φ i x) :
    FiniteMultiDualFeasible c ψ := by
  intro x
  exact (Finset.sum_le_sum fun i _ ↦ hψ i (x i)).trans (h x)

/-- Shifting each potential by a constant whose total is zero preserves dual feasibility. -/
theorem add_const {c : (∀ i, X i) → ℝ} {φ : ∀ i, X i → ℝ}
    (h : FiniteMultiDualFeasible c φ) (a : ι → ℝ) (ha : ∑ i, a i = 0) :
    FiniteMultiDualFeasible c (fun i x ↦ φ i x + a i) := by
  intro x
  rw [Finset.sum_add_distrib, ha, add_zero]
  exact h x

end FiniteMultiDualFeasible

end DualFeasible

section Finite

variable [Fintype ι] [∀ i, Fintype (X i)]
attribute [local instance] Classical.decEq

/-- Integrating the sum of the coordinate potentials against a coupling gives their dual value.
This is the finite change-of-variables identity behind multi-marginal weak duality. -/
theorem FiniteMultiCoupling.sum_mul_mass_eq_finiteMultiDualValue
    (π : FiniteMultiCoupling μ) (φ : ∀ i, X i → ℝ) :
    ∑ x, (∑ i, φ i (x i)) * (π.1 x).toReal = finiteMultiDualValue μ φ := by
  rw [finiteMultiDualValue_def]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← π.map_eval i]
  let _ : MeasurableSpace (∀ i, X i) := ⊤
  let _ : MeasurableSpace (X i) := ⊤
  have hmap := MeasureTheory.integral_map (μ := π.1.toMeasure) (φ := Function.eval i)
    (measurable_of_finite (Function.eval i)).aemeasurable
    (measurable_of_finite (φ i)).aestronglyMeasurable
  rw [PMF.toMeasure_map (Function.eval i) π.1
    (measurable_of_finite (Function.eval i))] at hmap
  simpa only [PMF.integral_eq_sum, smul_eq_mul, mul_comm] using hmap.symm

/-- The cost of a plan minus the value of a family of potentials is the mass-weighted sum of
the pointwise dual gaps. -/
theorem FiniteMultiCoupling.cost_sub_finiteMultiDualValue (π : FiniteMultiCoupling μ)
    (c : (∀ i, X i) → ℝ) (φ : ∀ i, X i → ℝ) :
    π.cost c - finiteMultiDualValue μ φ =
      ∑ x, (c x - ∑ i, φ i (x i)) * (π.1 x).toReal := by
  rw [FiniteMultiCoupling.cost_def, ← π.sum_mul_mass_eq_finiteMultiDualValue φ]
  simp only [sub_mul, Finset.sum_sub_distrib]

/-- **Finite multi-marginal weak duality.** Every feasible family of potentials has value at
most the cost of every feasible plan. -/
theorem FiniteMultiCoupling.finiteMultiDualValue_le_cost (π : FiniteMultiCoupling μ)
    {c : (∀ i, X i) → ℝ} {φ : ∀ i, X i → ℝ} (hφ : FiniteMultiDualFeasible c φ) :
    finiteMultiDualValue μ φ ≤ π.cost c := by
  rw [← sub_nonneg]
  rw [π.cost_sub_finiteMultiDualValue]
  exact Finset.sum_nonneg fun x _ ↦
    mul_nonneg (sub_nonneg.2 (hφ x)) ENNReal.toReal_nonneg

/-- **Finite multi-marginal complementary slackness.** A feasible plan and feasible family of
potentials have the same value exactly when every configuration carrying mass saturates the
dual constraint. -/
theorem FiniteMultiCoupling.cost_eq_finiteMultiDualValue_iff (π : FiniteMultiCoupling μ)
    {c : (∀ i, X i) → ℝ} {φ : ∀ i, X i → ℝ} (hφ : FiniteMultiDualFeasible c φ) :
    π.cost c = finiteMultiDualValue μ φ ↔
      ∀ x, π.1 x ≠ 0 → ∑ i, φ i (x i) = c x := by
  rw [← sub_eq_zero, π.cost_sub_finiteMultiDualValue,
    Finset.sum_eq_zero_iff_of_nonneg fun x _ ↦
      mul_nonneg (sub_nonneg.2 (hφ x)) ENNReal.toReal_nonneg]
  constructor
  · intro h x hx
    rcases mul_eq_zero.1 (h x (Finset.mem_univ x)) with hgap | hmass
    · linarith
    · rcases (ENNReal.toReal_eq_zero_iff (π.1 x)).1 hmass with hzero | htop
      · exact (hx hzero).elim
      · exact (π.1.apply_ne_top x htop).elim
  · intro h x _
    by_cases hx : π.1 x = 0
    · simp [hx]
    · rw [h x hx, sub_self, zero_mul]

/-- A complementary-slackness pair is simultaneously primal- and dual-optimal among all finite
multi-marginal plans and all feasible families of potentials. -/
theorem FiniteMultiCoupling.forall_cost_le_and_forall_finiteMultiDualValue_le_of_eq
    (π : FiniteMultiCoupling μ) {c : (∀ i, X i) → ℝ} {φ : ∀ i, X i → ℝ}
    (hφ : FiniteMultiDualFeasible c φ) (heq : π.cost c = finiteMultiDualValue μ φ) :
    (∀ σ : FiniteMultiCoupling μ, π.cost c ≤ σ.cost c) ∧
      ∀ ψ, FiniteMultiDualFeasible c ψ → finiteMultiDualValue μ ψ ≤ finiteMultiDualValue μ φ := by
  constructor
  · intro σ
    rw [heq]
    exact σ.finiteMultiDualValue_le_cost hφ
  · intro ψ hψ
    rw [← heq]
    exact π.finiteMultiDualValue_le_cost hψ

end Finite

/-! ### Attainment on finite spaces -/

section Attainment

variable [Fintype ι] [∀ i, Fintype (X i)]
attribute [local instance] Classical.decEq

/-- Real-valued probability vectors on the finite dependent product. -/
private def multiStdSimplexSet : Set ((∀ i, X i) → ℝ) :=
  {f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}

/-- Real-valued plans with the prescribed coordinate marginals. -/
private def MultiRealPlans (μ : ∀ i, PMF (X i)) : Set ((∀ i, X i) → ℝ) :=
  {f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1 ∧
    ∀ i a, ∑ x with x i = a, f x = ((μ i) a).toReal}

/-- The cost functional on real-valued plans. -/
private def multiCostFun (c : (∀ i, X i) → ℝ) (f : (∀ i, X i) → ℝ) : ℝ :=
  ∑ x, c x * f x

private theorem FiniteMultiCoupling.toRealFun_mem_multiRealPlans (π : FiniteMultiCoupling μ) :
    (fun x ↦ (π.1 x).toReal) ∈ MultiRealPlans μ := by
  refine ⟨fun _ ↦ ENNReal.toReal_nonneg, PMF.sum_toReal_eq_one π.1, fun i a ↦ ?_⟩
  have h := congrArg (fun ν : PMF (X i) ↦ (ν a).toReal) (π.map_eval i)
  rw [PMF.map_apply, tsum_fintype] at h
  rw [← h, ENNReal.toReal_sum (fun x _ ↦ by
    by_cases hx : a = x i <;> simp [hx, π.1.apply_ne_top x])]
  simp only [Finset.sum_filter, apply_ite, ENNReal.toReal_zero, eq_comm]

/-- Turn a nonnegative real plan of total mass one into a finite multi-marginal coupling. -/
private def FiniteMultiCoupling.ofRealFun {f : (∀ i, X i) → ℝ}
    (hf : f ∈ MultiRealPlans μ) : FiniteMultiCoupling μ := by
  let π : PMF (∀ i, X i) := PMF.ofFintype (fun x ↦ ENNReal.ofReal (f x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun x _ ↦ hf.1 x, hf.2.1, ENNReal.ofReal_one])
  refine ⟨π, fun i ↦ ?_⟩
  ext a
  simp only [π, PMF.map_ofFintype, PMF.ofFintype_apply]
  rw [← ENNReal.ofReal_sum_of_nonneg fun x hx ↦ hf.1 x,
    hf.2.2 i a, ENNReal.ofReal_toReal ((μ i).apply_ne_top a)]

private theorem FiniteMultiCoupling.toRealFun_ofRealFun {f : (∀ i, X i) → ℝ}
    (hf : f ∈ MultiRealPlans μ) :
    (fun x ↦ ((FiniteMultiCoupling.ofRealFun hf).1 x).toReal) = f := by
  funext x
  exact ENNReal.toReal_ofReal (hf.1 x)

private theorem FiniteMultiCoupling.cost_eq_multiCostFun (π : FiniteMultiCoupling μ)
    (c : (∀ i, X i) → ℝ) :
    π.cost c = multiCostFun c (fun x ↦ (π.1 x).toReal) := π.cost_def c

private theorem FiniteMultiCoupling.cost_ofRealFun {f : (∀ i, X i) → ℝ}
    (hf : f ∈ MultiRealPlans μ) (c : (∀ i, X i) → ℝ) :
    (FiniteMultiCoupling.ofRealFun hf).cost c = multiCostFun c f := by
  rw [FiniteMultiCoupling.cost_eq_multiCostFun,
    FiniteMultiCoupling.toRealFun_ofRealFun]

private theorem convex_multiStdSimplexSet : Convex ℝ (multiStdSimplexSet (X := X)) := by
  intro f hf g hg a b ha hb hab
  refine ⟨fun x ↦ add_nonneg (smul_nonneg ha (hf.1 x)) (smul_nonneg hb (hg.1 x)), ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hf.2, hg.2, mul_one, hab]

private theorem isCompact_multiStdSimplexSet :
    IsCompact (multiStdSimplexSet (X := X)) := by
  have h : multiStdSimplexSet (X := X) =
      Set.range fun t : Convexity.StdSimplex ℝ (∀ i, X i) ↦ ⇑t.weights := by
    rw [Convexity.StdSimplex.range_toFun_comp_weights]
    ext f
    simp [multiStdSimplexSet]
  rw [h]
  exact isCompact_range
    (continuous_pi fun x ↦ Convexity.StdSimplex.continuous_weights_apply ℝ x)

private theorem isClosed_multiRealPlans : IsClosed (MultiRealPlans μ) := by
  have hnonneg : IsClosed {f : (∀ i, X i) → ℝ | ∀ x, 0 ≤ f x} := by
    simpa only [Set.ofPred_forall] using
      isClosed_iInter fun x ↦ isClosed_le continuous_const (continuous_apply x)
  have hsum : IsClosed {f : (∀ i, X i) → ℝ | ∑ x, f x = 1} :=
    isClosed_eq (continuous_finsetSum _ fun x _ ↦ continuous_apply x) continuous_const
  have hmarg : IsClosed {f : (∀ i, X i) → ℝ |
      ∀ i a, ∑ x with x i = a, f x = ((μ i) a).toReal} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun a ↦
      isClosed_eq (continuous_finsetSum _ fun x _ ↦ continuous_apply x) continuous_const
  exact hnonneg.inter (hsum.inter hmarg)

private theorem multiRealPlans_subset_multiStdSimplexSet :
    MultiRealPlans μ ⊆ multiStdSimplexSet := fun _ hf ↦ ⟨hf.1, hf.2.1⟩

private theorem isCompact_multiRealPlans : IsCompact (MultiRealPlans μ) :=
  IsCompact.of_isClosed_subset isCompact_multiStdSimplexSet isClosed_multiRealPlans
    multiRealPlans_subset_multiStdSimplexSet

private theorem multiRealPlans_nonempty : (MultiRealPlans μ).Nonempty :=
  ⟨fun x ↦ ((FiniteMultiCoupling.independent μ).1 x).toReal,
    FiniteMultiCoupling.toRealFun_mem_multiRealPlans _⟩

private theorem continuous_multiCostFun (c : (∀ i, X i) → ℝ) :
    Continuous (multiCostFun c) := by
  exact continuous_finsetSum _ fun x _ ↦ continuous_const.mul (continuous_apply x)

/-- **Finite multi-marginal primal attainment.** Every real cost has a minimizing coupling on
a nonempty finite family of finite spaces. -/
theorem FiniteMultiCoupling.exists_forall_cost_le (c : (∀ i, X i) → ℝ)
    (μ : ∀ i, PMF (X i)) :
    ∃ π : FiniteMultiCoupling μ, ∀ σ : FiniteMultiCoupling μ, π.cost c ≤ σ.cost c := by
  obtain ⟨f, hf, hmin⟩ := isCompact_multiRealPlans.exists_isMinOn multiRealPlans_nonempty
    (continuous_multiCostFun c).continuousOn
  refine ⟨FiniteMultiCoupling.ofRealFun hf, fun σ ↦ ?_⟩
  rw [FiniteMultiCoupling.cost_ofRealFun, FiniteMultiCoupling.cost_eq_multiCostFun]
  exact isMinOn_iff.1 hmin _ σ.toRealFun_mem_multiRealPlans

end Attainment

/-! ### Dual attainment

Shifting the potentials by constants of total zero changes neither dual feasibility nor the dual
value, so an arbitrary feasible family may first be *normalised*: subtract from each potential its
maximum and return the accumulated total to one coordinate, after which no potential exceeds a
bound `M` for the cost. A normalised family is then *confined to a box*: at a marginal point of
zero weight the potential may be lowered outright, and at a point of positive weight that weight
turns a lower bound for the dual value into a lower bound for the potential. Families of value at
least `-M` therefore have representatives in a compact box, where the dual value is attained. -/

section DualAttainment

variable [Fintype ι] [∀ i, Fintype (X i)] [Nonempty ι]
attribute [local instance] Classical.decEq

/-- **Normalising a dual-feasible family.** Subtracting from each potential its maximum and
returning the accumulated total to one coordinate preserves dual feasibility and the dual value,
and leaves every potential below any bound `M` for the cost. -/
private theorem exists_normalized_of_feasible {c : (∀ i, X i) → ℝ} {M : ℝ}
    (hM : ∀ z, |c z| ≤ M) {φ : ∀ i, X i → ℝ} (hφ : FiniteMultiDualFeasible c φ) :
    ∃ ψ, FiniteMultiDualFeasible c ψ ∧
      finiteMultiDualValue μ ψ = finiteMultiDualValue μ φ ∧ ∀ i x, ψ i x ≤ M := by
  have hX : ∀ i, Nonempty (X i) := fun i ↦ ⟨(μ i).support_nonempty.some⟩
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM fun i ↦ Classical.choice (hX i))
  choose xmax hxmax using fun i ↦ by
    have := hX i
    exact Finite.exists_max (φ i)
  let S : ℝ := ∑ i, φ i (xmax i)
  let a : ι → ℝ := fun i ↦ -φ i (xmax i) + if i = i₀ then S else 0
  let ψ : ∀ i, X i → ℝ := fun i x ↦ φ i x + a i
  have hasum : ∑ i, a i = 0 := by
    simp [a, S, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hψfeas : FiniteMultiDualFeasible c ψ := hφ.add_const a hasum
  have hψvalue : finiteMultiDualValue μ ψ = finiteMultiDualValue μ φ := by
    dsimp only [ψ]
    rw [finiteMultiDualValue_add_const, hasum, add_zero]
  -- Off the base coordinate the normalised potential is nonpositive.
  have hψ_nonbase : ∀ i, i ≠ i₀ → ∀ x, ψ i x ≤ 0 := by
    intro i hi x
    simp only [ψ, a, hi, ↓reduceIte, add_zero]
    linarith [hxmax i x]
  refine ⟨ψ, hψfeas, hψvalue, fun i x ↦ ?_⟩
  by_cases hi : i = i₀
  -- On the base coordinate, feasibility at a configuration built from the maximisers applies.
  · subst i
    let z : ∀ i, X i := Function.update xmax i₀ x
    have hsum : ∑ i, ψ i (z i) = ψ i₀ x := by
      rw [Finset.sum_eq_single i₀]
      · simp [z]
      · intro j _ hj
        have hji : j ≠ i₀ := hj
        simp [z, hji, ψ, a]
      · exact fun hi ↦ (hi (Finset.mem_univ i₀)).elim
    rw [← hsum]
    exact (hψfeas z).trans ((le_abs_self _).trans (hM z))
  · exact (hψ_nonbase i hi x).trans hM0

/-- **Confining a normalised family to a box.** A dual-feasible family bounded above by a cost
bound `M` and of dual value at least `-M` agrees in value with one confined to the box of radius
`B`, provided `B` dominates `(card ι + 2) * M` and its quotients by the positive marginal
weights. At a marginal point of zero weight the potential is simply replaced by `-B`. -/
private theorem exists_bounded_of_normalized {c : (∀ i, X i) → ℝ} {M B : ℝ}
    (hM : ∀ z, |c z| ≤ M) (hD : (Fintype.card ι + 2 : ℝ) * M ≤ B)
    (hquot : ∀ i x, ((μ i) x).toReal ≠ 0 →
      (Fintype.card ι + 2 : ℝ) * M / ((μ i) x).toReal ≤ B)
    {ψ : ∀ i, X i → ℝ} (hψfeas : FiniteMultiDualFeasible c ψ) (hψ_le : ∀ i x, ψ i x ≤ M)
    (hval : -M ≤ finiteMultiDualValue μ ψ) :
    ∃ χ, FiniteMultiDualFeasible c χ ∧
      finiteMultiDualValue μ χ = finiteMultiDualValue μ ψ ∧ ∀ i x, |χ i x| ≤ B := by
  have hX : ∀ i, Nonempty (X i) := fun i ↦ ⟨(μ i).support_nonempty.some⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM fun i ↦ Classical.choice (hX i))
  have hcard : (1 : ℝ) ≤ (Fintype.card ι : ℝ) :=
    Nat.one_le_cast.2 (Fintype.card_pos_iff.2 ‹Nonempty ι›)
  have hcard1 : (0 : ℝ) ≤ ((Fintype.card ι : ℝ) + 1) * M := mul_nonneg (by linarith) hM0
  have hMB : M ≤ B := by nlinarith
  have hB0 : 0 ≤ B := hM0.trans hMB
  -- Each marginal contributes at most `M` to the dual value, so it contributes at least
  -- `-((card ι) * M + M)` as well.
  let E : ι → ℝ := fun i ↦ ∑ x, ((μ i) x).toReal * ψ i x
  have hE_le : ∀ i, E i ≤ M := by
    intro i
    calc E i ≤ ∑ x, ((μ i) x).toReal * M :=
          Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hψ_le i x)
            ENNReal.toReal_nonneg
      _ = M := by rw [← Finset.sum_mul, PMF.sum_toReal_eq_one, one_mul]
  have hEsum : ∑ i, E i = finiteMultiDualValue μ ψ := by
    simp only [E, finiteMultiDualValue_def]
  have hE_lower : ∀ i, -((Fintype.card ι : ℝ) * M + M) ≤ E i := by
    intro i
    have hrest : ∑ j ∈ Finset.univ.erase i, E j ≤ (Fintype.card ι : ℝ) * M := calc
      ∑ j ∈ Finset.univ.erase i, E j ≤ ∑ j ∈ Finset.univ.erase i, M :=
        Finset.sum_le_sum fun j _ ↦ hE_le j
      _ ≤ ∑ _j : ι, M := by
        gcongr
        exact Finset.erase_subset _ _
      _ = (Fintype.card ι : ℝ) * M := by simp
    have hsplit : finiteMultiDualValue μ ψ = E i + ∑ j ∈ Finset.univ.erase i, E j := by
      rw [← hEsum]
      calc
        ∑ j, E j = ∑ j ∈ Finset.univ.erase i, E j + E i :=
          (Finset.sum_erase_add Finset.univ E (Finset.mem_univ i)).symm
        _ = E i + ∑ j ∈ Finset.univ.erase i, E j := add_comm _ _
    linarith
  let χ : ∀ i, X i → ℝ := fun i x ↦
    if ((μ i) x).toReal = 0 then -B else ψ i x
  have hχvalue : finiteMultiDualValue μ χ = finiteMultiDualValue μ ψ := by
    simp only [finiteMultiDualValue_def, χ]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : ((μ i) x).toReal = 0 <;> simp [hx]
  have hχ_le : ∀ i x, χ i x ≤ M := by
    intro i x
    by_cases hx : ((μ i) x).toReal = 0
    · simp [χ, hx]
      linarith
    · simpa only [χ, hx, ↓reduceIte] using hψ_le i x
  -- At a point of positive weight, that weight converts the bound on `E i` into a bound on `ψ`.
  have hχ_lower : ∀ i x, -B ≤ χ i x := by
    intro i x
    by_cases hx : ((μ i) x).toReal = 0
    · simp [χ, hx]
    · simp only [χ, hx, ↓reduceIte]
      have hw : 0 < ((μ i) x).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hx)
      have hothers : ∑ y ∈ Finset.univ.erase x, ((μ i) y).toReal * ψ i y ≤ M := calc
        ∑ y ∈ Finset.univ.erase x, ((μ i) y).toReal * ψ i y
            ≤ ∑ y ∈ Finset.univ.erase x, ((μ i) y).toReal * M :=
              Finset.sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_left (hψ_le i y)
                ENNReal.toReal_nonneg
        _ ≤ ∑ y, ((μ i) y).toReal * M := by
              gcongr
              exact Finset.erase_subset _ _
        _ = M := by rw [← Finset.sum_mul, PMF.sum_toReal_eq_one, one_mul]
      have hsplit : E i = ((μ i) x).toReal * ψ i x +
          ∑ y ∈ Finset.univ.erase x, ((μ i) y).toReal * ψ i y := by
        dsimp only [E]
        calc
          ∑ y, ((μ i) y).toReal * ψ i y =
              ∑ y ∈ Finset.univ.erase x, ((μ i) y).toReal * ψ i y +
                ((μ i) x).toReal * ψ i x :=
            (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ x)).symm
          _ = ((μ i) x).toReal * ψ i x +
              ∑ y ∈ Finset.univ.erase x, ((μ i) y).toReal * ψ i y := add_comm _ _
      have hprod : -((Fintype.card ι + 2 : ℝ) * M) ≤ ((μ i) x).toReal * ψ i x := by
        linarith [hE_lower i]
      have := (div_le_iff₀ hw).1 (hquot i x hx)
      nlinarith
  -- Feasibility survives the replacement: a configuration meeting a zero-weight point has one
  -- coordinate lowered to `-B`, which the bound `hD` more than pays for.
  have hχfeas : FiniteMultiDualFeasible c χ := by
    intro z
    by_cases hz : ∃ i, ((μ i) (z i)).toReal = 0
    · obtain ⟨i, hi⟩ := hz
      have hrest : ∑ j ∈ Finset.univ.erase i, χ j (z j) ≤ (Fintype.card ι : ℝ) * M := calc
        ∑ j ∈ Finset.univ.erase i, χ j (z j) ≤ ∑ j ∈ Finset.univ.erase i, M :=
          Finset.sum_le_sum fun j _ ↦ hχ_le j (z j)
        _ ≤ ∑ _j : ι, M := by
          gcongr
          exact Finset.erase_subset _ _
        _ = (Fintype.card ι : ℝ) * M := by simp
      calc
        ∑ j, χ j (z j) = χ i (z i) + ∑ j ∈ Finset.univ.erase i, χ j (z j) := by
          rw [add_comm]
          exact (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)).symm
        _ = -B + ∑ j ∈ Finset.univ.erase i, χ j (z j) := by simp [χ, hi]
        _ ≤ c z := by
          have hc : -M ≤ c z := neg_le_of_abs_le (hM z)
          linarith
    · have hz' : ∀ i, ((μ i) (z i)).toReal ≠ 0 := fun i hi ↦ hz ⟨i, hi⟩
      simpa only [χ, hz', ↓reduceIte] using hψfeas z
  exact ⟨χ, hχfeas, hχvalue, fun i x ↦ abs_le.2 ⟨hχ_lower i x, (hχ_le i x).trans hMB⟩⟩

/-- **Finite multi-marginal dual attainment.** Every real cost on a nonempty finite family of
finite spaces has a maximizing feasible family of marginal potentials. -/
theorem exists_forall_finiteMultiDualValue_le (c : (∀ i, X i) → ℝ)
    (μ : ∀ i, PMF (X i)) :
    ∃ φ, FiniteMultiDualFeasible c φ ∧
      ∀ ψ, FiniteMultiDualFeasible c ψ →
        finiteMultiDualValue μ ψ ≤ finiteMultiDualValue μ φ := by
  have hX : ∀ i, Nonempty (X i) := fun i ↦ ⟨(μ i).support_nonempty.some⟩
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have : Nonempty (∀ i, X i) := ⟨fun i ↦ Classical.choice (hX i)⟩
  obtain ⟨z₀, hz₀⟩ := Finite.exists_max fun z : ∀ i, X i ↦ |c z|
  set M := |c z₀| with hMdef
  have hM : ∀ z, |c z| ≤ M := hz₀
  have hM0 : 0 ≤ M := abs_nonneg _
  -- A box radius dominating `(card ι + 2) * M` and its quotients by the positive weights.
  let boundTerm : (Σ i, X i) → ℝ := fun q ↦
    max ((Fintype.card ι + 2 : ℝ) * M)
      (if ((μ q.1) q.2).toReal = 0 then 0
        else (Fintype.card ι + 2 : ℝ) * M / ((μ q.1) q.2).toReal)
  have : Nonempty (Σ i, X i) := ⟨⟨i₀, Classical.choice (hX i₀)⟩⟩
  obtain ⟨q₀, hq₀⟩ := Finite.exists_max boundTerm
  set B := boundTerm q₀ with hBdef
  have hB : ∀ q, boundTerm q ≤ B := hq₀
  have hD : (Fintype.card ι + 2 : ℝ) * M ≤ B := by
    obtain ⟨x⟩ := hX i₀
    exact (le_max_left _ _).trans (hB ⟨i₀, x⟩)
  have hquot : ∀ i x, ((μ i) x).toReal ≠ 0 →
      (Fintype.card ι + 2 : ℝ) * M / ((μ i) x).toReal ≤ B := by
    intro i x hx
    have hbq := hB ⟨i, x⟩
    simp only [boundTerm, hx, ↓reduceIte] at hbq
    exact (le_max_right _ _).trans hbq
  have hcard : (1 : ℝ) ≤ (Fintype.card ι : ℝ) :=
    Nat.one_le_cast.2 (Fintype.card_pos_iff.2 ‹Nonempty ι›)
  have hcard1 : (0 : ℝ) ≤ ((Fintype.card ι : ℝ) + 1) * M := mul_nonneg (by linarith) hM0
  have hMB : M ≤ B := by nlinarith
  have hB0 : 0 ≤ B := hM0.trans hMB
  -- The normalised feasible families of value at least `-M` form a compact set.
  set K : Set (∀ i, X i → ℝ) :=
    {φ | FiniteMultiDualFeasible c φ ∧ -M ≤ finiteMultiDualValue μ φ ∧
      ∀ i x, |φ i x| ≤ B} with hKdef
  have hKclosed : IsClosed K := by
    have hfeas : IsClosed {φ : ∀ i, X i → ℝ | FiniteMultiDualFeasible c φ} := by
      simp only [FiniteMultiDualFeasible, Set.ofPred_forall]
      exact isClosed_iInter fun z ↦ isClosed_le
        (continuous_finsetSum _ fun i _ ↦ (continuous_apply (z i)).comp (continuous_apply i))
        continuous_const
    have hvalue : IsClosed {φ : ∀ i, X i → ℝ | -M ≤ finiteMultiDualValue μ φ} := by
      apply isClosed_le continuous_const
      have hcont : Continuous fun φ : ∀ i, X i → ℝ ↦
          ∑ i, ∑ x, ((μ i) x).toReal * φ i x :=
        continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun x _ ↦
        continuous_const.mul ((continuous_apply x).comp (continuous_apply i))
      exact hcont
    have hbox : IsClosed {φ : ∀ i, X i → ℝ | ∀ i x, |φ i x| ≤ B} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i ↦ isClosed_iInter fun x ↦
        isClosed_le (((continuous_apply x).comp (continuous_apply i)).abs) continuous_const
    exact hfeas.inter (hvalue.inter hbox)
  have hKsub : K ⊆ Set.univ.pi fun i ↦ Set.univ.pi fun _ : X i ↦ Set.Icc (-B) B := by
    intro φ hφ i _ x _
    exact abs_le.1 (hφ.2.2 i x)
  have hKcompact : IsCompact K :=
    IsCompact.of_isClosed_subset
      (isCompact_univ_pi fun i ↦ isCompact_univ_pi fun _ ↦ isCompact_Icc)
      hKclosed hKsub
  -- The constant family of total value `-M` is the baseline element of `K`.
  let base : ∀ i, X i → ℝ := fun i _ ↦ if i = i₀ then -M else 0
  have hbasefeas : FiniteMultiDualFeasible c base := by
    intro z
    have hc : -M ≤ c z := neg_le_of_abs_le (hM z)
    simpa [base] using hc
  have hbasevalue : finiteMultiDualValue μ base = -M := by
    simp only [finiteMultiDualValue_def, base]
    rw [Finset.sum_eq_single i₀]
    · simp [← Finset.sum_mul]
    · intro i _ hi
      simp [hi]
    · exact fun hi ↦ (hi (Finset.mem_univ i₀)).elim
  have hbasebox : ∀ i x, |base i x| ≤ B := by
    intro i x
    by_cases hi : i = i₀
    · subst i
      simp only [base, ↓reduceIte, abs_neg, abs_of_nonneg hM0]
      exact hMB
    · simp [base, hi, hB0]
  have hKne : K.Nonempty := ⟨base, hbasefeas, hbasevalue.ge, hbasebox⟩
  have hcont : Continuous fun φ : ∀ i, X i → ℝ ↦ finiteMultiDualValue μ φ := by
    simp only [finiteMultiDualValue_def]
    exact continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun x _ ↦
      continuous_const.mul ((continuous_apply x).comp (continuous_apply i))
  obtain ⟨φmax, hφmax, hmax⟩ := hKcompact.exists_isMaxOn hKne hcont.continuousOn
  refine ⟨φmax, hφmax.1, fun φ hφ ↦ ?_⟩
  by_cases hlow : finiteMultiDualValue μ φ < -M
  · exact hlow.le.trans (hbasevalue ▸ isMaxOn_iff.1 hmax base ⟨hbasefeas, hbasevalue.ge, hbasebox⟩)
  · have hval : -M ≤ finiteMultiDualValue μ φ := le_of_not_gt hlow
    obtain ⟨ψ, hψfeas, hψvalue, hψ_le⟩ := exists_normalized_of_feasible (μ := μ) hM hφ
    have hvalψ : -M ≤ finiteMultiDualValue μ ψ := by rw [hψvalue]; exact hval
    obtain ⟨χ, hχfeas, hχvalue, hχbox⟩ :=
      exists_bounded_of_normalized (μ := μ) hM hD hquot hψfeas hψ_le hvalψ
    have hχvalue' : finiteMultiDualValue μ χ = finiteMultiDualValue μ φ := hχvalue.trans hψvalue
    have hχmem : χ ∈ K := ⟨hχfeas, hχvalue' ▸ hval, hχbox⟩
    rw [← hχvalue']
    exact isMaxOn_iff.1 hmax χ hχmem

end DualAttainment

/-! ### Strong duality -/

section StrongDuality

variable [Fintype ι] [∀ i, Fintype (X i)]
attribute [local instance] Classical.decEq

/-- The Lagrangian of the finite multi-marginal transport problem. -/
private def multiLagrangian (c : (∀ i, X i) → ℝ) (μ : ∀ i, PMF (X i))
    (f : (∀ i, X i) → ℝ) (φ : ∀ i, X i → ℝ) : ℝ :=
  ∑ z, (c z - ∑ i, φ i (z i)) * f z + finiteMultiDualValue μ φ

private theorem multiLagrangian_eq (c : (∀ i, X i) → ℝ) (μ : ∀ i, PMF (X i))
    (f : (∀ i, X i) → ℝ) (φ : ∀ i, X i → ℝ) :
    multiLagrangian c μ f φ = multiCostFun c f +
      ∑ i, ∑ a, φ i a * (((μ i) a).toReal - ∑ z with z i = a, f z) := by
  rw [multiLagrangian, finiteMultiDualValue_def, multiCostFun]
  simp only [sub_mul, Finset.sum_sub_distrib, sum_sum_eval_mul, mul_sub]
  simp [mul_comm]
  ring

private theorem multiLagrangian_affine_left (c : (∀ i, X i) → ℝ)
    (μ : ∀ i, PMF (X i)) (f g : (∀ i, X i) → ℝ) (φ : ∀ i, X i → ℝ)
    (a b : ℝ) (hab : a + b = 1) :
    multiLagrangian c μ (a • f + b • g) φ =
      a * multiLagrangian c μ f φ + b * multiLagrangian c μ g φ := by
  simp only [multiLagrangian]
  have hterm : ∀ z,
      (c z - ∑ i, φ i (z i)) * ((a • f + b • g) z) =
        a * ((c z - ∑ i, φ i (z i)) * f z) +
          b * ((c z - ∑ i, φ i (z i)) * g z) := by
    intro z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun z _ ↦ hterm z, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  obtain rfl : a = 1 - b := by linarith
  ring

private theorem multiLagrangian_affine_right (c : (∀ i, X i) → ℝ)
    (μ : ∀ i, PMF (X i)) (f : (∀ i, X i) → ℝ) (φ ψ : ∀ i, X i → ℝ)
    (a b : ℝ) (hab : a + b = 1) :
    multiLagrangian c μ f (a • φ + b • ψ) =
      a * multiLagrangian c μ f φ + b * multiLagrangian c μ f ψ := by
  rw [multiLagrangian_eq, multiLagrangian_eq, multiLagrangian_eq]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hterm : ∀ i x,
      (a * φ i x + b * ψ i x) * (((μ i) x).toReal - ∑ z with z i = x, f z) =
        a * (φ i x * (((μ i) x).toReal - ∑ z with z i = x, f z)) +
          b * (ψ i x * (((μ i) x).toReal - ∑ z with z i = x, f z)) := by
    intros
    ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  obtain rfl : a = 1 - b := by linarith
  ring

private theorem continuous_multiLagrangian_left (c : (∀ i, X i) → ℝ)
    (μ : ∀ i, PMF (X i)) (φ : ∀ i, X i → ℝ) :
    Continuous fun f ↦ multiLagrangian c μ f φ := by
  simp only [multiLagrangian]
  exact (continuous_finsetSum _ fun z _ ↦ continuous_const.mul (continuous_apply z)).add
    continuous_const

private theorem continuous_multiLagrangian_right (c : (∀ i, X i) → ℝ)
    (μ : ∀ i, PMF (X i)) (f : (∀ i, X i) → ℝ) :
    Continuous fun φ ↦ multiLagrangian c μ f φ := by
  have hcont : Continuous fun φ : ∀ i, X i → ℝ ↦ multiCostFun c f +
      ∑ i, ∑ a, φ i a * (((μ i) a).toReal - ∑ z with z i = a, f z) := by
    refine continuous_const.add <| continuous_finsetSum _ fun i _ ↦
      continuous_finsetSum _ fun a _ ↦ ?_
    have hi : Continuous fun φ : ∀ i, X i → ℝ ↦ φ i := continuous_apply i
    have hia : Continuous fun φ : ∀ i, X i → ℝ ↦ φ i a :=
      (continuous_apply a).comp hi
    exact hia.mul continuous_const
  exact hcont.congr fun φ ↦ (multiLagrangian_eq c μ f φ).symm

private theorem iSup_multiLagrangian_of_mem {f : (∀ i, X i) → ℝ}
    (c : (∀ i, X i) → ℝ) (hf : f ∈ MultiRealPlans μ) :
    ⨆ φ : ∀ i, X i → ℝ, ((multiLagrangian c μ f φ : ℝ) : EReal) =
      ((multiCostFun c f : ℝ) : EReal) := by
  have hconst : ∀ φ : ∀ i, X i → ℝ, multiLagrangian c μ f φ = multiCostFun c f := by
    intro φ
    rw [multiLagrangian_eq]
    simp [hf.2.2]
  simp only [hconst]
  exact iSup_const

private theorem iSup_multiLagrangian_of_notMem {f : (∀ i, X i) → ℝ}
    (c : (∀ i, X i) → ℝ) (hf : f ∈ multiStdSimplexSet)
    (hnot : f ∉ MultiRealPlans μ) :
    ⨆ φ : ∀ i, X i → ℝ, ((multiLagrangian c μ f φ : ℝ) : EReal) = ⊤ := by
  refine (EReal.eq_top_iff_forall_lt _).2 fun y ↦ ?_
  suffices h : ∃ φ : ∀ i, X i → ℝ, y < multiLagrangian c μ f φ by
    obtain ⟨φ, hφ⟩ := h
    exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hφ)
      (le_iSup (fun φ ↦ ((multiLagrangian c μ f φ : ℝ) : EReal)) φ)
  have hmarg : ¬∀ i a, ∑ z with z i = a, f z = ((μ i) a).toReal := by
    intro hmarg
    exact hnot ⟨hf.1, hf.2, hmarg⟩
  obtain ⟨i, hi⟩ := not_forall.1 hmarg
  obtain ⟨x, hx⟩ := not_forall.1 hi
  have hd : ((μ i) x).toReal - ∑ z with z i = x, f z ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  let t := (y + 1 - multiCostFun c f) /
    (((μ i) x).toReal - ∑ z with z i = x, f z)
  let φ : ∀ j, X j → ℝ := Pi.single i (fun a ↦ if a = x then t else 0)
  refine ⟨φ, ?_⟩
  rw [multiLagrangian_eq]
  have hsum : ∑ j, ∑ a, φ j a * (((μ j) a).toReal - ∑ z with z j = a, f z) =
      t * (((μ i) x).toReal - ∑ z with z i = x, f z) := by
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single x]
      · simp [φ]
      · intro a _ hax
        simp [φ, hax]
      · exact fun hxmem ↦ (hxmem (Finset.mem_univ x)).elim
    · intro j _ hji
      simp [φ, hji]
    · exact fun hi ↦ (hi (Finset.mem_univ i)).elim
  rw [hsum]
  dsimp only [t]
  rw [div_mul_eq_mul_div, mul_div_assoc, div_self hd, mul_one]
  linarith

private theorem iInf_multiLagrangian (c : (∀ i, X i) → ℝ) (μ : ∀ i, PMF (X i))
    (φ : ∀ i, X i → ℝ) (z₀ : ∀ i, X i)
    (hz₀ : ∀ z, c z₀ - ∑ i, φ i (z₀ i) ≤ c z - ∑ i, φ i (z i)) :
    ⨅ f ∈ multiStdSimplexSet, ((multiLagrangian c μ f φ : ℝ) : EReal) =
      ((finiteMultiDualValue μ φ + (c z₀ - ∑ i, φ i (z₀ i)) : ℝ) : EReal) := by
  refine le_antisymm ?_ (le_iInf₂ fun f hf ↦ ?_)
  · let point : (∀ i, X i) → ℝ := fun z ↦ if z = z₀ then 1 else 0
    have hpoint : point ∈ multiStdSimplexSet := by
      refine ⟨fun z ↦ by by_cases hz : z = z₀ <;> simp [point, hz], ?_⟩
      simp [point]
    refine (biInf_le _ hpoint).trans (le_of_eq ?_)
    rw [EReal.coe_eq_coe_iff, multiLagrangian]
    simp [point, add_comm]
  · rw [EReal.coe_le_coe_iff, multiLagrangian]
    have hcalc : c z₀ - ∑ i, φ i (z₀ i) ≤
        ∑ z, (c z - ∑ i, φ i (z i)) * f z := calc
      c z₀ - ∑ i, φ i (z₀ i) =
          ∑ z, (c z₀ - ∑ i, φ i (z₀ i)) * f z := by
            rw [← Finset.mul_sum, hf.2, mul_one]
      _ ≤ ∑ z, (c z - ∑ i, φ i (z i)) * f z :=
        Finset.sum_le_sum fun z _ ↦ mul_le_mul_of_nonneg_right (hz₀ z) (hf.1 z)
    linarith

/-- **Finite multi-marginal Kantorovich duality.** For a nonempty finite family of finite
spaces, the primal and dual problems have the same value and both attain it. -/
theorem exists_cost_eq_finiteMultiDualValue (c : (∀ i, X i) → ℝ)
    (μ : ∀ i, PMF (X i)) [Nonempty ι] :
    ∃ (π : FiniteMultiCoupling μ) (φ : ∀ i, X i → ℝ),
      (∀ σ : FiniteMultiCoupling μ, π.cost c ≤ σ.cost c) ∧
      FiniteMultiDualFeasible c φ ∧ π.cost c = finiteMultiDualValue μ φ := by
  have hX : ∀ i, Nonempty (X i) := fun i ↦ ⟨(μ i).support_nonempty.some⟩
  have : Nonempty (∀ i, X i) := ⟨fun i ↦ Classical.choice (hX i)⟩
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨π, hπ⟩ := FiniteMultiCoupling.exists_forall_cost_le c μ
  obtain ⟨φ, hφ, hφmax⟩ := exists_forall_finiteMultiDualValue_le c μ
  refine ⟨π, φ, hπ, hφ, le_antisymm ?_ (π.finiteMultiDualValue_le_cost hφ)⟩
  have key : (⨅ f ∈ multiStdSimplexSet, ⨆ ψ ∈ (Set.univ : Set (∀ i, X i → ℝ)),
        ((multiLagrangian c μ f ψ : ℝ) : EReal)) =
      ⨆ ψ ∈ (Set.univ : Set (∀ i, X i → ℝ)), ⨅ f ∈ multiStdSimplexSet,
        ((multiLagrangian c μ f ψ : ℝ) : EReal) := by
    refine Sion.minimax'
      (ne_X := (multiRealPlans_nonempty (μ := μ)).mono
        (multiRealPlans_subset_multiStdSimplexSet (μ := μ)))
      (cX := convex_multiStdSimplexSet) (kX := isCompact_multiStdSimplexSet)
      (cY := convex_univ) (hfy := fun ψ _ ↦ ?_) (hfy' := fun ψ _ ↦ ?_)
      (hfx := fun f _ ↦ ?_) (hfx' := fun f _ ↦ ?_)
    · exact (continuous_coe_real_ereal.comp
        (continuous_multiLagrangian_left c μ ψ)).lowerSemicontinuous.lowerSemicontinuousOn _
    · exact ConvexOn.quasiconvexOn_ereal_coe
        (Convex.convexOn_and_concaveOn_of_affine
          (g := fun f ↦ multiLagrangian c μ f ψ) convex_multiStdSimplexSet
          (fun f _ g _ a b _ _ hab ↦ multiLagrangian_affine_left c μ f g ψ a b hab)).1
    · exact (continuous_coe_real_ereal.comp
        (continuous_multiLagrangian_right c μ f)).upperSemicontinuous.upperSemicontinuousOn _
    · exact ConcaveOn.quasiconcaveOn_ereal_coe
        (Convex.convexOn_and_concaveOn_of_affine
          (g := fun ψ ↦ multiLagrangian c μ f ψ) convex_univ
          (fun φ _ ψ _ a b _ _ hab ↦ multiLagrangian_affine_right c μ f φ ψ a b hab)).2
  simp only [iSup_univ] at key
  have h1 : ((π.cost c : ℝ) : EReal) ≤ ⨅ f ∈ multiStdSimplexSet,
      ⨆ ψ : ∀ i, X i → ℝ, ((multiLagrangian c μ f ψ : ℝ) : EReal) := by
    refine le_iInf₂ fun f hf ↦ ?_
    by_cases hmem : f ∈ MultiRealPlans μ
    · rw [iSup_multiLagrangian_of_mem c hmem, EReal.coe_le_coe_iff,
        ← FiniteMultiCoupling.cost_ofRealFun hmem c]
      exact hπ _
    · rw [iSup_multiLagrangian_of_notMem c hf hmem]
      exact le_top
  have h2 : (⨆ ψ : ∀ i, X i → ℝ, ⨅ f ∈ multiStdSimplexSet,
      ((multiLagrangian c μ f ψ : ℝ) : EReal)) ≤
      ((finiteMultiDualValue μ φ : ℝ) : EReal) := by
    refine iSup_le fun ψ ↦ ?_
    obtain ⟨z₀, hz₀⟩ := Finite.exists_min fun z ↦ c z - ∑ i, ψ i (z i)
    rw [iInf_multiLagrangian c μ ψ z₀ hz₀, EReal.coe_le_coe_iff]
    let d := c z₀ - ∑ i, ψ i (z₀ i)
    let a : ι → ℝ := fun i ↦ if i = i₀ then d else 0
    have hasum : ∑ i, a i = d := by simp [a]
    have hshift : FiniteMultiDualFeasible c (fun i x ↦ ψ i x + a i) := by
      intro z
      have hz := hz₀ z
      simp only [a, Finset.sum_add_distrib, hasum]
      linarith
    have hle := hφmax (fun i x ↦ ψ i x + a i) hshift
    rw [finiteMultiDualValue_add_const, hasum] at hle
    exact hle
  rw [key] at h1
  exact EReal.coe_le_coe_iff.1 (h1.trans h2)

/-- The common optimal value of the finite multi-marginal primal and dual problems. -/
theorem exists_isLeast_cost_isGreatest_finiteMultiDualValue (c : (∀ i, X i) → ℝ)
    (μ : ∀ i, PMF (X i)) [Nonempty ι] :
    ∃ V : ℝ, IsLeast {r | ∃ π : FiniteMultiCoupling μ, π.cost c = r} V ∧
      IsGreatest {r | ∃ φ, FiniteMultiDualFeasible c φ ∧
        finiteMultiDualValue μ φ = r} V := by
  obtain ⟨π, φ, hπ, hφ, heq⟩ := exists_cost_eq_finiteMultiDualValue c μ
  refine ⟨π.cost c, ⟨⟨π, rfl⟩, ?_⟩, ⟨⟨φ, hφ, heq.symm⟩, ?_⟩⟩
  · rintro r ⟨σ, rfl⟩
    exact hπ σ
  · rintro r ⟨ψ, hψ, rfl⟩
    exact π.finiteMultiDualValue_le_cost hψ

/-- A feasible finite multi-marginal plan and potential family are both optimal exactly when
their pointwise dual gap vanishes on every configuration carrying mass. -/
theorem FiniteMultiCoupling.forall_cost_le_and_forall_finiteMultiDualValue_le_iff
    (π : FiniteMultiCoupling μ) {c : (∀ i, X i) → ℝ} {φ : ∀ i, X i → ℝ}
    [Nonempty ι] (hφ : FiniteMultiDualFeasible c φ) :
    ((∀ σ : FiniteMultiCoupling μ, π.cost c ≤ σ.cost c) ∧
      ∀ ψ, FiniteMultiDualFeasible c ψ →
        finiteMultiDualValue μ ψ ≤ finiteMultiDualValue μ φ) ↔
      ∀ z, π.1 z ≠ 0 → ∑ i, φ i (z i) = c z := by
  rw [← π.cost_eq_finiteMultiDualValue_iff hφ]
  constructor
  · rintro ⟨hmin, hmax⟩
    obtain ⟨σ, ψ, -, hψ, heq⟩ := exists_cost_eq_finiteMultiDualValue c μ
    have h1 := hmin σ
    have h2 := hmax ψ hψ
    have h3 := π.finiteMultiDualValue_le_cost hφ
    linarith
  · intro heq
    exact π.forall_cost_le_and_forall_finiteMultiDualValue_le_of_eq hφ heq

end StrongDuality

end TauCeti
