/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Duality.Certificate
public import TauCeti.MeasureTheory.OptimalTransport.Duality.LowerSemicontinuous
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Optimal plans of lower semicontinuous costs are cyclically monotone

For a lower semicontinuous cost `c : X × Y → ℝ≥0∞` on Polish spaces, every optimal coupling of
finite cost is concentrated on a measurable `c`-cyclically monotone set. The cost may take the
value `∞`. Unlike `TauCeti.IsOptimalCoupling.isCyclicallyMonotone_support`, continuity of the cost
is not needed; in exchange, the statement concerns some set of full measure rather than the
topological support of the plan.

The proof goes through strong duality instead of a perturbation of the plan. By
`TauCeti.isLUB_ofReal_kantorovichDualValue_integrable_of_lowerSemicontinuous` there are integrable
feasible pairs `(φ n, ψ n)` whose dual values tend to the optimal cost. Against an optimal plan
`π` the defects `c (x, y) - φ n x - ψ n y` are nonnegative and their `π`-integrals tend to zero,
so a subsequence of the defects tends to zero `π`-almost everywhere. On the set where this
happens, each equality `c (x, y) = lim (φ n x + ψ n y)` survives passage to the limit, while a
permutation of the targets only produces inequalities. That set is therefore `c`-cyclically
monotone: it is an *asymptotic contact set*, generalising the contact set of a single dual
feasible pair.

## Main statements

* `TauCeti.isCyclicallyMonotone_setOf_tendsto` — the asymptotic contact set of a family of dual
  feasible pairs is `c`-cyclically monotone;
* `TauCeti.IsCoupling.exists_seq_tendsto_ae_of_tendsto_kantorovichDualValue` — if the dual values
  of feasible pairs tend to the cost of a plan, then along a subsequence their split sums converge
  to the cost almost everywhere for that plan;
* `TauCeti.exists_seq_tendsto_kantorovichDualValue_of_lowerSemicontinuous` — on Polish spaces a
  finite optimal cost of a lower semicontinuous cost is the limit of real integrable dual values;
* `TauCeti.IsOptimalCoupling.exists_isCyclicallyMonotone_of_lowerSemicontinuous` — an optimal plan
  of finite cost for a lower semicontinuous cost on Polish spaces is concentrated on a measurable
  `c`-cyclically monotone set.

The converse, that concentration on a `c`-cyclically monotone set forces optimality when the cost
is finite-valued, is the Schachermayer--Teichmann theorem
`TauCeti.IsCoupling.isOptimalCoupling_iff_exists_isCyclicallyMonotone`.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Theorem 5.10 (ii);
  the limit of a maximizing dual sequence follows the proof given there.
* L. Ambrosio and A. Pratelli, *Existence and stability results in the `L¹` theory of optimal
  transportation*, in *Optimal Transportation and Applications*, Lecture Notes in Math. 1813,
  Springer 2003, Theorem 3.2.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v} {c : X × Y → ℝ≥0∞}

/-- **Asymptotic contact sets are `c`-cyclically monotone.** Let `(φ i, ψ i)` be a family of dual
feasible pairs for `c`, indexed along a nontrivial filter. The set of pairs `(x, y)` of finite cost
at which `φ i x + ψ i y` tends to `c (x, y)` is `c`-cyclically monotone. For a constant family this
set is the contact set of a single feasible pair. -/
theorem isCyclicallyMonotone_setOf_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {φ : ι → X → ℝ} {ψ : ι → Y → ℝ}
    (h : ∀ i, DualFeasible (fun z ↦ (c z : EReal)) (φ i) (ψ i)) :
    IsCyclicallyMonotone c
      {z | c z ≠ ∞ ∧ Tendsto (fun i ↦ φ i z.1 + ψ i z.2) l (𝓝 (c z).toReal)} := by
  rw [isCyclicallyMonotone_iff]
  intro n x y hmem σ
  by_cases htop : ∑ i, c (x i, y (σ i)) = ∞
  · simp [htop]
  have hfin : ∀ i, c (x i, y (σ i)) ≠ ∞ := fun i ↦
    ENNReal.sum_ne_top.1 htop i (Finset.mem_univ i)
  -- The diagonal sums of potentials converge to the diagonal cost, and each of them equals the
  -- permuted sum of potentials, which is bounded by the permuted cost.
  have hlim : Tendsto (fun j ↦ ∑ i, (φ j (x i) + ψ j (y i))) l
      (𝓝 (∑ i, (c (x i, y i)).toReal)) :=
    tendsto_finsetSum _ fun i _ ↦ (hmem i).2
  have hle : ∑ i, (c (x i, y i)).toReal ≤ ∑ i, (c (x i, y (σ i))).toReal := by
    refine le_of_tendsto' hlim fun j ↦ ?_
    rw [Finset.sum_add_distrib, ← Equiv.sum_comp σ fun i ↦ ψ j (y i), ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ ↦
      (ENNReal.ofReal_le_iff_le_toReal (hfin i)).1 ((h j).ofReal_add_le _ _)
  have hdiag : ∑ i, c (x i, y i) ≠ ∞ := ENNReal.sum_ne_top.2 fun i _ ↦ (hmem i).1
  rwa [← ENNReal.toReal_le_toReal hdiag htop, ENNReal.toReal_sum fun i _ ↦ (hmem i).1,
    ENNReal.toReal_sum fun i _ ↦ hfin i]

section Measure

variable [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  {π : Measure (X × Y)}

/-- **Maximizing dual sequences converge almost everywhere on a plan.** Let `π` couple `μ` and `ν`
with finite cost `∫⁻ c ∂π`, and let `(φ n, ψ n)` be integrable dual feasible pairs whose dual
values tend to that cost. Then along a subsequence, `φ n x + ψ n y` tends to `c (x, y)` for
`π`-almost every `(x, y)`. -/
theorem IsCoupling.exists_seq_tendsto_ae_of_tendsto_kantorovichDualValue
    (hπ : IsCoupling π μ ν) (hc : AEMeasurable c π) (hfin : ∫⁻ z, c z ∂π ≠ ∞)
    {φ : ℕ → X → ℝ} {ψ : ℕ → Y → ℝ} (hφ : ∀ n, Integrable (φ n) μ)
    (hψ : ∀ n, Integrable (ψ n) ν) (hf : ∀ n, DualFeasible (fun z ↦ (c z : EReal)) (φ n) (ψ n))
    (hlim : Tendsto (fun n ↦ kantorovichDualValue μ ν (φ n) (ψ n)) atTop
      (𝓝 (∫⁻ z, c z ∂π).toReal)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ z ∂π, Tendsto (fun k ↦ φ (ns k) z.1 + ψ (ns k) z.2) atTop (𝓝 (c z).toReal) := by
  have hg n : Integrable (fun z : X × Y ↦ φ n z.1 + ψ n z.2) π :=
    (hπ.integrable_comp_fst (hφ n)).add (hπ.integrable_comp_snd (hψ n))
  have hcint : Integrable (fun z ↦ (c z).toReal) π := integrable_toReal_of_lintegral_ne_top hc hfin
  have hlt := ae_lt_top' hc hfin
  -- The `L¹(π)` distance from the split sums to the cost is the duality gap.
  have hdist n : eLpNorm ((fun z : X × Y ↦ φ n z.1 + ψ n z.2) - fun z ↦ (c z).toReal) 1 π =
      ENNReal.ofReal ((∫⁻ z, c z ∂π).toReal - kantorovichDualValue μ ν (φ n) (ψ n)) := by
    have hle : ∀ᵐ z ∂π, φ n z.1 + ψ n z.2 ≤ (c z).toReal := hlt.mono fun z hz ↦
      (ENNReal.ofReal_le_iff_le_toReal hz.ne).1 ((hf n).ofReal_add_le z.1 z.2)
    rw [eLpNorm_one_eq_lintegral_enorm ((hg n).sub hcint).aestronglyMeasurable,
      ← integral_toReal hc hlt, kantorovichDualValue_eq_integral hπ (hφ n) (hψ n),
      ← integral_sub hcint (hg n),
      ofReal_integral_eq_lintegral_ofReal (f := fun z ↦ (c z).toReal - (φ n z.1 + ψ n z.2))
        (hcint.sub (hg n)) (hle.mono fun z hz ↦ sub_nonneg.2 hz)]
    refine lintegral_congr_ae (hle.mono fun z hz ↦ ?_)
    simp only [Pi.sub_apply]
    rw [← enorm_neg, neg_sub, Real.enorm_of_nonneg (sub_nonneg.2 hz)]
  have hmeas : TendstoInMeasure π (fun n z ↦ φ n z.1 + ψ n z.2) atTop fun z ↦ (c z).toReal := by
    refine tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero ?_
    simp_rw [hdist]
    rw [← ENNReal.ofReal_zero, ← sub_self (∫⁻ z, c z ∂π).toReal]
    exact ENNReal.tendsto_ofReal (tendsto_const_nhds.sub hlim)
  exact hmeas.exists_seq_tendsto_ae

end Measure

section Polish

variable [TopologicalSpace X] [MeasurableSpace X] [PolishSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [PolishSpace Y] [BorelSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {π : Measure (X × Y)}

/-- **A maximizing dual sequence for a lower semicontinuous cost.** On Polish spaces, a finite
optimal cost of a lower semicontinuous cost `c : X × Y → ℝ≥0∞` is the limit of the real values of
integrable dual feasible pairs. Unlike
`TauCeti.isLUB_ofReal_kantorovichDualValue_integrable_of_lowerSemicontinuous`, the dual values are
not truncated at zero. -/
theorem exists_seq_tendsto_kantorovichDualValue_of_lowerSemicontinuous
    (hc : LowerSemicontinuous c) (hfin : transportCost c μ ν ≠ ∞) :
    ∃ (φ : ℕ → X → ℝ) (ψ : ℕ → Y → ℝ), (∀ n, Integrable (φ n) μ) ∧
      (∀ n, Integrable (ψ n) ν) ∧ (∀ n, DualFeasible (fun z ↦ (c z : EReal)) (φ n) (ψ n)) ∧
      Tendsto (fun n ↦ kantorovichDualValue μ ν (φ n) (ψ n)) atTop
        (𝓝 (transportCost c μ ν).toReal) := by
  set C := (transportCost c μ ν).toReal
  have hpair (n : ℕ) : ∃ φ : X → ℝ, ∃ ψ : Y → ℝ, Integrable φ μ ∧ Integrable ψ ν ∧
      DualFeasible (fun z ↦ (c z : EReal)) φ ψ ∧
      C - 1 / ((n : ℝ) + 1) < kantorovichDualValue μ ν φ ψ := by
    have hε : 0 < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
    by_cases hneg : C - 1 / ((n : ℝ) + 1) < 0
    · -- Far below the optimal cost the zero pair already qualifies.
      exact ⟨fun _ ↦ 0, fun _ ↦ 0, integrable_zero X ℝ μ, integrable_zero Y ℝ ν,
        dualFeasible_zero c, by rwa [kantorovichDualValue_zero]⟩
    · -- Otherwise the truncation at zero is harmless and strong duality applies.
      have hlt : ENNReal.ofReal (C - 1 / ((n : ℝ) + 1)) < transportCost c μ ν := by
        rw [← ENNReal.ofReal_toReal hfin, ENNReal.ofReal_lt_ofReal_iff']
        exact ⟨sub_lt_self C hε, by linarith [not_lt.1 hneg]⟩
      obtain ⟨r, ⟨φ, ψ, hφ, hψ, hf, rfl⟩, hr⟩ := (lt_isLUB_iff
        (isLUB_ofReal_kantorovichDualValue_integrable_of_lowerSemicontinuous hc)).1 hlt
      exact ⟨φ, ψ, hφ, hψ, hf, ((ENNReal.ofReal_lt_ofReal_iff').1 hr).1⟩
  choose φ ψ hφ hψ hf hgt using hpair
  refine ⟨φ, ψ, hφ, hψ, hf, tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds
    (fun n ↦ (hgt n).le) fun n ↦
      (hf n).kantorovichDualValue_le_toReal_transportCost hfin (hφ n) (hψ n)⟩
  simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- **Optimal plans of lower semicontinuous costs are cyclically monotone.** For a lower
semicontinuous cost `c : X × Y → ℝ≥0∞` and probability measures on Polish spaces, an optimal
coupling of finite cost is concentrated on a measurable `c`-cyclically monotone set.

Finiteness of the optimal cost cannot be dropped: when it is infinite every coupling is optimal.
For a continuous cost, `TauCeti.IsOptimalCoupling.isCyclicallyMonotone_support` gives the
topological support as such a set. -/
theorem IsOptimalCoupling.exists_isCyclicallyMonotone_of_lowerSemicontinuous
    (h : IsOptimalCoupling c π μ ν) (hc : LowerSemicontinuous c)
    (hfin : transportCost c μ ν ≠ ∞) :
    ∃ S : Set (X × Y), MeasurableSet S ∧ IsCyclicallyMonotone c S ∧ π Sᶜ = 0 := by
  obtain ⟨φ, ψ, hφ, hψ, hf, hlim⟩ :=
    exists_seq_tendsto_kantorovichDualValue_of_lowerSemicontinuous hc hfin
  rw [← h.lintegral_eq] at hfin hlim
  obtain ⟨ns, -, hae⟩ := h.toIsCoupling.exists_seq_tendsto_ae_of_tendsto_kantorovichDualValue
    hc.measurable.aemeasurable hfin hφ hψ hf hlim
  set Γ := {z | c z ≠ ∞ ∧
    Tendsto (fun k ↦ φ (ns k) z.1 + ψ (ns k) z.2) atTop (𝓝 (c z).toReal)}
  have hΓ : π Γᶜ = 0 :=
    ae_iff.1 (((ae_lt_top hc.measurable hfin).mono fun _ hz ↦ hz.ne).and hae)
  refine ⟨(toMeasurable π Γᶜ)ᶜ, (measurableSet_toMeasurable π Γᶜ).compl,
    (isCyclicallyMonotone_setOf_tendsto fun k ↦ hf (ns k)).mono
      (compl_subset_comm.1 (subset_toMeasurable π Γᶜ)), ?_⟩
  rwa [compl_compl, measure_toMeasurable]

end Polish

end TauCeti
