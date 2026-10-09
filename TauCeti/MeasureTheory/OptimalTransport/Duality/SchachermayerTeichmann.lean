/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Duality.BoundedAbove

/-!
# The Schachermayer--Teichmann theorem

For a finite-valued measurable cost `c : X × Y → ℝ≥0∞` and probability measures on Polish
spaces, a coupling concentrated on a `c`-cyclically monotone set is optimal. Combined with
`TauCeti.IsOptimalCoupling.exists_isCyclicallyMonotone_of_lowerSemicontinuous`, this
characterises the optimal plans of finite cost for a finite-valued lower semicontinuous cost as
exactly the plans concentrated on a measurable `c`-cyclically monotone set. Optimality can thus be
checked on finite families of points, without solving the dual problem.

The cost must be finite everywhere. Ambrosio and Pratelli's example shows why: on the circle
`ℝ / ℤ` with Lebesgue measure as both marginals, fix an irrational `α` and let `c (x, x) = 1`,
`c (x, x + α) = 0`, and `c = ∞` elsewhere. Every nonidentity permutation of finitely many
distinct diagonal points has infinite cost: a finite-cost permutation could only move a point by
the translation `x ↦ x + α`, and a cycle of `k` such moves would give `k • α ∈ ℤ`, contradicting
irrationality. So the diagonal is `c`-cyclically monotone. Yet the identity plan costs `1`, while
the plan induced by the translation by `α` costs `0`.

The proof has two halves. First, Rüschendorf's potential of the cyclically monotone set gives real
potentials `φ`, `ψ`, feasible on a product of sets of full measure, on whose contact set the plan
is concentrated (`TauCeti.IsCoupling.exists_ae_add_eq_of_isCyclicallyMonotone`). These potentials
need not be integrable, so they are not a dual optimizer. Second, Schachermayer and Teichmann's
truncation argument shows that such *strongly `c`-monotone* plans are nevertheless optimal
(`TauCeti.IsCoupling.isOptimalCoupling_of_ae_mem_dualContactSet`).

## Main statements

* `TauCeti.IsCoupling.isOptimalCoupling_of_isCyclicallyMonotone` — a coupling concentrated on a
  `c`-cyclically monotone set is optimal for a finite-valued measurable cost;
* `TauCeti.IsCoupling.isOptimalCoupling_iff_exists_isCyclicallyMonotone` — **the
  Schachermayer--Teichmann theorem**: for a finite-valued lower semicontinuous cost, a coupling of
  finite cost is optimal if and only if it is concentrated on a measurable `c`-cyclically
  monotone set.

## References

* W. Schachermayer and J. Teichmann, *Characterization of optimal transport plans for the
  Monge--Kantorovich problem*, Proc. Amer. Math. Soc. 137 (2009), 519--529, Theorem 1.
* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Theorem 5.10 (ii).
* L. Ambrosio and A. Pratelli, *Existence and stability results in the `L¹` theory of optimal
  transportation*, in *Optimal Transportation and Applications*, Lecture Notes in Math. 1813,
  Springer 2003, for the counterexample with an infinite cost.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
  [MeasurableSpace Y] [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {c : X × Y → ℝ≥0∞} {π : Measure (X × Y)}

/-- **Cyclically monotone plans are optimal.** For a finite-valued measurable cost on a product
of Polish spaces, a coupling of two probability measures that is concentrated on a
`c`-cyclically monotone set `S` is an optimal coupling. The set `S` need not be measurable.

The finiteness of `c` cannot be dropped; see the module docstring. -/
theorem IsCoupling.isOptimalCoupling_of_isCyclicallyMonotone (hπ : IsCoupling π μ ν)
    (hc : Measurable c) (hctop : ∀ z, c z ≠ ∞) {S : Set (X × Y)}
    (hS : IsCyclicallyMonotone c S) (hπS : ∀ᵐ z ∂π, z ∈ S) : IsOptimalCoupling c π μ ν := by
  -- Pass to the real cost and to a measurable cyclically monotone subset of `S` of full measure.
  have hcr : (fun z ↦ ENNReal.ofReal (c z).toReal) = c :=
    funext fun z ↦ ENNReal.ofReal_toReal (hctop z)
  set S' := (toMeasurable π Sᶜ)ᶜ
  have hS' : IsCyclicallyMonotone (fun z ↦ (c z).toReal) S' := by
    rw [← isCyclicallyMonotone_ofReal_iff fun _ ↦ ENNReal.toReal_nonneg, hcr]
    exact hS.mono (compl_subset_comm.1 (subset_toMeasurable π Sᶜ))
  have hπS' : π S'ᶜ = 0 := by
    rw [compl_compl, measure_toMeasurable]
    exact ae_iff.1 hπS
  -- Rüschendorf's potentials of `S'` are strongly `c`-monotone potentials for `π`.
  obtain ⟨φ, ψ, A, B, -, -, hμA, hνB, hφ, hψ, hfeas, hsum⟩ :=
    hπ.exists_ae_add_eq_of_isCyclicallyMonotone hc.ennreal_toReal
      (measurableSet_toMeasurable π Sᶜ).compl hS' (ae_iff.2 hπS')
  exact hπ.isOptimalCoupling_of_ae_mem_dualContactSet hμA hνB hφ.aemeasurable hψ
    (fun x hx y hy ↦ (ENNReal.ofReal_le_ofReal (hfeas x hx y hy)).trans_eq
      (ENNReal.ofReal_toReal (hctop _)))
    (hsum.mono fun z hz ↦ mem_dualContactSet_of_toReal_eq (hctop z) hz.symm)

/-- **The Schachermayer--Teichmann theorem.** For a finite-valued lower semicontinuous cost on a
product of Polish spaces, a coupling of finite cost between two probability measures is optimal
if and only if it is concentrated on a measurable `c`-cyclically monotone set.

The finite-cost hypothesis is used only for the forward implication: when every coupling has
infinite cost, every coupling is optimal. -/
theorem IsCoupling.isOptimalCoupling_iff_exists_isCyclicallyMonotone (hπ : IsCoupling π μ ν)
    (hc : LowerSemicontinuous c) (hctop : ∀ z, c z ≠ ∞) (hfin : ∫⁻ z, c z ∂π ≠ ∞) :
    IsOptimalCoupling c π μ ν ↔
      ∃ S : Set (X × Y), MeasurableSet S ∧ IsCyclicallyMonotone c S ∧ π Sᶜ = 0 :=
  ⟨fun h ↦ h.exists_isCyclicallyMonotone_of_lowerSemicontinuous hc (h.lintegral_eq ▸ hfin),
    fun ⟨_, _, hS, hπS⟩ ↦
      hπ.isOptimalCoupling_of_isCyclicallyMonotone hc.measurable hctop hS (ae_iff.2 hπS)⟩

end TauCeti
