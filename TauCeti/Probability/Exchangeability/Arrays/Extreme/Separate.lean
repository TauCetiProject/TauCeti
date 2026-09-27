/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Extreme.Basic
public import TauCeti.Probability.Exchangeability.Arrays.AldousHoover.Decomposition

/-!
# Extreme separately exchangeable array laws

Independent finitely supported relabelings of the row and column indices act on array space.
Their invariant probability laws are exactly the separately exchangeable laws. For such a law,
ergodicity of this action is equivalent to joint dissociation: a corner-tail event is fixed by
both relabelings, while joint dissociation already makes the smaller diagonal action ergodic.
The general ergodic/extreme-point theorem then identifies the extreme separately exchangeable
laws with the jointly dissociated ones.

This is the ergodic component interface for the separate Aldous--Hoover representation. Its
extreme laws are the components for which the global noise can be removed. The existing
corner-tail disintegration therefore becomes a measurable mixture of extreme separately
exchangeable laws.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

open Filter MeasureTheory ProbabilityTheory TauCeti.MeasureTheory Set
open scoped ENNReal

namespace TauCeti.Probability

variable {α : Type*}

/-- Independent finitely supported permutations act on the two axes of an array. The inverse
permutations make reindexing a left action. -/
instance instSMulFinitaryPermPairArray :
    SMul (FinitaryPerm × FinitaryPerm) (ℕ × ℕ → α) :=
  ⟨fun g x => pairReindex (FinitaryPerm.toPerm g.1)⁻¹
    (FinitaryPerm.toPerm g.2)⁻¹ x⟩

/-- The separate action is coordinate reindexing on each axis. -/
@[simp]
theorem finitaryPermPair_smul_array_apply (g : FinitaryPerm × FinitaryPerm)
    (x : ℕ × ℕ → α) (p : ℕ × ℕ) :
    (g • x) p = x ((FinitaryPerm.toPerm g.1)⁻¹ p.1,
      (FinitaryPerm.toPerm g.2)⁻¹ p.2) := by
  -- Expose the reindexing map behind the scalar action.
  change (pairReindex (FinitaryPerm.toPerm g.1)⁻¹
    (FinitaryPerm.toPerm g.2)⁻¹ x) p = _
  rw [pairReindex_apply]

/-- Independent row and column permutations compose as a left action on arrays. -/
instance instMulActionFinitaryPermPairArray :
    MulAction (FinitaryPerm × FinitaryPerm) (ℕ × ℕ → α) where
  one_smul x := by ext p; simp
  mul_smul g h x := by ext p; simp [mul_inv_rev]

variable [MeasurableSpace α]

/-- Each independent finitary relabeling is measurable. -/
instance instMeasurableConstSMulFinitaryPermPairArray :
    MeasurableConstSMul (FinitaryPerm × FinitaryPerm) (ℕ × ℕ → α) :=
  ⟨fun _ => measurable_pairReindex _ _⟩

/-- A separately exchangeable array law is invariant under the separate finitary action. -/
theorem SeparatelyExchangeable.smulInvariantMeasure_pair {ρ : Measure (ℕ × ℕ → α)}
    (hρ : SeparatelyExchangeable ρ fun p x => x p) :
    SMulInvariantMeasure (FinitaryPerm × FinitaryPerm) (ℕ × ℕ → α) ρ := by
  constructor
  intro g s hs
  -- Unfold only the action, leaving the measurable reindexing map visible to `map_apply`.
  change ρ (pairReindex (FinitaryPerm.toPerm g.1)⁻¹
    (FinitaryPerm.toPerm g.2)⁻¹ ⁻¹' s) = ρ s
  rw [← Measure.map_apply (measurable_pairReindex _ _) hs]
  have hmap := congrArg (fun m : Measure (ℕ × ℕ → α) => m s)
    (separatelyExchangeable_iff.mp hρ (FinitaryPerm.toPerm g.1)⁻¹
      (FinitaryPerm.toPerm g.2)⁻¹)
  rw [← pairReindex_def, Measure.map_id'] at hmap
  exact hmap

/-- Finitary invariance under independent row and column relabelings implies separate
exchangeability, by finite-dimensional determinacy of the array law. -/
theorem separatelyExchangeable_of_smulInvariantMeasure_pair {ρ : Measure (ℕ × ℕ → α)}
    [IsFiniteMeasure ρ]
    [SMulInvariantMeasure (FinitaryPerm × FinitaryPerm) (ℕ × ℕ → α) ρ] :
    SeparatelyExchangeable ρ fun p x => x p := by
  apply separatelyExchangeable_of_map_pairReindex_finitary
  intro σ τ hσ hτ
  let g : FinitaryPerm × FinitaryPerm :=
    (FinitaryPerm.ofPerm σ⁻¹ (by simpa only [MulAction.fixedBy_inv ℕ] using hσ),
      FinitaryPerm.ofPerm τ⁻¹ (by simpa only [MulAction.fixedBy_inv ℕ] using hτ))
  ext s hs
  rw [Measure.map_apply (measurable_pairReindex _ _) hs]
  have h := SMulInvariantMeasure.measure_preimage_smul (μ := ρ) g hs
  have hact : (fun x : ℕ × ℕ → α => g • x) = pairReindex σ τ := by
    funext x p
    simp [finitaryPermPair_smul_array_apply, pairReindex_apply, g]
  rwa [hact] at h

/-- A corner-tail event is fixed by every separate finitary relabeling. -/
theorem preimage_finitaryPermPair_smul_array_eq_self_of_measurableSet_arrayTail
    {s : Set (ℕ × ℕ → α)}
    (hs : MeasurableSet[arrayTail (fun p (x : ℕ × ℕ → α) => x p)] s)
    (g : FinitaryPerm × FinitaryPerm) :
    (fun x : ℕ × ℕ → α => g • x) ⁻¹' s = s := by
  have h₁ : (MulAction.fixedBy ℕ (FinitaryPerm.toPerm g.1)⁻¹)ᶜ.Finite := by
    simpa only [FinitaryPerm.toPerm_inv] using FinitaryPerm.finite_compl_fixedBy_toPerm g.1⁻¹
  have h₂ : (MulAction.fixedBy ℕ (FinitaryPerm.toPerm g.2)⁻¹)ᶜ.Finite := by
    simpa only [FinitaryPerm.toPerm_inv] using FinitaryPerm.finite_compl_fixedBy_toPerm g.2⁻¹
  -- The action is exactly this two-axis reindexing.
  change pairReindex (FinitaryPerm.toPerm g.1)⁻¹
    (FinitaryPerm.toPerm g.2)⁻¹ ⁻¹' s = s
  exact preimage_pairReindex_eq_self_of_measurableSet_arrayTail hs h₁ h₂

/-- Joint dissociation is ergodicity for the independent row-and-column action on a separately
exchangeable array law. -/
theorem jointlyDissociated_iff_ergodicSMul_pair {ρ : Measure (ℕ × ℕ → α)}
    [IsZeroOrProbabilityMeasure ρ] (hexch : SeparatelyExchangeable ρ fun p x => x p) :
    JointlyDissociated ρ (fun p x => x p) ↔
      ErgodicSMul (FinitaryPerm × FinitaryPerm) (ℕ × ℕ → α) ρ := by
  constructor
  · intro hdiss
    let := hexch.smulInvariantMeasure_pair
    let := hexch.jointlyExchangeable.smulInvariantMeasure
    let : ErgodicSMul FinitaryPerm (ℕ × ℕ → α) ρ :=
      ergodicSMul_of_jointlyDissociated hdiss
    apply TauCeti.MeasureTheory.ergodicSMul_of_forall_smul_invariant
    intro s hs hinv
    apply MeasureTheory.aeconst_of_forall_preimage_smul_ae_eq FinitaryPerm hs.nullMeasurableSet
    intro g
    have hact : (fun x : ℕ × ℕ → α => (g, g) • x) = fun x => g • x := by
      funext x p
      simp [finitaryPermPair_smul_array_apply, finitaryPerm_smul_array_apply]
    exact EventuallyEq.of_eq (by rw [← hact]; exact hinv (g, g))
  · intro herg
    let := hexch.smulInvariantMeasure_pair
    let : ErgodicSMul (FinitaryPerm × FinitaryPerm) (ℕ × ℕ → α) ρ := herg
    apply (jointlyDissociated_iff_forall_arrayTail_measure_eq_zero_or_one
      (X := fun p (x : ℕ × ℕ → α) => x p)
      (fun p => measurable_pi_apply p) hexch.jointlyExchangeable).mpr
    intro s hs
    rcases eq_zero_or_isProbabilityMeasure ρ with rfl | _
    · exact Or.inl rfl
    have hconst : EventuallyEmptyOrUniv s (ae ρ) :=
      MeasureTheory.aeconst_of_forall_preimage_smul_ae_eq
        (FinitaryPerm × FinitaryPerm)
        ((arrayTail_le_ambient (X := fun p (x : ℕ × ℕ → α) => x p) 0
          fun p _ _ => measurable_pi_apply p) s hs).nullMeasurableSet
        fun g => EventuallyEq.of_eq
          (preimage_finitaryPermPair_smul_array_eq_self_of_measurableSet_arrayTail hs g)
    rcases eventuallyEmptyOrUniv_iff'.mp hconst with h | h
    · exact Or.inl (by simpa using measure_congr h)
    · exact Or.inr (by simpa using measure_congr h)

/-- The separately exchangeable probability laws on array path space. -/
def separatelyExchangeableProbabilityMeasures (α : Type*) [MeasurableSpace α] :
    Set (Measure (ℕ × ℕ → α)) :=
  {ρ | SeparatelyExchangeable ρ (fun p x => x p) ∧ IsProbabilityMeasure ρ}

/-- Membership in the separately exchangeable probability laws. -/
@[simp]
theorem mem_separatelyExchangeableProbabilityMeasures_iff
    {ρ : Measure (ℕ × ℕ → α)} :
    ρ ∈ separatelyExchangeableProbabilityMeasures α ↔
      SeparatelyExchangeable ρ (fun p x => x p) ∧ IsProbabilityMeasure ρ :=
  Iff.rfl

/-- Separately exchangeable probability laws are the invariant probability laws of the
independent finitary action. -/
theorem separatelyExchangeableProbabilityMeasures_eq :
    separatelyExchangeableProbabilityMeasures α =
      invariantMeasuresOfMeasureUnivEq (FinitaryPerm × FinitaryPerm) (ℕ × ℕ → α) 1 := by
  ext ρ
  rw [mem_invariantMeasuresOfMeasureUnivEq_iff]
  constructor
  · rintro ⟨hexch, hp⟩
    exact ⟨hexch.smulInvariantMeasure_pair, hp.measure_univ⟩
  · rintro ⟨hinv, hp⟩
    have : IsProbabilityMeasure ρ := ⟨hp⟩
    exact ⟨separatelyExchangeable_of_smulInvariantMeasure_pair, inferInstance⟩

/-- The separately exchangeable probability laws form a convex set. -/
theorem convex_separatelyExchangeableProbabilityMeasures :
    Convex ℝ≥0∞ (separatelyExchangeableProbabilityMeasures α) := by
  rw [separatelyExchangeableProbabilityMeasures_eq]
  exact convex_invariantMeasuresOfMeasureUnivEq

/-- A separately exchangeable probability law is extreme exactly when it is jointly
dissociated. -/
theorem jointlyDissociated_iff_mem_extremePoints_separatelyExchangeable
    {ρ : Measure (ℕ × ℕ → α)} [IsProbabilityMeasure ρ]
    (hexch : SeparatelyExchangeable ρ fun p x => x p) :
    JointlyDissociated ρ (fun p x => x p) ↔
      ρ ∈ extremePoints ℝ≥0∞ (separatelyExchangeableProbabilityMeasures α) := by
  rw [jointlyDissociated_iff_ergodicSMul_pair hexch,
    separatelyExchangeableProbabilityMeasures_eq]
  exact ErgodicSMul.iff_mem_extremePoints

/-- Every separately exchangeable probability law is a measurable mixture of extreme separately
exchangeable laws. The components are the jointly dissociated conditional laws of the array given
its corner tail. -/
theorem SeparatelyExchangeable.exists_extreme_kernel
    [StandardBorelSpace α] {ρ : Measure (ℕ × ℕ → α)} [IsProbabilityMeasure ρ]
    (hρ : SeparatelyExchangeable ρ fun p x => x p) :
    ∃ κ : ProbabilityTheory.Kernel unitInterval (ℕ × ℕ → α), IsMarkovKernel κ ∧
      (∀ᵐ u ∂(volume : Measure unitInterval),
        κ u ∈ extremePoints ℝ≥0∞ (separatelyExchangeableProbabilityMeasures α)) ∧
      κ ∘ₘ (volume : Measure unitInterval) = ρ := by
  obtain ⟨κ, hκ, hgood, hmix⟩ := hρ.exists_jointlyDissociated_kernel
  let := hκ
  refine ⟨κ, hκ, ?_, hmix⟩
  filter_upwards [hgood] with u hu
  exact (jointlyDissociated_iff_mem_extremePoints_separatelyExchangeable hu.1).mp hu.2

end TauCeti.Probability
