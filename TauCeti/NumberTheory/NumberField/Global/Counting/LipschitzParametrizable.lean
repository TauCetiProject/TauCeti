/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Lipschitz-parametrizable sets

A set is Lipschitz parametrizable in dimension `d` when finitely many Lipschitz images of the
unit `d`-cube cover it.  This is the boundary regularity condition used in lattice-point counting:
a codimension-one parametrization gives quantitative control on how many lattice cells can meet a
boundary.

This file supplies the elementary API needed to assemble parametrizations: the property is
monotone in the set, is preserved by Lipschitz images and finite unions, and holds for finite sets.
It also records the basic dimension consequence.  A Lipschitz-parametrizable subset of a
finite-dimensional real normed space has additive Haar measure zero whenever the parameter
dimension is strictly smaller than the ambient dimension.  The proof compares additive Haar
measure with Hausdorff measure and uses the fact that Lipschitz maps do not increase Hausdorff
dimension.

## Main declarations

* `TauCeti.GlobalNumberFields.IsLipschitzParametrizable`: finite Lipschitz parametrizability by a
  unit cube;
* `TauCeti.GlobalNumberFields.IsLipschitzParametrizable.union`: closure under binary unions;
* `TauCeti.GlobalNumberFields.IsLipschitzParametrizable.image`: closure under Lipschitz images;
* `TauCeti.GlobalNumberFields.IsLipschitzParametrizable.measure_zero`: a parametrized set has
  additive Haar measure zero below the ambient dimension.

The definition and its use in the lattice-point estimate follow Lang, *Algebraic Number Theory*,
Chapter VI, Section 2.
-/

public section

open MeasureTheory Set

namespace TauCeti

namespace GlobalNumberFields

/-- A set is Lipschitz parametrizable in dimension `d` if it is covered by finitely many
Lipschitz images of the unit cube in `Fin d → ℝ`. -/
def IsLipschitzParametrizable {E : Type*} [PseudoEMetricSpace E] (d : ℕ) (S : Set E) : Prop :=
  ∃ (n : ℕ) (C : NNReal) (f : Fin n → (Fin d → ℝ) → E),
    (∀ i, LipschitzOnWith C (f i) (Icc (0 : Fin d → ℝ) 1)) ∧
      S ⊆ ⋃ i, f i '' Icc (0 : Fin d → ℝ) 1

namespace IsLipschitzParametrizable

variable {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
  {d : ℕ} {S T : Set E}

/-- Every subset of a Lipschitz-parametrizable set is Lipschitz parametrizable with the same
charts. -/
theorem mono (hT : IsLipschitzParametrizable d T) (hST : S ⊆ T) :
    IsLipschitzParametrizable d S := by
  obtain ⟨n, C, f, hf, hT⟩ := hT
  exact ⟨n, C, f, hf, hST.trans hT⟩

/-- The empty set is Lipschitz parametrizable in every dimension. -/
@[simp]
theorem empty : IsLipschitzParametrizable d (∅ : Set E) := by
  exact ⟨0, 0, Fin.elim0, fun i ↦ i.elim0, Set.empty_subset _⟩

/-- A singleton is Lipschitz parametrizable in every dimension. -/
theorem singleton (x : E) : IsLipschitzParametrizable d ({x} : Set E) := by
  refine ⟨1, 0, fun (_ : Fin 1) (_ : Fin d → ℝ) ↦ x,
    fun _ ↦ (LipschitzWith.const (α := Fin d → ℝ) x).lipschitzOnWith, ?_⟩
  intro y hy
  have hyx : y = x := Set.mem_singleton_iff.mp hy
  subst y
  refine Set.mem_iUnion.2 ⟨0, ?_⟩
  exact ⟨0, by simp⟩

/-- The union of two Lipschitz-parametrizable sets in the same dimension is Lipschitz
parametrizable. -/
theorem union (hS : IsLipschitzParametrizable d S) (hT : IsLipschitzParametrizable d T) :
    IsLipschitzParametrizable d (S ∪ T) := by
  obtain ⟨m, C, f, hf, hSf⟩ := hS
  obtain ⟨n, D, g, hg, hTg⟩ := hT
  let e : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv
  let charts : Fin (m + n) → (Fin d → ℝ) → E := fun i ↦
    Sum.elim f g (e.symm i)
  refine ⟨m + n, max C D, charts, ?_, ?_⟩
  · intro i
    rcases h : e.symm i with j | j
    · simpa only [charts, h, Sum.elim_inl] using (hf j).weaken (le_max_left C D)
    · simpa only [charts, h, Sum.elim_inr] using (hg j).weaken (le_max_right C D)
  · rintro x (hx | hx)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hSf hx)
      refine Set.mem_iUnion.2 ⟨e (Sum.inl i), ?_⟩
      simpa only [charts, Equiv.symm_apply_apply, Sum.elim_inl] using hi
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hTg hx)
      refine Set.mem_iUnion.2 ⟨e (Sum.inr i), ?_⟩
      simpa only [charts, Equiv.symm_apply_apply, Sum.elim_inr] using hi

/-- A finite union of sets parametrized in the same dimension is Lipschitz parametrizable. -/
theorem biUnion_finset {I : Type*} (s : Finset I) {A : I → Set E}
    (hA : ∀ i ∈ s, IsLipschitzParametrizable d (A i)) :
    IsLipschitzParametrizable d (⋃ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.set_biUnion_insert]
      exact (hA i (Finset.mem_insert_self i s)).union
        (ih fun j hj ↦ hA j (Finset.mem_insert_of_mem hj))

/-- A finite set is Lipschitz parametrizable in every dimension. -/
theorem finite (hS : S.Finite) : IsLipschitzParametrizable d S := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact empty
  | @insert x S hx hS ih =>
      rw [insert_eq, singleton_union]
      exact (singleton (d := d) x).union ih

/-- The image of a Lipschitz-parametrizable set under a Lipschitz map is Lipschitz
parametrizable. -/
theorem image {g : E → F} {K : NNReal} (hg : LipschitzWith K g)
    (hS : IsLipschitzParametrizable d S) : IsLipschitzParametrizable d (g '' S) := by
  obtain ⟨n, C, f, hf, hSf⟩ := hS
  refine ⟨n, K * C, fun i ↦ g ∘ f i, fun i ↦ hg.comp_lipschitzOnWith (hf i), ?_⟩
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.1 (hSf hx)
  exact Set.mem_iUnion.2 ⟨i, z, hz, rfl⟩

/-- A set Lipschitz parametrized in dimension `d` has zero additive Haar measure in a
finite-dimensional real normed space of dimension strictly larger than `d`.

This statement is formulated for an arbitrary additive Haar measure, so it applies directly to
the volume normalization used by a lattice and is invariant under later linear coordinate
changes. -/
theorem measure_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {d : ℕ} {S : Set E}
    (hS : IsLipschitzParametrizable d S) (hd : d < Module.finrank ℝ E) : μ S = 0 := by
  obtain ⟨n, C, f, hf, hSf⟩ := hS
  have hμ : μ ≪ μH[(Module.finrank ℝ E : ℝ)] :=
    Measure.absolutelyContinuous_isAddHaarMeasure μ _
  have hdim : dimH (Set.univ : Set (Fin d → ℝ)) = d := by
    rw [Real.dimH_univ_eq_finrank, Module.finrank_pi]
    simp only [Fintype.card_fin]
  apply measure_mono_null hSf
  apply measure_iUnion_null
  intro i
  apply measure_zero_of_dimH_lt (μ := μ) (d := (Module.finrank ℝ E : NNReal)) hμ
  calc
    dimH (f i '' Icc (0 : Fin d → ℝ) 1) ≤ dimH (Icc (0 : Fin d → ℝ) 1) :=
      (hf i).dimH_image_le
    _ ≤ dimH (Set.univ : Set (Fin d → ℝ)) := dimH_mono (Set.subset_univ _)
    _ = d := hdim
    _ < Module.finrank ℝ E := by exact_mod_cast hd

end IsLipschitzParametrizable

end GlobalNumberFields

end TauCeti
