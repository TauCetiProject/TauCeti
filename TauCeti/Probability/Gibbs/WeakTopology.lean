/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The weak topology on a closed set of finite-alphabet configurations

Let `I` be a countable index set, `S` a finite alphabet with the discrete topology and the discrete
σ-algebra, and `X ⊆ I → S` a closed set of configurations, with the subspace topology and the trace
of the product σ-algebra. Then `X` is a compact metrisable Borel space and the space of probability
measures `ProbabilityMeasure X` with the weak topology is compact
(`TauCeti.compactSpace_of_isClosed`, and Mathlib's instances).

The traces on `X` of cylinder events `{ω : ω|_s ∈ t}`, for a finite `s ⊆ I`, are clopen and
measurable (`TauCeti.isClopen_preimage_cylinder`, `TauCeti.measurableSet_preimage_cylinder`), and
weak convergence of probability measures on `X` is convergence of the masses of these traces,
`TauCeti.tendsto_iff_forall_tendsto_cylinder`. It suffices to test the *point cylinders*
`{x : x = η on s}`, which form a π-system containing arbitrarily small neighbourhoods of every
point, `TauCeti.tendsto_of_forall_tendsto_pointCylinder`.

For `S = Bool` the *correlation functions* `ρ_F(μ) = μ{x : x = 1 on F}`, `F ⊆ I` finite
(`TauCeti.correlationFunction`), determine `μ` (`TauCeti.ext_of_correlationFunction`), and weak
convergence is convergence of all correlation functions,
`TauCeti.tendsto_iff_forall_tendsto_correlationFunction`. A point cylinder is the set of
configurations that are `1` on `A` and `0` on `B`, which is the set `{x = 1 on A}` minus the finite
union of the sets `{x = 1 on A ∪ {b}}`, `b ∈ B`, so its mass is a difference of masses of finite
unions of elements of the π-system of the sets `{x = 1 on F}`.

These are the finite-alphabet subshift facts of the DimerModelsAndLozengeTilings roadmap, stated
for any closed set of configurations; invariance under a group action plays no role in them.

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge University Press (2021),
  Definition 13.1 and Lemma 13.2.
-/

public section

open MeasureTheory Filter Topology Set
open scoped NNReal

namespace TauCeti

variable {I S : Type*} [TopologicalSpace S] {X : Set (I → S)}

/-- A closed set of configurations in a finite alphabet is compact. -/
theorem compactSpace_of_isClosed [Finite S] (hX : IsClosed X) : CompactSpace X :=
  isCompact_iff_compactSpace.mp hX.isCompact

variable [DiscreteTopology S]

/-- The trace on a set of configurations of a cylinder event is clopen. -/
theorem isClopen_preimage_cylinder (s : Finset I) (t : Set (s → S)) :
    IsClopen ((↑) ⁻¹' cylinder (α := fun _ : I => S) s t : Set X) := by
  have h : IsClopen (cylinder (α := fun _ : I => S) s t) :=
    (isClopen_discrete t).preimage (continuous_pi fun i => continuous_apply (i : I))
  exact h.preimage continuous_subtypeVal

/-- The trace on a set of configurations of a point cylinder `{ω : ω = η on s}` is open. -/
theorem isOpen_pointCylinder (s : Finset I) (η : I → S) :
    IsOpen {x : X | ∀ i ∈ s, (x : I → S) i = η i} := by
  simp only [ofPred_forall]
  refine isOpen_biInter_finset fun i _ => ?_
  have h := (isOpen_discrete ({η i} : Set S)).preimage
    ((continuous_apply i).comp (continuous_subtypeVal (p := (· ∈ X))))
  exact h

variable [MeasurableSpace S] [DiscreteMeasurableSpace S]

omit [TopologicalSpace S] [DiscreteTopology S] in
/-- The trace on a set of configurations of a cylinder event is measurable. -/
theorem measurableSet_preimage_cylinder [Finite S] (s : Finset I) (t : Set (s → S)) :
    MeasurableSet ((↑) ⁻¹' cylinder (α := fun _ : I => S) s t : Set X) :=
  measurable_subtypeVal
    (MeasurableSet.cylinder (α := fun _ : I => S) s t.toFinite.measurableSet)

/-- The trace on a set of configurations of a point cylinder is measurable. -/
theorem measurableSet_pointCylinder (s : Finset I) (η : I → S) :
    MeasurableSet {x : X | ∀ i ∈ s, (x : I → S) i = η i} := by
  simp only [ofPred_forall]
  refine Finset.measurableSet_biInter s fun i _ => ?_
  have h := (measurable_pi_apply i).comp (measurable_subtypeVal (p := (· ∈ X)))
    (measurableSet_singleton (η i))
  exact h

variable [Countable I] [Finite S]

/-- **Weak convergence from point cylinders.** If the masses of all point cylinders
`{x : x = η on s}` converge, then the probability measures converge weakly. -/
theorem tendsto_of_forall_tendsto_pointCylinder {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {μ : ι → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    (h : ∀ (s : Finset I) (η : I → S),
      Tendsto (fun i => μ i {x : X | ∀ j ∈ s, (x : I → S) j = η j}) l
        (𝓝 (ν {x : X | ∀ j ∈ s, (x : I → S) j = η j}))) :
    Tendsto μ l (𝓝 ν) := by
  classical
  let C : Set (Set X) :=
    {A | ∃ (s : Finset I) (η : I → S), A = {x : X | ∀ j ∈ s, (x : I → S) j = η j}}
  have hC : IsPiSystem C := by
    rintro _ ⟨s, η, rfl⟩ _ ⟨s', η', rfl⟩ ⟨z, hz, hz'⟩
    refine ⟨s ∪ s', fun j => (z : I → S) j, ?_⟩
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_union]
    constructor
    · rintro ⟨hx, hx'⟩ j (hj | hj)
      · rw [hx j hj, hz j hj]
      · rw [hx' j hj, hz' j hj]
    · intro hx
      exact ⟨fun j hj => (hx j (Or.inl hj)).trans (hz j hj),
        fun j hj => (hx j (Or.inr hj)).trans (hz' j hj)⟩
  refine IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem hC ?_ ?_ ?_
  · rintro _ ⟨s, η, rfl⟩
    exact measurableSet_pointCylinder s η
  · intro u hu x hx
    obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.mp hu
    obtain ⟨F, u', hu', hsub⟩ := isOpen_pi_iff.mp hU x.val hx
    refine ⟨{y : X | ∀ j ∈ F, (y : I → S) j = x.val j}, ⟨F, x.val, rfl⟩,
      (isOpen_pointCylinder F x.val).mem_nhds fun j _ => rfl, fun y hy => hsub ?_⟩
    intro j hj
    rw [hy j hj]
    exact (hu' j hj).2
  · rintro _ ⟨s, η, rfl⟩
    exact h s η

/-- **Weak convergence is convergence on cylinder events.** For probability measures on a set of
configurations in a finite alphabet over a countable index set, weak convergence along a countably
generated filter is convergence of the masses of the traces of all cylinder events. -/
theorem tendsto_iff_forall_tendsto_cylinder {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {μ : ι → ProbabilityMeasure X} {ν : ProbabilityMeasure X} :
    Tendsto μ l (𝓝 ν) ↔ ∀ (s : Finset I) (t : Set (s → S)),
      Tendsto (fun i => μ i ((↑) ⁻¹' cylinder (α := fun _ : I => S) s t)) l
        (𝓝 (ν ((↑) ⁻¹' cylinder (α := fun _ : I => S) s t))) := by
  refine ⟨fun h s t => ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto h
    (isClopen_preimage_cylinder s t),
    fun h => tendsto_of_forall_tendsto_pointCylinder fun s η => ?_⟩
  have hP : {x : X | ∀ j ∈ s, (x : I → S) j = η j} =
      (↑) ⁻¹' cylinder (α := fun _ : I => S) s {fun j : s => η j} := by
    ext x
    simp [cylinder, funext_iff]
  rw [hP]
  exact h s _

section Bool

variable {X : Set (I → Bool)}

omit [Countable I] in
/-- The **correlation function** `ρ_F(μ) = μ{x : x = 1 on F}` of a probability measure on a set
of `Bool`-valued configurations, for a finite set `F` of indices. -/
noncomputable def correlationFunction (μ : ProbabilityMeasure X) (F : Finset I) : ℝ≥0 :=
  μ {x : X | ∀ i ∈ F, (x : I → Bool) i = true}

omit [Countable I] in
/-- Unfolding lemma for `correlationFunction`. -/
theorem correlationFunction_def (μ : ProbabilityMeasure X) (F : Finset I) :
    correlationFunction μ F = μ {x : X | ∀ i ∈ F, (x : I → Bool) i = true} :=
  (rfl)

omit [Countable I] in
/-- A point cylinder in `Bool`-valued configurations is the set where the configuration is `1`
on `A` minus the union of the sets where it is `1` on `A ∪ {b}`, for `b ∈ B`. -/
private theorem pointCylinder_eq_diff [DecidableEq I] (s : Finset I) (η : I → Bool) :
    {x : X | ∀ j ∈ s, (x : I → Bool) j = η j} =
      {x : X | ∀ j ∈ s.filter (η · = true), (x : I → Bool) j = true} \
        ⋃ b ∈ s.filter (η · = false),
          {x : X | ∀ j ∈ insert b (s.filter (η · = true)), (x : I → Bool) j = true} := by
  ext x
  simp only [mem_ofPred_eq, Set.mem_sdiff, mem_iUnion, Finset.mem_filter, Finset.mem_insert,
    exists_prop, not_exists, not_and]
  constructor
  · intro hx
    refine ⟨fun j ⟨hj, hηj⟩ => (hx j hj).trans hηj, fun b ⟨hb, hηb⟩ hall => ?_⟩
    have := hall b (Or.inl rfl)
    rw [hx b hb, hηb] at this
    exact Bool.false_ne_true this
  · rintro ⟨h1, h0⟩ j hj
    cases hηj : η j
    · by_contra hxj
      refine h0 j ⟨hj, hηj⟩ fun k hk => ?_
      rcases hk with rfl | hk
      · simpa using hxj
      · exact h1 k hk
    · exact h1 j ⟨hj, hηj⟩

/-- **Weak convergence is convergence of correlation functions.** For probability measures on a
set of `Bool`-valued configurations over a countable index set, weak convergence along a
countably generated filter is convergence of all correlation functions. -/
theorem tendsto_iff_forall_tendsto_correlationFunction {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {μ : ι → ProbabilityMeasure X} {ν : ProbabilityMeasure X} :
    Tendsto μ l (𝓝 ν) ↔
      ∀ F : Finset I, Tendsto (fun i => correlationFunction (μ i) F) l
        (𝓝 (correlationFunction ν F)) := by
  classical
  refine ⟨fun h F => ?_, fun h => tendsto_of_forall_tendsto_pointCylinder fun s η => ?_⟩
  · have hF : {x : X | ∀ i ∈ F, (x : I → Bool) i = true} =
        (↑) ⁻¹' cylinder (α := fun _ : I => Bool) F {fun _ => true} := by
      ext x
      simp [cylinder, funext_iff]
    simp only [correlationFunction_def, hF]
    exact ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto h
      (isClopen_preimage_cylinder F _)
  let C : Set (Set X) := {A | ∃ F : Finset I, A = {x : X | ∀ i ∈ F, (x : I → Bool) i = true}}
  have hC : IsPiSystem C := by
    rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩ -
    refine ⟨F ∪ G, ?_⟩
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, Finset.mem_union]
    exact ⟨fun ⟨hF, hG⟩ i hi => hi.elim (hF i) (hG i),
      fun h => ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩⟩
  have hCmeas : ∀ A ∈ C, MeasurableSet A := by
    rintro _ ⟨F, rfl⟩
    simpa using measurableSet_pointCylinder (X := X) F (fun _ => true)
  have hCtend : ∀ A ∈ C, Tendsto (fun i => μ i A) l (𝓝 (ν A)) := by
    rintro _ ⟨F, rfl⟩
    exact h F
  set A := s.filter (η · = true)
  set T : Finset (Set X) := (s.filter (η · = false)).image
    fun b => {x : X | ∀ j ∈ insert b A, (x : I → Bool) j = true}
  have hTC : ∀ t ∈ T, t ∈ C := by
    intro t ht
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨_, rfl⟩
  have hU : (⋃ b ∈ s.filter (η · = false),
      {x : X | ∀ j ∈ insert b A, (x : I → Bool) j = true}) = ⋃ t ∈ T, t := by
    simp [T]
  have hsub : (⋃ t ∈ T, t) ⊆ {x : X | ∀ j ∈ A, (x : I → Bool) j = true} := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp ht
    exact fun j hj => hxt j (Finset.mem_insert_of_mem hj)
  have hmeasU : MeasurableSet (⋃ t ∈ T, t) :=
    Finset.measurableSet_biUnion T fun t ht => hCmeas t (hTC t ht)
  have hdiff (ρ : ProbabilityMeasure X) :
      ρ {x : X | ∀ j ∈ s, (x : I → Bool) j = η j} =
        ρ {x : X | ∀ j ∈ A, (x : I → Bool) j = true} - ρ (⋃ t ∈ T, t) := by
    rw [pointCylinder_eq_diff, hU]
    rw [← ENNReal.coe_inj, ENNReal.coe_sub, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
      ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact measure_sdiff hsub hmeasU.nullMeasurableSet (measure_ne_top _ _)
  simp only [hdiff]
  exact (h A).sub (IsPiSystem.tendsto_probabilityMeasure_biUnion hC hTC hCmeas hCtend)

/-- **Correlation functions determine the measure.** Two probability measures on a set of
`Bool`-valued configurations over a countable index set with the same correlation functions are
equal. -/
theorem ext_of_correlationFunction {μ ν : ProbabilityMeasure X}
    (h : ∀ F : Finset I, correlationFunction μ F = correlationFunction ν F) : μ = ν :=
  tendsto_nhds_unique (tendsto_const_nhds (x := μ) (f := (atTop : Filter ℕ)))
    (tendsto_iff_forall_tendsto_correlationFunction.mpr fun F => by
      simp [h F])

end Bool

end TauCeti
