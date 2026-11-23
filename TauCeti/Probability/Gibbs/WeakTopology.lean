/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The weak topology on a closed set of configurations

Let `S` be an alphabet with the discrete topology and the discrete σ-algebra, and `X ⊆ I → S` a set
of configurations, with the subspace topology and the trace of the product σ-algebra. When `S` is
finite and `X` is closed, `X` is compact (`isCompact_iff_compactSpace.mp hX.isCompact`), and
Mathlib's instances then make it a compact metrisable Borel space when `I` is countable, so the
space of probability measures `ProbabilityMeasure X` with the weak topology is compact. This
applies to the carrier of a subshift `SymbolicDynamics.FullShift.Subshift`.

The traces on `X` of cylinder events `{ω : ω|_s ∈ t}`, for a finite `s ⊆ I`, are clopen, and
measurable when `S` is countable (`TauCeti.isClopen_preimage_cylinder`,
`TauCeti.measurableSet_preimage_cylinder`). For countable `I` and `S`, weak convergence of
probability measures on `X` is convergence of the masses of these traces,
`TauCeti.tendsto_iff_forall_tendsto_cylinder`. It suffices to test the traces of the cylinder sets
`SymbolicDynamics.FullShift.cylinder s η = {x : x = η on s}`, which form a π-system
(`SymbolicDynamics.FullShift.isPiSystem_cylinder`) containing arbitrarily small neighbourhoods of
every point, `TauCeti.tendsto_of_forall_tendsto_fullShift_cylinder`.

For `S = Bool` the *correlation functions* `ρ_F(μ) = μ{x : x = 1 on F}`, `F ⊆ I` finite
(`MeasureTheory.ProbabilityMeasure.correlationFunction`), determine `μ`
(`TauCeti.ext_of_correlationFunction`), and for countable `I` weak convergence is convergence of
all correlation functions, `TauCeti.tendsto_iff_forall_tendsto_correlationFunction`. The set of
configurations that are `1` on `A` and `0` on `B` is the set `{x = 1 on A}` minus the finite union
of the sets `{x = 1 on A ∪ {b}}`, `b ∈ B`, so its mass is a difference of masses of finite unions
of elements of the π-system of the sets `{x = 1 on F}`.

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge University Press (2021),
  Definition 13.1 and Lemma 13.2.
-/

public section

open MeasureTheory Filter Topology Set
open scoped NNReal

namespace SymbolicDynamics.FullShift

variable {G A : Type*}

/-- A cylinder set is the cylinder event, in the sense of `MeasureTheory.cylinder`, of the single
pattern `x|_U`. -/
theorem cylinder_eq_cylinder_singleton (U : Finset G) (x : G → A) :
    FullShift.cylinder U x = MeasureTheory.cylinder (α := fun _ : G => A) U {U.restrict x} := by
  ext y
  simp [FullShift.mem_cylinder, funext_iff]

/-- Cylinder sets are measurable. -/
theorem measurableSet_cylinder [MeasurableSpace A] [MeasurableSingletonClass A] (U : Finset G)
    (x : G → A) : MeasurableSet (FullShift.cylinder U x) := by
  rw [cylinder_eq_cylinder_singleton]
  exact MeasurableSet.cylinder _ (measurableSet_singleton _)

/-- The cylinder sets form a π-system. -/
theorem isPiSystem_cylinder :
    IsPiSystem {C : Set (G → A) | ∃ (U : Finset G) (x : G → A), C = FullShift.cylinder U x} := by
  classical
  rintro _ ⟨U, x, rfl⟩ _ ⟨V, y, rfl⟩ ⟨z, hzx, hzy⟩
  refine ⟨U ∪ V, z, ?_⟩
  ext w
  simp only [mem_inter_iff, FullShift.mem_cylinder, Finset.mem_union]
  constructor
  · rintro ⟨hwx, hwy⟩ j (hj | hj)
    · rw [hwx j hj, hzx j hj]
    · rw [hwy j hj, hzy j hj]
  · intro hw
    exact ⟨fun j hj => (hw j (Or.inl hj)).trans (hzx j hj),
      fun j hj => (hw j (Or.inr hj)).trans (hzy j hj)⟩

/-- The cylinder sets of a constant configuration form a π-system. -/
theorem isPiSystem_cylinder_const (a : A) :
    IsPiSystem {C : Set (G → A) | ∃ U : Finset G, C = FullShift.cylinder U fun _ => a} := by
  classical
  rintro _ ⟨U, rfl⟩ _ ⟨V, rfl⟩ -
  refine ⟨U ∪ V, ?_⟩
  ext w
  simp only [mem_inter_iff, FullShift.mem_cylinder, Finset.mem_union]
  exact ⟨fun ⟨hU, hV⟩ i hi => hi.elim (hU i) (hV i),
    fun h => ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩⟩

end SymbolicDynamics.FullShift

open SymbolicDynamics

namespace TauCeti

section Alphabet

variable {I S : Type*} [TopologicalSpace S] [DiscreteTopology S] {X : Set (I → S)}

/-- The trace on a set of configurations of a cylinder event is clopen. -/
theorem isClopen_preimage_cylinder (s : Finset I) (t : Set (s → S)) :
    IsClopen ((↑) ⁻¹' cylinder (α := fun _ : I => S) s t : Set X) := by
  have h : IsClopen (cylinder (α := fun _ : I => S) s t) :=
    (isClopen_discrete t).preimage (continuous_pi fun i => continuous_apply (i : I))
  exact h.preimage continuous_subtypeVal

variable [MeasurableSpace S] [DiscreteMeasurableSpace S]

omit [TopologicalSpace S] [DiscreteTopology S] in
/-- The trace on a set of configurations of a cylinder event is measurable. -/
theorem measurableSet_preimage_cylinder [Countable S] (s : Finset I) (t : Set (s → S)) :
    MeasurableSet ((↑) ⁻¹' cylinder (α := fun _ : I => S) s t : Set X) :=
  measurable_subtypeVal
    (MeasurableSet.cylinder (α := fun _ : I => S) s (Set.to_countable t).measurableSet)

variable [Countable I] [Countable S]

/-- **Weak convergence from cylinder sets.** If the masses of the traces of all cylinder sets
`{x : x = η on s}` converge, then the probability measures converge weakly. -/
theorem tendsto_of_forall_tendsto_fullShift_cylinder {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {μ : ι → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    (h : ∀ (s : Finset I) (η : I → S),
      Tendsto (fun i => μ i ((↑) ⁻¹' FullShift.cylinder s η)) l
        (𝓝 (ν ((↑) ⁻¹' FullShift.cylinder s η)))) :
    Tendsto μ l (𝓝 ν) := by
  refine (FullShift.isPiSystem_cylinder.comap ((↑) : X → I → S)
    ).tendsto_probabilityMeasure_of_tendsto_of_mem ?_ ?_ ?_
  · rintro _ ⟨_, ⟨s, η, rfl⟩, rfl⟩
    exact measurable_subtypeVal (FullShift.measurableSet_cylinder s η)
  · -- Every open set contains a cylinder neighbourhood of each of its points.
    intro u hu x hx
    obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.mp hu
    obtain ⟨F, u', hu', hsub⟩ := isOpen_pi_iff.mp hU x.val hx
    refine ⟨_, ⟨_, ⟨F, x.val, rfl⟩, rfl⟩,
      ((FullShift.isOpen_cylinder F x.val).preimage continuous_subtypeVal).mem_nhds
        fun _ _ => rfl, fun y hy => hsub fun j hj => ?_⟩
    rw [FullShift.mem_cylinder.mp hy j hj]
    exact (hu' j hj).2
  · rintro _ ⟨_, ⟨s, η, rfl⟩, rfl⟩
    exact h s η

/-- **Weak convergence is convergence on cylinder events.** For probability measures on a set of
configurations in a countable alphabet over a countable index set, weak convergence along a
countably generated filter is convergence of the masses of the traces of all cylinder events. -/
theorem tendsto_iff_forall_tendsto_cylinder {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {μ : ι → ProbabilityMeasure X} {ν : ProbabilityMeasure X} :
    Tendsto μ l (𝓝 ν) ↔ ∀ (s : Finset I) (t : Set (s → S)),
      Tendsto (fun i => μ i ((↑) ⁻¹' cylinder (α := fun _ : I => S) s t)) l
        (𝓝 (ν ((↑) ⁻¹' cylinder (α := fun _ : I => S) s t))) := by
  refine ⟨fun h s t => ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto h
    (isClopen_preimage_cylinder s t),
    fun h => tendsto_of_forall_tendsto_fullShift_cylinder fun s η => ?_⟩
  simpa only [FullShift.cylinder_eq_cylinder_singleton] using h s {s.restrict η}

end Alphabet

end TauCeti

namespace MeasureTheory.ProbabilityMeasure

variable {I : Type*} {X : Set (I → Bool)}

/-- The **correlation function** `ρ_F(μ) = μ{x : x = 1 on F}` of a probability measure on a set
of `Bool`-valued configurations, for a finite set `F` of indices. -/
noncomputable def correlationFunction (μ : ProbabilityMeasure X) (F : Finset I) : ℝ≥0 :=
  μ ((↑) ⁻¹' FullShift.cylinder F fun _ => true)

/-- Unfolding lemma for `correlationFunction`. -/
theorem correlationFunction_def (μ : ProbabilityMeasure X) (F : Finset I) :
    μ.correlationFunction F = μ ((↑) ⁻¹' FullShift.cylinder F fun _ => true) :=
  (rfl)

/-- The correlation function of the empty set of indices is `1`. -/
@[simp]
theorem correlationFunction_empty (μ : ProbabilityMeasure X) : μ.correlationFunction ∅ = 1 := by
  simp [correlationFunction_def, FullShift.cylinder]

/-- Correlation functions decrease as the set of indices grows. -/
theorem antitone_correlationFunction (μ : ProbabilityMeasure X) :
    Antitone μ.correlationFunction :=
  fun _ _ hFG => μ.apply_mono fun _ hx j hj => hx j (hFG hj)

end MeasureTheory.ProbabilityMeasure

namespace TauCeti

section Bool

variable {I : Type*} {X : Set (I → Bool)}

/-- A cylinder set in `Bool`-valued configurations is the set where the configuration is `1` on
`A` minus the union of the sets where it is `1` on `A ∪ {b}`, for `b ∈ B`. -/
private theorem fullShift_cylinder_eq_diff [DecidableEq I] (s : Finset I) (η : I → Bool) :
    FullShift.cylinder s η =
      FullShift.cylinder (s.filter (η · = true)) (fun _ => true) \
        ⋃ b ∈ s.filter (η · = false),
          FullShift.cylinder (insert b (s.filter (η · = true))) fun _ => true := by
  ext x
  simp only [FullShift.mem_cylinder, Set.mem_sdiff, mem_iUnion, Finset.mem_filter,
    Finset.mem_insert, exists_prop, not_exists, not_and]
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

/-- The mass of the trace of a cylinder set in `Bool`-valued configurations is a correlation
function minus the mass of a finite union of traces of cylinder sets of the constant `1`. -/
private theorem apply_preimage_fullShift_cylinder [DecidableEq I] (ρ : ProbabilityMeasure X)
    (s : Finset I) (η : I → Bool) :
    ρ ((↑) ⁻¹' FullShift.cylinder s η) = ρ.correlationFunction (s.filter (η · = true)) -
      ρ (⋃ t ∈ (s.filter (η · = false)).image
          (fun b => (↑) ⁻¹' FullShift.cylinder (insert b (s.filter (η · = true))) fun _ => true),
        t) := by
  have hsub : (⋃ b ∈ s.filter (η · = false), ((↑) ⁻¹' FullShift.cylinder
      (insert b (s.filter (η · = true))) fun _ => true : Set X)) ⊆
      (↑) ⁻¹' FullShift.cylinder (s.filter (η · = true)) fun _ => true :=
    iUnion₂_subset fun _ _ _ hx j hj => hx j (Finset.mem_insert_of_mem hj)
  have hmeas : MeasurableSet (⋃ b ∈ s.filter (η · = false), ((↑) ⁻¹' FullShift.cylinder
      (insert b (s.filter (η · = true))) fun _ => true : Set X)) :=
    Finset.measurableSet_biUnion _ fun _ _ =>
      measurable_subtypeVal (FullShift.measurableSet_cylinder _ _)
  rw [Finset.set_biUnion_finset_image, ProbabilityMeasure.correlationFunction_def,
    fullShift_cylinder_eq_diff, preimage_sdiff, preimage_iUnion₂, ← ENNReal.coe_inj,
    ENNReal.coe_sub]
  simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact measure_sdiff hsub hmeas.nullMeasurableSet (measure_ne_top _ _)

/-- **Weak convergence is convergence of correlation functions.** For probability measures on a
set of `Bool`-valued configurations over a countable index set, weak convergence along a
countably generated filter is convergence of all correlation functions. -/
theorem tendsto_iff_forall_tendsto_correlationFunction [Countable I] {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {μ : ι → ProbabilityMeasure X} {ν : ProbabilityMeasure X} :
    Tendsto μ l (𝓝 ν) ↔
      ∀ F : Finset I, Tendsto (fun i => (μ i).correlationFunction F) l
        (𝓝 (ν.correlationFunction F)) := by
  classical
  refine ⟨fun h F => ?_, fun h => tendsto_of_forall_tendsto_fullShift_cylinder fun s η => ?_⟩
  · -- Correlation functions are masses of clopen sets.
    simp only [ProbabilityMeasure.correlationFunction_def,
      FullShift.cylinder_eq_cylinder_singleton]
    exact ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto h
      (isClopen_preimage_cylinder F _)
  · -- A cylinder set is the difference of a correlation event and a finite union of correlation
    -- events, which lie in a π-system of measurable sets on which the masses converge.
    have hC := (FullShift.isPiSystem_cylinder_const (G := I) true).comap ((↑) : X → I → Bool)
    simp only [apply_preimage_fullShift_cylinder]
    refine (h _).sub (hC.tendsto_probabilityMeasure_biUnion ?_ ?_ ?_)
    · intro t ht
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp ht
      exact ⟨_, ⟨_, rfl⟩, rfl⟩
    · rintro _ ⟨_, ⟨F, rfl⟩, rfl⟩
      exact measurable_subtypeVal (FullShift.measurableSet_cylinder _ _)
    · rintro _ ⟨_, ⟨F, rfl⟩, rfl⟩
      exact h F

/-- **Correlation functions determine the measure.** Two probability measures on a set of
`Bool`-valued configurations with the same correlation functions are equal. -/
theorem ext_of_correlationFunction {μ ν : ProbabilityMeasure X}
    (h : ∀ F : Finset I, μ.correlationFunction F = ν.correlationFunction F) : μ = ν := by
  let C : Set (Set X) := {A | ∃ t ∈ {C : Set (I → Bool) | ∃ F : Finset I,
    C = FullShift.cylinder F fun _ => true}, (↑) ⁻¹' t = A}
  have hmem (F : Finset I) : ((↑) ⁻¹' FullShift.cylinder F fun _ => true : Set X) ∈ C :=
    ⟨_, ⟨F, rfl⟩, rfl⟩
  -- The traces of the cylinder sets of the constant `1` generate the trace σ-algebra, because
  -- the set where a coordinate is `0` is the complement of the set where it is `1`.
  have hgen : (inferInstance : MeasurableSpace X) = MeasurableSpace.generateFrom C := by
    refine le_antisymm (Measurable.comap_le ?_) (MeasurableSpace.generateFrom_le ?_)
    · let : MeasurableSpace X := MeasurableSpace.generateFrom C
      refine measurable_pi_iff.mpr fun i => measurable_to_countable' fun b => ?_
      have h1 := MeasurableSpace.measurableSet_generateFrom (hmem {i})
      cases b
      · convert h1.compl using 1
        ext x
        simp [FullShift.mem_cylinder]
      · convert h1 using 1
        ext x
        simp [FullShift.mem_cylinder]
    · rintro _ ⟨_, ⟨F, rfl⟩, rfl⟩
      exact measurable_subtypeVal (FullShift.measurableSet_cylinder _ _)
  refine ProbabilityMeasure.toMeasure_injective (ext_of_generate_finite C hgen
    ((FullShift.isPiSystem_cylinder_const true).comap _) ?_ (by simp))
  rintro _ ⟨_, ⟨F, rfl⟩, rfl⟩
  have := congrArg ((↑) : ℝ≥0 → ENNReal) (h F)
  simpa only [ProbabilityMeasure.correlationFunction_def,
    ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using this

end Bool

end TauCeti
