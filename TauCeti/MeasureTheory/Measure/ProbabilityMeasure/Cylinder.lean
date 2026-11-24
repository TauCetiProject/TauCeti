/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Constructions.Cylinder.FullShift
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Dirac
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Convex

/-!
# The weak topology on a closed set of configurations

Let `S` be an alphabet with the discrete topology and the discrete σ-algebra, and `X ⊆ I → S` a set
of configurations, with the subspace topology and the trace of the product σ-algebra. When `S` is
finite and `X` is closed, `X` is compact (`isCompact_iff_compactSpace.mp hX.isCompact`), and
Mathlib's instances then make it a compact metrisable Borel space when `I` is countable, so the
space of probability measures `ProbabilityMeasure X` with the weak topology is compact by the
instance in `Mathlib.MeasureTheory.Measure.Prokhorov`. This applies to the carrier of a subshift
`SymbolicDynamics.FullShift.Subshift`.

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
(`TauCeti.ext_of_correlationFunction`), because the traces of the sets `{x : x = 1 on F}` generate
the trace σ-algebra (`TauCeti.measurableSpace_eq_generateFrom_cylinder_true`), and for countable
`I` weak convergence is convergence of all correlation functions,
`TauCeti.tendsto_iff_forall_tendsto_correlationFunction`. The set of configurations that are `1`
on `A` and `0` on `B` is the set `{x = 1 on A}` minus the finite union of the sets
`{x = 1 on A ∪ {b}}`, `b ∈ B`, so its mass is a difference of masses of finite unions of elements
of the π-system of the sets `{x = 1 on F}`. Correlation functions are affine in the measure
(`MeasureTheory.ProbabilityMeasure.correlationFunction_convexComb`), and the correlation function
of the point mass at `x` is `1` or `0` according as `x = 1` on `F` or not
(`MeasureTheory.ProbabilityMeasure.correlationFunction_diracProba`).

## References

* V. Gorin, *Lectures on random lozenge tilings*, Cambridge University Press (2021),
  Definition 13.1 and Lemma 13.2.
-/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

open SymbolicDynamics

namespace TauCeti

section Alphabet

variable {I S : Type*} [TopologicalSpace S] [DiscreteTopology S] {X : Set (I → S)}

/-- The trace on a set of configurations of a cylinder event is clopen. -/
theorem isClopen_preimage_cylinder (s : Finset I) (t : Set (s → S)) :
    IsClopen ((↑) ⁻¹' cylinder (α := fun _ : I => S) s t : Set X) := by
  have h : IsClopen (cylinder (α := fun _ : I => S) s t) :=
    (isClopen_discrete t).preimage (Finset.continuous_restrict s)
  exact h.preimage continuous_subtypeVal

omit [TopologicalSpace S] [DiscreteTopology S] in
/-- The trace on a set of configurations of a cylinder set is measurable. -/
theorem measurableSet_preimage_fullShift_cylinder [MeasurableSpace S] [MeasurableSingletonClass S]
    (s : Finset I) (η : I → S) : MeasurableSet ((↑) ⁻¹' FullShift.cylinder s η : Set X) :=
  measurable_subtypeVal (FullShift.measurableSet_cylinder s η)

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
    exact measurableSet_preimage_fullShift_cylinder s η
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

/-- The correlation function of the point mass at `x` is `1` if `x = 1` on `F`, and `0`
otherwise. -/
@[simp]
theorem correlationFunction_diracProba (x : X) (F : Finset I) :
    (diracProba x).correlationFunction F = if ∀ i ∈ F, (x : I → Bool) i = true then 1 else 0 := by
  rw [correlationFunction_def,
    diracProba_apply' _ (TauCeti.measurableSet_preimage_fullShift_cylinder _ _)]
  split_ifs with h <;> simpa [Set.indicator, FullShift.mem_cylinder] using h

/-- **Correlation functions are affine.** The correlation function of a convex combination of
probability measures is the convex combination of their correlation functions. -/
@[simp]
theorem correlationFunction_convexComb {a b : ℝ≥0∞} (hab : a + b = 1)
    (P Q : ProbabilityMeasure X) (F : Finset I) :
    (convexComb hab P Q).correlationFunction F =
      a.toNNReal * P.correlationFunction F + b.toNNReal * Q.correlationFunction F := by
  simp only [correlationFunction_def]
  exact convexComb_apply hab P Q _

end MeasureTheory.ProbabilityMeasure

namespace TauCeti

section Bool

variable {I : Type*} {X : Set (I → Bool)}

/-- The trace of a cylinder set in `Bool`-valued configurations is the trace of the set where the
configuration is `1` on `A` minus the union of the traces of the sets where it is `1` on
`A ∪ {b}`, for `b ∈ B`. -/
private theorem preimage_fullShift_cylinder_eq_diff [DecidableEq I] (s : Finset I) (η : I → Bool) :
    ((↑) ⁻¹' FullShift.cylinder s η : Set X) =
      (↑) ⁻¹' FullShift.cylinder (s.filter (η · = true)) (fun _ => true) \
        ⋃ t ∈ (s.filter (η · = false)).image
          (fun b => (↑) ⁻¹' FullShift.cylinder (insert b (s.filter (η · = true))) fun _ => true),
          t := by
  rw [Finset.set_biUnion_finset_image, ← preimage_iUnion₂, ← preimage_sdiff]
  congr 1
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
  rw [preimage_fullShift_cylinder_eq_diff, ← ENNReal.coe_inj, ENNReal.coe_sub]
  simp only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    ProbabilityMeasure.correlationFunction_def]
  refine measure_sdiff (iUnion₂_subset fun t ht => ?_)
    (Finset.measurableSet_biUnion _ fun t ht => ?_).nullMeasurableSet (measure_ne_top _ _) <;>
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp ht
  · exact fun x hx j hj => hx j (Finset.mem_insert_of_mem hj)
  · exact measurableSet_preimage_fullShift_cylinder _ _

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
    have hC := (FullShift.isPiSystem_cylinder_fixed (G := I) fun _ => true).comap
      ((↑) : X → I → Bool)
    simp only [apply_preimage_fullShift_cylinder]
    refine (h _).sub (hC.tendsto_probabilityMeasure_biUnion ?_ ?_ ?_)
    · intro t ht
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp ht
      exact ⟨_, ⟨_, rfl⟩, rfl⟩
    · rintro _ ⟨_, ⟨F, rfl⟩, rfl⟩
      exact measurableSet_preimage_fullShift_cylinder _ _
    · rintro _ ⟨_, ⟨F, rfl⟩, rfl⟩
      exact h F

/-- The traces of the cylinder sets of the constant `1` generate the trace σ-algebra on a set of
`Bool`-valued configurations. -/
theorem measurableSpace_eq_generateFrom_cylinder_true :
    (inferInstance : MeasurableSpace X) = MeasurableSpace.generateFrom
      (range fun F : Finset I => (↑) ⁻¹' FullShift.cylinder F fun _ => true) := by
  set C := range fun F : Finset I => ((↑) ⁻¹' FullShift.cylinder F fun _ => true : Set X)
  refine le_antisymm (Measurable.comap_le ?_) (MeasurableSpace.generateFrom_le ?_)
  · -- The set where a coordinate is `0` is the complement of the set where it is `1`.
    let : MeasurableSpace X := MeasurableSpace.generateFrom C
    refine measurable_pi_iff.mpr fun i => measurable_to_countable' fun b => ?_
    have h1 := MeasurableSpace.measurableSet_generateFrom (s := C) ⟨{i}, rfl⟩
    cases b
    · convert h1.compl using 1
      ext x
      simp [FullShift.mem_cylinder]
    · convert h1 using 1
      ext x
      simp [FullShift.mem_cylinder]
  · rintro _ ⟨F, rfl⟩
    exact measurableSet_preimage_fullShift_cylinder _ _

/-- **Correlation functions determine the measure.** Two probability measures on a set of
`Bool`-valued configurations with the same correlation functions are equal. -/
theorem ext_of_correlationFunction {μ ν : ProbabilityMeasure X}
    (h : ∀ F : Finset I, μ.correlationFunction F = ν.correlationFunction F) : μ = ν := by
  have hC : IsPiSystem
      (range fun F : Finset I => ((↑) ⁻¹' FullShift.cylinder F fun _ => true : Set X)) := by
    convert (FullShift.isPiSystem_cylinder_fixed fun _ => true).comap ((↑) : X → I → Bool) using 1
    ext
    simp [eq_comm]
  refine ProbabilityMeasure.toMeasure_injective
    (ext_of_generate_finite _ measurableSpace_eq_generateFrom_cylinder_true hC ?_ (by simp))
  rintro _ ⟨F, rfl⟩
  have := congrArg ((↑) : ℝ≥0 → ENNReal) (h F)
  simpa only [ProbabilityMeasure.correlationFunction_def,
    ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using this

end Bool

end TauCeti
