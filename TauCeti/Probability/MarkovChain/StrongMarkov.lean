/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.MarkovProperty
public import TauCeti.Probability.Process.StoppedValue
public import TauCeti.MeasureTheory.Integral.Bind

/-!
# The strong Markov property of a homogeneous chain

Let `X` be the coordinate process on path space `ℕ → α` under the path law
`markovChainLaw ν κ`, write `ℙₓ = markovChainLaw (dirac x) κ` for the law of the chain started at
`x`, and let `τ : (ℕ → α) → WithTop ℕ` be a stopping time of the natural filtration
`MeasureTheory.Filtration.piLE`. On the event `{τ < ∞}` write
`X τ = stoppedValue (fun n x => x n) τ` for the state at time `τ` and
`θ_τ X = stoppedValue (fun n => (shift α)^[n]) τ` for the path seen from time `τ`, that is
`(X (τ + k))ₖ`. The *strong Markov property* says that, conditionally on
the information `𝓕_τ = hτ.measurableSpace` available at time `τ` and on `{τ < ∞}`, the future path
`θ_τ X` is a chain with law `ℙ_{X τ}`.

Every statement below is restricted to `{τ < ∞}`, so the arbitrary values of `X τ` and `θ_τ X`
off that event never enter. This file proves the property in the following forms.

* As a law on an event of `𝓕_τ`
  (`MeasureTheory.Measure.markovChainLaw_restrict_map_stoppedValue_shift_iterate`): restricted to
  `A ∩ {τ < ∞}` with `A ∈ 𝓕_τ`, the future path has the law of the chain whose initial measure is
  the law of `X τ` restricted to the same event. When `X τ` is a fixed state `y` there, as at an
  entrance time of `{y}`, this law is a multiple of `ℙ_y`
  (`MeasureTheory.Measure.markovChainLaw_restrict_map_stoppedValue_shift_iterate_eq_smul`).
* As an identity of probabilities
  (`MeasureTheory.Measure.markovChainLaw_inter_preimage_stoppedValue_shift_iterate`):
  `ℙ(A ∩ {τ < ∞} ∩ {θ_τ X ∈ B}) = ∫_{A ∩ {τ < ∞}} ℙ_{X τ}(B)`.
* As identities of conditional expectations given `𝓕_τ`, for integrable test functions
  (`MeasureTheory.Measure.condExp_stoppedValue_shift_iterate_markovChainLaw`) and for events
  (`MeasureTheory.Measure.condExp_indicator_stoppedValue_shift_iterate_markovChainLaw`).
* For an almost surely finite stopping time, without the restriction to `{τ < ∞}`
  (`MeasureTheory.Measure.markovChainLaw_restrict_map_stoppedValue_shift_iterate_of_ae_ne_top` and
  `MeasureTheory.Measure.condExp_stoppedValue_shift_iterate_markovChainLaw_of_ae_ne_top`).

The proof decomposes `{τ < ∞}` into the events `{τ = n}`. An event of `𝓕_τ` meets `{τ = n}` in an
event of the history up to time `n`, on which the Markov property at the fixed time `n`
(`MeasureTheory.Measure.markovChainLaw_restrict_map_shift_iterate`) identifies the law of the
future path; the path law is additive in the initial measure, which reassembles the pieces.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, Theorem 1.4.2.
* Olav Kallenberg, *Foundations of Modern Probability*, 2nd edition, Springer, 2002, Proposition
  8.9.
-/

public section

open ProbabilityTheory TauCeti.Probability

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] (ν : Measure α) (κ : Kernel α α) [IsMarkovKernel κ]
  {τ : (ℕ → α) → WithTop ℕ}

/-- **The strong Markov property, as a law on an event of `𝓕_τ`.** For a stopping time `τ` of the
natural filtration and an event `A` of the σ-algebra of `τ`, the law of the future path
`θ_τ X = (X (τ + k))ₖ` on `A ∩ {τ < ∞}` is the path law of the chain whose initial measure is the
law of `X τ` on the same event. -/
theorem markovChainLaw_restrict_map_stoppedValue_shift_iterate
    [IsFiniteMeasure ν] (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => α)) τ)
    {A : Set (ℕ → α)} (hA : MeasurableSet[hτ.measurableSpace] A) :
    ((markovChainLaw ν κ).restrict (A ∩ {x | τ x ≠ ⊤})).map
        (stoppedValue (fun n => (shift α)^[n]) τ) =
      markovChainLaw (((markovChainLaw ν κ).restrict (A ∩ {x | τ x ≠ ⊤})).map
        (stoppedValue (fun n x => x n) τ)) κ := by
  set P := markovChainLaw ν κ
  set θ := stoppedValue (fun n => (shift α)^[n]) τ
  set Y := stoppedValue (fun n (x : ℕ → α) => x n) τ
  have hτm : Measurable τ := hτ.measurable'
  have hθ : Measurable θ :=
    measurable_stoppedValue_of_countable (fun n => measurable_shift_iterate n) hτm
  have hY : Measurable Y :=
    (Filtration.adapted_piLE.measurable_stoppedValue hτ).mono hτ.measurableSpace_le le_rfl
  set E : ℕ → Set (ℕ → α) := fun n => A ∩ {x | τ x = WithTop.some n}
  have hEn : ∀ n, MeasurableSet[Filtration.piLE n] (E n) := fun n =>
    (hτ.measurableSet_inter_eq_iff A n).1 (hA.inter (hτ.measurableSet_eq_of_countable' n))
  have hE : ∀ n, MeasurableSet (E n) := fun n => Filtration.le _ n _ (hEn n)
  have hU : A ∩ {x | τ x ≠ ⊤} = ⋃ n, E n := by
    ext x
    cases h : τ x <;> simp [E, h]
  have hd : Pairwise (Function.onFun Disjoint E) := fun m n hmn =>
    Set.disjoint_left.2 fun x hm hn => hmn (WithTop.coe_injective (hm.2.symm.trans hn.2))
  rw [hU, Measure.restrict_iUnion hd hE, Measure.map_sum hθ.aemeasurable,
    Measure.map_sum hY.aemeasurable, markovChainLaw_eq_comp, Measure.bind_sum _ _
      κ.markovChainKernel.measurable.aemeasurable]
  congr 1
  funext n
  -- On `{τ = n}` the stopped quantities are those at the fixed time `n`, and `A ∩ {τ = n}` is an
  -- event of the history `X 0, …, X n`, where the Markov property at time `n` applies.
  have hτn : ∀ᵐ x ∂P.restrict (E n), τ x = WithTop.some n :=
    ae_restrict_of_forall_mem (hE n) fun x hx => hx.2
  have hθn : (P.restrict (E n)).map θ = (P.restrict (E n)).map (shift α)^[n] :=
    Measure.map_congr (hτn.mono fun x hx => by simp only [θ, stoppedValue, hx, WithTop.untopD_coe])
  have hYn : (P.restrict (E n)).map Y = (P.restrict (E n)).map fun x => x n :=
    Measure.map_congr (hτn.mono fun x hx => by simp only [Y, stoppedValue, hx, WithTop.untopD_coe])
  have hEn' := hEn n
  rw [Filtration.piLE_eq_comap_prefix] at hEn'
  obtain ⟨B, hB, hBE⟩ := hEn'
  rw [hθn, hYn, ← markovChainLaw_eq_comp, ← hBE]
  exact markovChainLaw_restrict_map_shift_iterate ν κ n hB

/-- **The strong Markov property at a stopping time where the chain sits at a fixed state.** If
`X τ = y` on `A ∩ {τ < ∞}`, as when `τ` is the entrance time of `{y}`, the future path on that
event has law `ℙ(A ∩ {τ < ∞}) • ℙ_y`: it is a chain started at `y`, independent of `A`. -/
theorem markovChainLaw_restrict_map_stoppedValue_shift_iterate_eq_smul
    [IsFiniteMeasure ν] (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => α)) τ)
    {A : Set (ℕ → α)} (hA : MeasurableSet[hτ.measurableSpace] A) {y : α}
    (hy : ∀ x ∈ A ∩ {x | τ x ≠ ⊤}, stoppedValue (fun n x => x n) τ x = y) :
    ((markovChainLaw ν κ).restrict (A ∩ {x | τ x ≠ ⊤})).map
        (stoppedValue (fun n => (shift α)^[n]) τ) =
      markovChainLaw ν κ (A ∩ {x | τ x ≠ ⊤}) • markovChainLaw (Measure.dirac y) κ := by
  have hS : MeasurableSet (A ∩ {x | τ x ≠ ⊤}) :=
    hτ.measurableSpace_le _ hA |>.inter ((measurableSet_singleton ⊤).preimage hτ.measurable').compl
  rw [markovChainLaw_restrict_map_stoppedValue_shift_iterate ν κ hτ hA,
    Measure.map_congr (ae_restrict_of_forall_mem hS hy), Measure.map_const,
    Measure.restrict_apply_univ]
  simp only [markovChainLaw_eq_comp]
  exact Measure.bind_smul _ _ κ.markovChainKernel.measurable.aemeasurable

/-- **The strong Markov property, for events.** For a stopping time `τ` of the natural filtration,
an event `A` of the σ-algebra of `τ` and a measurable set `B` of paths,
`ℙ(A ∩ {τ < ∞} ∩ {θ_τ X ∈ B}) = ∫_{A ∩ {τ < ∞}} ℙ_{X τ}(B)`. -/
theorem markovChainLaw_inter_preimage_stoppedValue_shift_iterate
    [IsFiniteMeasure ν] (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => α)) τ)
    {A : Set (ℕ → α)} (hA : MeasurableSet[hτ.measurableSpace] A) {B : Set (ℕ → α)}
    (hB : MeasurableSet B) :
    markovChainLaw ν κ (A ∩ {x | τ x ≠ ⊤} ∩ stoppedValue (fun n => (shift α)^[n]) τ ⁻¹' B) =
      ∫⁻ x in A ∩ {x | τ x ≠ ⊤},
        markovChainLaw (Measure.dirac (stoppedValue (fun n x => x n) τ x)) κ B
          ∂markovChainLaw ν κ := by
  have hτm : Measurable τ := hτ.measurable'
  have hθ : Measurable (stoppedValue (fun n => (shift α)^[n]) τ) :=
    measurable_stoppedValue_of_countable (fun n => measurable_shift_iterate n) hτm
  have hY : Measurable (stoppedValue (fun n (x : ℕ → α) => x n) τ) :=
    (Filtration.adapted_piLE.measurable_stoppedValue hτ).mono hτ.measurableSpace_le le_rfl
  rw [Set.inter_comm, ← Measure.restrict_apply (hB.preimage hθ), ← Measure.map_apply hθ hB,
    markovChainLaw_restrict_map_stoppedValue_shift_iterate ν κ hτ hA,
    markovChainLaw_eq_comp, Measure.bind_apply hB (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hB) hY]
  simp

section CondExp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The strong Markov property, for test functions.** For a stopping time `τ` of the natural
filtration and a function `f` of paths that is integrable for the law of the future path on
`{τ < ∞}`, the conditional expectation given `𝓕_τ` of `f (θ_τ X)` on `{τ < ∞}` is `∫ f dℙ_{X τ}`
there. -/
theorem condExp_stoppedValue_shift_iterate_markovChainLaw
    [IsFiniteMeasure ν] (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => α)) τ)
    {f : (ℕ → α) → E}
    (hf : Integrable f (markovChainLaw (((markovChainLaw ν κ).restrict {x | τ x ≠ ⊤}).map
      (stoppedValue (fun n x => x n) τ)) κ)) :
    (markovChainLaw ν κ)[{x | τ x ≠ ⊤}.indicator
        (fun x => f (stoppedValue (fun n => (shift α)^[n]) τ x)) | hτ.measurableSpace]
      =ᵐ[markovChainLaw ν κ] {x | τ x ≠ ⊤}.indicator fun x =>
        ∫ y, f y ∂markovChainLaw (Measure.dirac (stoppedValue (fun n x => x n) τ x)) κ := by
  set P := markovChainLaw ν κ
  set θ := stoppedValue (fun n => (shift α)^[n]) τ
  set Y := stoppedValue (fun n (x : ℕ → α) => x n) τ
  set S := {x | τ x ≠ ⊤}
  set g : α → E := fun z => ∫ y, f y ∂markovChainLaw (Measure.dirac z) κ
  have hτm : Measurable τ := hτ.measurable'
  have hθ : Measurable θ :=
    measurable_stoppedValue_of_countable (fun n => measurable_shift_iterate n) hτm
  have hYτ : Measurable[hτ.measurableSpace] Y := Filtration.adapted_piLE.measurable_stoppedValue hτ
  have hY : Measurable Y := hYτ.mono hτ.measurableSpace_le le_rfl
  have hSτ : MeasurableSet[hτ.measurableSpace] S :=
    ((measurableSet_singleton ⊤).preimage hτ.measurable).compl
  have hS : MeasurableSet S := hτ.measurableSpace_le _ hSτ
  -- For `s ∈ 𝓕_τ`, the future path on `s ∩ {τ < ∞}` is the chain started from the law of `X τ`
  -- there; its law is dominated by the law of the future path on `{τ < ∞}`.
  have hlaw : ∀ s, MeasurableSet[hτ.measurableSpace] s →
      (P.restrict (s ∩ S)).map θ = markovChainLaw ((P.restrict (s ∩ S)).map Y) κ :=
    fun s hs => markovChainLaw_restrict_map_stoppedValue_shift_iterate ν κ hτ hs
  have hfS : (P.restrict S).map θ = markovChainLaw ((P.restrict S).map Y) κ := by
    simpa using hlaw Set.univ MeasurableSet.univ
  have hfs : ∀ s, MeasurableSet[hτ.measurableSpace] s →
      Integrable f (markovChainLaw ((P.restrict (s ∩ S)).map Y) κ) := fun s hs => by
    rw [← hlaw s hs]
    refine hf.mono_measure ?_
    rw [← hfS]
    exact Measure.map_mono (Measure.restrict_mono Set.inter_subset_right le_rfl) hθ
  -- Integrating against a path law averages the integrals against the laws started at fixed
  -- states, since the path law is a mixture of the latter.
  have hbind : ∀ {μ : Measure α}, Integrable f (markovChainLaw μ κ) →
      Integrable g μ ∧ ∫ y, f y ∂markovChainLaw μ κ = ∫ z, g z ∂μ := fun {μ} hμ => by
    rw [markovChainLaw_eq_comp] at hμ ⊢
    simp only [g, ← Kernel.markovChainKernel_apply]
    exact ⟨integrable_integral_bind κ.markovChainKernel.measurable hμ,
      integral_bind κ.markovChainKernel.measurable.aemeasurable hμ⟩
  have hgS : Integrable g ((P.restrict S).map Y) := (hbind hf).1
  have hfθ : Integrable (S.indicator fun x => f (θ x)) P := by
    rw [integrable_indicator_iff hS]
    rw [← hfS] at hf
    exact (integrable_map_measure hf.1 hθ.aemeasurable).1 hf
  have hgY : Integrable (S.indicator fun x => g (Y x)) P := by
    rw [integrable_indicator_iff hS]
    exact (integrable_map_measure hgS.1 hY.aemeasurable).1 hgS
  refine (ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le hfθ
    (fun s _ _ => hgY.integrableOn) (fun s hs _ => ?_) ?_).symm
  · rw [setIntegral_indicator hS, setIntegral_indicator hS,
      ← integral_map hY.aemeasurable (hbind (hfs s hs)).1.1, ← (hbind (hfs s hs)).2, ← hlaw s hs,
      integral_map hθ.aemeasurable (by rw [hlaw s hs]; exact (hfs s hs).1)]
  · -- `g ∘ X τ` is `𝓕_τ`-measurable up to null sets on `{τ < ∞}`, and vanishes off it.
    have hgm : AEStronglyMeasurable[hτ.measurableSpace] (fun x => g (Y x)) (P.restrict S) :=
      (hgS.1.comp_ae_measurable' hY.aemeasurable).mono (measurable_iff_comap_le.1 hYτ)
    refine ⟨S.indicator (hgm.mk _), hgm.stronglyMeasurable_mk.indicator hSτ, ?_⟩
    filter_upwards [(ae_restrict_iff' hS).1 hgm.ae_eq_mk] with x hx
    by_cases hxS : x ∈ S
    · simp [Set.indicator_of_mem hxS, hx hxS]
    · simp [Set.indicator_of_notMem hxS]

/-- **The strong Markov property, for events.** For a stopping time `τ` of the natural filtration
and a measurable set `B` of paths, the conditional probability given `𝓕_τ` that `τ < ∞` and the
future path `θ_τ X` lies in `B` is `ℙ_{X τ}(B)` on `{τ < ∞}`, and zero off it. -/
theorem condExp_indicator_stoppedValue_shift_iterate_markovChainLaw
    [IsFiniteMeasure ν] (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => α)) τ)
    {B : Set (ℕ → α)} (hB : MeasurableSet B) :
    (markovChainLaw ν κ)[({x | τ x ≠ ⊤} ∩ stoppedValue (fun n => (shift α)^[n]) τ ⁻¹' B).indicator 1
        | hτ.measurableSpace]
      =ᵐ[markovChainLaw ν κ] {x | τ x ≠ ⊤}.indicator
        fun x => (markovChainLaw (Measure.dirac (stoppedValue (fun n x => x n) τ x)) κ).real B := by
  have : IsFiniteMeasure (markovChainLaw (((markovChainLaw ν κ).restrict {x | τ x ≠ ⊤}).map
      (stoppedValue (fun n x => x n) τ)) κ) := by
    rw [markovChainLaw_eq_comp]; infer_instance
  have h := condExp_stoppedValue_shift_iterate_markovChainLaw ν κ hτ
    (f := B.indicator (1 : (ℕ → α) → ℝ)) ((integrable_const (1 : ℝ)).indicator hB)
  have hind : (fun x => B.indicator (1 : (ℕ → α) → ℝ) (stoppedValue (fun n => (shift α)^[n]) τ x)) =
      (stoppedValue (fun n => (shift α)^[n]) τ ⁻¹' B).indicator 1 := by
    funext x
    by_cases hx : stoppedValue (fun n => (shift α)^[n]) τ x ∈ B <;> simp [hx]
  simp_rw [integral_indicator_one hB] at h
  rwa [hind, Set.indicator_indicator] at h

/-- **The strong Markov property at an almost surely finite stopping time, as a law on an event of
`𝓕_τ`.** If `τ < ∞` almost surely, the law of the future path `θ_τ X` on an event `A` of the
σ-algebra of `τ` is the path law of the chain whose initial measure is the law of `X τ` on `A`. -/
theorem markovChainLaw_restrict_map_stoppedValue_shift_iterate_of_ae_ne_top
    [IsFiniteMeasure ν] (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => α)) τ)
    (hτ_fin : ∀ᵐ x ∂markovChainLaw ν κ, τ x ≠ ⊤) {A : Set (ℕ → α)}
    (hA : MeasurableSet[hτ.measurableSpace] A) :
    ((markovChainLaw ν κ).restrict A).map (stoppedValue (fun n => (shift α)^[n]) τ) =
      markovChainLaw (((markovChainLaw ν κ).restrict A).map
        (stoppedValue (fun n x => x n) τ)) κ := by
  have h : (markovChainLaw ν κ).restrict (A ∩ {x | τ x ≠ ⊤}) = (markovChainLaw ν κ).restrict A :=
    Measure.restrict_congr_set (inter_ae_eq_left_of_ae_eq_univ (ae_eq_univ.2 hτ_fin))
  simpa only [h] using markovChainLaw_restrict_map_stoppedValue_shift_iterate ν κ hτ hA

/-- **The strong Markov property at an almost surely finite stopping time, for test functions.**
If `τ < ∞` almost surely and `f` is integrable for the law of the future path, the conditional
expectation of `f (θ_τ X)` given `𝓕_τ` is `∫ f dℙ_{X τ}`. -/
theorem condExp_stoppedValue_shift_iterate_markovChainLaw_of_ae_ne_top
    [IsFiniteMeasure ν] (hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => α)) τ)
    (hτ_fin : ∀ᵐ x ∂markovChainLaw ν κ, τ x ≠ ⊤) {f : (ℕ → α) → E}
    (hf : Integrable f (markovChainLaw ((markovChainLaw ν κ).map
      (stoppedValue (fun n x => x n) τ)) κ)) :
    (markovChainLaw ν κ)[fun x => f (stoppedValue (fun n => (shift α)^[n]) τ x) |
        hτ.measurableSpace]
      =ᵐ[markovChainLaw ν κ] fun x =>
        ∫ y, f y ∂markovChainLaw (Measure.dirac (stoppedValue (fun n x => x n) τ x)) κ := by
  have hS : (markovChainLaw ν κ).restrict {x | τ x ≠ ⊤} = markovChainLaw ν κ :=
    Measure.restrict_eq_self_of_ae_mem hτ_fin
  have hind : ∀ h : (ℕ → α) → E, {x | τ x ≠ ⊤}.indicator h =ᵐ[markovChainLaw ν κ] h := fun h =>
    hτ_fin.mono fun x hx => Set.indicator_of_mem hx h
  rw [← hS] at hf
  exact (condExp_congr_ae (hind _)).symm.trans
    ((condExp_stoppedValue_shift_iterate_markovChainLaw ν κ hτ hf).trans (hind _))

end CondExp

end MeasureTheory.Measure
