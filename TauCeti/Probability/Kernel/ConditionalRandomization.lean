/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Kernel.Randomization
public import Mathlib.Probability.Independence.Conditional

/-!
# Randomizing conditionally independent variables

Conditionally independent random variables can be represented by measurable functions of the
conditioning variable, fed by separate independent noise variables. Keeping the noises separate,
rather than coding the product conditional law with one noise variable, records the conditional
independence in the functional representation. The construction is given both for a pair and for
an arbitrary finite family.

This is the conditional randomization step used when a probabilistic factorization is converted
into separate latent variables. It combines Mathlib's factorization of a conditionally independent
joint law into a product of conditional distributions with measurable randomization of the
coordinate kernels.

## Main result

* `ProbabilityTheory.CondIndepFun.exists_independent_coding` — conditionally independent random
  variables are generated from separate independent uniform variables given the conditioning
  variable.
* `ProbabilityTheory.iCondIndepFun.exists_independent_coding` — the finite-family version, with
  one independent uniform coordinate per family member.

## References

* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Lemma 4.22 and Theorem 8.5.
-/

public section

noncomputable section

namespace ProbabilityTheory

open MeasureTheory unitInterval

variable {Ω β γ δ : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace β]
  [MeasurableSpace γ] [MeasurableSpace δ]

/-- **Conditional independence as a functional representation.** If `X` and `Y` are conditionally
independent given `Z`, then their joint law with `Z` is obtained by keeping `Z` and applying two
measurable coding functions to separate independent uniform variables. In particular, the noises
used for `X` and `Y` are independent both of one another and of the original sample carrying `Z`.
-/
theorem CondIndepFun.exists_independent_coding
    [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace γ] [Nonempty γ]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → β} {Y : Ω → γ} {Z : Ω → δ}
    {hZ : Measurable Z}
    (h : CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le X Y μ)
    (hX : Measurable X) (hY : Measurable Y) :
    ∃ f : δ → I → β, ∃ g : δ → I → γ,
      Measurable (Function.uncurry f) ∧ Measurable (Function.uncurry g) ∧
        (μ.prod ((volume : Measure I).prod (volume : Measure I))).map
            (fun p => (Z p.1, f (Z p.1) p.2.1, g (Z p.1) p.2.2)) =
          μ.map fun ω => (Z ω, X ω, Y ω) := by
  let κX := condDistrib X Z μ
  let κY := condDistrib Y Z μ
  obtain ⟨f, hf, hf_map⟩ := Kernel.exists_measurable_map_eq_unitInterval κX
  obtain ⟨g, hg, hg_map⟩ := Kernel.exists_measurable_map_eq_unitInterval κY
  refine ⟨f, g, hf, hg, ?_⟩
  let F : δ × (I × I) → δ × (β × γ) :=
    fun p => (p.1, f p.1 p.2.1, g p.1 p.2.2)
  let G : Ω × (I × I) → δ × (I × I) := Prod.map Z id
  have hF : Measurable F := by
    fun_prop
  have hG : Measurable G := hZ.prodMap measurable_id
  have hprod :
      (μ.map Z).prod ((volume : Measure I).prod (volume : Measure I)) =
        (μ.prod ((volume : Measure I).prod (volume : Measure I))).map G := by
    simpa only [G, Measure.map_id] using
      Measure.map_prod_map μ ((volume : Measure I).prod (volume : Measure I)) hZ measurable_id
  have hcode :
      ((μ.map Z).prod ((volume : Measure I).prod (volume : Measure I))).map F =
        μ.map fun ω => (Z ω, X ω, Y ω) := by
    refine (κX.map_prod_prod_eq_compProd_prod_of_map
      κY volume volume f g hf hg hf_map hg_map).trans ?_
    rw [Measure.compProd_eq_comp_prod]
    exact ((condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hX hY hZ).mp h).symm
  calc
    (μ.prod ((volume : Measure I).prod (volume : Measure I))).map
        (fun p => (Z p.1, f (Z p.1) p.2.1, g (Z p.1) p.2.2)) =
        ((μ.prod ((volume : Measure I).prod (volume : Measure I))).map G).map F := by
          rw [Measure.map_map hF hG]
          rfl
    _ = ((μ.map Z).prod ((volume : Measure I).prod (volume : Measure I))).map F := by
      rw [hprod]
    _ = μ.map fun ω => (Z ω, X ω, Y ω) := hcode

/-! ## Families -/

section Families

variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
  [∀ i, StandardBorelSpace (β i)] [∀ i, Nonempty (β i)]

/-- The conditional law of a finite conditionally independent family factors on measurable
rectangles into the product of its one-coordinate conditional laws. -/
theorem iCondIndepFun.condDistrib_pi_apply_ae_eq_prod
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ∀ i, Ω → β i} {Z : Ω → δ}
    (hZ : Measurable Z)
    (h : iCondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le X μ)
    (hX : ∀ i, Measurable (X i)) (s : ∀ i, Set (β i)) (hs : ∀ i, MeasurableSet (s i)) :
    ∀ᵐ ω ∂μ,
      condDistrib (fun ω i => X i ω) Z μ (Z ω) (Set.univ.pi s) =
        ∏ i, condDistrib (X i) Z μ (Z ω) (s i) := by
  classical
  have hfactor := (iCondIndepFun_iff_condExp_inter_preimage_eq_mul
    (m' := MeasurableSpace.comap Z inferInstance) (fun i => inferInstance) X hX).mp h
    Finset.univ (sets := s) (fun i _ => hs i)
  have hvec : Measurable (fun ω i => X i ω) := Measurable.of_eval hX
  have hpi : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  filter_upwards [hfactor,
    condDistrib_ae_eq_condExp hZ hvec hpi,
    ae_all_iff.2 (fun i => condDistrib_ae_eq_condExp hZ (hX i) (hs i))]
      with ω hfac hwhole hcoord
  have hpre : (fun ω i => X i ω) ⁻¹' Set.univ.pi s =
      ⋂ i ∈ (Finset.univ : Finset ι), X i ⁻¹' s i := by
    ext x
    simp [Set.mem_pi]
  rw [← Measure.pi_pi (μ := fun i => condDistrib (X i) Z μ (Z ω)) s,
    ← measureReal_eq_measureReal_iff]
  rw [hpre] at hwhole
  simp only [Finset.prod_apply] at hfac
  rw [hwhole, hfac]
  simp only [Measure.real, Measure.pi_pi]
  rw [ENNReal.toReal_prod]
  exact Finset.prod_congr rfl fun i _ => (hcoord i).symm

/-- **Conditional independence as a finite-family functional representation.** Suppose each
coordinate of a finite conditionally independent family is realized from the conditioning
variable and its own noise coordinate. Applying those realizations to a product noise preserves
the joint law of the conditioning variable and the whole family. -/
theorem iCondIndepFun.map_prod_pi_coding_eq
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ∀ i, Ω → β i} {Z : Ω → δ}
    (hZ : Measurable Z)
    (h : iCondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le X μ)
    (hX : ∀ i, Measurable (X i))
    {ξ : Type*} [MeasurableSpace ξ] {ρ : Measure ξ} [IsProbabilityMeasure ρ]
    (f : ∀ i, δ → ξ → β i) (hf : ∀ i, Measurable (Function.uncurry (f i)))
    (hmap : ∀ i z, ρ.map (f i z) = condDistrib (X i) Z μ z) :
    (μ.prod (Measure.pi fun _ : ι => ρ)).map
        (fun p => (Z p.1, fun i => f i (Z p.1) (p.2 i))) =
      μ.map fun ω => (Z ω, fun i => X i ω) := by
  classical
  let F : Ω × (ι → ξ) → δ × (∀ i, β i) :=
    fun p => (Z p.1, fun i => f i (Z p.1) (p.2 i))
  let G : Ω → δ × (∀ i, β i) := fun ω => (Z ω, fun i => X i ω)
  have hF : Measurable F := hZ.comp measurable_fst |>.prodMk <|
    Measurable.of_eval fun i => (hf i).comp
      ((hZ.comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hG : Measurable G := hZ.prodMk (Measurable.of_eval hX)
  let C : Set (Set (δ × (∀ i, β i))) := Set.image2 (· ×ˢ ·)
    {s : Set δ | MeasurableSet s}
    (Set.univ.pi '' Set.univ.pi fun i => {s : Set (β i) | MeasurableSet s})
  apply Measure.ext_of_generateFrom_of_cover_subset (S := C) (T := {Set.univ})
  · exact (generateFrom_eq_prod MeasurableSpace.generateFrom_measurableSet generateFrom_pi
      isCountablySpanning_measurableSet
      (IsCountablySpanning.pi fun _ => isCountablySpanning_measurableSet)).symm
  · exact IsPiSystem.prod MeasurableSpace.isPiSystem_measurableSet
      isPiSystem_pi
  · intro t ht
    simp only [Set.mem_singleton_iff] at ht
    subst t
    refine ⟨Set.univ, by simp, Set.univ, ?_, Set.univ_prod_univ⟩
    exact ⟨fun _ => Set.univ, by simp⟩
  · exact Set.countable_singleton _
  · simp
  · intro t ht
    simp only [Set.mem_singleton_iff] at ht
    subst t
    simp
  · rintro _ ⟨A, hA, B, ⟨s, hs, rfl⟩, rfl⟩
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi] at hA hs
    have hB : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
    have hvec : Measurable (fun ω i => X i ω) := Measurable.of_eval hX
    have hcode : Measurable (fun p : δ × (ι → ξ) =>
        (p.1, fun i => f i p.1 (p.2 i))) := by
      exact measurable_fst.prodMk <| Measurable.of_eval fun i =>
        (hf i).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
    have hprod :
        (μ.prod (Measure.pi fun _ : ι => ρ)).map (Prod.map Z id) =
          (μ.map Z).prod (Measure.pi fun _ : ι => ρ) := by
      simpa using
        (Measure.map_prod_map μ (Measure.pi fun _ : ι => ρ) hZ measurable_id).symm
    have hleft :
        (μ.prod (Measure.pi fun _ : ι => ρ)).map F (A ×ˢ Set.univ.pi s) =
          ∫⁻ z in A, ∏ i, condDistrib (X i) Z μ z (s i) ∂μ.map Z := by
      have hFcomp : F = (fun p : δ × (ι → ξ) =>
          (p.1, fun i => f i p.1 (p.2 i))) ∘ Prod.map Z id := rfl
      rw [hFcomp,
        ← Measure.map_map hcode (hZ.prodMap measurable_id), hprod,
        Measure.map_apply hcode (hA.prod hB), Measure.prod_apply (hcode (hA.prod hB))]
      rw [← lintegral_indicator hA]
      refine lintegral_congr fun z => ?_
      rw [Set.indicator]
      by_cases hz : z ∈ A
      · rw [ite_eq_left hz]
        have hfz : Measurable (fun (u : ι → ξ) i => f i z (u i)) :=
          Measurable.of_eval fun i => (hf i).of_uncurry_left.comp (measurable_pi_apply i)
        have : ∀ i, SigmaFinite (ρ.map (f i z)) := fun i => by
          rw [hmap i z]
          infer_instance
        have hpush : (Measure.pi fun _ : ι => ρ).map (fun u i => f i z (u i)) =
            Measure.pi fun i => condDistrib (X i) Z μ z := by
          rw [Measure.pi_map_pi fun i => (hf i).of_uncurry_left.aemeasurable]
          simp_rw [hmap]
        have hsection :
            Prod.mk z ⁻¹' (fun p : δ × (ι → ξ) =>
                (p.1, fun i => f i p.1 (p.2 i))) ⁻¹' (A ×ˢ Set.univ.pi s) =
              (fun u i => f i z (u i)) ⁻¹' Set.univ.pi s := by
          ext u
          simp [hz]
        rw [hsection, ← Measure.map_apply hfz hB, hpush, Measure.pi_pi]
      · rw [ite_eq_right hz]
        have hsection :
            Prod.mk z ⁻¹' (fun p : δ × (ι → ξ) =>
                (p.1, fun i => f i p.1 (p.2 i))) ⁻¹' (A ×ˢ Set.univ.pi s) = ∅ := by
          ext u
          simp [hz]
        rw [hsection]
        exact measure_empty
    have hright :
        μ.map G (A ×ˢ Set.univ.pi s) =
          ∫⁻ z in A, ∏ i, condDistrib (X i) Z μ z (s i) ∂μ.map Z := by
      have hdisintegrate :
          μ.map G = μ.map Z ⊗ₘ condDistrib (fun ω i => X i ω) Z μ :=
        (compProd_map_condDistrib hZ.aemeasurable hvec.aemeasurable).symm
      rw [hdisintegrate, Measure.compProd_apply (hA.prod hB)]
      have hfac := h.condDistrib_pi_apply_ae_eq_prod hZ hX s hs
      have hfac' : ∀ᵐ z ∂μ.map Z,
          condDistrib (fun ω i => X i ω) Z μ z (Set.univ.pi s) =
            ∏ i, condDistrib (X i) Z μ z (s i) := by
        rw [MeasureTheory.ae_map_iff hZ.aemeasurable]
        · exact hfac
        · exact measurableSet_eq_fun
            (Kernel.measurable_coe _ hB)
            (Finset.measurable_prod _ fun i _ => Kernel.measurable_coe _ (hs i))
      rw [← lintegral_indicator hA]
      refine lintegral_congr_ae ?_
      filter_upwards [hfac'] with z hz
      rw [Set.indicator]
      by_cases hzA : z ∈ A
      · rw [ite_eq_left hzA]
        simpa [hzA] using hz
      · rw [ite_eq_right hzA]
        simp [hzA]
    exact hleft.trans hright.symm

/-- **A finite conditionally independent family has a functional representation by independent
uniform noises.** Every coordinate is a jointly measurable function of the conditioning variable
and its own uniform coordinate, and the resulting family has the same joint law with the
conditioning variable as the original family. -/
theorem iCondIndepFun.exists_independent_coding
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ∀ i, Ω → β i} {Z : Ω → δ}
    (hZ : Measurable Z)
    (h : iCondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le X μ)
    (hX : ∀ i, Measurable (X i)) :
    ∃ f : ∀ i, δ → I → β i, (∀ i, Measurable (Function.uncurry (f i))) ∧
      (μ.prod (Measure.pi fun _ : ι => (volume : Measure I))).map
          (fun p => (Z p.1, fun i => f i (Z p.1) (p.2 i))) =
        μ.map fun ω => (Z ω, fun i => X i ω) := by
  choose f hf hmap using fun i =>
    Kernel.exists_measurable_map_eq_unitInterval (condDistrib (X i) Z μ)
  exact ⟨f, hf, h.map_prod_pi_coding_eq hZ hX f hf hmap⟩

end Families

end ProbabilityTheory

end

end
