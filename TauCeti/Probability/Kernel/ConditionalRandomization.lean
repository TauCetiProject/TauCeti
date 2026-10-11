/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Kernel.Randomization
public import Mathlib.Probability.Independence.Conditional
import TauCeti.MeasureTheory.Measure.Measurability

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
coordinate kernels. The joint-law identities hold for any finite base measure; when the base
measure is a probability measure, the product noise coordinates are independent of one another
and of the original sample.

Conversely, codings of conditionally independent variables obtained separately, each jointly
with the conditioning variable, can be fed with independent noises to realize their joint law with
the conditioning variable; this is done for a pair and for a finite family.

## Main results

* `ProbabilityTheory.CondIndepFun.exists_independent_coding` — conditionally independent random
  variables are generated from separate independent uniform variables given the conditioning
  variable.
* `ProbabilityTheory.CondIndepFun.map_prod_prod_eq_of_map_prod_eq` — given codings of the two
  variables, independent noises realize their joint law with the conditioning variable.
* `ProbabilityTheory.iCondIndepFun.exists_independent_coding` — the finite-family version, with
  one independent uniform coordinate per family member.
* `ProbabilityTheory.iCondIndepFun.map_prod_pi_eq_of_map_prod_eq` — given codings of each member
  of a finite family, independent noises realize its joint law with the conditioning variable.

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
measurable coding functions to separate uniform coordinates. When `μ` is a probability measure,
the noises are independent both of one another and of the original sample carrying `Z`.
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

/-- **Gluing conditionally independent codings.** Suppose `X` and `Y` are conditionally independent
given `Z`, and each is realized, jointly with `Z`, by a measurable function of `Z` and an
independent noise, with laws `ρ₁` and `ρ₂`. Then feeding independent noises into the two codings
realizes the joint law of `(Z, X, Y)`. -/
theorem CondIndepFun.map_prod_prod_eq_of_map_prod_eq
    [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace γ] [Nonempty γ]
    {ξ ζ : Type*} [MeasurableSpace ξ] [MeasurableSpace ζ]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → β} {Y : Ω → γ} {Z : Ω → δ}
    (hZ : Measurable Z)
    (h : CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le X Y μ)
    (hX : Measurable X) (hY : Measurable Y)
    {ρ₁ : Measure ξ} {ρ₂ : Measure ζ} [IsProbabilityMeasure ρ₁] [IsProbabilityMeasure ρ₂]
    {f : δ → ξ → β} {g : δ → ζ → γ}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (hfX : ((μ.map Z).prod ρ₁).map (fun p => (p.1, f p.1 p.2)) = μ.map fun ω => (Z ω, X ω))
    (hgY : ((μ.map Z).prod ρ₂).map (fun p => (p.1, g p.1 p.2)) = μ.map fun ω => (Z ω, Y ω)) :
    ((μ.map Z).prod (ρ₁.prod ρ₂)).map (fun p => (p.1, f p.1 p.2.1, g p.1 p.2.2)) =
      μ.map fun ω => (Z ω, X ω, Y ω) := by
  -- The randomizations realize the kernels `z ↦ ρ₁.map (f z)` and `z ↦ ρ₂.map (g z)`, which are
  -- therefore versions of the conditional distributions of `X` and `Y` given `Z`.
  let κ : Kernel δ β := ⟨fun z => ρ₁.map (f z),
    TauCeti.MeasureTheory.measurable_map_of_measurable_uncurry hf⟩
  let η : Kernel δ γ := ⟨fun z => ρ₂.map (g z),
    TauCeti.MeasureTheory.measurable_map_of_measurable_uncurry hg⟩
  have : IsMarkovKernel κ := ⟨fun z => inferInstanceAs (IsProbabilityMeasure (ρ₁.map (f z)))⟩
  have : IsMarkovKernel η := ⟨fun z => inferInstanceAs (IsProbabilityMeasure (ρ₂.map (g z)))⟩
  have hκ : condDistrib X Z μ =ᵐ[μ.map Z] κ :=
    condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hZ hX
      (hfX.symm.trans (κ.map_prod_eq_compProd_of_map ρ₁ f hf fun _ => rfl))
  have hη : condDistrib Y Z μ =ᵐ[μ.map Z] η :=
    condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hZ hY
      (hgY.symm.trans (η.map_prod_eq_compProd_of_map ρ₂ g hg fun _ => rfl))
  rw [κ.map_prod_prod_eq_compProd_prod_of_map η ρ₁ ρ₂ f g hf hg (fun _ => rfl) (fun _ => rfl),
    (condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hX hY hZ).mp h,
    ← Measure.compProd_eq_comp_prod]
  refine Measure.compProd_congr ?_
  filter_upwards [hκ, hη] with z hκz hηz
  rw [Kernel.prod_apply, Kernel.prod_apply, hκz, hηz]

/-! ## Families -/

section Families

variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
  [∀ i, StandardBorelSpace (β i)] [∀ i, Nonempty (β i)]

/-- The conditional law of a finite conditionally independent family factors on measurable
rectangles into the product of its one-coordinate conditional laws, almost everywhere under the
law of the conditioning variable. -/
theorem iCondIndepFun.condDistrib_apply_pi_ae_eq_prod
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ∀ i, Ω → β i} {Z : Ω → δ}
    (hZ : Measurable Z)
    (h : iCondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le X μ)
    (hX : ∀ i, Measurable (X i)) (s : ∀ i, Set (β i)) (hs : ∀ i, MeasurableSet (s i)) :
    ∀ᵐ z ∂μ.map Z,
      condDistrib (fun ω i => X i ω) Z μ z (Set.univ.pi s) =
        ∏ i, condDistrib (X i) Z μ z (s i) := by
  classical
  rw [ae_map_iff hZ.aemeasurable]
  swap
  · exact measurableSet_eq_fun
      (Kernel.measurable_coe _ (MeasurableSet.univ_pi hs))
      (Finset.measurable_prod _ fun i _ => Kernel.measurable_coe _ (hs i))
  have hfactor := (Kernel.iIndepFun_iff_measure_inter_preimage_eq_mul
    (κ := condExpKernel μ (MeasurableSpace.comap Z inferInstance))
    (fun i => inferInstance) X).mp h Finset.univ (sets := s) (fun i _ => hs i)
  have hvec : Measurable (fun ω i => X i ω) := Measurable.of_eval hX
  have hpi : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  filter_upwards [ae_of_ae_trim hZ.comap_le hfactor,
    condDistrib_apply_ae_eq_condExpKernel_map hvec hZ hpi,
    ae_all_iff.2 (fun i => condDistrib_apply_ae_eq_condExpKernel_map (hX i) hZ (hs i))]
      with ω hfac hwhole hcoord
  have hpre : (fun ω i => X i ω) ⁻¹' Set.univ.pi s =
      ⋂ i ∈ (Finset.univ : Finset ι), X i ⁻¹' s i := by
    ext x
    simp [Set.mem_pi]
  rw [hwhole, Kernel.map_apply' _ hvec _ hpi, hpre, hfac]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hcoord i, Kernel.map_apply' _ (hX i) _ (hs i)]

/-- **Conditional independence as a finite-family functional representation.** Suppose each
coordinate of a finite conditionally independent family is realized from the conditioning
variable and its own noise coordinate, almost everywhere under the law of the conditioning
variable. Applying those realizations to a product noise preserves the joint law of the
conditioning variable and the whole family. -/
theorem iCondIndepFun.map_prod_pi_eq_of_ae_map_eq
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ∀ i, Ω → β i} {Z : Ω → δ}
    (hZ : Measurable Z)
    (h : iCondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le X μ)
    (hX : ∀ i, Measurable (X i))
    {ξ : ι → Type*} [∀ i, MeasurableSpace (ξ i)] {ρ : ∀ i, Measure (ξ i)}
    [∀ i, IsProbabilityMeasure (ρ i)]
    (f : ∀ i, δ → ξ i → β i) (hf : ∀ i, Measurable (Function.uncurry (f i)))
    (hmap : ∀ i, ∀ᵐ z ∂μ.map Z, (ρ i).map (f i z) = condDistrib (X i) Z μ z) :
    (μ.prod (Measure.pi ρ)).map
        (fun p => (Z p.1, fun i => f i (Z p.1) (p.2 i))) =
      μ.map fun ω => (Z ω, fun i => X i ω) := by
  classical
  let F : δ → (∀ i, ξ i) → (∀ i, β i) := fun z u i => f i z (u i)
  have hF : Measurable (Function.uncurry F) :=
    TauCeti.Probability.measurable_pi_uncurry_prod hf
  let κ : Kernel δ (∀ i, β i) := ⟨fun z => (Measure.pi ρ).map (F z),
    TauCeti.MeasureTheory.measurable_map_of_measurable_uncurry hF⟩
  have : IsMarkovKernel κ :=
    ⟨fun z => inferInstanceAs (IsProbabilityMeasure ((Measure.pi ρ).map (F z)))⟩
  have hcode : Measurable (fun p : δ × (∀ i, ξ i) => (p.1, F p.1 p.2)) :=
    measurable_fst.prodMk hF
  have hprod : (μ.prod (Measure.pi ρ)).map (Prod.map Z id) =
      (μ.map Z).prod (Measure.pi ρ) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map μ (Measure.pi ρ) hZ measurable_id).symm
  have hcomp : (fun p : Ω × (∀ i, ξ i) => (Z p.1, fun i => f i (Z p.1) (p.2 i))) =
      (fun p : δ × (∀ i, ξ i) => (p.1, F p.1 p.2)) ∘ Prod.map Z id := rfl
  rw [hcomp, ← Measure.map_map hcode (hZ.prodMap measurable_id), hprod,
    κ.map_prod_eq_compProd_of_map (Measure.pi ρ) F hF (fun _ => rfl),
    ← compProd_map_condDistrib hZ.aemeasurable (Measurable.of_eval hX).aemeasurable]
  -- It suffices to compare the two composition-products on base sets times coordinate rectangles.
  let C : Set (Set (δ × (∀ i, β i))) := Set.image2 (· ×ˢ ·)
    {s : Set δ | MeasurableSet s}
    (Set.univ.pi '' Set.univ.pi fun i => {s : Set (β i) | MeasurableSet s})
  apply ext_of_generate_finite C
  · exact (generateFrom_eq_prod MeasurableSpace.generateFrom_measurableSet generateFrom_pi
      isCountablySpanning_measurableSet
      (IsCountablySpanning.pi fun _ => isCountablySpanning_measurableSet)).symm
  · exact IsPiSystem.prod MeasurableSpace.isPiSystem_measurableSet isPiSystem_pi
  · rintro _ ⟨A, hA, B, ⟨s, hs, rfl⟩, rfl⟩
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi] at hA hs
    have hB : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
    rw [Measure.compProd_apply_prod hA hB, Measure.compProd_apply_prod hA hB]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (ae_all_iff.2 hmap),
      ae_restrict_of_ae (h.condDistrib_apply_pi_ae_eq_prod hZ hX s hs)] with z hzmap hfac
    rw [hfac]
    have hpush : κ z = Measure.pi fun i => condDistrib (X i) Z μ z := by
      dsimp only [κ, Kernel.coe_mk, F]
      rw [Measure.pi_map_pi fun i => (hf i).of_uncurry_left.aemeasurable]
      simp_rw [hzmap]
    rw [hpush, Measure.pi_pi]
  · simp

/-- **Gluing conditionally independent codings of a finite family.** Suppose a finite family is
conditionally independent given `Z`, and each coordinate `X i` is realized, jointly with `Z`, by a
measurable function of `Z` and an independent noise with law `ρ i`. Then feeding independent
noises into the codings realizes the joint law of `Z` and the whole family. -/
theorem iCondIndepFun.map_prod_pi_eq_of_map_prod_eq
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ∀ i, Ω → β i} {Z : Ω → δ}
    (hZ : Measurable Z)
    (h : iCondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le X μ)
    (hX : ∀ i, Measurable (X i))
    {ξ : ι → Type*} [∀ i, MeasurableSpace (ξ i)] {ρ : ∀ i, Measure (ξ i)}
    [∀ i, IsProbabilityMeasure (ρ i)]
    {f : ∀ i, δ → ξ i → β i} (hf : ∀ i, Measurable (Function.uncurry (f i)))
    (hfX : ∀ i, ((μ.map Z).prod (ρ i)).map (fun p => (p.1, f i p.1 p.2)) =
      μ.map fun ω => (Z ω, X i ω)) :
    ((μ.map Z).prod (Measure.pi ρ)).map (fun p => (p.1, fun i => f i p.1 (p.2 i))) =
      μ.map fun ω => (Z ω, fun i => X i ω) := by
  -- Each randomization realizes the kernel `z ↦ (ρ i).map (f i z)`, which is therefore a version
  -- of the conditional distribution of `X i` given `Z`.
  have hmap (i : ι) : ∀ᵐ z ∂μ.map Z, (ρ i).map (f i z) = condDistrib (X i) Z μ z := by
    let κ : Kernel δ (β i) := ⟨fun z => (ρ i).map (f i z),
      TauCeti.MeasureTheory.measurable_map_of_measurable_uncurry (hf i)⟩
    have : IsMarkovKernel κ :=
      ⟨fun z => inferInstanceAs (IsProbabilityMeasure ((ρ i).map (f i z)))⟩
    filter_upwards [condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hZ (hX i)
      ((hfX i).symm.trans (κ.map_prod_eq_compProd_of_map (ρ i) (f i) (hf i) fun _ => rfl))]
      with z hz using hz.symm
  have hcode : Measurable (fun p : δ × (∀ i, ξ i) => (p.1, fun i => f i p.1 (p.2 i))) :=
    measurable_fst.prodMk (TauCeti.Probability.measurable_pi_uncurry_prod hf)
  have hprod : (μ.map Z).prod (Measure.pi ρ) = (μ.prod (Measure.pi ρ)).map (Prod.map Z id) := by
    simpa using Measure.map_prod_map μ (Measure.pi ρ) hZ measurable_id
  rw [hprod, Measure.map_map hcode (hZ.prodMap measurable_id)]
  exact h.map_prod_pi_eq_of_ae_map_eq hZ hX f hf hmap

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
  exact ⟨f, hf, h.map_prod_pi_eq_of_ae_map_eq hZ hX f hf fun i =>
    Filter.Eventually.of_forall (hmap i)⟩

end Families

end ProbabilityTheory

end

end
