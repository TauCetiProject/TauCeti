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

Two random variables that are conditionally independent given a third can be represented by two
measurable functions of the conditioning variable, fed by separate independent uniform variables.
Keeping the uniforms separate, rather than coding the product conditional law with one uniform,
records the conditional independence in the functional representation.

This is the conditional randomization step used when a probabilistic factorization is converted
into separate latent variables. It combines Mathlib's factorization of a conditionally independent
joint law into a product of conditional distributions with measurable randomization of the two
kernels.

Conversely, codings of two conditionally independent variables obtained separately, each jointly
with the conditioning variable, can be fed with independent noises to realize the joint law of all
three.

## Main results

* `ProbabilityTheory.CondIndepFun.exists_independent_coding` — conditionally independent random
  variables are generated from separate independent uniform variables given the conditioning
  variable.
* `ProbabilityTheory.CondIndepFun.map_prod_prod_eq_of_map_prod_eq` — given codings of the two
  variables, independent noises realize their joint law with the conditioning variable.

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

end ProbabilityTheory

end

end
