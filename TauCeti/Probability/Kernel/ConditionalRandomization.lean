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

Two random variables that are conditionally independent given a third can be represented by two
measurable functions of the conditioning variable, fed by separate independent uniform variables.
Keeping the uniforms separate, rather than coding the product conditional law with one uniform,
records the conditional independence in the functional representation.

This is the conditional randomization step used when a probabilistic factorization is converted
into separate latent variables. It combines Mathlib's factorization of a conditionally independent
joint law into a product of conditional distributions with measurable randomization of the two
kernels.

## Main result

* `ProbabilityTheory.CondIndepFun.exists_independent_coding` — conditionally independent random
  variables are generated from separate independent uniform variables given the conditioning
  variable.

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

end ProbabilityTheory

end

end
