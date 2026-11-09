/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.UniformContinuous.Semigroup
public import TauCeti.Analysis.Semigroups.Generator.Basic

/-!
# The Laplacian as the heat generator in the supremum norm

A bounded uniformly continuous `C²` function with bounded first and second derivatives and
uniformly continuous Laplacian belongs to the domain of the heat generator on bounded uniformly
continuous functions. The generator sends it to its Laplacian, with Mathlib's sign convention
`∂ₜu = Δu`.

`heatSemigroupBUC_sub_eq_integral` is Duhamel's identity in the Banach space of bounded uniformly
continuous functions. Strong continuity applied to the Laplacian gives convergence of the time
difference quotients in supremum norm. No compact support is required, and this file does not
characterize the full generator domain.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Chapter II, 2.12 (the diffusion semigroup).
* L. C. Evans, *Partial Differential Equations*, Sections 2.3.1 and 7.4.
-/

public section

noncomputable section

namespace TauCeti

open BoundedContinuousFunction Filter InnerProductSpace Laplacian MeasureTheory Semigroups Set
  Topology

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f g : uniformContinuousSubmodule ℝ E F} {M₁ M₂ : ℝ}

/-- **Duhamel's identity in supremum norm.** For bounded uniformly continuous `C²` data `f`
with bounded first and second derivatives and bounded uniformly continuous Laplacian `g`,
`e^{tΔ} f - f = ∫₀ᵗ e^{sΔ} g ds` as a Banach-valued integral. -/
theorem heatSemigroupBUC_sub_eq_integral (hf : ContDiff ℝ 2 (f.val : E → F))
    (h₁ : ∀ y, ‖fderiv ℝ (f.val : E → F) y‖ ≤ M₁)
    (h₂ : ∀ y, ‖fderiv ℝ (fderiv ℝ (f.val : E → F)) y‖ ≤ M₂)
    (hg : Δ (f.val : E → F) = (g.val : E → F)) {t : ℝ} (ht : 0 < t) :
    (heatSemigroupBUC (E := E) (F := F)).realOperator t f - f =
      ∫ s in Ioc 0 t, (heatSemigroupBUC (E := E) (F := F)).realOperator s g := by
  let S := (heatSemigroupBUC (E := E) (F := F)).toStronglyContinuousSemigroup
  have hint : IntegrableOn (fun s ↦ S.realOperator s g) (Ioc 0 t) :=
    (S.continuous_realOperator_apply g).integrableOn_Ioc
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  let ev : (uniformContinuousSubmodule ℝ E F) →L[ℝ] F :=
    (evalCLM ℝ x).comp (uniformContinuousSubmodule ℝ E F).subtypeL
  have heval : ∀ (u : uniformContinuousSubmodule ℝ E F), ev u = u.val x := fun _ ↦ rfl
  have hcont : ∀ (u : E →ᵇ F), Continuous (fun s : ℝ ↦ heatCauchyPotential u s x) := fun u ↦
    (continuous_heatCauchyPotential u.continuous u.norm_coe_le_norm).comp
      (continuous_id.prodMk continuous_const)
  have hpoint : heatCauchyPotential f.val t x - f.val x =
      ∫ s in Ioc 0 t, heatCauchyPotential g.val s x := by
    rw [← intervalIntegral.integral_of_le ht.le]
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.le
      (hcont f.val).continuousOn (fun s hs ↦ ?_)
      ((hcont g.val).intervalIntegrable 0 t)
    · simpa only [heatCauchyPotential_zero] using hFTC.symm
    · simpa only [hg] using hasDerivAt_heatCauchyPotential hf f.val.norm_coe_le_norm h₁ h₂ hs.1 x
  calc
    _ = ev (S.realOperator t f - f) := (heval _).symm
    _ = heatCauchyPotential f.val t x - f.val x := by
      rw [map_sub, heval, heval]
      simp only [S, heatSemigroupBUC_realOperator, coe_heatCauchyPotentialBUC,
        heatCauchyPotentialBCF_apply]
    _ = ∫ s in Ioc 0 t, heatCauchyPotential g.val s x := hpoint
    _ = ev (∫ s in Ioc 0 t, S.realOperator s g) := by
      rw [← ev.integral_comp_comm hint]
      congr 1
      ext s
      rw [heval]
      simp only [S, heatSemigroupBUC_realOperator, coe_heatCauchyPotentialBUC,
        heatCauchyPotentialBCF_apply]
    _ = _ := heval _

/-- The time difference quotients of the heat orbit converge to the Laplacian in supremum norm
for bounded `C²` data with bounded first and second derivatives and uniformly continuous
Laplacian. -/
theorem tendsto_heatSemigroupBUC_sub (hf : ContDiff ℝ 2 (f.val : E → F))
    (h₁ : ∀ y, ‖fderiv ℝ (f.val : E → F) y‖ ≤ M₁)
    (h₂ : ∀ y, ‖fderiv ℝ (fderiv ℝ (f.val : E → F)) y‖ ≤ M₂)
    (hg : Δ (f.val : E → F) = (g.val : E → F)) :
    Tendsto (fun t ↦ (1 / t) • ((heatSemigroupBUC (E := E) (F := F)).realOperator t f - f))
      (𝓝[>] 0) (𝓝 g) :=
  (heatSemigroupBUC.tendsto_average_orbit_zero g).congr'
    (eventually_mem_nhdsWithin.mono fun t (ht : 0 < t) ↦ by
      dsimp only
      rw [heatSemigroupBUC_sub_eq_integral hf h₁ h₂ hg ht])

/-- Bounded uniformly continuous `C²` data with bounded first and second derivatives and
bounded uniformly continuous Laplacian lie in the domain of the heat generator. -/
theorem mem_domain_heatSemigroupBUC (hf : ContDiff ℝ 2 (f.val : E → F))
    (h₁ : ∀ y, ‖fderiv ℝ (f.val : E → F) y‖ ≤ M₁)
    (h₂ : ∀ y, ‖fderiv ℝ (fderiv ℝ (f.val : E → F)) y‖ ≤ M₂)
    (hg : Δ (f.val : E → F) = (g.val : E → F)) :
    f ∈ (heatSemigroupBUC (E := E) (F := F)).domain :=
  (heatSemigroupBUC.mem_domain_iff_tendsto f).2
    ⟨g, tendsto_heatSemigroupBUC_sub hf h₁ h₂ hg⟩

/-- **The heat generator is the Laplacian** on bounded uniformly continuous `C²` functions with
bounded first and second derivatives and bounded uniformly continuous Laplacian. -/
theorem generator_heatSemigroupBUC (hf : ContDiff ℝ 2 (f.val : E → F))
    (h₁ : ∀ y, ‖fderiv ℝ (f.val : E → F) y‖ ≤ M₁)
    (h₂ : ∀ y, ‖fderiv ℝ (fderiv ℝ (f.val : E → F)) y‖ ≤ M₂)
    (hg : Δ (f.val : E → F) = (g.val : E → F)) :
    (heatSemigroupBUC (E := E) (F := F)).generator ⟨f, by
      rw [StronglyContinuousSemigroup.generator_domain]
      exact mem_domain_heatSemigroupBUC hf h₁ h₂ hg⟩ = g :=
  heatSemigroupBUC.generator_eq_of_tendsto (mem_domain_heatSemigroupBUC hf h₁ h₂ hg)
    (tendsto_heatSemigroupBUC_sub hf h₁ h₂ hg)

end TauCeti
