/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.Generator
public import TauCeti.Analysis.Semigroups.Generation.LumerPhillips
import TauCeti.Analysis.Semigroups.Dissipative.Duality
import TauCeti.MeasureTheory.Function.Lp.Duality

/-!
# The Laplacian is m-dissipative on `Lᵖ`

Let `E` be a finite-dimensional real inner product space, `F` a real Banach space and
`1 ≤ p < ∞`. The distributional Laplacian `Δ` on `Lᵖ(E; F)`, with domain `{f ∈ Lᵖ : Δf ∈ Lᵖ}`
(`TauCeti.weakLaplacianLp`), is the generator of the heat semigroup
(`TauCeti.generator_heatSemigroup_eq_weakLaplacianLp`). This file records what this says about
`Δ` from the point of view of the Lumer–Phillips theorem.

* `Δ` is densely defined (`TauCeti.dense_domain_weakLaplacianLp`) and **m-dissipative**
  (`TauCeti.isMDissipative_weakLaplacianLp`): `λ ‖u‖ ≤ ‖λ u - Δu‖` for `λ > 0` and `u` in the
  domain, and `λ - Δ` maps the domain onto `Lᵖ`.
* The contraction semigroup that the Lumer–Phillips theorem builds from `Δ`, the limit of the
  exponentials of the Yosida approximations, is the heat semigroup
  (`TauCeti.yosidaLimitSemigroup_weakLaplacianLp_eq_heatSemigroup`).
* For functions with values in a real inner product space, dissipativity takes its classical
  integral form: every `u` in the domain satisfies

  `∫ ‖u‖ ^ (p - 2) ⟪u, Δu⟫ ≤ 0`

  (`TauCeti.integral_norm_rpow_sub_two_mul_inner_weakLaplacianLp_nonpos`), where
  `‖u‖ ^ (p - 2) u` vanishes where `u` does. For real-valued `u` this is `∫ |u| ^ (p - 2) u Δu ≤ 0`;
  for `p = 2` it is `∫ u Δu ≤ 0`, the nonnegativity of `-Δ`, and for `p = 1` it is
  `∫ sign(u) Δu ≤ 0`. Integration against `‖u‖ ^ (p - 2) u`, scaled by `‖u‖_p ^ (2 - p)`, is an
  element of the duality set of `u` in `Lᵖ`
  (`MeasureTheory.Lp.exists_mem_dualitySet_apply_eq_integral`; for `1 < p < ∞` the only one), and
  the generator of a contraction semigroup is nonpositive against every element of the duality set
  (`TauCeti.Semigroups.ContractionSemigroup.apply_generator_nonpos_of_mem_dualitySet`).

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Example II.3.26 and Theorem II.3.15 (dissipativity on `Lᵖ` and the Lumer–Phillips theorem).
* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Chapter 7, §7.3 (the Laplacian is m-dissipative on `Lᵖ`).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Semigroups

open scoped ENNReal InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The domain `{f ∈ Lᵖ : Δf ∈ Lᵖ}` of the distributional Laplacian is dense in `Lᵖ` for
`1 ≤ p < ∞`. -/
theorem dense_domain_weakLaplacianLp (hp : p ≠ ∞) :
    Dense ((weakLaplacianLp E F p).domain : Set (Lp F p (volume : Measure E))) := by
  rw [← generator_heatSemigroup_eq_weakLaplacianLp hp,
    StronglyContinuousSemigroup.generator_domain]
  exact (heatSemigroup hp).toStronglyContinuousSemigroup.dense_domain

/-- **The Laplacian is m-dissipative on `Lᵖ`**, `1 ≤ p < ∞`: `λ ‖u‖ ≤ ‖λ u - Δu‖` for every
`λ > 0` and every `u ∈ Lᵖ` with `Δu ∈ Lᵖ`, and `λ - Δ` maps this domain onto `Lᵖ`. -/
theorem isMDissipative_weakLaplacianLp (hp : p ≠ ∞) :
    IsMDissipative (weakLaplacianLp E F p) :=
  generator_heatSemigroup_eq_weakLaplacianLp (E := E) (F := F) hp ▸
    (heatSemigroup hp).isMDissipative_generator

/-- **The Lumer–Phillips semigroup of the Laplacian is the heat semigroup.** The contraction
semigroup on `Lᵖ` that the Lumer–Phillips theorem builds from the densely defined m-dissipative
Laplacian, the limit of the exponentials of its Yosida approximations, is the heat semigroup
`e^{tΔ}`. -/
theorem yosidaLimitSemigroup_weakLaplacianLp_eq_heatSemigroup (hp : p ≠ ∞) :
    (isMDissipative_weakLaplacianLp (E := E) (F := F) hp).yosidaLimitSemigroup
      (dense_domain_weakLaplacianLp hp) = heatSemigroup hp :=
  ContractionSemigroup.eq_of_generator_eq
    (((isMDissipative_weakLaplacianLp (E := E) (F := F) hp).yosidaLimitSemigroup_generator
      (dense_domain_weakLaplacianLp hp)).trans (generator_heatSemigroup_eq_weakLaplacianLp hp).symm)

/-- **Dissipativity of the Laplacian on `Lᵖ` in integral form.** For `1 ≤ p < ∞`, every `u ∈ Lᵖ`
with values in a real inner product space whose distributional Laplacian lies in `Lᵖ` satisfies
`∫ ‖u‖ ^ (p - 2) ⟪u, Δu⟫ ≤ 0`. Here `‖u‖ ^ (p - 2) u` vanishes where `u` does; for real-valued `u`
this is `∫ |u| ^ (p - 2) u Δu ≤ 0`, which for `p = 2` is `∫ u Δu ≤ 0` and for `p = 1` is
`∫ sign(u) Δu ≤ 0`. -/
theorem integral_norm_rpow_sub_two_mul_inner_weakLaplacianLp_nonpos {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (hp : p ≠ ∞)
    (u : (weakLaplacianLp E H p).domain) :
    ∫ x, ‖(u : Lp H p (volume : Measure E)) x‖ ^ (p.toReal - 2) *
      ⟪(u : Lp H p (volume : Measure E)) x, weakLaplacianLp E H p u x⟫_ℝ ≤ 0 := by
  obtain ⟨f, hf, hfv⟩ :=
    Lp.exists_mem_dualitySet_apply_eq_integral ℝ hp (u : Lp H p (volume : Measure E))
  -- The generator of the heat semigroup is nonpositive against the duality set.
  have hA : f (weakLaplacianLp E H p u) ≤ 0 :=
    (generator_heatSemigroup_eq_weakLaplacianLp (E := E) (F := H) hp ▸
      fun x hx ↦ (heatSemigroup hp).apply_generator_nonpos_of_mem_dualitySet x hx :
      ∀ x : (weakLaplacianLp E H p).domain, f ∈ dualitySet ℝ (x : Lp H p (volume : Measure E)) →
        f (weakLaplacianLp E H p x) ≤ 0) u hf
  simp only [hfv, RCLike.ofReal_real_eq_id, id_eq, real_inner_smul_left] at hA
  rcases eq_or_ne (u : Lp H p (volume : Measure E)) 0 with hu | hu
  · simp [hu]
  · exact nonpos_of_mul_nonpos_right hA (by positivity)

end TauCeti
