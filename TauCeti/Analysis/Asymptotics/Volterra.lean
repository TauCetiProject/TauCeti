/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import TauCeti.Analysis.Asymptotics.Volterra.RightTail
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.ODE.Gronwall.Tail
import TauCeti.MeasureTheory.Group.Integral
import TauCeti.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Order.Interval.Set.OrdConnected
import TauCeti.Topology.Algebra.Group.Pointwise
import TauCeti.Topology.Order.Interval.Basic

/-!
# Volterra integral equations with separable kernel bounds

Let `I : Set ℝ` be an order-connected set (in particular, any finite or infinite interval `(a, b)`
with `-∞ ≤ a < b ≤ ∞`), let `K x v` be a kernel continuous on `{(x, v) | x ∈ I ∧ v ∈ I ∧ x ≤ v}`
with a separable bound `‖K x v‖ ≤ P x * Q v`, where `P, Q ≥ 0` are continuous on `I`, and let `J`,
`ψ` be continuous on `I` such that for every `x ∈ I` the tail integrals

* `Φ x = ∫ v in I ∩ Ioi x, Q v * ‖J v‖` and
* `Ψ x = ∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖`

converge. Then the Volterra integral equation

  `h x = ∫ v in I ∩ Ioi x, K x v • (J v + ψ v • h v)`

has a unique continuous solution `h` on `I` satisfying `h = O(P)` towards the right endpoint of
`I`, and it obeys the bound `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` for every `x ∈ I`.

When `P` is a constant `P₀ ≥ 0` and `‖ψ v‖ ≤ ‖J v‖` on `I` (for instance `ψ = J` when `E = 𝕜`),
the solution obeys the sharper bound `‖h x‖ ≤ exp (P₀ * Φ x) - 1`. (A dual form on `(a, ∞)` with
`‖J‖ ≤ ‖ψ‖` and bound `exp (P₀ * ∫ Q * ‖ψ‖) - 1` is also provided for continuous and bounded
solutions.)

When `I` is open, `K x x = 0`, and `∂K/∂x (x, v) = K' x v` exists for `x < v`, extends
continuously to `x ≤ v`, and satisfies `‖K' x v‖ ≤ P₁ x * Q v` for a continuous `P₁ ≥ 0`, every
such solution is `C¹` on `I` with derivative `h' x = ∫ v in I ∩ Ioi x, K' x v • (J v + ψ v • h v)`,
satisfying `‖h' x‖ ≤ P₁ x * Φ x * exp (Ψ x)` and, in the constant-`P₀` case with `‖ψ‖ ≤ ‖J‖`,
`P₀ * ‖h' x‖ ≤ P₁ x * (exp (P₀ * Φ x) - 1)`.

All of these results also hold for the mirrored left-tail equation
`h x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h v)`, obtained by reflecting `x ↦ -x`.
Specializing any right-tail theorem to a half-line `Ioi a` is immediate using
`ordConnected_Ioi`, `Ioi_subset_Ioi`, and `Filter.map_val_Ioi_atTop`. On `(a, ∞)`, ray bounds and
measurability-only uniqueness results also hold via Grönwall's inequality on a ray
(`TauCeti.le_mul_exp_integral_Ioi_of_le_mul_add_integral_Ioi`).

This formalizes Olver's theorem on Volterra integral equations (Chapter 6, Theorem 10.1), which
underlies the existence, uniqueness, and error-bound theorems for the Liouville–Green
approximation and for linear differential equations at an irregular singularity of rank one
(DLMF §§2.7, 2.8).

The kernel `K` and coefficient `ψ` take values in any normed field `𝕜`, and the forcing `J` and
unknown `h` in any real normed space which is also a normed `𝕜`-space (with completeness assumed
only for existence, and `[NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 E]` only for differentiability).

## Main results

Right-tail Volterra equation on an order-connected set `I ⊆ ℝ`:

* `TauCeti.exists_volterra_solution_on`: existence of a continuous solution with the bound
  `‖h x‖ ≤ P x * Φ x * exp (Ψ x)`.
* `TauCeti.exists_volterra_solution`: specialization to a half-line `(a, ∞)`
  (Olver, Chapter 6, Theorem 10.1).
* `TauCeti.isBigO_of_norm_le_volterra_bound_on`: any function satisfying the Volterra bound is
  `O(P)` towards the right endpoint of `I`.
* `TauCeti.norm_volterra_solution_le_on`: every continuous solution with `h = O(P)` satisfies
  `‖h x‖ ≤ P x * Φ x * exp (Ψ x)`.
* `TauCeti.volterra_solution_eqOn`: uniqueness among continuous solutions with `h = O(P)`.
* `TauCeti.norm_volterra_solution_le_exp_sub_one_on`: sharper bound
  `‖h x‖ ≤ exp (P₀ * Φ x) - 1` for constant `P₀` and `‖ψ‖ ≤ ‖J‖`.
* `TauCeti.hasDerivAt_volterra_solution_on`, `TauCeti.contDiffOn_volterra_solution_on`:
  `C¹` regularity and derivative integral formula on an open interval `I`.
* `TauCeti.norm_deriv_volterra_solution_le_on`,
  `TauCeti.mul_norm_deriv_volterra_solution_le_exp_sub_one_on`: general and sharper derivative
  bounds.

Left-tail Volterra equation (`I ∩ Iio x`), proved by reflection `x ↦ -x`:

* `TauCeti.exists_volterra_solution_Iio_on`, `TauCeti.isBigO_of_norm_le_volterra_bound_Iio_on`,
  `TauCeti.norm_volterra_solution_Iio_le_on`, `TauCeti.volterra_solution_Iio_eqOn`,
  `TauCeti.norm_volterra_solution_Iio_le_exp_sub_one_on`,
  `TauCeti.hasDerivAt_volterra_solution_Iio_on`, `TauCeti.contDiffOn_volterra_solution_Iio_on`,
  `TauCeti.norm_deriv_volterra_solution_Iio_le_on`,
  `TauCeti.mul_norm_deriv_volterra_solution_Iio_le_exp_sub_one_on`.

Half-line `(a, ∞)` specializations, ray bounds, and measurable-data uniqueness:

* `TauCeti.volterra_solution_unique`, `TauCeti.norm_volterra_solution_le`,
  `TauCeti.existsUnique_volterra_solution`: uniqueness and existence-and-uniqueness on `(a, ∞)`.
* `TauCeti.norm_volterra_solution_le_exp_sub_one`, `TauCeti.exists_volterra_solution_exp_sub_one`:
  sharper bound and existence on `(a, ∞)` for `‖J‖ ≤ ‖ψ‖`.
* `TauCeti.norm_volterra_solution_le_of_isBigO_principal_Ici`,
  `TauCeti.norm_volterra_solution_le_exp_sub_one_of_isBigO_principal_Ici`: ray bounds without
  continuity or measurability.
* `TauCeti.volterra_solution_unique_of_integrableOn`,
  `TauCeti.volterra_solution_unique_of_aestronglyMeasurable` (via
  `TauCeti.integrableOn_volterra_of_isBigO`): uniqueness on `(a, ∞)` for integrable/measurable data.
* `TauCeti.hasDerivAt_volterra_solution`, `TauCeti.contDiffOn_volterra_solution`,
  `TauCeti.norm_deriv_volterra_solution_le`: half-line specializations of `C¹` regularity and
  derivative bounds.

The discrete analogue is `TauCeti.existsUnique_discrete_volterra_solution`.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 6, §10.
* NIST Digital Library of Mathematical Functions, §2.7(iii), <https://dlmf.nist.gov/2.7.iii>.
-/

public section

open Asymptotics Filter Set MeasureTheory Function
open scoped Nat Pointwise Topology

namespace TauCeti

/-! ### Left-tail Volterra integral equations (`I ∩ Iio x`)

Every right-tail theorem above transfers to the mirrored left-tail equation
`h x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h v)` via the reflection `x ↦ -x`. -/

section LeftTail

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] {I : Set ℝ} {K : ℝ → ℝ → 𝕜} {J : ℝ → E} {ψ : ℝ → 𝕜} {P Q : ℝ → ℝ}

private lemma volterra_eq_comp_neg {h : ℝ → E}
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h v)) :
    ∀ x ∈ -I, h (-x) = ∫ v in -I ∩ Ioi x, K (-x) (-v) • (J (-v) + ψ (-v) • h (-v)) :=
  fun x hx ↦ (heq (-x) hx).trans
    (setIntegral_comp_neg_inter_Ioi (fun v ↦ K (-x) v • (J v + ψ v • h v)) I x).symm

/-- **Left-tail Volterra integral equations, existence on an interval.** Mirrored analogue of
`TauCeti.exists_volterra_solution_on` for `h x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h v)`. -/
theorem exists_volterra_solution_Iio_on [CompleteSpace E] (hI : I.OrdConnected)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.2 ≤ p.1})
    (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I)
    (hP : ContinuousOn P I) (hQ : ContinuousOn Q I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, v ≤ x → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Iio x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Iio x)) :
    ∃ h : ℝ → E, ContinuousOn h I ∧
      (∀ x ∈ I, h x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h v)) ∧
      ∀ x ∈ I, ‖h x‖ ≤ P x * (∫ v in I ∩ Iio x, Q v * ‖J v‖) *
        Real.exp (∫ v in I ∩ Iio x, P v * Q v * ‖ψ v‖) := by
  obtain ⟨g, hgcont, hgeq, hgle⟩ := exists_volterra_solution_on (I := -I)
    (K := fun x v ↦ K (-x) (-v)) hI.neg hK.uncurry_comp_neg
    hJ.comp_neg hψ.comp_neg hP.comp_neg hQ.comp_neg
    (fun _ hx ↦ hP0 _ hx) (fun _ hx ↦ hQ0 _ hx)
    (fun _ hx _ hv hxv ↦ hKle _ hx _ hv (neg_le_neg hxv))
    (fun x hx ↦ (hΦ (-x) hx).comp_neg_inter_Ioi)
    (fun x hx ↦ (hΨ (-x) hx).comp_neg_inter_Ioi)
  refine ⟨fun x ↦ g (-x), neg_neg I ▸ hgcont.comp_neg, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have hx' := hgeq (-x) (by simpa using hx)
    simp only [neg_neg] at hx'
    exact hx'.trans (by simpa using
      setIntegral_comp_neg_inter_Ioi (fun v ↦ K x v • (J v + ψ v • g (-v))) I (-x))
  · simpa only [setIntegral_comp_neg_inter_Ioi (fun v ↦ Q v * ‖J v‖) I (-x),
      setIntegral_comp_neg_inter_Ioi (fun v ↦ P v * Q v * ‖ψ v‖) I (-x), neg_neg] using
      hgle (-x) (by simpa using hx)

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
/-- Any function satisfying the left-tail Volterra bound on `I` is `O(P)` towards the left endpoint
of `I`. -/
theorem isBigO_of_norm_le_volterra_bound_Iio_on (hI : MeasurableSet I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Iio x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Iio x))
    {h : ℝ → E}
    (hh : ∀ x ∈ I, ‖h x‖ ≤ P x * (∫ v in I ∩ Iio x, Q v * ‖J v‖) *
      Real.exp (∫ v in I ∩ Iio x, P v * Q v * ‖ψ v‖)) :
    h =O[map ((↑) : I → ℝ) atBot] P := by
  rw [← Asymptotics.isBigO_comp_neg_map_atTop I]
  refine isBigO_of_norm_le_volterra_bound_on hI.neg (fun _ hx ↦ hP0 _ hx) (fun _ hx ↦ hQ0 _ hx)
    (fun x hx ↦ (hΦ (-x) hx).comp_neg_inter_Ioi)
    (fun x hx ↦ (hΨ (-x) hx).comp_neg_inter_Ioi) fun x hx ↦ ?_
  simpa only [setIntegral_comp_neg_inter_Ioi (fun v ↦ Q v * ‖J v‖) I x,
    setIntegral_comp_neg_inter_Ioi (fun v ↦ P v * Q v * ‖ψ v‖) I x] using hh (-x) hx

/-- **A priori left-tail Volterra bound.** Mirrored analogue of
`TauCeti.norm_volterra_solution_le_on`. -/
theorem norm_volterra_solution_Iio_le_on (hI : I.OrdConnected)
    (hψ : ContinuousOn ψ I) (hQ : ContinuousOn Q I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, v ≤ x → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Iio x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Iio x))
    {h : ℝ → E} (hh : ContinuousOn h I) (hO : h =O[map ((↑) : I → ℝ) atBot] P)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h v)) :
    ∀ x ∈ I, ‖h x‖ ≤ P x * (∫ v in I ∩ Iio x, Q v * ‖J v‖) *
      Real.exp (∫ v in I ∩ Iio x, P v * Q v * ‖ψ v‖) := by
  have hbound := norm_volterra_solution_le_on (I := -I) (K := fun x v ↦ K (-x) (-v))
    hI.neg hψ.comp_neg hQ.comp_neg (fun _ hx ↦ hP0 _ hx) (fun _ hx ↦ hQ0 _ hx)
    (fun _ hx _ hv hxv ↦ hKle _ hx _ hv (neg_le_neg hxv))
    (fun x hx ↦ (hΦ (-x) hx).comp_neg_inter_Ioi)
    (fun x hx ↦ (hΨ (-x) hx).comp_neg_inter_Ioi)
    hh.comp_neg ((Asymptotics.isBigO_comp_neg_map_atTop I).2 hO)
    (volterra_eq_comp_neg heq)
  intro x hx
  simpa only [setIntegral_comp_neg_inter_Ioi (fun v ↦ Q v * ‖J v‖) I (-x),
    setIntegral_comp_neg_inter_Ioi (fun v ↦ P v * Q v * ‖ψ v‖) I (-x), neg_neg] using
    hbound (-x) (by simpa using hx)

/-- **Left-tail Volterra integral equations, uniqueness.** Mirrored analogue of
`TauCeti.volterra_solution_eqOn`. -/
theorem volterra_solution_Iio_eqOn (hI : I.OrdConnected)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.2 ≤ p.1})
    (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I) (hQ : ContinuousOn Q I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, v ≤ x → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Iio x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Iio x))
    {h₁ h₂ : ℝ → E} (hh₁ : ContinuousOn h₁ I) (hh₂ : ContinuousOn h₂ I)
    (hO₁ : h₁ =O[map ((↑) : I → ℝ) atBot] P) (hO₂ : h₂ =O[map ((↑) : I → ℝ) atBot] P)
    (heq₁ : ∀ x ∈ I, h₁ x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h₁ v))
    (heq₂ : ∀ x ∈ I, h₂ x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h₂ v)) :
    EqOn h₁ h₂ I := by
  have heq := volterra_solution_eqOn (I := -I) (K := fun x v ↦ K (-x) (-v))
    hI.neg hK.uncurry_comp_neg hJ.comp_neg hψ.comp_neg hQ.comp_neg
    (fun _ hx ↦ hP0 _ hx) (fun _ hx ↦ hQ0 _ hx)
    (fun _ hx _ hv hxv ↦ hKle _ hx _ hv (neg_le_neg hxv))
    (fun x hx ↦ (hΦ (-x) hx).comp_neg_inter_Ioi)
    (fun x hx ↦ (hΨ (-x) hx).comp_neg_inter_Ioi)
    hh₁.comp_neg hh₂.comp_neg
    ((Asymptotics.isBigO_comp_neg_map_atTop I).2 hO₁)
    ((Asymptotics.isBigO_comp_neg_map_atTop I).2 hO₂)
    (volterra_eq_comp_neg heq₁) (volterra_eq_comp_neg heq₂)
  intro x hx
  simpa using heq (Set.neg_mem_neg.2 hx)

/-- **Sharper left-tail Volterra bound for constant `P₀` and `‖ψ‖ ≤ ‖J‖`.** Mirrored analogue of
`TauCeti.norm_volterra_solution_le_exp_sub_one_on`. -/
theorem norm_volterra_solution_Iio_le_exp_sub_one_on {P₀ : ℝ} (hI : I.OrdConnected)
    (hψ : ContinuousOn ψ I) (hQ : ContinuousOn Q I)
    (hP₀ : 0 ≤ P₀) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, v ≤ x → ‖K x v‖ ≤ P₀ * Q v)
    (hψJ : ∀ v ∈ I, ‖ψ v‖ ≤ ‖J v‖)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Iio x))
    {h : ℝ → E} (hh : ContinuousOn h I) (hO : h =O[map ((↑) : I → ℝ) atBot] fun _ ↦ P₀)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h v)) :
    ∀ x ∈ I, ‖h x‖ ≤ Real.exp (P₀ * ∫ v in I ∩ Iio x, Q v * ‖J v‖) - 1 := by
  have hbound := norm_volterra_solution_le_exp_sub_one_on (I := -I) (K := fun x v ↦ K (-x) (-v))
    hI.neg hψ.comp_neg hQ.comp_neg hP₀ (fun _ hx ↦ hQ0 _ hx)
    (fun _ hx _ hv hxv ↦ hKle _ hx _ hv (neg_le_neg hxv))
    (fun _ hv ↦ hψJ _ hv) (fun x hx ↦ (hΦ (-x) hx).comp_neg_inter_Ioi)
    hh.comp_neg ((Asymptotics.isBigO_comp_neg_map_atTop I).2 hO)
    (volterra_eq_comp_neg heq)
  intro x hx
  simpa only [setIntegral_comp_neg_inter_Ioi (fun v ↦ Q v * ‖J v‖) I (-x), neg_neg] using
    hbound (-x) (by simpa using hx)

section LeftDifferentiability

variable [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 E] {K' : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ}

/-- Shared reflection step proving both `HasDerivAt` and `ContDiffOn ℝ 1` for left-tail Volterra
solutions from the corresponding right-tail theorems on `-I`. -/
private lemma volterra_Iio_hasDerivAt_and_contDiffOn (hIopen : IsOpen I) (hI : I.OrdConnected)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.2 ≤ p.1})
    (hKdiag : ∀ x ∈ I, K x x = 0)
    (hKderiv : ∀ x ∈ I, ∀ v ∈ I, v < x → HasDerivAt (fun t ↦ K t v) (K' x v) x)
    (hK' : ContinuousOn (uncurry K') {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.2 ≤ p.1})
    (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I) (hQ : ContinuousOn Q I)
    (hP₁ : ContinuousOn P₁ I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, v ≤ x → ‖K x v‖ ≤ P x * Q v)
    (hK'le : ∀ x ∈ I, ∀ v ∈ I, v ≤ x → ‖K' x v‖ ≤ P₁ x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Iio x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Iio x))
    {h : ℝ → E} (hh : ContinuousOn h I) (hO : h =O[map ((↑) : I → ℝ) atBot] P)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h v)) :
    (∀ x ∈ I, HasDerivAt h (∫ v in I ∩ Iio x, K' x v • (J v + ψ v • h v)) x) ∧
      ContDiffOn ℝ 1 h I := by
  have hKderiv' : ∀ x ∈ -I, ∀ v ∈ -I, x < v →
      HasDerivAt (fun t ↦ K (-t) (-v)) (-K' (-x) (-v)) x := fun x hx v hv hxv ↦ by
    simpa only [Function.comp_def, neg_one_smul] using
      (hKderiv (-x) hx (-v) hv (neg_lt_neg hxv)).scomp x (hasDerivAt_neg x)
  have hKle' : ∀ x ∈ -I, ∀ v ∈ -I, x ≤ v → ‖K (-x) (-v)‖ ≤ P (-x) * Q (-v) :=
    fun _ hx _ hv hxv ↦ hKle _ hx _ hv (neg_le_neg hxv)
  have hK'le' : ∀ x ∈ -I, ∀ v ∈ -I, x ≤ v → ‖-K' (-x) (-v)‖ ≤ P₁ (-x) * Q (-v) :=
    fun _ hx _ hv hxv ↦ by simpa using hK'le _ hx _ hv (neg_le_neg hxv)
  have hΦ' : ∀ x ∈ -I, IntegrableOn (fun v ↦ Q (-v) * ‖J (-v)‖) (-I ∩ Ioi x) :=
    fun x hx ↦ (hΦ (-x) hx).comp_neg_inter_Ioi
  have hΨ' : ∀ x ∈ -I, IntegrableOn (fun v ↦ P (-v) * Q (-v) * ‖ψ (-v)‖) (-I ∩ Ioi x) :=
    fun x hx ↦ (hΨ (-x) hx).comp_neg_inter_Ioi
  have hO' : (fun x ↦ h (-x)) =O[map ((↑) : (-I : Set ℝ) → ℝ) atTop] (fun x ↦ P (-x)) :=
    (Asymptotics.isBigO_comp_neg_map_atTop I).2 hO
  have heq' := volterra_eq_comp_neg heq
  refine ⟨fun x hx ↦ ?_, ?_⟩
  · have hd := hasDerivAt_volterra_solution_on (I := -I) (K := fun x v ↦ K (-x) (-v))
      (K' := fun x v ↦ -K' (-x) (-v)) (P₁ := fun x ↦ P₁ (-x))
      hIopen.neg hI.neg hK.uncurry_comp_neg (fun _ hx ↦ hKdiag _ hx) hKderiv'
      hK'.uncurry_comp_neg.neg hJ.comp_neg hψ.comp_neg hQ.comp_neg hP₁.comp_neg
      (fun _ hx ↦ hP0 _ hx) (fun _ hx ↦ hQ0 _ hx) hKle' hK'le' hΦ' hΨ' hh.comp_neg hO' heq'
    have h1 := (hd (-x) (by simpa using hx)).scomp x (hasDerivAt_neg x)
    simpa only [Function.comp_def, neg_neg, neg_smul, integral_neg, one_smul,
      setIntegral_comp_neg_inter_Ioi (fun v ↦ K' x v • (J v + ψ v • h v)) I (-x)] using h1
  · have hg := contDiffOn_volterra_solution_on (I := -I) (K := fun x v ↦ K (-x) (-v))
      (K' := fun x v ↦ -K' (-x) (-v)) (P₁ := fun x ↦ P₁ (-x))
      hIopen.neg hI.neg hK.uncurry_comp_neg (fun _ hx ↦ hKdiag _ hx) hKderiv'
      hK'.uncurry_comp_neg.neg hJ.comp_neg hψ.comp_neg hQ.comp_neg hP₁.comp_neg
      (fun _ hx ↦ hP0 _ hx) (fun _ hx ↦ hQ0 _ hx) hKle' hK'le' hΦ' hΨ' hh.comp_neg hO' heq'
    simpa only [Function.comp_def, neg_neg] using
      hg.comp contDiff_neg.contDiffOn fun _ hx ↦ Set.neg_mem_neg.2 hx

/-- **Left-tail Volterra integral equations, derivative formula.** Mirrored analogue of
`TauCeti.hasDerivAt_volterra_solution_on`. -/
theorem hasDerivAt_volterra_solution_Iio_on (hIopen : IsOpen I) (hI : I.OrdConnected)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.2 ≤ p.1})
    (hKdiag : ∀ x ∈ I, K x x = 0)
    (hKderiv : ∀ x ∈ I, ∀ v ∈ I, v < x → HasDerivAt (fun t ↦ K t v) (K' x v) x)
    (hK' : ContinuousOn (uncurry K') {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.2 ≤ p.1})
    (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I) (hQ : ContinuousOn Q I)
    (hP₁ : ContinuousOn P₁ I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, v ≤ x → ‖K x v‖ ≤ P x * Q v)
    (hK'le : ∀ x ∈ I, ∀ v ∈ I, v ≤ x → ‖K' x v‖ ≤ P₁ x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Iio x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Iio x))
    {h : ℝ → E} (hh : ContinuousOn h I) (hO : h =O[map ((↑) : I → ℝ) atBot] P)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h v)) :
    ∀ x ∈ I, HasDerivAt h (∫ v in I ∩ Iio x, K' x v • (J v + ψ v • h v)) x :=
  (volterra_Iio_hasDerivAt_and_contDiffOn hIopen hI hK hKdiag hKderiv hK' hJ hψ hQ hP₁ hP0 hQ0
    hKle hK'le hΦ hΨ hh hO heq).1

/-- **Left-tail Volterra integral equations, `C¹` regularity.** Mirrored analogue of
`TauCeti.contDiffOn_volterra_solution_on`. -/
theorem contDiffOn_volterra_solution_Iio_on (hIopen : IsOpen I) (hI : I.OrdConnected)
    (hK : ContinuousOn (uncurry K) {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.2 ≤ p.1})
    (hKdiag : ∀ x ∈ I, K x x = 0)
    (hKderiv : ∀ x ∈ I, ∀ v ∈ I, v < x → HasDerivAt (fun t ↦ K t v) (K' x v) x)
    (hK' : ContinuousOn (uncurry K') {p | p.1 ∈ I ∧ p.2 ∈ I ∧ p.2 ≤ p.1})
    (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I) (hQ : ContinuousOn Q I)
    (hP₁ : ContinuousOn P₁ I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hKle : ∀ x ∈ I, ∀ v ∈ I, v ≤ x → ‖K x v‖ ≤ P x * Q v)
    (hK'le : ∀ x ∈ I, ∀ v ∈ I, v ≤ x → ‖K' x v‖ ≤ P₁ x * Q v)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Iio x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Iio x))
    {h : ℝ → E} (hh : ContinuousOn h I) (hO : h =O[map ((↑) : I → ℝ) atBot] P)
    (heq : ∀ x ∈ I, h x = ∫ v in I ∩ Iio x, K x v • (J v + ψ v • h v)) :
    ContDiffOn ℝ 1 h I :=
  (volterra_Iio_hasDerivAt_and_contDiffOn hIopen hI hK hKdiag hKderiv hK' hJ hψ hQ hP₁ hP0 hQ0
    hKle hK'le hΦ hΨ hh hO heq).2

end LeftDifferentiability

private lemma hasDerivAt_comp_neg_volterra {K' : ℝ → ℝ → 𝕜} {h : ℝ → E} {x : ℝ}
    (hderiv : HasDerivAt h (∫ v in I ∩ Iio x, K' x v • (J v + ψ v • h v)) x) :
    HasDerivAt (fun t ↦ h (-t))
      (∫ v in -I ∩ Ioi (-x), (-K' x (-v)) • (J (-v) + ψ (-v) • h (-v))) (-x) := by
  have hd0 : HasDerivAt h (∫ v in I ∩ Iio x, K' x v • (J v + ψ v • h v)) (- -x) := by
    simpa only [neg_neg] using hderiv
  simpa only [Function.comp_def, neg_smul, integral_neg, one_smul,
    setIntegral_comp_neg_inter_Ioi (fun v ↦ K' x v • (J v + ψ v • h v)) I (-x), neg_neg] using
    hd0.scomp (-x) (hasDerivAt_neg (-x))

/-- **Derivative bound for a left-tail Volterra solution.** Mirrored analogue of
`TauCeti.norm_deriv_volterra_solution_le_on`. -/
theorem norm_deriv_volterra_solution_Iio_le_on {K' : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ} (hI : MeasurableSet I)
    (hP0 : ∀ v ∈ I, 0 ≤ P v) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    {x : ℝ} (hP₁0 : 0 ≤ P₁ x)
    (hK'le : ∀ v ∈ I, v ≤ x → ‖K' x v‖ ≤ P₁ x * Q v)
    (hΦ : IntegrableOn (fun u ↦ Q u * ‖J u‖) (I ∩ Iio x))
    (hΨ : IntegrableOn (fun u ↦ P u * Q u * ‖ψ u‖) (I ∩ Iio x))
    {h : ℝ → E}
    (hhle : ∀ v ∈ I ∩ Iio x, ‖h v‖ ≤ P v * (∫ u in I ∩ Iio v, Q u * ‖J u‖) *
      Real.exp (∫ u in I ∩ Iio v, P u * Q u * ‖ψ u‖))
    (hderiv : HasDerivAt h (∫ v in I ∩ Iio x, K' x v • (J v + ψ v • h v)) x) :
    ‖deriv h x‖ ≤ P₁ x * (∫ v in I ∩ Iio x, Q v * ‖J v‖) *
      Real.exp (∫ v in I ∩ Iio x, P v * Q v * ‖ψ v‖) := by
  have hle := norm_deriv_volterra_solution_le_on (I := -I) (K' := fun t v ↦ -K' (-t) (-v))
    (P₁ := fun t ↦ P₁ (-t)) hI.neg (fun _ hv ↦ hP0 _ hv) (fun _ hv ↦ hQ0 _ hv)
    (x := -x) (by simpa using hP₁0) (fun v hv hxv ↦ by simpa using hK'le (-v) hv (neg_le.1 hxv))
    (MeasureTheory.IntegrableOn.comp_neg_inter_Ioi (x := -x) (by simpa using hΦ))
    (MeasureTheory.IntegrableOn.comp_neg_inter_Ioi (x := -x) (by simpa using hΨ))
    (fun v hv ↦ by
      have hv' : -v ∈ I ∩ Iio x := ⟨hv.1, neg_lt.1 hv.2⟩
      simpa only [setIntegral_comp_neg_inter_Ioi (fun u ↦ Q u * ‖J u‖) I v,
        setIntegral_comp_neg_inter_Ioi (fun u ↦ P u * Q u * ‖ψ u‖) I v] using hhle (-v) hv')
    (by simpa only [neg_neg] using hasDerivAt_comp_neg_volterra hderiv)
  simpa only [deriv_comp_neg, neg_neg, norm_neg,
    setIntegral_comp_neg_inter_Ioi (fun v ↦ Q v * ‖J v‖) I (-x),
    setIntegral_comp_neg_inter_Ioi (fun v ↦ P v * Q v * ‖ψ v‖) I (-x)] using hle

/-- **Sharper derivative bound for a left-tail Volterra solution with constant `P₀` and
`‖ψ‖ ≤ ‖J‖`.** Mirrored analogue of
`TauCeti.mul_norm_deriv_volterra_solution_le_exp_sub_one_on`. -/
theorem mul_norm_deriv_volterra_solution_Iio_le_exp_sub_one_on {K' : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ}
    {P₀ : ℝ} (hI : MeasurableSet I) (hP₀ : 0 ≤ P₀) (hQ0 : ∀ v ∈ I, 0 ≤ Q v)
    (hψJ : ∀ v ∈ I, ‖ψ v‖ ≤ ‖J v‖) {x : ℝ} (hP₁0 : 0 ≤ P₁ x)
    (hK'le : ∀ v ∈ I, v ≤ x → ‖K' x v‖ ≤ P₁ x * Q v)
    (hΦ : IntegrableOn (fun u ↦ Q u * ‖J u‖) (I ∩ Iio x))
    {h : ℝ → E}
    (hhle : ∀ v ∈ I ∩ Iio x, ‖h v‖ ≤ Real.exp (P₀ * ∫ u in I ∩ Iio v, Q u * ‖J u‖) - 1)
    (hderiv : HasDerivAt h (∫ v in I ∩ Iio x, K' x v • (J v + ψ v • h v)) x) :
    P₀ * ‖deriv h x‖ ≤ P₁ x * (Real.exp (P₀ * ∫ v in I ∩ Iio x, Q v * ‖J v‖) - 1) := by
  have hle := mul_norm_deriv_volterra_solution_le_exp_sub_one_on (I := -I)
    (K' := fun t v ↦ -K' (-t) (-v)) (P₁ := fun t ↦ P₁ (-t)) hI.neg hP₀
    (fun _ hv ↦ hQ0 _ hv) (fun _ hv ↦ hψJ _ hv) (x := -x) (by simpa using hP₁0)
    (fun v hv hxv ↦ by simpa using hK'le (-v) hv (neg_le.1 hxv))
    (MeasureTheory.IntegrableOn.comp_neg_inter_Ioi (x := -x) (by simpa using hΦ))
    (fun v hv ↦ by
      have hv' : -v ∈ I ∩ Iio x := ⟨hv.1, neg_lt.1 hv.2⟩
      simpa only [setIntegral_comp_neg_inter_Ioi (fun u ↦ Q u * ‖J u‖) I v] using hhle (-v) hv')
    (by simpa only [neg_neg] using hasDerivAt_comp_neg_volterra hderiv)
  simpa only [deriv_comp_neg, neg_neg, norm_neg,
    setIntegral_comp_neg_inter_Ioi (fun v ↦ Q v * ‖J v‖) I (-x)] using hle

end LeftTail

/-! ### Degenerate case `K = 0` -/

example {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace ℝ E] [CompleteSpace E] {I : Set ℝ} (hI : I.OrdConnected)
    {J : ℝ → E} {ψ : ℝ → 𝕜} {P Q : ℝ → ℝ}
    (hJ : ContinuousOn J I) (hψ : ContinuousOn ψ I) (hP : ContinuousOn P I) (hQ : ContinuousOn Q I)
    (hP0 : ∀ x ∈ I, 0 ≤ P x) (hQ0 : ∀ x ∈ I, 0 ≤ Q x)
    (hΦ : ∀ x ∈ I, IntegrableOn (fun v ↦ Q v * ‖J v‖) (I ∩ Ioi x))
    (hΨ : ∀ x ∈ I, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (I ∩ Ioi x)) :
    ∃ h : ℝ → E, EqOn h 0 I ∧
      ∀ x ∈ I, (0 : ℝ) ≤ P x * (∫ v in I ∩ Ioi x, Q v * ‖J v‖) *
        Real.exp (∫ v in I ∩ Ioi x, P v * Q v * ‖ψ v‖) := by
  have hKle : ∀ x ∈ I, ∀ v ∈ I, x ≤ v → ‖(0 : 𝕜)‖ ≤ P x * Q v := fun x hx v hv _ ↦ by
    simpa using mul_nonneg (hP0 x hx) (hQ0 v hv)
  obtain ⟨h, hcont, heq, hle⟩ := exists_volterra_solution_on (K := fun _ _ ↦ (0 : 𝕜)) hI
    continuousOn_const hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ
  have hzero : EqOn h 0 I := volterra_solution_eqOn (K := fun _ _ ↦ (0 : 𝕜)) hI
    continuousOn_const hJ hψ hQ hP0 hQ0 hKle hΦ hΨ hcont continuousOn_const
    (isBigO_of_norm_le_volterra_bound_on hI.measurableSet hP0 hQ0 hΦ hΨ hle)
    (Asymptotics.isBigO_zero P _) heq fun _ _ ↦ by simp
  exact ⟨h, hzero, fun x hx ↦ by simpa [hzero hx] using hle x hx⟩

section HalfLine

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] {a : ℝ} {K : ℝ → ℝ → 𝕜} {J : ℝ → E} {ψ : ℝ → 𝕜} {P Q : ℝ → ℝ}

omit [NormedSpace ℝ E] in
/-- The separable bound for `v ↦ K x v • y` on `[x, ∞)`. -/
private lemma norm_kernel_smul_Ioi_le (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    {x v : ℝ} (hx : a < x) (hv : x ≤ v) (y : E) : ‖K x v • y‖ ≤ P x * (Q v * ‖y‖) := by
  rw [norm_smul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hKle x v hx hv) (norm_nonneg _)

omit [NormedSpace ℝ E] in
/-- If `K x` and `F` are almost everywhere strongly measurable on `(x, ∞)`, and `‖F‖ ≤ B` there
with `Q * B` integrable on `(x, ∞)`, then `v ↦ K x v • F v` is integrable on `(x, ∞)`. -/
private lemma integrableOn_kernel_smul_of_le
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v) {F : ℝ → E} {B : ℝ → ℝ} {x : ℝ}
    (hx : a < x) (hKm : AEStronglyMeasurable (K x) (volume.restrict (Ioi x)))
    (hFm : AEStronglyMeasurable F (volume.restrict (Ioi x))) (hFB : ∀ v ∈ Ioi x, ‖F v‖ ≤ B v)
    (hB : IntegrableOn (fun v ↦ Q v * B v) (Ioi x)) :
    IntegrableOn (fun v ↦ K x v • F v) (Ioi x) := by
  refine Integrable.mono' (hB.const_mul (P x)) (hKm.smul hFm) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : x < v)
  refine (norm_kernel_smul_Ioi_le hKle hx hv.le _).trans ?_
  rw [← mul_assoc, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left (hFB v hv) ((norm_nonneg _).trans (hKle x v hx hv.le))

/-! ### Solutions on a ray

The bounds in this section concern a solution of the equation on a ray `[x, ∞)` only, which is
`O(P)` on that ray. They need no continuity, measurability or completeness: the error bound
comes from Grönwall's inequality on a ray,
`TauCeti.le_mul_exp_integral_Ioi_of_le_mul_add_integral_Ioi`. -/

section Ray

omit [NormedSpace ℝ E] in
/-- If `K x`, `J`, `ψ` and `h` are almost everywhere strongly measurable on `(x, ∞)` (with respect
to the restriction of the Lebesgue measure), for some `x > a` at which `Φ x` and `Ψ x` converge,
and `h` is `O(P)` on `[x, ∞)`, then the integrand `v ↦ K x v • (J v + ψ v • h v)` of the Volterra
equation is integrable on `(x, ∞)`. -/
theorem integrableOn_volterra_of_isBigO (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v) {x : ℝ} (hx : a < x)
    (hKm : AEStronglyMeasurable (K x) (volume.restrict (Ioi x)))
    (hJm : AEStronglyMeasurable J (volume.restrict (Ioi x)))
    (hψm : AEStronglyMeasurable ψ (volume.restrict (Ioi x)))
    (hΦ : IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) {h : ℝ → E}
    (hm : AEStronglyMeasurable h (volume.restrict (Ioi x))) (hh : h =O[𝓟 (Ici x)] P) :
    IntegrableOn (fun v ↦ K x v • (J v + ψ v • h v)) (Ioi x) := by
  obtain ⟨C, hC⟩ := (isBigO_principal_iff_of_nonneg fun v (hv : x ≤ v) ↦
    hP0 v (hx.trans_le hv)).1 hh
  refine integrableOn_kernel_smul_of_le (B := fun v ↦ ‖J v‖ + ‖ψ v‖ * (C * P v)) hKle hx hKm
    (hJm.add (hψm.smul hm))
    (fun v (hv : x < v) ↦ (norm_add_le _ _).trans (by rw [norm_smul]; gcongr; exact hC v hv.le))
    ?_
  refine (hΦ.add (hΨ.const_mul C)).congr_fun (fun v _ ↦ ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  ring

/-- **Volterra integral equations, bound on a ray.** Let `‖K x v‖ ≤ P x * Q v` for `a < x ≤ v`,
where `P ≥ 0` on `(a, ∞)`, and let `x > a` be such that `Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and
`Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖` converge. Then every solution of the Volterra equation
`h y = ∫ v in Ioi y, K y v • (J v + ψ v • h v)` on `[x, ∞)` that is `O(P)` on `[x, ∞)` satisfies
`‖h x‖ ≤ P x * Φ x * exp (Ψ x)` (the error bound of Olver, Chapter 6, Theorem 10.1). -/
theorem norm_volterra_solution_le_of_isBigO_principal_Ici (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v) {x : ℝ} (hx : a < x) {h : ℝ → E}
    (h_eq : ∀ y ∈ Ici x, h y = ∫ v in Ioi y, K y v • (J v + ψ v • h v))
    (hΦ : IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) (h_isBigO : h =O[𝓟 (Ici x)] P) :
    ‖h x‖ ≤ P x * (∫ v in Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖) := by
  rcases (hP0 x hx).eq_or_lt with hPx | hPx
  · -- if `P x = 0`, then `K x v = 0` for every `v ≥ x`, so `h x = 0`
    rw [← hPx, zero_mul, zero_mul, h_eq x self_mem_Ici]
    refine (norm_integral_le_of_norm_le (g := fun _ ↦ (0 : ℝ)) (integrable_zero _ _ _)
      ?_).trans_eq (by simp)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : x < v)
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right ((hKle x v hx hv.le).trans_eq (by rw [← hPx, zero_mul]))
      (norm_nonneg _)).trans_eq (zero_mul _)
  -- otherwise `Q ≥ 0` on `[x, ∞)`, and Grönwall's inequality applies to `‖h‖`
  have hQ0 : ∀ v ∈ Ici x, 0 ≤ Q v := fun v (hv : x ≤ v) ↦
    nonneg_of_mul_nonneg_right ((norm_nonneg _).trans (hKle x v hx hv)) hPx
  obtain ⟨C, hC⟩ := (isBigO_principal_iff_of_nonneg fun v (hv : x ≤ v) ↦
    hP0 v (hx.trans_le hv)).1 h_isBigO
  have hΨ' : IntegrableOn (fun v ↦ P v * (Q v * ‖ψ v‖)) (Ioi x) := by
    simpa only [mul_assoc] using hΨ
  simpa only [mul_assoc] using le_mul_exp_integral_Ioi_of_le_mul_add_integral_Ioi
    (u := fun y ↦ ‖h y‖)
    (A := ∫ v in Ioi x, Q v * ‖J v‖) hΨ' hC fun y (hy : x ≤ y) b hb hgb ↦ by
    have hya := hx.trans_le hy
    have hJy := hΦ.mono_set (Ioi_subset_Ioi hy)
    rw [h_eq y hy]
    calc ‖∫ v in Ioi y, K y v • (J v + ψ v • h v)‖
        ≤ ∫ v in Ioi y, P y * (Q v * ‖J v‖ + Q v * ‖ψ v‖ * b v) := by
          refine norm_integral_le_of_norm_le ((hJy.add hgb).const_mul (P y)) ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : y < v)
          have hQv := hQ0 v (hy.trans hv.le)
          refine (norm_kernel_smul_Ioi_le hKle hya hv.le _).trans ?_
          gcongr P y * ?_
          · exact hP0 y hya
          calc Q v * ‖J v + ψ v • h v‖ ≤ Q v * (‖J v‖ + ‖ψ v‖ * b v) := by
                gcongr
                exact (norm_add_le _ _).trans (by rw [norm_smul]; gcongr; exact hb v hv)
            _ = _ := by ring
      _ = P y * ((∫ v in Ioi y, Q v * ‖J v‖) + ∫ v in Ioi y, Q v * ‖ψ v‖ * b v) := by
          rw [integral_const_mul, integral_add hJy hgb]
      _ ≤ P y * ((∫ v in Ioi x, Q v * ‖J v‖) + ∫ v in Ioi y, Q v * ‖ψ v‖ * b v) := by
          refine mul_le_mul_of_nonneg_left (add_le_add_left ?_ _) (hP0 y hya)
          exact setIntegral_mono_set hΦ ((ae_restrict_iff' measurableSet_Ioi).2
            (ae_of_all _ fun v (hv : x < v) ↦ mul_nonneg (hQ0 v hv.le) (norm_nonneg _)))
            (Ioi_subset_Ioi hy).eventuallySubset

/-- **Volterra integral equations, uniqueness among solutions with integrable integrands.** Let
`‖K x v‖ ≤ P x * Q v` for `a < x ≤ v`, where `P ≥ 0` on `(a, ∞)`, and let
`Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖` converge for every `x > a`. Then two solutions `h₁`, `h₂`
of the Volterra equation `h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` on `(a, ∞)` whose
integrands are integrable on `(x, ∞)`, and which are `O(P)` on `[x, ∞)`, for every `x > a`, agree
on `(a, ∞)`. -/
theorem volterra_solution_unique_of_integrableOn (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) {h₁ h₂ : ℝ → E}
    (h₁_int : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ K x v • (J v + ψ v • h₁ v)) (Ioi x))
    (h₂_int : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ K x v • (J v + ψ v • h₂ v)) (Ioi x))
    (h₁_eq : ∀ x ∈ Ioi a, h₁ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₁ v))
    (h₂_eq : ∀ x ∈ Ioi a, h₂ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₂ v))
    (h₁_isBigO : ∀ x ∈ Ioi a, h₁ =O[𝓟 (Ici x)] P)
    (h₂_isBigO : ∀ x ∈ Ioi a, h₂ =O[𝓟 (Ici x)] P) :
    EqOn h₁ h₂ (Ioi a) := by
  intro x₀ (hx₀ : a < x₀)
  -- the difference solves the homogeneous equation
  have hd : ∀ y ∈ Ici x₀, (h₁ - h₂) y =
      ∫ v in Ioi y, K y v • ((0 : ℝ → E) v + ψ v • (h₁ - h₂) v) := fun y (hy : x₀ ≤ y) ↦ by
    have hya := hx₀.trans_le hy
    rw [Pi.sub_apply, h₁_eq y hya, h₂_eq y hya, ← integral_sub (h₁_int y hya) (h₂_int y hya)]
    refine integral_congr_ae (ae_of_all _ fun v ↦ ?_)
    simp only [Pi.sub_apply, Pi.zero_apply, zero_add, smul_sub, smul_add]
    abel
  -- so the bound with zero forcing gives `‖h₁ x₀ - h₂ x₀‖ ≤ 0`
  have hle := norm_volterra_solution_le_of_isBigO_principal_Ici hP0 hKle hx₀ hd (by simp)
    (hΨ x₀ hx₀) ((h₁_isBigO x₀ hx₀).sub (h₂_isBigO x₀ hx₀))
  simp only [Pi.zero_apply, norm_zero, mul_zero, integral_zero, zero_mul] at hle
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

/-- **Volterra integral equations, uniqueness among measurable solutions.** Let
`‖K x v‖ ≤ P x * Q v` for `a < x ≤ v`, where `P ≥ 0` on `(a, ∞)`, let `K x` be almost everywhere
strongly measurable on `(x, ∞)` for every `x > a` and `J`, `ψ` almost everywhere strongly
measurable on `(a, ∞)`, and let `Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and
`Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖` converge for every `x > a`. Then two solutions of the
Volterra equation `h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` that are almost everywhere
strongly measurable on `(a, ∞)` and `O(P)` on `[x, ∞)` for every
`x > a` agree on `(a, ∞)`. This is the uniqueness part of Olver, Chapter 6, Theorem 10.1, for
measurable rather than continuous data; compare `volterra_solution_unique`. -/
theorem volterra_solution_unique_of_aestronglyMeasurable (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hKm : ∀ x ∈ Ioi a, AEStronglyMeasurable (K x) (volume.restrict (Ioi x)))
    (hJm : AEStronglyMeasurable J (volume.restrict (Ioi a)))
    (hψm : AEStronglyMeasurable ψ (volume.restrict (Ioi a)))
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) {h₁ h₂ : ℝ → E}
    (h₁_meas : AEStronglyMeasurable h₁ (volume.restrict (Ioi a)))
    (h₂_meas : AEStronglyMeasurable h₂ (volume.restrict (Ioi a)))
    (h₁_eq : ∀ x ∈ Ioi a, h₁ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₁ v))
    (h₂_eq : ∀ x ∈ Ioi a, h₂ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₂ v))
    (h₁_isBigO : ∀ x ∈ Ioi a, h₁ =O[𝓟 (Ici x)] P)
    (h₂_isBigO : ∀ x ∈ Ioi a, h₂ =O[𝓟 (Ici x)] P) :
    EqOn h₁ h₂ (Ioi a) := by
  have hint {h : ℝ → E} (hm : AEStronglyMeasurable h (volume.restrict (Ioi a)))
      (hh : ∀ x ∈ Ioi a, h =O[𝓟 (Ici x)] P) (x : ℝ) (hx : x ∈ Ioi a) :
      IntegrableOn (fun v ↦ K x v • (J v + ψ v • h v)) (Ioi x) :=
    have hsub : Ioi x ⊆ Ioi a := Ioi_subset_Ioi (le_of_lt hx)
    integrableOn_volterra_of_isBigO hP0 hKle hx (hKm x hx) (hJm.mono_set hsub)
      (hψm.mono_set hsub) (hΦ x hx) (hΨ x hx) (hm.mono_set hsub) (hh x hx)
  exact volterra_solution_unique_of_integrableOn hP0 hKle hΨ (hint h₁_meas h₁_isBigO)
    (hint h₂_meas h₂_isBigO) h₁_eq h₂_eq h₁_isBigO h₂_isBigO

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
/-- A function satisfying the bound `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` of
`exists_volterra_solution` on `(a, ∞)`, where `Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and
`Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖`, is `O(P)` on `[x, ∞)` for every `x > a`. -/
theorem isBigO_principal_Ici_of_norm_le_volterra_bound (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x)
    (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) {h : ℝ → E}
    (hh : ∀ x ∈ Ioi a, ‖h x‖ ≤ P x * (∫ v in Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖)) :
    ∀ x ∈ Ioi a, h =O[𝓟 (Ici x)] P := fun x (hx : a < x) ↦
  (isBigO_principal_iff_of_nonneg fun v (hv : x ≤ v) ↦ hP0 v (hx.trans_le hv)).2
    ⟨(∫ u in Ioi x, Q u * ‖J u‖) * Real.exp (∫ u in Ioi x, P u * Q u * ‖ψ u‖),
      fun v (hv : x ≤ v) ↦ by
        have hva : a < v := hx.trans_le hv
        have hΦx : 0 ≤ ∫ u in Ioi x, Q u * ‖J u‖ := setIntegral_nonneg measurableSet_Ioi
          fun u hu ↦ mul_nonneg (hQ0 u (hx.trans hu)) (norm_nonneg _)
        have hΦle := antitoneOn_integral_Ioi (fun u hu ↦ mul_nonneg (hQ0 u hu) (norm_nonneg _))
          hΦ hx hva hv
        have hΨle := antitoneOn_integral_Ioi
          (fun u hu ↦ mul_nonneg (mul_nonneg (hP0 u hu) (hQ0 u hu)) (norm_nonneg _))
          hΨ hx hva hv
        have hPv := hP0 v hva
        calc ‖h v‖ ≤ P v * (∫ u in Ioi v, Q u * ‖J u‖) *
                Real.exp (∫ u in Ioi v, P u * Q u * ‖ψ u‖) := hh v hva
          _ ≤ P v * (∫ u in Ioi x, Q u * ‖J u‖) *
                Real.exp (∫ u in Ioi x, P u * Q u * ‖ψ u‖) := by gcongr
          _ = _ := by ring⟩

end Ray

section Uniqueness

/-- **Volterra integral equations, uniqueness.** Under the hypotheses of
`exists_volterra_solution`, two solutions of `h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` that
are continuous on `(a, ∞)` and `O(P)` at infinity coincide on `(a, ∞)`. -/
theorem volterra_solution_unique (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
    (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x) (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) {h₁ h₂ : ℝ → E}
    (h₁_cont : ContinuousOn h₁ (Ioi a)) (h₂_cont : ContinuousOn h₂ (Ioi a))
    (h₁_eq : ∀ x ∈ Ioi a, h₁ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₁ v))
    (h₂_eq : ∀ x ∈ Ioi a, h₂ x = ∫ v in Ioi x, K x v • (J v + ψ v • h₂ v))
    (h₁_isBigO : h₁ =O[atTop] P) (h₂_isBigO : h₂ =O[atTop] P) : EqOn h₁ h₂ (Ioi a) := by
  have hIoi (x : ℝ) (hx : a < x) : Ioi a ∩ Ioi x = Ioi x :=
    inter_eq_right.2 (Ioi_subset_Ioi hx.le)
  exact volterra_solution_eqOn ordConnected_Ioi (hK.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩)
    hJ hψ hQ hP0 hQ0 (fun x hx v _ hxv ↦ hKle x v hx hxv)
    (fun x hx ↦ by simpa only [hIoi x hx] using hΦ x hx)
    (fun x hx ↦ by simpa only [hIoi x hx] using hΨ x hx)
    h₁_cont h₂_cont
    (by rwa [Filter.map_val_Ioi_atTop]) (by rwa [Filter.map_val_Ioi_atTop])
    (fun x hx ↦ by simpa only [hIoi x hx] using h₁_eq x hx)
    (fun x hx ↦ by simpa only [hIoi x hx] using h₂_eq x hx)

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
/-- A function satisfying the bound `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` of `exists_volterra_solution`
on `(a, ∞)`, where `Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and `Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖`,
is `O(P)` at infinity. -/
theorem isBigO_of_norm_le_volterra_bound (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x)
    (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x) (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) {h : ℝ → E}
    (hh : ∀ x ∈ Ioi a, ‖h x‖ ≤ P x * (∫ v in Ioi x, Q v * ‖J v‖) *
      Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖)) :
    h =O[atTop] P :=
  (isBigO_principal_Ici_of_norm_le_volterra_bound hP0 hQ0 hΦ hΨ hh (a + 1)
    (lt_add_one a)).mono (le_principal_iff.2 (Ici_mem_atTop _))

/-- **Volterra integral equations, bound.** Let `J`, `ψ` and `Q` be continuous on `(a, ∞)`,
with `P, Q ≥ 0` there, `‖K x v‖ ≤ P x * Q v` for `a < x ≤ v`, and let
`Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and `Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖` converge for every
`x > a`. Then every solution of `h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` that is
continuous on `(a, ∞)` and `O(P)` at infinity satisfies `‖h x‖ ≤ P x * Φ x * exp (Ψ x)` for every
`x > a`. -/
theorem norm_volterra_solution_le
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
    (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x) (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) {h : ℝ → E}
    (h_cont : ContinuousOn h (Ioi a))
    (h_eq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (h_isBigO : h =O[atTop] P) {x : ℝ} (hx : x ∈ Ioi a) :
    ‖h x‖ ≤ P x * (∫ v in Ioi x, Q v * ‖J v‖) * Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖) := by
  have _ := hJ
  have hIoi (y : ℝ) (hy : a < y) : Ioi a ∩ Ioi y = Ioi y :=
    inter_eq_right.2 (Ioi_subset_Ioi hy.le)
  simpa only [hIoi x hx] using norm_volterra_solution_le_on ordConnected_Ioi hψ hQ hP0 hQ0
    (fun x hx v _ hxv ↦ hKle x v hx hxv)
    (fun y hy ↦ by simpa only [hIoi y hy] using hΦ y hy)
    (fun y hy ↦ by simpa only [hIoi y hy] using hΨ y hy)
    h_cont (by rwa [Filter.map_val_Ioi_atTop])
    (fun y hy ↦ by simpa only [hIoi y hy] using h_eq y hy) x hx

/-- **Volterra integral equations, existence and uniqueness.** Under the hypotheses of
`exists_volterra_solution`, the equation `h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` has, on
`(a, ∞)`, exactly one solution that is continuous there and `O(P)` at infinity: the restrictions
to `(a, ∞)` of all such solutions `h : ℝ → E` coincide. Values outside `(a, ∞)` are not
constrained by the equation, so uniqueness is stated for the restriction. -/
theorem existsUnique_volterra_solution [CompleteSpace E]
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a))
    (hP : ContinuousOn P (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
    (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x) (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x)) :
    ∃! g : Ioi a → E, ∃ h : ℝ → E, (Ioi a).domRestrict h = g ∧ ContinuousOn h (Ioi a) ∧
      (∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)) ∧ h =O[atTop] P := by
  obtain ⟨h, hh_cont, hh_eq, hh_le⟩ :=
    exists_volterra_solution hK hJ hψ hP hQ hP0 hQ0 hKle hΦ hΨ
  have hh_isBigO := isBigO_of_norm_le_volterra_bound hP0 hQ0 hΦ hΨ hh_le
  refine ⟨(Ioi a).domRestrict h, ⟨h, rfl, hh_cont, hh_eq, hh_isBigO⟩, ?_⟩
  rintro _ ⟨h', rfl, hh'_cont, hh'_eq, hh'_isBigO⟩
  funext x
  exact volterra_solution_unique hK hJ hψ hQ hP0 hQ0 hKle hΦ hΨ hh'_cont hh_cont hh'_eq hh_eq
    hh'_isBigO hh_isBigO x.property

end Uniqueness

/-! ### The sharper bound when the forcing is dominated by the coefficient -/

/-- **Volterra integral equations, sharper bound on a ray.** Let `‖K x v‖ ≤ Q v` for
`a < x ≤ v` and `‖J v‖ ≤ ‖ψ v‖` for `v > a`, and let `x > a` be such that
`Φ x = ∫ v in Ioi x, Q v * ‖ψ v‖` converges. Then every solution of the Volterra equation
`h y = ∫ v in Ioi y, K y v • (J v + ψ v • h v)` on `[x, ∞)` that is bounded on `[x, ∞)`
satisfies `‖h x‖ ≤ exp (Φ x) - 1`.

This is Olver's sharper bound `|h(x)| ≤ e^{P₀ Φ(x)} - 1` for a constant `P = P₀` and `J = ψ`
(Chapter 6, Theorem 10.1), with the constant `P₀` absorbed into `Q`; the form with `P₀` for
continuous solutions on `(a, ∞)` is `norm_volterra_solution_le_exp_sub_one`. When
`‖J v‖ = ‖ψ v‖`, for example when `J = ψ`, it improves on the bound `Φ x * exp (Φ x)` that
`norm_volterra_solution_le_of_isBigO_principal_Ici` gives with `P = 1`, since `e^t - 1 ≤ t e^t`
for `t ≥ 0`. For a forcing `J` with `‖J v‖ < ‖ψ v‖` the comparison is with that bound after
replacing `‖J‖` by `‖ψ‖`, which only enlarges it; the general bound itself can then be smaller,
for example `0` when `J = 0`. -/
theorem norm_volterra_solution_le_exp_sub_one_of_isBigO_principal_Ici
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ Q v) (hJψ : ∀ v ∈ Ioi a, ‖J v‖ ≤ ‖ψ v‖) {x : ℝ}
    (hx : a < x) {h : ℝ → E}
    (h_eq : ∀ y ∈ Ici x, h y = ∫ v in Ioi y, K y v • (J v + ψ v • h v))
    (hΦ : IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (Ioi x))
    (h_isBigO : h =O[𝓟 (Ici x)] fun _ ↦ (1 : ℝ)) :
    ‖h x‖ ≤ Real.exp (∫ v in Ioi x, Q v * ‖ψ v‖) - 1 := by
  obtain ⟨C, hC⟩ := isBigO_principal.1 h_isBigO
  -- Grönwall's inequality applies to `1 + ‖h‖`, with `P = 1`
  have hle := le_mul_exp_integral_Ioi_of_le_mul_add_integral_Ioi (u := fun y ↦ 1 + ‖h y‖)
    (P := fun _ ↦ 1)
    (g := fun v ↦ Q v * ‖ψ v‖) (A := 1) (C := 1 + C) (by simpa only [one_mul] using hΦ)
    (fun y hy ↦ by have := hC y hy; rw [norm_one, mul_one] at this; linarith)
    fun y (hy : x ≤ y) b hb hgb ↦ by
    have hya := hx.trans_le hy
    rw [one_mul, h_eq y hy]
    gcongr
    refine norm_integral_le_of_norm_le hgb ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : y < v)
    have hKv := hKle y v hya hv.le
    have hQv : 0 ≤ Q v := (norm_nonneg _).trans hKv
    have hF : ‖J v + ψ v • h v‖ ≤ ‖ψ v‖ * (1 + ‖h v‖) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, mul_add, mul_one]
      gcongr
      exact hJψ v (hya.trans hv)
    rw [norm_smul, mul_assoc]
    exact mul_le_mul hKv (hF.trans (by gcongr; exact hb v hv)) (norm_nonneg _) hQv
  simp only [one_mul] at hle
  linarith

/-- **Volterra integral equations, sharper bound.** If the kernel bound is
`‖K x v‖ ≤ P₀ * Q v` with a constant `P₀`, and the forcing is dominated by the coefficient,
`‖J v‖ ≤ ‖ψ v‖` (for instance `J = ψ` when `E = 𝕜`), then every solution of
`h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` that is continuous on `(a, ∞)` and bounded at
infinity satisfies `‖h x‖ ≤ exp (P₀ * ∫ v in Ioi x, Q v * ‖ψ v‖) - 1` for every `x > a`.
For `J = ψ` this sharpens the bound of `norm_volterra_solution_le`, which then reads
`‖h x‖ ≤ P₀ Φ x * exp (P₀ Φ x)` with `Φ x = ∫ v in Ioi x, Q v * ‖ψ v‖`. -/
theorem norm_volterra_solution_le_exp_sub_one {P₀ : ℝ}
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P₀ * Q v) (hJψ : ∀ v ∈ Ioi a, ‖J v‖ ≤ ‖ψ v‖)
    (hψint : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (Ioi x)) {h : ℝ → E}
    (h_cont : ContinuousOn h (Ioi a))
    (h_eq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (h_isBigO : h =O[atTop] fun _ ↦ (1 : ℝ)) {x : ℝ} (hx : x ∈ Ioi a) :
    ‖h x‖ ≤ Real.exp (P₀ * ∫ v in Ioi x, Q v * ‖ψ v‖) - 1 := by
  -- `h` is bounded on `[x, ∞)`, and the bound on a ray applies with the weight `P₀ * Q`
  have hb : h =O[𝓟 (Ici x)] fun _ ↦ (1 : ℝ) :=
    h_isBigO.isBigO_principal_Ici_of_continuousOn (h_cont.mono (Ici_subset_Ioi.2 hx))
      continuousOn_const fun _ _ ↦ by simp
  have hint : IntegrableOn (fun v ↦ P₀ * Q v * ‖ψ v‖) (Ioi x) := by
    have := (hψint x hx).const_mul P₀
    simp only [← mul_assoc] at this
    exact this
  have hle := norm_volterra_solution_le_exp_sub_one_of_isBigO_principal_Ici
    (Q := fun v ↦ P₀ * Q v) hKle hJψ hx (fun y hy ↦ h_eq y (lt_of_lt_of_le hx hy)) hint hb
  simp_rw [mul_assoc] at hle
  rwa [integral_const_mul] at hle

omit [NormedSpace 𝕜 E] [NormedSpace ℝ E] in
/-- A function satisfying the bound `‖h x‖ ≤ exp (Φ x) - 1` of
`norm_volterra_solution_le_exp_sub_one` on `(a, ∞)`, where `Φ x = ∫ v in Ioi x, Q v * ‖ψ v‖`
with `Q ≥ 0`, is bounded on `[x, ∞)` for every `x > a`. -/
theorem isBigO_principal_Ici_one_of_norm_le_exp_sub_one (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (Ioi x)) {h : ℝ → E}
    (hh : ∀ x ∈ Ioi a, ‖h x‖ ≤ Real.exp (∫ v in Ioi x, Q v * ‖ψ v‖) - 1) :
    ∀ x ∈ Ioi a, h =O[𝓟 (Ici x)] fun _ ↦ (1 : ℝ) := fun x (hx : a < x) ↦
  isBigO_principal.2 ⟨Real.exp (∫ v in Ioi x, Q v * ‖ψ v‖) - 1, fun v (hv : x ≤ v) ↦ by
    rw [norm_one, mul_one]
    refine (hh v (hx.trans_le hv)).trans ?_
    gcongr Real.exp ?_ - 1
    exact antitoneOn_integral_Ioi (fun u hu ↦ mul_nonneg (hQ0 u hu) (norm_nonneg _)) hΦ hx
      (hx.trans_le hv) hv⟩

/-- **Volterra integral equations, existence with the sharper bound.** Let `K` be continuous on
`{(x, v) | a < x ≤ v}` with `‖K x v‖ ≤ Q v` there, where `Q` is continuous on `(a, ∞)`, and let
`J`, `ψ` be continuous on `(a, ∞)` with `‖J v‖ ≤ ‖ψ v‖` there and
`Φ x = ∫ v in Ioi x, Q v * ‖ψ v‖` convergent for every `x > a`. Then the Volterra equation
`h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` has a solution, continuous on `(a, ∞)`, such that
`‖h x‖ ≤ exp (Φ x) - 1` for every `x > a`. -/
theorem exists_volterra_solution_exp_sub_one [CompleteSpace E]
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ Q v) (hJψ : ∀ v ∈ Ioi a, ‖J v‖ ≤ ‖ψ v‖)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖ψ v‖) (Ioi x)) :
    ∃ h : ℝ → E, ContinuousOn h (Ioi a) ∧
      (∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)) ∧
      ∀ x ∈ Ioi a, ‖h x‖ ≤ Real.exp (∫ v in Ioi x, Q v * ‖ψ v‖) - 1 := by
  have hQ0 : ∀ v ∈ Ioi a, 0 ≤ Q v := fun v (hv : a < v) ↦
    (norm_nonneg _).trans (hKle v v hv le_rfl)
  -- the general theory applies with `P = 1`
  have hP0 : ∀ x ∈ Ioi a, (0 : ℝ) ≤ (fun _ : ℝ ↦ (1 : ℝ)) x := fun _ _ ↦ zero_le_one
  have hKle' : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ (fun _ : ℝ ↦ (1 : ℝ)) x * Q v :=
    fun x v hx hv ↦ (hKle x v hx hv).trans_eq (one_mul _).symm
  have hΦJ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x) := fun x (hx : a < x) ↦ by
    refine (hΦ x hx).mono' (((hQ.mul hJ.norm).mono (Ioi_subset_Ioi hx.le)).aestronglyMeasurable
      measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : x < v)
    have hQv := hQ0 v (hx.trans hv)
    rw [Real.norm_of_nonneg (mul_nonneg hQv (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hJψ v (hx.trans hv)) hQv
  have hΨ : ∀ x ∈ Ioi a,
      IntegrableOn (fun v ↦ (fun _ : ℝ ↦ (1 : ℝ)) v * Q v * ‖ψ v‖) (Ioi x) := fun x hx ↦ by
    simpa only [one_mul] using hΦ x hx
  obtain ⟨h, h_cont, h_eq, h_le⟩ :=
    exists_volterra_solution hK hJ hψ continuousOn_const hQ hP0 hQ0 hKle' hΦJ hΨ (E := E)
  exact ⟨h, h_cont, h_eq, fun x hx ↦
    norm_volterra_solution_le_exp_sub_one_of_isBigO_principal_Ici hKle hJψ hx
    (fun y hy ↦ h_eq y (lt_of_lt_of_le hx hy)) (hΦ x hx)
    (isBigO_principal_Ici_of_norm_le_volterra_bound hP0 hQ0 hΦJ hΨ h_le x hx)⟩

section Derivative

variable [NormedAlgebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 E] {K₁ : ℝ → ℝ → 𝕜} {P₁ : ℝ → ℝ}

/-- **Volterra integral equations, derivative.** Under the hypotheses of
`exists_volterra_solution`, let `K` vanish on the diagonal and have a partial derivative `K₁` in
its first variable for `a < x < v`, continuous on `{(x, v) | a < x ≤ v}` with
`‖K₁ x v‖ ≤ P₁ x * Q v` there, where `P₁` is continuous on `(a, ∞)`. Then every solution of
`h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` that is continuous on `(a, ∞)` and `O(P)` at
infinity has derivative `∫ v in Ioi x, K₁ x v • (J v + ψ v • h v)` at every `x > a`. -/
theorem hasDerivAt_volterra_solution
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
    (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x) (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x))
    (hKdiag : ∀ x ∈ Ioi a, K x x = 0) (hK₁ : ContinuousOn (uncurry K₁) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hKderiv : ∀ x v, a < x → x < v → HasDerivAt (fun y ↦ K y v) (K₁ x v) x)
    (hP₁ : ContinuousOn P₁ (Ioi a)) (hK₁le : ∀ x v, a < x → x ≤ v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    {h : ℝ → E} (h_cont : ContinuousOn h (Ioi a))
    (h_eq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (h_isBigO : h =O[atTop] P) {x : ℝ} (hx : x ∈ Ioi a) :
    HasDerivAt h (∫ v in Ioi x, K₁ x v • (J v + ψ v • h v)) x := by
  have hIoi (y : ℝ) (hy : a < y) : Ioi a ∩ Ioi y = Ioi y :=
    inter_eq_right.2 (Ioi_subset_Ioi hy.le)
  simpa only [hIoi x hx] using hasDerivAt_volterra_solution_on isOpen_Ioi ordConnected_Ioi
    (hK.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩) hKdiag
    (fun y hy v _ hvy ↦ hKderiv y v hy hvy)
    (hK₁.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩)
    hJ hψ hQ hP₁ hP0 hQ0
    (fun y hy v _ hyv ↦ hKle y v hy hyv) (fun y hy v _ hyv ↦ hK₁le y v hy hyv)
    (fun y hy ↦ by simpa only [hIoi y hy] using hΦ y hy)
    (fun y hy ↦ by simpa only [hIoi y hy] using hΨ y hy)
    h_cont (by rwa [Filter.map_val_Ioi_atTop])
    (fun y hy ↦ by simpa only [hIoi y hy] using h_eq y hy) x hx

/-- **Volterra integral equations, regularity.** Under the hypotheses of
`hasDerivAt_volterra_solution`, every solution of
`h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` that is continuous on `(a, ∞)` and `O(P)` at
infinity is continuously differentiable on `(a, ∞)`. -/
theorem contDiffOn_volterra_solution
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
    (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x) (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x))
    (hKdiag : ∀ x ∈ Ioi a, K x x = 0) (hK₁ : ContinuousOn (uncurry K₁) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hKderiv : ∀ x v, a < x → x < v → HasDerivAt (fun y ↦ K y v) (K₁ x v) x)
    (hP₁ : ContinuousOn P₁ (Ioi a)) (hK₁le : ∀ x v, a < x → x ≤ v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    {h : ℝ → E} (h_cont : ContinuousOn h (Ioi a))
    (h_eq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (h_isBigO : h =O[atTop] P) : ContDiffOn ℝ 1 h (Ioi a) := by
  have hIoi (y : ℝ) (hy : a < y) : Ioi a ∩ Ioi y = Ioi y :=
    inter_eq_right.2 (Ioi_subset_Ioi hy.le)
  exact contDiffOn_volterra_solution_on isOpen_Ioi ordConnected_Ioi
    (hK.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩) hKdiag
    (fun y hy v _ hvy ↦ hKderiv y v hy hvy)
    (hK₁.mono fun _ hp ↦ ⟨hp.1, hp.2.2⟩)
    hJ hψ hQ hP₁ hP0 hQ0
    (fun y hy v _ hyv ↦ hKle y v hy hyv) (fun y hy v _ hyv ↦ hK₁le y v hy hyv)
    (fun y hy ↦ by simpa only [hIoi y hy] using hΦ y hy)
    (fun y hy ↦ by simpa only [hIoi y hy] using hΨ y hy)
    h_cont (by rwa [Filter.map_val_Ioi_atTop])
    (fun y hy ↦ by simpa only [hIoi y hy] using h_eq y hy)

/-- **Volterra integral equations, derivative bound.** Under the hypotheses of
`hasDerivAt_volterra_solution`, and with `P₁ ≥ 0`, every solution of
`h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v)` that is continuous on `(a, ∞)` and `O(P)` at
infinity satisfies `‖deriv h x‖ ≤ P₁ x * Φ x * exp (Ψ x)` for every `x > a`, where
`Φ x = ∫ v in Ioi x, Q v * ‖J v‖` and `Ψ x = ∫ v in Ioi x, P v * Q v * ‖ψ v‖`. -/
theorem norm_deriv_volterra_solution_le
    (hK : ContinuousOn (uncurry K) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hJ : ContinuousOn J (Ioi a)) (hψ : ContinuousOn ψ (Ioi a)) (hQ : ContinuousOn Q (Ioi a))
    (hP0 : ∀ x ∈ Ioi a, 0 ≤ P x) (hQ0 : ∀ x ∈ Ioi a, 0 ≤ Q x)
    (hKle : ∀ x v, a < x → x ≤ v → ‖K x v‖ ≤ P x * Q v)
    (hΦ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ Q v * ‖J v‖) (Ioi x))
    (hΨ : ∀ x ∈ Ioi a, IntegrableOn (fun v ↦ P v * Q v * ‖ψ v‖) (Ioi x))
    (hKdiag : ∀ x ∈ Ioi a, K x x = 0) (hK₁ : ContinuousOn (uncurry K₁) {p | a < p.1 ∧ p.1 ≤ p.2})
    (hKderiv : ∀ x v, a < x → x < v → HasDerivAt (fun y ↦ K y v) (K₁ x v) x)
    (hP₁ : ContinuousOn P₁ (Ioi a)) (hP₁0 : ∀ x ∈ Ioi a, 0 ≤ P₁ x)
    (hK₁le : ∀ x v, a < x → x ≤ v → ‖K₁ x v‖ ≤ P₁ x * Q v)
    {h : ℝ → E} (h_cont : ContinuousOn h (Ioi a))
    (h_eq : ∀ x ∈ Ioi a, h x = ∫ v in Ioi x, K x v • (J v + ψ v • h v))
    (h_isBigO : h =O[atTop] P) {x : ℝ} (hx : x ∈ Ioi a) :
    ‖deriv h x‖ ≤
      P₁ x * (∫ v in Ioi x, Q v * ‖J v‖) * Real.exp (∫ v in Ioi x, P v * Q v * ‖ψ v‖) := by
  have hIoi (y : ℝ) (hy : a < y) : Ioi a ∩ Ioi y = Ioi y :=
    inter_eq_right.2 (Ioi_subset_Ioi hy.le)
  have hle {v} (hv : v ∈ Ioi a) :=
    norm_volterra_solution_le hJ hψ hQ hP0 hQ0 hKle hΦ hΨ h_cont h_eq h_isBigO hv
  have hd := hasDerivAt_volterra_solution hK hJ hψ hQ hP0 hQ0 hKle hΦ hΨ hKdiag hK₁ hKderiv
    hP₁ hK₁le h_cont h_eq h_isBigO hx
  simpa only [hIoi x hx] using norm_deriv_volterra_solution_le_on measurableSet_Ioi hP0 hQ0
    (hP₁0 x hx) (fun v _ hxv ↦ hK₁le x v hx hxv)
    (by simpa only [hIoi x hx] using hΦ x hx)
    (by simpa only [hIoi x hx] using hΨ x hx)
    (fun v hv ↦ by simpa only [hIoi v hv.1] using hle hv.1)
    (by simpa only [hIoi x hx] using hd)

end Derivative

end HalfLine

end TauCeti
