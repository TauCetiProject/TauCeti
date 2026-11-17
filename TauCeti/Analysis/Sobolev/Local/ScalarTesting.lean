/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.WeakDeriv.Coordinates
public import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Function.StronglyMeasurable.Nonseparable

/-!
# Dual scalar testing and separability obstructions for Banach-valued local Sobolev maps

For a complete real normed space `F`, continuous linear functionals `ℓ : StrongDual ℝ F` separate
points by Hahn–Banach. Consequently:

1. Applying any `ℓ : StrongDual ℝ F` (or any coordinate evaluation `lp.evalCLM` on `lp G r`)
   carries `MemLpLoc` and `MemWkpLoc` into the corresponding scalar or coordinate class directly
   via `TauCeti.MemLpLoc.clm_comp` and `TauCeti.MemWkpLoc.clm_comp`.
2. Conversely, once a map `u : E → F` and a candidate derivative field `D : E → E →L[ℝ] F` are
   already known to lie in `MemLpLoc p U` (for `1 ≤ p`), scalar weak differentiability of `ℓ ∘ u`
   with derivative `x ↦ ℓ ∘L D x` for every `ℓ : StrongDual ℝ F` suffices to place `u` in
   `MemWkpLoc p U 1`.
3. Without prior Bochner measurability (`AEStronglyMeasurable`), scalar testing does **not**
   suffice on nonseparable targets: for the uncountable orthonormal family
   `u : E → lp (fun _ : E => ℝ) 2`, `x ↦ lp.single 2 x 1` on any nontrivial finite-dimensional
   real normed space `E`, `StrongDual.comp_lp_single_ae_eq_zero` shows `ℓ ∘ u = 0` almost
   everywhere for every `ℓ : StrongDual ℝ (lp (fun _ : E => ℝ) 2)`, so every scalar composition
   `ℓ ∘ u` belongs to `MemWkpLoc p U k` of every order `k` and exponent `p`. Yet
   `TauCeti.not_aestronglyMeasurable_lp_single` shows `u` fails Bochner strong measurability on
   every set of positive measure, so `u` fails `MemLpLoc p U` and `MemWkpLoc p U k` on every domain
   with nonempty interior.

## Main declarations

* `TauCeti.memWkpLoc_one_of_forall_strongDual`,
  `TauCeti.memWkpLoc_one_opens_of_forall_strongDual`: sufficiency of dual testing for
  `MemWkpLoc p U 1` once `u` and `D` lie in `MemLpLoc p U` (`1 ≤ p`).
* `TauCeti.memWkpLoc_strongDual_comp_lp_single`, `TauCeti.not_memLpLoc_lp_single`,
  `TauCeti.not_memWkpLoc_lp_single`: local Sobolev membership of dual compositions versus failure
  of `MemLpLoc` and `MemWkpLoc` for `x ↦ lp.single 2 x 1`.
* `TauCeti.forall_strongDual_memWkpLoc_and_not_memLpLoc_lp_single`: on any domain `U` with
  nonempty interior in a nontrivial finite-dimensional space, all scalar dual compositions and
  coordinates lie in `MemWkpLoc p U k`, whereas the map itself lies in neither `MemLpLoc p U` nor
  `MemWkpLoc p U k`.

## References

* W. Arendt, M. Kreuter, *Mapping theorems for Sobolev spaces of vector-valued functions*,
  Studia Math. 240 (2018), 275–299.
* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces*, Vol. I,
  Theorem 1.1.20 (Pettis measurability theorem).
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

/-! ### Dual testing and Bochner integrability -/

section StrongDual

/-- **Sufficiency of dual scalar testing for `MemWkpLoc` of order `1`.** Once `u : E → F` and a
candidate derivative field `D : E → E →L[ℝ] F` into a complete space `F` already belong to
`MemLpLoc p U` with `1 ≤ p`, `u` belongs to `MemWkpLoc p U 1` as soon as `ℓ ∘ u` has weak
derivative `x ↦ ℓ ∘L D x` on `interior U` for every `ℓ : StrongDual ℝ F`. -/
theorem memWkpLoc_one_of_forall_strongDual {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [LocallyCompactSpace E] [MeasureSpace E] [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {p : ℝ≥0∞} {U : Set E} {u : E → F} (D : E → E →L[ℝ] F) (hp : 1 ≤ p)
    (hu : MemLpLoc p U u) (hD : MemLpLoc p U D)
    (h : ∀ ℓ : StrongDual ℝ F,
      HasWeakFDerivOn volume (Opens.interior U) (fun x => ℓ (u x)) (fun x => ℓ.comp (D x))) :
    MemWkpLoc p U 1 u := by
  have hu_int : LocallyIntegrableOn u (Opens.interior U) volume :=
    (hu.mono_set interior_subset).locallyIntegrableOn hp isOpen_interior.isLocallyClosed
  have hD_int : ∀ v : E, LocallyIntegrableOn (fun x => D x v) (Opens.interior U) volume := fun v =>
    ((hD.mono_set interior_subset).clm_comp
      (ContinuousLinearMap.apply ℝ F v)).locallyIntegrableOn hp isOpen_interior.isLocallyClosed
  exact memWkpLoc_one_iff.2 ⟨hu, D, hasWeakFDerivOn_of_forall_strongDual hu_int hD_int h, hD⟩

/-- **Sufficiency of dual scalar testing on an open set.** For an open set `Ω : Opens E` and
`1 ≤ p`, local `Lᵖ` bounds on `u` and `D` together with scalar weak differentiability against all
`ℓ : StrongDual ℝ F` give `MemWkpLoc p Ω 1 u`. -/
theorem memWkpLoc_one_opens_of_forall_strongDual {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [LocallyCompactSpace E] [MeasureSpace E] [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {p : ℝ≥0∞} {Ω : Opens E} {u : E → F} (D : E → E →L[ℝ] F) (hp : 1 ≤ p)
    (hu : MemLpLoc p Ω u) (hD : MemLpLoc p Ω D)
    (h : ∀ ℓ : StrongDual ℝ F,
      HasWeakFDerivOn volume Ω (fun x => ℓ (u x)) (fun x => ℓ.comp (D x))) :
    MemWkpLoc p Ω 1 u := by
  refine memWkpLoc_one_of_forall_strongDual D hp hu hD fun ℓ => ?_
  rw [Opens.interior_coe]
  exact h ℓ

end StrongDual

/-! ### Non-sufficiency of scalar testing without Bochner measurability -/

section NormedDomain

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

/-- On any nontrivial finite-dimensional real normed space, every continuous linear functional
composed with `x ↦ lp.single 2 x 1` belongs to `MemWkpLoc p U k` for every exponent `p`, set `U`,
and order `k`. -/
theorem memWkpLoc_strongDual_comp_lp_single (p : ℝ≥0∞) (U : Set E) (k : ℕ)
    (ℓ : StrongDual ℝ (lp (fun _ : E => ℝ) 2)) :
    MemWkpLoc p U k (fun x : E => ℓ (lp.single (E := fun _ : E => ℝ) 2 x 1)) :=
  memWkpLoc_zero_fun.congr_ae <|
    ae_restrict_of_ae (ℓ.comp_lp_single_ae_eq_zero (μ := volume) (fun _ => (1 : ℝ))).symm

/-- On any set `U` with nonempty interior in a nontrivial finite-dimensional real normed space,
`x ↦ lp.single 2 x 1` fails `MemLpLoc p U` for every exponent `p : ℝ≥0∞` (including `0` and `∞`),
because it is not `AEStronglyMeasurable` on any closed ball of positive radius inside `U`. -/
theorem not_memLpLoc_lp_single {U : Set E} (hU : (interior U).Nonempty) (p : ℝ≥0∞) :
    ¬ MemLpLoc p U (fun x : E => lp.single (E := fun _ : E => ℝ) 2 x 1) := by
  obtain ⟨x₀, hx₀⟩ := hU
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x₀ hx₀
  have hsub : Metric.closedBall x₀ (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans (hball.trans interior_subset)
  have hpos_ball : 0 < (volume : Measure E) (Metric.ball x₀ (r / 2)) :=
    Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.2 (half_pos hr))
  have hpos : (volume : Measure E) (Metric.closedBall x₀ (r / 2)) ≠ 0 :=
    (hpos_ball.trans_le (measure_mono Metric.ball_subset_closedBall)).ne'
  intro hmem
  exact not_aestronglyMeasurable_lp_single (fun _ _ => one_ne_zero) hpos
    (memLpLoc_iff.1 hmem (Metric.closedBall x₀ (r / 2)) hsub
      (isCompact_closedBall x₀ (r / 2))).aestronglyMeasurable

/-- On any set `U` with nonempty interior in a nontrivial finite-dimensional real normed space,
`x ↦ lp.single 2 x 1` fails `MemWkpLoc p U k` for every exponent `p : ℝ≥0∞` and order `k : ℕ`. -/
theorem not_memWkpLoc_lp_single {U : Set E} (hU : (interior U).Nonempty) (p : ℝ≥0∞) (k : ℕ) :
    ¬ MemWkpLoc p U k (fun x : E => lp.single (E := fun _ : E => ℝ) 2 x 1) := fun h =>
  not_memLpLoc_lp_single hU p h.memLpLoc

/-- **Scalar dual testing and coordinatewise membership do not imply `MemLpLoc` or `MemWkpLoc`
without Bochner measurability.** For `u : E → lp (fun _ : E => ℝ) 2`, `x ↦ lp.single 2 x 1` on any
domain `U` with nonempty interior in a nontrivial finite-dimensional space `E`, every scalar
composition `ℓ ∘ u` (`ℓ : StrongDual ℝ _`) and every coordinate `x ↦ u x y` belongs to
`MemWkpLoc p U k` for all `p` and `k`, while `u` itself belongs to neither `MemLpLoc p U` nor
`MemWkpLoc p U k`. -/
theorem forall_strongDual_memWkpLoc_and_not_memLpLoc_lp_single {U : Set E}
    (hU : (interior U).Nonempty) (p : ℝ≥0∞) (k : ℕ) :
    (∀ ℓ : StrongDual ℝ (lp (fun _ : E => ℝ) 2),
      MemWkpLoc p U k (fun x : E => ℓ (lp.single (E := fun _ : E => ℝ) 2 x 1))) ∧
    (∀ y : E, MemWkpLoc p U k (fun x : E => lp.single (E := fun _ : E => ℝ) 2 x 1 y)) ∧
    ¬ MemLpLoc p U (fun x : E => lp.single (E := fun _ : E => ℝ) 2 x 1) ∧
    ¬ MemWkpLoc p U k (fun x : E => lp.single (E := fun _ : E => ℝ) 2 x 1) :=
  ⟨memWkpLoc_strongDual_comp_lp_single p U k,
    fun y => memWkpLoc_strongDual_comp_lp_single p U k (lp.evalCLM ℝ (fun _ : E => ℝ) 2 y),
    not_memLpLoc_lp_single hU p, not_memWkpLoc_lp_single hU p k⟩

end NormedDomain

end TauCeti
