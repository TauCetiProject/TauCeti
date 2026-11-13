/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.LiouvilleMeasure
public import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Support

import TauCeti.MeasureTheory.Measure.Support

/-!
# The Duistermaat–Heckman measure

Let `σ` be a two-form on a manifold `M` modelled on a space of dimension `2 * n`, and let
`μ : M → F` be a map, typically the moment map `μ : M → 𝔱*` of a Hamiltonian torus action. The
**Duistermaat–Heckman measure** (`TauCeti.SmoothTwoForm.duistermaatHeckmanMeasure σ n μ`) is the
pushforward `μ_* |σⁿ / n!|` of the Liouville measure along `μ`: it measures a set of moment values
by the symplectic volume of its preimage. By the Duistermaat–Heckman theorem, for an effective
action on a compact connected manifold its density with respect to Lebesgue measure is piecewise
polynomial and records the symplectic volumes of the reduced spaces; for a symplectic toric manifold
it is `(2π)ⁿ` times Lebesgue measure on the moment polytope. Those theorems rest on symplectic
reduction and are not proved here.

This file develops the basic properties of the measure that need no reduction theory.

* **Total mass.** For measurable `μ`, the measure of the whole space is the symplectic volume of
  `M` (`TauCeti.SmoothTwoForm.duistermaatHeckmanMeasure_univ`); it is a finite measure on a compact
  manifold (`TauCeti.SmoothTwoForm.isFiniteMeasure_duistermaatHeckmanMeasure`).
* **Properness.** If `μ` is a proper map to a Hausdorff space, the measure is finite on compact
  sets (`TauCeti.SmoothTwoForm.isFiniteMeasureOnCompacts_duistermaatHeckmanMeasure`), hence locally
  finite when the target is locally compact, even when `M` is not compact.
* **Moment map normalizations.** Composing `μ` with a measurable map `g` pushes the measure forward
  along `g` (`TauCeti.SmoothTwoForm.duistermaatHeckmanMeasure_comp`). This covers the two standard
  changes of moment map: shifting `μ` by a constant translates the measure
  (`TauCeti.SmoothTwoForm.duistermaatHeckmanMeasure_add_const`), and restricting the action to a
  subtorus `𝔰 ⊆ 𝔱` replaces `μ` by its composition with the restriction `𝔱* → 𝔰*`.
* **Rescaling and restriction.** Replacing `σ` by `r • σ` multiplies the measure by `|r|ⁿ`
  (`TauCeti.SmoothTwoForm.duistermaatHeckmanMeasure_smul`), and restricting `σ` and `μ` to an open
  subset `U` gives the pushforward of the Liouville measure restricted to `U`
  (`TauCeti.SmoothTwoForm.duistermaatHeckmanMeasure_mpullback_subtypeVal`).
* **Support.** For a nondegenerate form and a continuous map, the support of the measure is the
  closure of the image of `μ` (`TauCeti.SmoothTwoForm.support_duistermaatHeckmanMeasure`).
* **Invariance.** A differentiable homeomorphism `Φ : M → N` with `Φ^* τ = σ`, intertwining the
  maps `μ = ν ∘ Φ`, identifies the two Duistermaat–Heckman measures
  (`Homeomorph.duistermaatHeckmanMeasure_eq`). In particular equivariant symplectomorphisms
  preserving the moment maps preserve the measure.

The measure of the linear model `ℂ^ι` of a torus action at a fixed point is computed in
`TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.DuistermaatHeckman`.

## References

* J. J. Duistermaat and G. J. Heckman, *On the variation in the cohomology of the symplectic form
  of the reduced phase space*, Invent. Math. 69 (1982), 259–268.
* Victor Guillemin, *Moment maps and combinatorial invariants of Hamiltonian `T^n`-spaces*,
  Progress in Mathematics 122, Birkhäuser (1994), Chapter 2.
-/

public section

noncomputable section

open Module MeasureTheory Set
open scoped ContDiff Manifold

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  {n : ℕ} [Fact (finrank ℝ E = 2 * n)] [MeasurableSpace F]

namespace TauCeti

namespace SmoothTwoForm

variable (σ : SmoothTwoForm I M) (n) in
/-- The **Duistermaat–Heckman measure** `μ_* |σⁿ / n!|` of a map `μ : M → F`, typically the moment
map of a Hamiltonian torus action: the pushforward of the Liouville measure of `σ` along `μ`. -/
def duistermaatHeckmanMeasure (μ : M → F) : Measure F :=
  (σ.liouvilleMeasure n).map μ

variable {σ : SmoothTwoForm I M} {μ : M → F}

variable (σ n μ) in
/-- The Duistermaat–Heckman measure is the pushforward of the Liouville measure. -/
theorem duistermaatHeckmanMeasure_def :
    σ.duistermaatHeckmanMeasure n μ = (σ.liouvilleMeasure n).map μ :=
  (rfl)

/-- The Duistermaat–Heckman measure of a measurable set of values is the Liouville measure of its
preimage. -/
theorem duistermaatHeckmanMeasure_apply (hμ : Measurable μ) {s : Set F} (hs : MeasurableSet s) :
    σ.duistermaatHeckmanMeasure n μ s = σ.liouvilleMeasure n (μ ⁻¹' s) :=
  Measure.map_apply hμ hs

/-- **The total mass of the Duistermaat–Heckman measure is the symplectic volume.** -/
theorem duistermaatHeckmanMeasure_univ (hμ : Measurable μ) :
    σ.duistermaatHeckmanMeasure n μ univ = σ.liouvilleMeasure n univ := by
  rw [duistermaatHeckmanMeasure_apply hμ MeasurableSet.univ, preimage_univ]

/-- **Changing the moment map.** The Duistermaat–Heckman measure of `g ∘ μ` is the pushforward
along `g` of that of `μ`. For a linear map `g` this is the measure of the restricted action of a
subtorus, and for a translation `g` it is the measure of a shifted moment map. -/
theorem duistermaatHeckmanMeasure_comp {G : Type*} [MeasurableSpace G] {g : F → G}
    (hg : Measurable g) (hμ : Measurable μ) :
    σ.duistermaatHeckmanMeasure n (g ∘ μ) = (σ.duistermaatHeckmanMeasure n μ).map g :=
  (Measure.map_map hg hμ).symm

/-- **Shifting the moment map.** Adding a constant `c` to `μ` translates its Duistermaat–Heckman
measure by `c`. -/
theorem duistermaatHeckmanMeasure_add_const [Add F] [MeasurableAdd F] (hμ : Measurable μ) (c : F) :
    σ.duistermaatHeckmanMeasure n (fun x ↦ μ x + c) =
      (σ.duistermaatHeckmanMeasure n μ).map (· + c) :=
  duistermaatHeckmanMeasure_comp (measurable_add_const c) hμ

/-- **Rescaling the form.** Replacing `σ` by `r • σ` multiplies the Duistermaat–Heckman measure by
`|r|ⁿ`. -/
@[simp]
theorem duistermaatHeckmanMeasure_smul (hμ : Measurable μ) (r : ℝ) :
    (r • σ).duistermaatHeckmanMeasure n μ =
      ENNReal.ofReal (|r| ^ n) • σ.duistermaatHeckmanMeasure n μ := by
  rw [duistermaatHeckmanMeasure_def, duistermaatHeckmanMeasure_def, liouvilleMeasure_smul,
    Measure.map_smul _ hμ.aemeasurable]

/-- **Restriction to an open subset.** The Duistermaat–Heckman measure of the restrictions of `σ`
and of a measurable map `μ` to an open subset `U` is the pushforward along `μ` of the restriction
to `U` of the Liouville measure of `σ`. -/
theorem duistermaatHeckmanMeasure_mpullback_subtypeVal (U : TopologicalSpace.Opens M)
    [LindelofSpace U] (hμ : Measurable μ) :
    duistermaatHeckmanMeasure n (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ)
        (μ ∘ Subtype.val) = ((σ.liouvilleMeasure n).restrict U).map μ := by
  rw [duistermaatHeckmanMeasure_def, ← Measure.map_map hμ measurable_subtype_coe,
    map_liouvilleMeasure_mpullback_subtypeVal]

/-- On a compact manifold the Duistermaat–Heckman measure is finite. -/
instance isFiniteMeasure_duistermaatHeckmanMeasure [CompactSpace M] :
    IsFiniteMeasure (σ.duistermaatHeckmanMeasure n μ) := by
  rw [duistermaatHeckmanMeasure_def]
  infer_instance

/-- **Properness gives finiteness on compact sets.** The Duistermaat–Heckman measure of a proper
map to a Hausdorff space is finite on compact sets, even when `M` is not compact. -/
theorem isFiniteMeasureOnCompacts_duistermaatHeckmanMeasure [TopologicalSpace F] [BorelSpace F]
    [T2Space F] (hμ : IsProperMap μ) :
    IsFiniteMeasureOnCompacts (σ.duistermaatHeckmanMeasure n μ) :=
  Measure.isFiniteMeasureOnCompacts_map_of_isProperMap _ hμ

/-- **Properness gives local finiteness.** The Duistermaat–Heckman measure of a proper map to a
locally compact Hausdorff space, such as the dual of the Lie algebra of a torus, is locally
finite. -/
theorem isLocallyFiniteMeasure_duistermaatHeckmanMeasure [TopologicalSpace F] [BorelSpace F]
    [T2Space F] [WeaklyLocallyCompactSpace F] (hμ : IsProperMap μ) :
    IsLocallyFiniteMeasure (σ.duistermaatHeckmanMeasure n μ) :=
  have := isFiniteMeasureOnCompacts_duistermaatHeckmanMeasure (σ := σ) (n := n) hμ
  inferInstance

/-- **The support of the Duistermaat–Heckman measure.** For a nondegenerate two-form and a
continuous map `μ`, the Duistermaat–Heckman measure charges exactly the closure of the image of
`μ`: a value lies in its support exactly when it is a limit of values of `μ`. -/
theorem support_duistermaatHeckmanMeasure [TopologicalSpace F] [BorelSpace F]
    (hσ : σ.IsNondegenerate) (hμ : Continuous μ) :
    (σ.duistermaatHeckmanMeasure n μ).support = closure (range μ) := by
  have := hσ.isOpenPosMeasure_liouvilleMeasure (n := n)
  exact Measure.support_map_eq_closure_range _ Measure.support_eq_univ hμ

end SmoothTwoForm

end TauCeti

namespace Homeomorph

open TauCeti

variable {H' N : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E H'} [TopologicalSpace N]
  [ChartedSpace H' N] [IsManifold J ∞ N] [MeasurableSpace N] [BorelSpace N] [LindelofSpace N]

/-- **Invariance of the Duistermaat–Heckman measure.** If a differentiable homeomorphism
`Φ : M → N` pulls `τ` back to `σ` and `μ = ν ∘ Φ`, then `σ` and `μ` have the same
Duistermaat–Heckman measure as `τ` and `ν`. In particular an equivariant symplectomorphism
intertwining two moment maps preserves the Duistermaat–Heckman measure. -/
theorem duistermaatHeckmanMeasure_eq {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N}
    (Φ : M ≃ₜ N) (hΦ : MDifferentiable I J Φ) (h : mpullback I J Φ τ.1 = σ.1) {μ : M → F}
    {ν : N → F} (hν : Measurable ν) (hμν : ν ∘ Φ = μ) :
    σ.duistermaatHeckmanMeasure n μ = τ.duistermaatHeckmanMeasure n ν := by
  rw [SmoothTwoForm.duistermaatHeckmanMeasure_def, SmoothTwoForm.duistermaatHeckmanMeasure_def,
    ← hμν, ← Measure.map_map hν Φ.measurable,
    (Φ.measurePreserving_liouvilleMeasure hΦ h).map_eq]

end Homeomorph
