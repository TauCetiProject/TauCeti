/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.StrongUnitary.Basic
public import TauCeti.MeasureTheory.Constructions.Polish.SeparatesPoints

/-!
# Borel structure and matrix-coefficient measurability on `StrongUnitary`

This file equips `TauCeti.StrongUnitary 𝕜 H` with its Borel σ-algebra (`borel _`) and `BorelSpace`
instance, and proves the **matrix-coefficient comparison** (Williams, Lemma D.43).

When `H` is separable, `StrongUnitary 𝕜 H` is Polish, hence a `StandardBorelSpace`, with automatic
`MeasurableMul₂` and `MeasurableInv` instances from Mathlib's Borel-group hierarchy (as well as
`MeasurableSMul₂ (unitary 𝕜) (StrongUnitary 𝕜 H)` once `[MeasurableSpace 𝕜]` and
`[OpensMeasurableSpace 𝕜]` are in scope, and `MeasurableSMul₂ Circle (StrongUnitary ℂ H)` once
`Mathlib.MeasureTheory.Group.Circle` is imported). Applying
`TauCeti.measurableSpace_eq_iSup_comap_of_separatesPoints` to the continuous matrix coefficients
`u ↦ ⟪d i, u (d j)⟫_𝕜` along a countable dense family `d : ι → H` shows that these countably many
coefficients generate the Borel σ-algebra of `StrongUnitary 𝕜 H`, yielding the four-way equivalence
for any map `φ : X → StrongUnitary 𝕜 H` from a measurable space `X`:
1. `Measurable φ`;
2. `∀ η : H, Measurable fun x => φ x η`;
3. `∀ ξ η : H, Measurable fun x => ⟪ξ, φ x η⟫_𝕜`;
4. `∀ i j : ι, Measurable fun x => ⟪d i, φ x (d j)⟫_𝕜` for a countable dense family `d : ι → H`.

## Main declarations

* `TauCeti.StrongUnitary.instMeasurableSpace` and `TauCeti.StrongUnitary.instBorelSpace`: the Borel
  σ-algebra of the strong operator topology on `StrongUnitary 𝕜 H`.
* `TauCeti.StrongUnitary.measurableSpace_eq_iSup_comap_inner_of_dense`: matrix coefficients along a
  countable dense family generate the Borel σ-algebra of `StrongUnitary 𝕜 H`.
* `TauCeti.StrongUnitary.measurable_iff_forall_measurable_apply`,
  `TauCeti.StrongUnitary.measurable_iff_forall_measurable_apply_of_dense`,
  `TauCeti.StrongUnitary.measurable_iff_forall_measurable_inner`, and
  `TauCeti.StrongUnitary.measurable_iff_forall_measurable_inner_of_dense`: the four-way coefficient
  and orbit characterization of Borel measurability into `StrongUnitary 𝕜 H`.

## References

* D. P. Williams, *Crossed Products of C*-Algebras*, Mathematical Surveys and Monographs 134, AMS,
  2007, Lemmas D.20 and D.43.
* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156, Springer,
  1995, Theorem 12.2 and Corollary 15.2.
-/

public noncomputable section

open MeasurableSpace MeasureTheory Topology TopologicalSpace
open scoped InnerProductSpace

namespace TauCeti.StrongUnitary

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- `StrongUnitary 𝕜 H` is equipped with the Borel σ-algebra of its strong operator topology. -/
instance instMeasurableSpace : MeasurableSpace (StrongUnitary 𝕜 H) :=
  borel (StrongUnitary 𝕜 H)

/-- The measurable structure on `StrongUnitary 𝕜 H` is its Borel σ-algebra. -/
instance instBorelSpace : BorelSpace (StrongUnitary 𝕜 H) :=
  ⟨rfl⟩

section Inner

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- **Countable dense matrix coefficients generate the Borel σ-algebra of `StrongUnitary 𝕜 H`**
(Williams, Lemmas D.20 and D.43). -/
theorem measurableSpace_eq_iSup_comap_inner_of_dense {ι : Type*} [Countable ι] {d : ι → H}
    (hd : DenseRange d) :
    (instMeasurableSpace : MeasurableSpace (StrongUnitary 𝕜 H)) =
      ⨆ (i : ι) (j : ι),
        MeasurableSpace.comap (fun u : StrongUnitary 𝕜 H => ⟪d i, u (d j)⟫_𝕜) inferInstance := by
  have : SeparableSpace H := .of_denseRange d hd
  have hgen := measurableSpace_eq_iSup_comap_of_separatesPoints
    (α := StrongUnitary 𝕜 H) (ι := ι × ι) (β := fun _ => 𝕜)
    (f := fun p u => ⟪d p.1, u (d p.2)⟫_𝕜)
    (fun p => (continuous_const.inner (continuous_eval_const (d p.2))).measurable)
    fun u v huv =>
      ext (congrFun <| hd.equalizer (map_continuous u) (map_continuous v) <|
        funext fun j => hd.eq_of_inner_right 𝕜 fun i => huv (i, j))
  exact hgen.trans iSup_prod

/-- **Coefficient comparison (countable dense subset)** (Williams, Lemma D.43): for a countable
dense family `d : ι → H`, a map `φ : X → StrongUnitary 𝕜 H` is Borel-measurable if and only if every
matrix coefficient `x ↦ ⟪d i, φ x (d j)⟫_𝕜` is measurable. -/
theorem measurable_iff_forall_measurable_inner_of_dense {X ι : Type*} [MeasurableSpace X]
    [Countable ι] {d : ι → H} (hd : DenseRange d) {φ : X → StrongUnitary 𝕜 H} :
    Measurable φ ↔ ∀ i j : ι, Measurable fun x => ⟪d i, φ x (d j)⟫_𝕜 := by
  refine ⟨fun hφ i j => (continuous_const.inner (continuous_eval_const (d j))).measurable.comp hφ,
    fun h => ?_⟩
  rw [measurable_iff_comap_le, measurableSpace_eq_iSup_comap_inner_of_dense hd]
  simp_rw [comap_iSup, iSup_le_iff, comap_comp, Function.comp_def, ← measurable_iff_comap_le]
  exact h

/-- **Coefficient comparison (all matrix coefficients)** (Williams, Lemma D.43): for separable `H`,
a map `φ : X → StrongUnitary 𝕜 H` is Borel-measurable if and only if every matrix coefficient
`x ↦ ⟪ξ, φ x η⟫_𝕜` is measurable. -/
theorem measurable_iff_forall_measurable_inner [SeparableSpace H] {X : Type*} [MeasurableSpace X]
    {φ : X → StrongUnitary 𝕜 H} :
    Measurable φ ↔ ∀ ξ η : H, Measurable fun x => ⟪ξ, φ x η⟫_𝕜 := by
  refine ⟨fun hφ ξ η => (continuous_const.inner (continuous_eval_const η)).measurable.comp hφ,
    fun h => ?_⟩
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq H
  exact (measurable_iff_forall_measurable_inner_of_dense hd).2 fun i j => h (d i) (d j)

end Inner

section Apply

variable [MeasurableSpace H] [BorelSpace H]

/-- **Coefficient comparison (dense orbits)** (Williams, Lemma D.43): for a countable dense family
`d : ι → H`, a map `φ : X → StrongUnitary 𝕜 H` is Borel-measurable if and only if every orbit
`x ↦ φ x (d i)` is Borel-measurable into `H`. -/
theorem measurable_iff_forall_measurable_apply_of_dense {X ι : Type*} [MeasurableSpace X]
    [Countable ι] {d : ι → H} (hd : DenseRange d) {φ : X → StrongUnitary 𝕜 H} :
    Measurable φ ↔ ∀ i : ι, Measurable fun x => φ x (d i) := by
  let : MeasurableSpace 𝕜 := borel 𝕜
  have : BorelSpace 𝕜 := ⟨rfl⟩
  refine ⟨fun hφ i => (continuous_eval_const (d i)).measurable.comp hφ, fun h => ?_⟩
  exact (measurable_iff_forall_measurable_inner_of_dense hd).2 fun i j =>
    (continuous_const.inner continuous_id).measurable.comp (h j)

/-- **Coefficient comparison (all orbits)** (Williams, Lemma D.43): for separable `H`, a map
`φ : X → StrongUnitary 𝕜 H` is Borel-measurable if and only if every orbit `x ↦ φ x η` is
Borel-measurable into `H`. -/
theorem measurable_iff_forall_measurable_apply [SeparableSpace H] {X : Type*} [MeasurableSpace X]
    {φ : X → StrongUnitary 𝕜 H} :
    Measurable φ ↔ ∀ η : H, Measurable fun x => φ x η := by
  refine ⟨fun hφ η => (continuous_eval_const η).measurable.comp hφ, fun h => ?_⟩
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq H
  exact (measurable_iff_forall_measurable_apply_of_dense hd).2 fun i => h (d i)

end Apply

end TauCeti.StrongUnitary
